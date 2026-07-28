"""Tests for the advisory cross-process verification concurrency lease.

These exercise the lease with real ``multiprocessing`` workers (no provider
calls, no Lean) to prove that at most ``cap`` processes hold a slot at once,
and unit-test the fail-open branches with injected clock/sleep.
"""

from __future__ import annotations

import multiprocessing as mp
import tempfile
import time
import unittest
from pathlib import Path

from harness import verify_lease as vl


def _worker(lease_dir: str, cap: int, barrier, current, peak, lock, hold_seconds: float) -> None:
    # Line up so every worker races for a slot at the same instant; without a
    # barrier the workers could trivially run one-at-a-time by luck.
    barrier.wait()
    with vl.verify_lease(cap=cap, lease_dir=lease_dir, timeout=30.0, poll=0.01) as reason:
        if reason not in ("acquired", "disabled", "timeout", "reentrant", "no_fcntl", "no_lease_dir"):
            raise AssertionError(f"unexpected reason: {reason}")
        with lock:
            current.value += 1
            if current.value > peak.value:
                peak.value = current.value
        time.sleep(hold_seconds)
        with lock:
            current.value -= 1


def _run_workers(cap: int, workers: int, hold_seconds: float = 0.2) -> int:
    ctx = mp.get_context("spawn")
    with tempfile.TemporaryDirectory(prefix="verity-lease-test-") as tmp:
        barrier = ctx.Barrier(workers)
        current = ctx.Value("i", 0)
        peak = ctx.Value("i", 0)
        lock = ctx.Lock()
        procs = [
            ctx.Process(
                target=_worker,
                args=(tmp, cap, barrier, current, peak, lock, hold_seconds),
            )
            for _ in range(workers)
        ]
        for proc in procs:
            proc.start()
        for proc in procs:
            proc.join(timeout=60)
            if proc.is_alive():  # pragma: no cover - defensive
                proc.terminate()
                raise AssertionError("worker did not finish in time")
            if proc.exitcode != 0:
                raise AssertionError(f"worker exited with {proc.exitcode}")
        return peak.value


class CrossProcessLeaseTests(unittest.TestCase):
    def test_cap_one_serializes(self) -> None:
        peak = _run_workers(cap=1, workers=4)
        self.assertEqual(peak, 1)

    def test_cap_two_allows_two(self) -> None:
        peak = _run_workers(cap=2, workers=4)
        self.assertLessEqual(peak, 2)
        self.assertGreaterEqual(peak, 2)

    def test_disabled_cap_allows_full_parallelism(self) -> None:
        # cap<=0 disables leasing entirely: all workers should overlap, proving
        # the serialization in the cap=1 case is caused by the lease.
        peak = _run_workers(cap=0, workers=4)
        self.assertEqual(peak, 4)


class FailOpenUnitTests(unittest.TestCase):
    def test_disabled_yields_disabled(self) -> None:
        with vl.verify_lease(cap=0) as reason:
            self.assertEqual(reason, "disabled")

    def test_timeout_fails_open(self) -> None:
        # Hold the single slot in-process via a raw flock, then a second
        # acquisition with an immediate deadline must fail open with "timeout".
        with tempfile.TemporaryDirectory() as tmp:
            import fcntl

            slot = Path(tmp) / "slot-0.lock"
            holder = open(slot, "a+")
            fcntl.flock(holder.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
            try:
                fake_clock = iter([0.0, 0.0, 100.0])

                def clock() -> float:
                    return next(fake_clock)

                slept: list[float] = []
                with vl.verify_lease(
                    cap=1,
                    lease_dir=tmp,
                    timeout=1.0,
                    poll=0.5,
                    clock=clock,
                    sleep=slept.append,
                ) as reason:
                    self.assertEqual(reason, "timeout")
            finally:
                fcntl.flock(holder.fileno(), fcntl.LOCK_UN)
                holder.close()

    def test_reentrant_passthrough(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            with vl.verify_lease(cap=1, lease_dir=tmp) as outer:
                self.assertEqual(outer, "acquired")
                with vl.verify_lease(cap=1, lease_dir=tmp) as inner:
                    self.assertEqual(inner, "reentrant")

    def test_no_fcntl_fails_open(self) -> None:
        original = vl.fcntl
        vl.fcntl = None
        try:
            with vl.verify_lease(cap=1) as reason:
                self.assertEqual(reason, "no_fcntl")
        finally:
            vl.fcntl = original

    def test_unwritable_lease_dir_fails_open(self) -> None:
        with vl.verify_lease(cap=1, lease_dir="/proc/nonexistent/verity-lease") as reason:
            self.assertEqual(reason, "no_lease_dir")

    def test_env_cap_override(self) -> None:
        import os
        from unittest import mock

        with mock.patch.dict(os.environ, {vl.ENV_CAP: "0"}):
            with vl.verify_lease() as reason:
                self.assertEqual(reason, "disabled")


if __name__ == "__main__":
    unittest.main()

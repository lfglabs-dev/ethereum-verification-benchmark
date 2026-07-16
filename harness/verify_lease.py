"""Advisory cross-process concurrency lease for memory-heavy Lean work.

Motivation: multi-provider benchmark runs happily overlap their model-API
latency, but the Lean verification/build step is memory-heavy (a single
``lean`` can peak tens of GB). Running several of those in parallel across
independent runner processes has OOM-killed the host kernel mid-verification,
which corrupts comparison artifacts and reads as a spurious proof failure.

This module gives those independent processes a shared, *advisory* counting
semaphore built on ``fcntl.flock`` over a small pool of slot files. It lets at
most ``cap`` verifications run concurrently across every process on the host
(default 1), while the cheap model-API portion of each run stays fully
parallel.

Design constraints:

* **Advisory / fail-open.** The lease is an optimization, never a correctness
  gate. If the lease directory cannot be created, ``fcntl`` is unavailable, or
  acquisition times out, we *proceed anyway* rather than deadlock or crash a
  benchmark run. The context manager yields a short reason string describing
  what happened so callers/tests can observe it.
* **Provider-neutral / fair.** Slots are anonymous. Whoever wins the ``flock``
  race next runs next; there is no per-provider reservation or priority.
* **Bounded.** Acquisition waits at most ``timeout`` seconds, then fails open.
* **Re-entrant per thread.** A thread that already holds the lease passes
  straight through nested acquisitions (reason ``"reentrant"``) so the same
  process verifying inside an already-leased section never self-deadlocks.
* **Testable without provider calls.** ``clock`` and ``sleep`` are injectable,
  and the whole thing is exercised with plain ``multiprocessing`` workers.
"""

from __future__ import annotations

import contextlib
import os
import tempfile
import threading
import time
from pathlib import Path
from typing import Callable, Iterator

try:
    import fcntl
except ImportError:  # pragma: no cover - non-POSIX fallback
    fcntl = None  # type: ignore[assignment]

ENV_CAP = "DEFAULT_HARNESS_VERIFY_CONCURRENCY"
ENV_LEASE_DIR = "DEFAULT_HARNESS_VERIFY_LEASE_DIR"
ENV_TIMEOUT = "DEFAULT_HARNESS_VERIFY_LEASE_TIMEOUT_SECONDS"
ENV_POLL = "DEFAULT_HARNESS_VERIFY_LEASE_POLL_SECONDS"

_DEFAULT_CAP = 1
_DEFAULT_TIMEOUT_SECONDS = 1800.0
_DEFAULT_POLL_SECONDS = 0.25

# Per-thread re-entrancy flag: True while this thread is inside a real
# (non-passthrough) lease section, so nested acquisitions short-circuit.
_local = threading.local()


def _env_int(name: str, default: int) -> int:
    raw = os.environ.get(name)
    if raw is None or not raw.strip():
        return default
    try:
        return int(raw.strip())
    except ValueError:
        return default


def _env_float(name: str, default: float) -> float:
    raw = os.environ.get(name)
    if raw is None or not raw.strip():
        return default
    try:
        return float(raw.strip())
    except ValueError:
        return default


def _resolve_cap(cap: int | None) -> int:
    if cap is None:
        cap = _env_int(ENV_CAP, _DEFAULT_CAP)
    return cap


def _resolve_lease_dir(lease_dir: Path | str | None) -> Path:
    if lease_dir is None:
        env_dir = os.environ.get(ENV_LEASE_DIR)
        if env_dir and env_dir.strip():
            lease_dir = env_dir.strip()
        else:
            lease_dir = Path(tempfile.gettempdir()) / "verity-verify-lease"
    return Path(lease_dir)


def _held() -> bool:
    return bool(getattr(_local, "held", False))


@contextlib.contextmanager
def verify_lease(
    *,
    cap: int | None = None,
    lease_dir: Path | str | None = None,
    timeout: float | None = None,
    poll: float | None = None,
    label: str = "",
    clock: Callable[[], float] = time.monotonic,
    sleep: Callable[[float], None] = time.sleep,
) -> Iterator[str]:
    """Hold at most ``cap`` concurrent verification slots across processes.

    Yields a short reason string describing how the slot was obtained or why
    the lease fell open:

    * ``"acquired"`` - a real cross-process slot was taken and is held.
    * ``"reentrant"`` - this thread already holds a slot; passed through.
    * ``"disabled"`` - ``cap <= 0``; leasing is turned off.
    * ``"no_fcntl"`` - ``fcntl`` unavailable on this platform.
    * ``"no_lease_dir"`` - the lease directory could not be prepared.
    * ``"timeout"`` - waited ``timeout`` seconds without a free slot; proceeded.

    The body always runs exactly once regardless of the reason: the lease is
    advisory and must never block real work.
    """
    cap = _resolve_cap(cap)
    if cap <= 0:
        yield "disabled"
        return
    if fcntl is None:
        yield "no_fcntl"
        return
    if _held():
        # Same thread already inside a leased section; nesting must not
        # self-deadlock on our own exclusive locks.
        yield "reentrant"
        return

    directory = _resolve_lease_dir(lease_dir)
    try:
        directory.mkdir(parents=True, exist_ok=True)
    except OSError:
        yield "no_lease_dir"
        return

    if timeout is None:
        timeout = _env_float(ENV_TIMEOUT, _DEFAULT_TIMEOUT_SECONDS)
    if poll is None:
        poll = _env_float(ENV_POLL, _DEFAULT_POLL_SECONDS)
    if poll <= 0:
        poll = _DEFAULT_POLL_SECONDS

    slot_paths = [directory / f"slot-{index}.lock" for index in range(cap)]
    handles = []
    for path in slot_paths:
        try:
            handles.append(open(path, "a+"))
        except OSError:
            # Could not open one of the slot files; close what we opened and
            # fail open rather than partially lease.
            for opened in handles:
                opened.close()
            yield "no_lease_dir"
            return

    acquired_handle = None
    deadline = clock() + timeout
    try:
        while True:
            for handle in handles:
                try:
                    fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
                except OSError:
                    continue
                acquired_handle = handle
                break
            if acquired_handle is not None:
                break
            if clock() >= deadline:
                break
            sleep(poll)

        if acquired_handle is None:
            # Bounded wait elapsed: proceed anyway (advisory / fail-open).
            yield "timeout"
            return

        _local.held = True
        try:
            yield "acquired"
        finally:
            _local.held = False
            try:
                fcntl.flock(acquired_handle.fileno(), fcntl.LOCK_UN)
            except OSError:
                pass
    finally:
        for handle in handles:
            handle.close()

from __future__ import annotations

import os
import sys
import tempfile
import time
import unittest
from pathlib import Path

from harness import lean_check, process_utils, verifier

SAMPLE = "obtain ⟨h1, h2⟩ := hPre\n∀ x ∈ s, α → β \U0001d4d0\r\nend\n"


class DecodeChunksTests(unittest.TestCase):
    def test_split_mid_codepoint_at_every_offset_is_lossless(self) -> None:
        data = SAMPLE.encode("utf-8")
        expected = data.decode("utf-8").replace("\r\n", "\n")
        for cut in range(len(data) + 1):
            with self.subTest(cut=cut):
                self.assertEqual(process_utils.decode_chunks([data[:cut], data[cut:]]), expected)

    def test_8k_chunk_boundary_inside_three_byte_codepoint(self) -> None:
        # Regression: "'utf-8' codec can't decode byte 0xe2 in position 8191".
        data = b"x" * 8191 + "⟨tail⟩".encode("utf-8")
        chunks = [data[i : i + 8192] for i in range(0, len(data), 8192)]
        self.assertEqual(chunks[0][-1], 0xE2)
        self.assertEqual(process_utils.decode_chunks(chunks), data.decode("utf-8"))

    def test_byte_identical_for_valid_utf8_without_newline_translation(self) -> None:
        data = SAMPLE.encode("utf-8")
        self.assertEqual(process_utils.decode_chunks([data], translate_newlines=False), data.decode("utf-8"))

    def test_truncated_tail_is_replaced_not_raised(self) -> None:
        data = b"x" * 8191 + b"\xe2"
        self.assertEqual(process_utils.decode_output(data), "x" * 8191 + "�")

    def test_str_and_none_pass_through(self) -> None:
        self.assertEqual(process_utils.decode_output(None), "")
        self.assertEqual(process_utils.decode_output("already text"), "already text")

    def test_lean_check_tolerates_truncated_utf8_output(self) -> None:
        script = "import sys; sys.stdout.buffer.write(b'x' * 8191 + b'\\xe2'); sys.exit(1)"
        with tempfile.TemporaryDirectory() as tmp:
            code, output = lean_check._run_lean_command_unleased(Path(tmp), [sys.executable, "-c", script], 30)
        self.assertEqual(code, 1)
        self.assertEqual(output, "x" * 8191 + "�")


def _pid_alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    # A zombie still answers kill(0); treat it as dead.
    try:
        with open(f"/proc/{pid}/stat", encoding="utf-8") as handle:
            return handle.read().rsplit(")", 1)[1].split()[0] != "Z"
    except OSError:
        return False


# Parent ("lake") spawns a grandchild ("lean") that sleeps and ignores
# SIGTERM, writes its pid, then sleeps itself.
PARENT_SCRIPT = """
import subprocess, sys, time
child = subprocess.Popen([sys.executable, "-c",
    "import signal, time; signal.signal(signal.SIGTERM, signal.SIG_IGN); time.sleep(600)"])
with open(sys.argv[1], "w") as handle:
    handle.write(str(child.pid))
print("started \u27e8lean\u27e9", flush=True)
time.sleep(600)
"""


class ProcessGroupKillTests(unittest.TestCase):
    def _run_and_get_grandchild(self, runner) -> tuple[object, int]:
        with tempfile.TemporaryDirectory() as tmp:
            pid_file = Path(tmp) / "grandchild.pid"
            started = time.monotonic()
            result = runner(Path(tmp), [sys.executable, "-c", PARENT_SCRIPT, str(pid_file)])
            self.assertLess(time.monotonic() - started, 30)
            grandchild = int(pid_file.read_text(encoding="utf-8"))
        return result, grandchild

    def _assert_dead(self, pid: int) -> None:
        deadline = time.monotonic() + 5
        while _pid_alive(pid) and time.monotonic() < deadline:
            time.sleep(0.05)
        if _pid_alive(pid):
            os.kill(pid, 9)
            self.fail(f"grandchild {pid} survived the timeout kill")

    def test_timeout_kills_grandchild_in_process_group(self) -> None:
        (code, stdout, _stderr, timed_out), grandchild = self._run_and_get_grandchild(
            lambda cwd, command: process_utils.run_in_process_group(command, cwd=cwd, timeout=2)
        )
        self.assertTrue(timed_out)
        self.assertEqual(code, 124)
        self.assertIn("started ⟨lean⟩", stdout)
        self._assert_dead(grandchild)

    def test_lean_check_timeout_kills_grandchild(self) -> None:
        (code, output), grandchild = self._run_and_get_grandchild(
            lambda cwd, command: lean_check._run_lean_command_unleased(cwd, command, 2)
        )
        self.assertEqual(code, 124)
        self.assertTrue(output.endswith("\ntimeout"))
        self._assert_dead(grandchild)

    def test_verifier_timeout_kills_grandchild(self) -> None:
        (code, output), grandchild = self._run_and_get_grandchild(
            lambda cwd, command: verifier._run(command, cwd, 2, lease=False)
        )
        self.assertEqual(code, 124)
        self.assertTrue(output.endswith("\ntimeout"))
        self._assert_dead(grandchild)

    def test_completed_command_returns_exit_code(self) -> None:
        code, stdout, stderr, timed_out = process_utils.run_in_process_group(
            [sys.executable, "-c", "import sys; print('ok'); sys.stderr.write('err'); sys.exit(3)"],
            cwd=None,
            timeout=30,
        )
        self.assertEqual((code, stdout, stderr, timed_out), (3, "ok\n", "err", False))


if __name__ == "__main__":
    unittest.main()

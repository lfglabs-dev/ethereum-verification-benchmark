from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

from harness import lean_check, process_utils

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


if __name__ == "__main__":
    unittest.main()

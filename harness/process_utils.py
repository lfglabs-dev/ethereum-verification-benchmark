"""Subprocess helpers shared by the Lean check and verifier paths.

* Output decoding.  ``subprocess`` in text mode decodes captured output with
  strict UTF-8.  When a timed-out ``lake``/``lean`` is killed, its pipe can end
  in the middle of a multi-byte code point (C stdio flushes in 8 KiB blocks),
  which raised ``UnicodeDecodeError ... position 8191: unexpected end of data``
  and turned a plain timeout into a harness error.  Output is therefore
  captured as bytes and decoded with an incremental decoder that tolerates a
  truncated tail; valid UTF-8 decodes byte-for-byte identically.
"""

from __future__ import annotations

import codecs
from collections.abc import Iterable


def decode_chunks(chunks: Iterable[bytes | str], *, translate_newlines: bool = True) -> str:
    """Decode a sequence of byte chunks as UTF-8 without splitting code points.

    Chunk boundaries may fall anywhere, including inside a multi-byte code
    point.  Only genuinely invalid or truncated trailing bytes are replaced
    with U+FFFD.  ``translate_newlines`` mirrors ``text=True`` semantics.
    """
    decoder = codecs.getincrementaldecoder("utf-8")(errors="replace")
    parts: list[str] = []
    for chunk in chunks:
        if isinstance(chunk, str):
            parts.append(chunk)
        elif chunk:
            parts.append(decoder.decode(chunk))
    parts.append(decoder.decode(b"", final=True))
    text = "".join(parts)
    if translate_newlines:
        text = text.replace("\r\n", "\n").replace("\r", "\n")
    return text


def decode_output(data: bytes | str | None) -> str:
    if data is None:
        return ""
    return decode_chunks([data])

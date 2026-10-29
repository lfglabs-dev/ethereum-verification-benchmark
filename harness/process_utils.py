"""Subprocess helpers shared by the Lean check and verifier paths.

Two failure modes motivated this module:

* Output decoding.  ``subprocess`` in text mode decodes captured output with
  strict UTF-8.  When a timed-out ``lake``/``lean`` is killed, its pipe can end
  in the middle of a multi-byte code point (C stdio flushes in 8 KiB blocks),
  which raised ``UnicodeDecodeError ... position 8191: unexpected end of data``
  and turned a plain timeout into a harness error.  Output is therefore
  captured as bytes and decoded with an incremental decoder that tolerates a
  truncated tail; valid UTF-8 decodes byte-for-byte identically.

* Orphaned children.  ``subprocess.run(timeout=...)`` only kills the direct
  child, so ``lake``'s ``lean`` child survived (re-parented to init) and kept
  holding memory and build locks.  Commands are started in their own session
  and the whole process group is terminated on timeout.
"""

from __future__ import annotations

import codecs
import os
import signal
import subprocess
from collections.abc import Iterable, Mapping
from pathlib import Path

TERMINATE_GRACE_SECONDS = 5.0
DRAIN_TIMEOUT_SECONDS = 10.0


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


def _signal_group(process: subprocess.Popen, sig: int) -> None:
    try:
        os.killpg(process.pid, sig)
    except (ProcessLookupError, PermissionError):
        pass


def kill_process_group(process: subprocess.Popen, *, grace_seconds: float = TERMINATE_GRACE_SECONDS) -> None:
    """SIGTERM the process group, escalate to SIGKILL, and reap the leader.

    The group is signalled even when the leader already exited, so that
    grandchildren (``lean`` under ``lake``) do not outlive a timeout.
    """
    _signal_group(process, signal.SIGTERM)
    try:
        process.wait(timeout=grace_seconds)
    except subprocess.TimeoutExpired:
        pass
    # Always follow up with SIGKILL: the leader may have exited on SIGTERM
    # while a descendant in the same group ignored or delayed it.
    _signal_group(process, signal.SIGKILL)
    process.wait()


def run_in_process_group(
    command: list[str],
    *,
    cwd: Path | str | None,
    timeout: float,
    env: Mapping[str, str] | None = None,
) -> tuple[int, str, str, bool]:
    """Run ``command`` in a new session; return (code, stdout, stderr, timed_out).

    On timeout the whole process group is terminated and partial output is
    returned.  Output is decoded with :func:`decode_output`.
    """
    process = subprocess.Popen(
        command,
        cwd=cwd,
        env=dict(env) if env is not None else None,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        start_new_session=True,
    )
    try:
        stdout, stderr = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        kill_process_group(process)
        try:
            stdout, stderr = process.communicate(timeout=DRAIN_TIMEOUT_SECONDS)
        except subprocess.TimeoutExpired as exc:
            # A descendant escaped the group and still holds the pipes; do not
            # block forever on it.
            stdout, stderr = exc.stdout, exc.stderr
            for stream in (process.stdout, process.stderr):
                if stream is not None:
                    stream.close()
        return 124, decode_output(stdout), decode_output(stderr), True
    except BaseException:
        kill_process_group(process, grace_seconds=1.0)
        raise
    return int(process.returncode or 0), decode_output(stdout), decode_output(stderr), False

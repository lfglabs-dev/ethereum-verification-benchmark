"""Proof-body patching for the default harness.

Turning a model response (tactic body or whole file) into a candidate
file while preserving the theorem statement byte-identically. Extracted
from runners/lean_tools.py."""

from __future__ import annotations

import re

def _strip_thinking(text: str) -> str:
    return re.sub(r"(?s)<think>.*?</think>\s*", "", text).strip()

def _extract_lean_file(text: str) -> str:
    text = _strip_thinking(text)
    fenced = re.search(r"```(?:lean)?\s*(.*?)```", text, flags=re.DOTALL | re.IGNORECASE)
    if fenced:
        return fenced.group(1).strip() + "\n"
    return text.strip() + "\n"

def _looks_like_full_file(body: str) -> bool:
    return bool(re.search(r"(?m)^\s*(?:import|namespace)\s+\S", body)) and bool(
        re.search(r"(?m)^\s*(?:theorem|lemma)\s+\S", body)
    )

def _indent_proof_body(text: str) -> str:
    body = _extract_lean_file(text)
    theorem_body = re.search(r"(?s)\b(?:theorem|lemma)\s+[A-Za-z0-9_'.]+.*?:=\s*by[ \t]*(?:\n)?", body)
    if theorem_body:
        body = body[theorem_body.end() :]
    body = re.sub(r"(?m)^end\s+[A-Za-z0-9_'.]+\s*$.*", "", body, flags=re.DOTALL)
    lines: list[str] = []
    in_preamble = True
    for raw_line in body.splitlines():
        line = raw_line.rstrip()
        stripped = line.strip()
        if in_preamble and (
            not stripped or stripped.startswith(("import ", "namespace ", "open ", "/--", "-/", "--"))
        ):
            continue
        in_preamble = False
        if stripped.startswith(("Explanation", "This proof", "The proof", "Note:", "```")):
            break
        lines.append(line)
    while lines and not lines[0].strip():
        lines.pop(0)
    while lines and not lines[-1].strip():
        lines.pop()
    if not lines:
        return ""
    # Preserve the proof's relative indentation exactly; only normalize the
    # common left margin so the body sits two spaces under `:= by`.
    min_indent = min(len(line) - len(line.lstrip()) for line in lines if line.strip())
    normalized = [line[min_indent:] if line.strip() else "" for line in lines]
    return "\n".join(f"  {line}" if line else "" for line in normalized) + "\n"

def _patch_proof_body(original: str, proof_body: str) -> str:
    extracted = _extract_lean_file(proof_body)
    if _looks_like_full_file(extracted):
        return extracted
    replacement = ":= by\n" + _indent_proof_body(proof_body)
    pattern = re.compile(
        r":=\s*by\s*(?:--[^\n]*\n\s*)?(?:exact\s+\?_[A-Za-z0-9_']*|sorry|admit)\b",
        re.MULTILINE,
    )
    if pattern.search(original):
        return pattern.sub(lambda _match: replacement.rstrip(), original, count=1) + ("\n" if original.endswith("\n") else "")
    marker = ":= by"
    index = original.find(marker)
    if index == -1:
        return original
    end_index = original.find("\n\nend ", index)
    if end_index == -1:
        end_index = len(original)
    return original[:index] + replacement + original[end_index:]

FORBIDDEN_PROOF_RE = re.compile(r"\b(sorry|admit|axiom)\b|\?_[A-Za-z0-9_']*")

def _contains_forbidden_proof_token(text: str) -> bool:
    return FORBIDDEN_PROOF_RE.search(text) is not None

def _decl_basename(theorem_name: object) -> str | None:
    if not isinstance(theorem_name, str) or not theorem_name:
        return None
    return theorem_name.split(".")[-1]

def _candidate_from_response(original: str, response_text: str, theorem_name: object) -> str:
    return _patch_proof_body(original, response_text)

def _theorem_statement(original: str, theorem_name: object) -> str:
    decl_name = _decl_basename(theorem_name)
    if not decl_name:
        return ""
    pattern = re.compile(
        rf"(?ms)^\s*(?:theorem|lemma)\s+{re.escape(decl_name)}\b.*?:=\s*by",
    )
    match = pattern.search(original)
    if match:
        return original[match.start() : match.end()].rsplit(":=", 1)[0].strip()[:2000]
    generic = re.search(r"(?ms)^\s*(?:theorem|lemma)\s+[A-Za-z0-9_'.]+.*?:=\s*by", original)
    if generic:
        return original[generic.start() : generic.end()].rsplit(":=", 1)[0].strip()[:2000]
    return ""

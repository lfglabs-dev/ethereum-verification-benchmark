#!/usr/bin/env python3
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CASE = ROOT / "cases" / "unlink_xyz" / "pool" / "case.yaml"
FORMAL_AUDIT = ROOT / "Benchmark" / "Cases" / "UnlinkXyz" / "Pool" / "FormalAudit.lean"

AUDIT_TARGET = "7617b3eebcf37ab42124fe570eb7e065cf8c8461"
VERITY_PIN = "7d0ae8b2152d2da6cbafc3480e73fb1b2364670f"

REQUIRED_SNIPPETS = [
    f"upstream_commit: {AUDIT_TARGET}",
    f"audit_target_commit: {AUDIT_TARGET}",
    f"source_ref: https://github.com/unlink-xyz/monorepo@{AUDIT_TARGET}:protocol/contracts/src/UnlinkPool.sol",
    "stage: proof_complete",
    "spec_status: frozen",
    "proof_status: complete",
    f"verity_version: {VERITY_PIN}",
]


def main() -> int:
    errors: list[str] = []
    case_text = CASE.read_text(encoding="utf-8")
    formal_text = FORMAL_AUDIT.read_text(encoding="utf-8")

    for snippet in REQUIRED_SNIPPETS:
        if snippet not in case_text:
            errors.append(f"{CASE.relative_to(ROOT)}: missing `{snippet}`")

    if re.search(r"\bdef\s+\S+\s*:\s*Prop\s*:=\s*False\b", formal_text):
        errors.append(
            f"{FORMAL_AUDIT.relative_to(ROOT)}: abstract audit assumptions must be opaque, not `Prop := False`"
        )

    required_formal_snippets = [
        "opaque groth16_soundness : Prop",
        "opaque authority_binding : Prop",
        "example : countProofState .provedFromConcrete = 24 := by native_decide",
        "example : countProofState .assumed = 9 := by native_decide",
        "example : countProofState .outOfModel = 12 := by native_decide",
        "example : countProofState .counterexample = 3 := by native_decide",
        "example : concreteEvidenceAtoms.length = 17 := by native_decide",
        "example : countEvidenceKind .structuralScan = 11 := by native_decide",
        "example : countEvidenceKind .behavioralStateTheorem = 1 := by native_decide",
        "example : countEvidenceKind .constantManifest = 4 := by native_decide",
        "example : countEvidenceKind .artifactImport = 1 := by native_decide",
    ]
    for snippet in required_formal_snippets:
        if snippet not in formal_text:
            errors.append(f"{FORMAL_AUDIT.relative_to(ROOT)}: missing checked manifest line `{snippet}`")

    if "summary := \"Groth16 knowledge/soundness for the deployed phase-2 verification key" not in formal_text:
        errors.append(
            f"{FORMAL_AUDIT.relative_to(ROOT)}: AP-Ax1 must name the deployed phase-2 verification key boundary"
        )

    if errors:
        print("Unlink formal-audit regression check failed", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1
    print("Unlink formal-audit regression check passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

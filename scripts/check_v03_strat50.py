#!/usr/bin/env python3
"""Fail closed unless the committed v0.3 STRAT-50 panel is reproducible."""
from __future__ import annotations

import hashlib
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
GENERATOR_PATH = ROOT / "scripts" / "generate_stratified_panel.py"
SPEC = importlib.util.spec_from_file_location("generate_stratified_panel", GENERATOR_PATH)
assert SPEC and SPEC.loader
GENERATOR = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GENERATOR)

MANIFEST = ROOT / "benchmark-versions" / "v0.3.json"
PANEL = ROOT / "analysis" / "v0.3_strat50" / "panel.json"
METADATA = ROOT / "analysis" / "v0.3_strat50" / "panel-metadata.json"
CANONICAL_MANIFEST_SHA256 = "98961c8ab23a4855d9eb4422b3a0d87517249ea4c8c98cc6f717cdb8ad7c942e"
CANONICAL_PANEL_SHA256 = "6921cc27d522ecbfd0798e9bca9251526f10923855cc28dde4b22507f92eaf25"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    manifest_sha256 = sha256(MANIFEST)
    panel_sha256 = sha256(PANEL)
    if manifest_sha256 != CANONICAL_MANIFEST_SHA256:
        raise SystemExit(
            f"v0.3 manifest hash changed: expected {CANONICAL_MANIFEST_SHA256}, got {manifest_sha256}"
        )
    if panel_sha256 != CANONICAL_PANEL_SHA256:
        raise SystemExit(
            f"v0.3 STRAT-50 byte identity changed: expected {CANONICAL_PANEL_SHA256}, got {panel_sha256}"
        )
    manifest = json.loads(MANIFEST.read_text())
    actual_panel = json.loads(PANEL.read_text())
    actual_metadata = json.loads(METADATA.read_text())
    expected_panel, expected_metadata = GENERATOR.generate_panel(
        manifest, panel_size=50, seed=42
    )
    expected_panel_bytes = (json.dumps(expected_panel, indent=2) + "\n").encode()
    if PANEL.read_bytes() != expected_panel_bytes:
        raise SystemExit("v0.3 STRAT-50 panel is not canonical byte-for-byte JSON")
    expected_metadata["manifest_sha256"] = f"sha256:{CANONICAL_MANIFEST_SHA256}"
    expected_metadata["panel_sha256"] = f"sha256:{CANONICAL_PANEL_SHA256}"
    expected_metadata_bytes = (json.dumps(expected_metadata, indent=2) + "\n").encode()

    if actual_panel != expected_panel:
        raise SystemExit(
            "v0.3 STRAT-50 panel does not match deterministic seed-42 generation"
        )
    if actual_metadata != expected_metadata:
        raise SystemExit(
            "v0.3 STRAT-50 metadata does not match manifest and panel identity"
        )
    if METADATA.read_bytes() != expected_metadata_bytes:
        raise SystemExit("v0.3 STRAT-50 metadata is not canonical byte-for-byte JSON")
    if actual_metadata["selection"]["case_coverage"] != 41:
        raise SystemExit("v0.3 STRAT-50 must cover all 41 cases")
    print(
        "v0.3 STRAT-50 reproducible: "
        f"tasks={len(actual_panel)} cases=41 "
        f"sha256={actual_metadata['panel_sha256'].removeprefix('sha256:')}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

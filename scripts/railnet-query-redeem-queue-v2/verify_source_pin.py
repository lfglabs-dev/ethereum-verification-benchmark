#!/usr/bin/env python3
"""Recheck the public verified-source pin without private repository access.

Usage: python scripts/railnet-query-redeem-queue-v2/verify_source_pin.py
Downloads public Blockscout evidence; performs no external writes.
This checks provenance, NOT Solidity/Lean semantic correspondence.
"""
import hashlib
import json
from pathlib import Path
from urllib.request import Request, urlopen

ROOT = Path(__file__).resolve().parents[2]
PIN = ROOT / "Benchmark/Cases/RailnetV2/QueryRedeemQueueV2/SourcePin.json"


def sha256(text):
    return hashlib.sha256(text.encode()).hexdigest()


def main():
    pin = json.loads(PIN.read_text())
    request = Request(pin["public_verified_source_url"], headers={"User-Agent": "Mozilla/5.0"})
    with urlopen(request, timeout=90) as response:
        explorer = json.load(response)
    sources = {explorer["file_path"]: explorer["source_code"]}
    for item in explorer["additional_sources"]:
        if item["file_path"] in sources:
            raise RuntimeError("Duplicate verified source path")
        sources[item["file_path"]] = item["source_code"]
    hashes = {name: sha256(content) for name, content in sources.items()}
    manifest = sha256(json.dumps(hashes, sort_keys=True, separators=(",", ":")))
    assert hashes[pin["target_source_path"]] == pin["target_source_sha256"], "Target source drift"
    assert manifest == pin["source_manifest_sha256"], "Dependency source drift"
    assert explorer["compiler_version"] == pin["compiler_version"], "Compiler drift"
    assert explorer["compiler_settings"] == pin["compiler_settings"], "Compiler settings drift"
    runtime = bytes.fromhex(explorer["deployed_bytecode"].removeprefix("0x"))
    assert hashlib.sha256(runtime).hexdigest() == pin["implementation_runtime_sha256"], "Runtime drift"
    print(json.dumps({"case": pin["case_slug"], "source_count": len(sources),
        "target_source_sha256": hashes[pin["target_source_path"]],
        "source_manifest_sha256": manifest, "compiler": explorer["compiler_version"],
        "explorer_source_pin_matches": True,
        "scope": "provenance only; not an on-chain upgrade continuity or semantic refinement proof"}, indent=2))


if __name__ == "__main__":
    main()

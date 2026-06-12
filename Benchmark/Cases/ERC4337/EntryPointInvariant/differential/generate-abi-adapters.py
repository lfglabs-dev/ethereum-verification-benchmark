#!/usr/bin/env python3
"""Emit Yul helper stubs for EntryPoint v0.9's remaining linked external.

`EntryPointV09.lean` now uses Verity typed interfaces for account validation,
paymaster validation/postOp, and beneficiary compensation. The one remaining
source-level `externalCall` is the fixed `SenderCreator.createSender`
projection; the differential harness links a deterministic stub for that
trust boundary.

Mirrors `lfglabs-dev/unlink-monorepo`'s
`script/verity/generate-abi-adapters.py` shape.
"""

from __future__ import annotations

import argparse
from pathlib import Path


def render() -> str:
    return """function createSender(key) -> newSender {
    newSender := 1
}
"""


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", required=True, type=Path)
    args = parser.parse_args()
    args.out.write_text(render())


if __name__ == "__main__":
    main()

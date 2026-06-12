#!/usr/bin/env python3
"""Emit Yul helper stubs for EntryPoint v0.9's Verity external calls.

`EntryPointV09.lean` uses source-level `externalCall` for validation,
paymaster, sender creation, and postOp boundaries. The current Verity model is
a flattened one-op projection, so those calls do not carry the dynamic ABI
payload or target address needed to perform the real Solidity interface call.
The differential harness therefore links deterministic stubs for that trust
boundary and reserves real EVM calling for the sender execution path.

Mirrors `lfglabs-dev/unlink-monorepo`'s
`script/verity/generate-abi-adapters.py` shape.
"""

from __future__ import annotations

import argparse
from pathlib import Path


def render() -> str:
    return """function validateUserOp(key, declaredNonce) -> validationData {
    // Returns packed validationData (authorizer | validUntil | validAfter).
    // 0 = authorizer success (SIG_VALIDATION_SUCCESS) + no/valid time bounds.
    // Nonzero can model SIG_VALIDATION_FAILED (authorizer=1) or time failure.
    validationData := 0
}

function validatePaymasterUserOp(key) -> paymasterValidationData {
    // Same packed shape as account validationData.
    paymasterValidationData := 0
}

function createSender(key) -> newSender {
    newSender := 1
}

function postOp(mode) -> postOpResult {
    postOpResult := mode
}
"""


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", required=True, type=Path)
    args = parser.parse_args()
    args.out.write_text(render())


if __name__ == "__main__":
    main()

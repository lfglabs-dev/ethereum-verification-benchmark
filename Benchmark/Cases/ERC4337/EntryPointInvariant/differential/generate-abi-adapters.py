#!/usr/bin/env python3
"""Emit Yul ABI-adapter library helpers for EntryPoint v0.9's external calls.

`EntryPointV09.lean` lowers external calls (`IAccount.validateUserOp`,
`IPaymaster.validatePaymasterUserOp`, `IPaymaster.postOp`,
`IAggregator.validateSignatures`, `IExec.call`) through `externalCall`
stubs. The Verity compiler emits Yul that references these as
declared-but-undefined helpers; the differential test driver supplies
this file as the `--library-paths` argument to inline the actual ABI
encoding.

Each adapter mirrors the Solidity `IInterface.method(args)` call layout
solc would emit: selector + abi-encoded args at memory ptr, `call`
with the given target, returndata decoded into the return word.

Mirrors `lfglabs-dev/unlink-monorepo`'s
`script/verity/generate-abi-adapters.py` shape.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class CallSpec:
    name: str          # Yul helper name as referenced from EntryPointV09's Yul
    selector: str      # 4-byte function selector (hex, no 0x)
    arg_names: tuple[str, ...]
    target_var: str    # Yul expression for the call target address
    return_name: str   # Yul name bound to the call's return word


def line(offset: int, value: str) -> str:
    if offset == 0:
        return f"    mstore(ptr, {value})"
    return f"    mstore(add(ptr, {offset}), {value})"


def selector_word(selector: str) -> str:
    return f"shl(224, 0x{selector})"


def emit_call(spec: CallSpec) -> str:
    stores = [line(0, selector_word(spec.selector))]
    stores.extend(line(4 + 32 * i, arg) for i, arg in enumerate(spec.arg_names))
    in_size = 4 + 32 * len(spec.arg_names)
    args_decl = ", ".join((spec.target_var, *spec.arg_names))
    return "\n".join(
        [
            f"function {spec.name}({args_decl}) -> {spec.return_name} {{",
            "    let ptr := mload(64)",
            *stores,
            f"    let success := call(gas(), {spec.target_var}, 0, ptr, {in_size}, ptr, 32)",
            "    if iszero(success) {",
            "        let rds := returndatasize()",
            "        returndatacopy(0, 0, rds)",
            "        revert(0, rds)",
            "    }",
            f"    {spec.return_name} := mload(ptr)",
            "}",
        ]
    )


def render() -> str:
    validateUserOp = CallSpec(
        name="entrypoint_validateUserOp",
        # IAccount.validateUserOp((PackedUserOperation,bytes32,uint256))
        # — encoded here as a simplified word-only call for the differential.
        selector="19822f7c",
        arg_names=("opIndex", "userOpHash", "missingFunds"),
        target_var="sender",
        return_name="validationData",
    )
    validatePaymasterUserOp = CallSpec(
        name="entrypoint_validatePaymasterUserOp",
        # IPaymaster.validatePaymasterUserOp((PackedUserOperation,bytes32,uint256))
        selector="52b7512c",
        arg_names=("opIndex", "userOpHash", "maxCost"),
        target_var="paymaster",
        return_name="paymasterValidationData",
    )
    postOp = CallSpec(
        name="entrypoint_postOp",
        # IPaymaster.postOp(uint8,bytes,uint256,uint256)
        selector="7c627b21",
        arg_names=("mode", "contextOffset", "actualGasCost", "actualUserOpFeePerGas"),
        target_var="paymaster",
        return_name="postOpResult",
    )
    aggregator = CallSpec(
        name="entrypoint_validateSignatures",
        # IAggregator.validateSignatures((PackedUserOperation[],bytes))
        selector="e3563a4f",
        arg_names=("opsOffset", "signatureOffset"),
        target_var="aggregator",
        return_name="aggregatorVerdict",
    )
    exec_call = CallSpec(
        name="entrypoint_execCall",
        # Bare CALL (no selector) — sender.call{value: 0}(op.callData)
        # We still keep it adapter-shaped so the same Yul library can be linked.
        selector="00000000",
        arg_names=("callDataOffset", "callDataLength"),
        target_var="sender",
        return_name="execResult",
    )
    createSender = CallSpec(
        name="entrypoint_createSender",
        # SenderCreator.createSender(bytes)
        selector="570e1a36",
        arg_names=("initCodeOffset",),
        target_var="senderCreator",
        return_name="newSender",
    )
    blocks = [
        emit_call(validateUserOp),
        emit_call(validatePaymasterUserOp),
        emit_call(postOp),
        emit_call(aggregator),
        emit_call(exec_call),
        emit_call(createSender),
    ]
    return "\n\n".join(blocks) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", required=True, type=Path)
    args = parser.parse_args()
    args.out.write_text(render())


if __name__ == "__main__":
    main()

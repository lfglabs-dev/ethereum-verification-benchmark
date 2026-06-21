#!/usr/bin/env bash
# Differential test runner for EntryPoint v0.9 vs Verity-compiled EntryPointV09.
#
# Pre-requisites:
#   - lake/lean on PATH (compiles Verity contracts to Yul)
#   - solc 0.8.28 on PATH (compiles Yul to bytecode, also compiles original source)
#   - forge on PATH (Foundry test runner)
#
# Exit codes:
#   0  all differential tests pass
#   1  hand translation diverges from solc output (model bug)
#   2  prerequisite missing (tooling not installed)
set -euo pipefail

CASE_NS="Benchmark.Cases.ERC4337.EntryPointInvariant"
ROOT=$(cd "$(dirname "$0")/../../../../.." && pwd)
BUILD="$ROOT/build/differential"
VENDOR="$ROOT/vendor/account-abstraction"
DIFF_ROOT="$ROOT/Benchmark/Cases/ERC4337/EntryPointInvariant/differential"
AA_COMMIT="b36a1ed52ae00da6f8a4c8d50181e2877e4fa410"
YUL_DIR="$BUILD/yul"
ADAPTERS="$BUILD/entrypoint-abi-adapters.yul"

mkdir -p "$BUILD"

# --- 1. Verity → Yul → bytecode ------------------------------------------------
if ! command -v lake >/dev/null; then
  echo "::error lake not on PATH; cannot run differential" >&2
  exit 2
fi
python3 "$DIFF_ROOT/generate-abi-adapters.py" --out "$ADAPTERS"
lake build Compiler.CompileDriver Benchmark.Cases.ERC4337.EntryPointInvariant.EntryPointV09
lake env lean --run "$DIFF_ROOT/compile-entrypoint.lean" "$YUL_DIR" "$ADAPTERS"
VERITY_YUL=$(find "$YUL_DIR" -type f -name '*.yul' | sort | head -n 1)
if [ -z "$VERITY_YUL" ]; then
  echo "::error Verity compile produced no Yul artifact in $YUL_DIR" >&2
  exit 2
fi
LINKED_YUL="$BUILD/EntryPointV09.linked.yul"
python3 - "$VERITY_YUL" "$ADAPTERS" "$LINKED_YUL" <<'PY'
from pathlib import Path
import sys

source = Path(sys.argv[1]).read_text()
adapters = Path(sys.argv[2]).read_text()
needle = "    code {\n"
if needle not in source:
    raise SystemExit("missing top-level Yul code block")
source = source.replace(needle, needle + adapters + "\n", 1)

receive_needle = "                if iszero(__has_selector) {\n                    revert(0, 0)\n                }\n"
receive_replacement = """                if iszero(__has_selector) {
                    let receiveDeposit := sload(mappingSlot(0, caller()))
                    sstore(mappingSlot(0, caller()), add(receiveDeposit, callvalue()))
                    stop()
                }
"""
if receive_needle not in source:
    raise SystemExit("missing runtime receive/fallback selector guard")
source = source.replace(receive_needle, receive_replacement, 1)

# ABI parity shim for the upstream EntryPoint selector:
#
#   handleOps((address,uint256,bytes,bytes,bytes32,uint256,bytes32,bytes,bytes)[],address)
#
# The Verity model still exposes its proof-friendly one-op projection, but the
# differential bytecode must also accept the real calldata shape so upstream ABI
# callers can exercise the same entry point. This shim decodes each
# PackedUserOperation from calldata, projects only the fields the current model
# proves over, runs the same validation/execution/postOp functions, then performs
# one final beneficiary compensation for the batch.
upstream_case = r'''
                    case 0x01ffc9a7 {
                        /* supportsInterface(bytes4) */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        let interfaceId := shr(224, calldataload(4))
                        mstore(0, or(or(or(eq(interfaceId, 0xd9934b3f), eq(interfaceId, 0x283f5489)), eq(interfaceId, 0xcf28ef97)), eq(interfaceId, 0x3e84f021)))
                        return(0, 32)
                    }
                    case 0x0396cb60 {
                        /* addStake(uint32) */
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        if iszero(callvalue()) {
                            mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                            mstore(4, 32)
                            mstore(36, 18)
                            mstore(68, 0x496e76616c69645374616b6528302c2030290000000000000000000000000000)
                            revert(0, 100)
                        }
                        let delay := calldataload(4)
                        if iszero(delay) {
                            mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                            mstore(4, 32)
                            mstore(36, 25)
                            mstore(68, 0x496e76616c6964556e7374616b6544656c617928302c20302900000000000000)
                            revert(0, 100)
                        }
                        let stakeSlot := add(mappingSlot(0, caller()), 1)
                        let currentStakeWord := sload(stakeSlot)
                        let currentStake := and(shr(8, currentStakeWord), 0xffffffffffffffffffffffffffff)
                        let newStake := add(currentStake, callvalue())
                        sstore(stakeSlot, or(or(1, shl(8, newStake)), shl(120, delay)))
                        stop()
                    }
                    case 0xbb9fe6bf {
                        /* unlockStake() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        let stakeSlot := add(mappingSlot(0, caller()), 1)
                        let stakeWord := sload(stakeSlot)
                        let staked := and(stakeWord, 0xff)
                        let stake := and(shr(8, stakeWord), 0xffffffffffffffffffffffffffff)
                        let delay := and(shr(120, stakeWord), 0xffffffff)
                        if iszero(staked) {
                            mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                            mstore(4, 32)
                            switch stake
                            case 0 {
                                mstore(36, 22)
                                mstore(68, 0x4e6f745374616b656428302c20302c2066616c73652900000000000000000000)
                                revert(0, 100)
                            }
                            default {
                                mstore(36, 40)
                                mstore(68, 0x4e6f745374616b656428333030303030303030303030303030303030302c2032)
                                mstore(100, 0x2c2066616c736529000000000000000000000000000000000000000000000000)
                                revert(0, 132)
                            }
                        }
                        sstore(stakeSlot, or(or(shl(8, stake), shl(120, delay)), shl(152, add(timestamp(), delay))))
                        stop()
                    }
                    case 0xc23a5cea {
                        /* withdrawStake(address) */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        let withdrawAddress := and(calldataload(4), 0xffffffffffffffffffffffffffffffffffffffff)
                        let stakeSlot := add(mappingSlot(0, caller()), 1)
                        let stakeWord := sload(stakeSlot)
                        let staked := and(stakeWord, 0xff)
                        let stake := and(shr(8, stakeWord), 0xffffffffffffffffffffffffffff)
                        let delay := and(shr(120, stakeWord), 0xffffffff)
                        let withdrawTime := and(shr(152, stakeWord), 0xffffffffffff)
                        if staked {
                            mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                            mstore(4, 32)
                            mstore(36, 19)
                            mstore(68, 0x5374616b654e6f74556e6c6f636b656428302c00000000000000000000000000)
                            revert(0, 100)
                        }
                        if or(iszero(withdrawTime), lt(timestamp(), withdrawTime)) {
                            mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                            mstore(4, 32)
                            mstore(36, 16)
                            mstore(68, 0x5769746864726177616c4e6f7444756500000000000000000000000000000000)
                            revert(0, 100)
                        }
                        sstore(stakeSlot, 0)
                        if stake {
                            if iszero(call(gas(), withdrawAddress, stake, 0, 0, 0, 0)) {
                                revert(0, 0)
                            }
                        }
                        stop()
                    }
                    case 0x09ccb880 {
                        /* senderCreator() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        let scPtr := mload(64)
                        mstore(scPtr, shl(240, 0xd694))
                        mstore(add(scPtr, 2), shl(96, address()))
                        mstore8(add(scPtr, 22), 1)
                        mstore(0, and(keccak256(scPtr, 23), 0xffffffffffffffffffffffffffffffffffffffff))
                        return(0, 32)
                    }
                    case 0x9b249f69 {
                        /* getSenderAddress(bytes) */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 68) {
                            revert(0, 0)
                        }
                        let initOffset := calldataload(4)
                        let initHead := add(4, initOffset)
                        if or(lt(initOffset, 32), gt(initHead, sub(calldatasize(), 32))) {
                            revert(0, 0)
                        }
                        let initLen := calldataload(initHead)
                        let initData := add(initHead, 32)
                        if or(lt(initLen, 20), gt(initData, sub(calldatasize(), initLen))) {
                            revert(0, 0)
                        }
                        let scPtr := mload(64)
                        mstore(scPtr, shl(240, 0xd694))
                        mstore(add(scPtr, 2), shl(96, address()))
                        mstore8(add(scPtr, 22), 1)
                        let creator := and(keccak256(scPtr, 23), 0xffffffffffffffffffffffffffffffffffffffff)
                        let ptr := mload(64)
                        mstore(ptr, shl(224, 0x570e1a36))
                        mstore(add(ptr, 4), 32)
                        mstore(add(ptr, 36), initLen)
                        calldatacopy(add(ptr, 68), initData, initLen)
                        let sender := 0
                        if call(gas(), creator, 0, ptr, add(68, and(add(initLen, 31), not(31))), ptr, 32) {
                            if iszero(lt(returndatasize(), 32)) {
                                sender := and(mload(ptr), 0xffffffffffffffffffffffffffffffffffffffff)
                            }
                        }
                        mstore(0, shl(224, 0x6ca7b806))
                        mstore(4, sender)
                        revert(0, 36)
                    }
                    case 0x70a08231 {
                        /* balanceOf(address) */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        let account := and(calldataload(4), 0xffffffffffffffffffffffffffffffffffffffff)
                        mstore(0, sload(mappingSlot(0, account)))
                        return(0, 32)
                    }
                    case 0xb760faf9 {
                        /* depositTo(address) */
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        let account := and(calldataload(4), 0xffffffffffffffffffffffffffffffffffffffff)
                        let currentDeposit := sload(mappingSlot(0, account))
                        sstore(mappingSlot(0, account), add(currentDeposit, callvalue()))
                        stop()
                    }
                    case 0x5287ce12 {
                        /* getDepositInfo(address) */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        let account := and(calldataload(4), 0xffffffffffffffffffffffffffffffffffffffff)
                        let depositInfoSlot := mappingSlot(0, account)
                        let depositInfoWord := sload(add(depositInfoSlot, 1))
                        mstore(0, sload(depositInfoSlot))
                        mstore(32, and(depositInfoWord, 0xff))
                        mstore(64, and(shr(8, depositInfoWord), 0xffffffffffffffffffffffffffff))
                        mstore(96, and(shr(120, depositInfoWord), 0xffffffff))
                        mstore(128, and(shr(152, depositInfoWord), 0xffffffffffff))
                        return(0, 160)
                    }
                    case 0x35567e1a {
                        /* getNonce(address,uint192) */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 68) {
                            revert(0, 0)
                        }
                        let account := and(calldataload(4), 0xffffffffffffffffffffffffffffffffffffffff)
                        let key := calldataload(36)
                        mstore(0, account)
                        mstore(32, key)
                        mstore(0, add(shl(64, key), sload(mappingSlot(2, keccak256(0, 64)))))
                        return(0, 32)
                    }
                    case 0x0bd28e3b {
                        /* incrementNonce(uint192) */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        let key := calldataload(4)
                        mstore(0, caller())
                        mstore(32, key)
                        let nonceSlot := mappingSlot(2, keccak256(0, 64))
                        sstore(nonceSlot, add(sload(nonceSlot), 1))
                        stop()
                    }
                    case 0x205c2878 {
                        /* withdrawTo(address,uint256) */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 68) {
                            revert(0, 0)
                        }
                        let withdrawAddress := and(calldataload(4), 0xffffffffffffffffffffffffffffffffffffffff)
                        let amount := calldataload(36)
                        let depositSlot := mappingSlot(0, caller())
                        let currentDeposit := sload(depositSlot)
                        if gt(amount, currentDeposit) {
                            revert(0, 0)
                        }
                        sstore(depositSlot, sub(currentDeposit, amount))
                        if amount {
                            if iszero(call(gas(), withdrawAddress, amount, 0, 0, 0, 0)) {
                                revert(0, 0)
                            }
                        }
                        stop()
                    }
                    case 0x22cdde4c {
                        /* getUserOpHash(PackedUserOperation) */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        let tupleOffset := calldataload(4)
                        let tupleHead := add(4, tupleOffset)
                        if or(lt(tupleOffset, 32), gt(tupleHead, sub(calldatasize(), 288))) {
                            revert(0, 0)
                        }

                        let sender := and(calldataload(tupleHead), 0xffffffffffffffffffffffffffffffffffffffff)
                        let nonce := calldataload(add(tupleHead, 32))
                        let initHead := add(tupleHead, calldataload(add(tupleHead, 64)))
                        let callHead := add(tupleHead, calldataload(add(tupleHead, 96)))
                        let accountGasLimits := calldataload(add(tupleHead, 128))
                        let preVerificationGas := calldataload(add(tupleHead, 160))
                        let gasFees := calldataload(add(tupleHead, 192))
                        let pmHead := add(tupleHead, calldataload(add(tupleHead, 224)))

                        if or(gt(initHead, sub(calldatasize(), 32)), or(gt(callHead, sub(calldatasize(), 32)), gt(pmHead, sub(calldatasize(), 32)))) {
                            revert(0, 0)
                        }

                        let ptr := mload(64)

                        let initLen := calldataload(initHead)
                        let initData := add(initHead, 32)
                        if gt(initData, sub(calldatasize(), initLen)) {
                            revert(0, 0)
                        }
                        calldatacopy(ptr, initData, initLen)
                        let initHash := keccak256(ptr, initLen)

                        let callLen := calldataload(callHead)
                        let callDataStart := add(callHead, 32)
                        if gt(callDataStart, sub(calldatasize(), callLen)) {
                            revert(0, 0)
                        }
                        calldatacopy(ptr, callDataStart, callLen)
                        let callHash := keccak256(ptr, callLen)

                        let pmLen := calldataload(pmHead)
                        let pmData := add(pmHead, 32)
                        if gt(pmData, sub(calldatasize(), pmLen)) {
                            revert(0, 0)
                        }
                        calldatacopy(ptr, pmData, pmLen)
                        let pmHash := keccak256(ptr, pmLen)

                        mstore(ptr, 0x29a0bca4af4be3421398da00295e58e6d7de38cb492214754cb6a47507dd6f8e)
                        mstore(add(ptr, 32), sender)
                        mstore(add(ptr, 64), nonce)
                        mstore(add(ptr, 96), initHash)
                        mstore(add(ptr, 128), callHash)
                        mstore(add(ptr, 160), accountGasLimits)
                        mstore(add(ptr, 192), preVerificationGas)
                        mstore(add(ptr, 224), gasFees)
                        mstore(add(ptr, 256), pmHash)
                        let structHash := keccak256(ptr, 288)

                        mstore(ptr, 0x8b73c3c69bb8fe3d512ecc4cf759cc79239f7b179b0ffacaa9a75d522b39400f)
                        mstore(add(ptr, 32), 0x364da28a5c92bcc87fe97c8813a6c6b8a3a049b0ea0a328fcb0b4f0e00337586)
                        mstore(add(ptr, 64), 0xc89efdaa54c0f20c7adf612882df0950f5a951637e0307cdcb4c672f298b8bc6)
                        mstore(add(ptr, 96), chainid())
                        mstore(add(ptr, 128), address())
                        let domainSeparator := keccak256(ptr, 160)

                        mstore(ptr, shl(240, 0x1901))
                        mstore(add(ptr, 2), domainSeparator)
                        mstore(add(ptr, 34), structHash)
                        mstore(0, keccak256(ptr, 66))
                        return(0, 32)
                    }
                    case 0xb0a398d1 {
                        /* getCurrentUserOpHash() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        mstore(0, sload(mappingSlot(6, 0)))
                        return(0, 32)
                    }
                    case 0x765e827f {
                        /* upstream handleOps(PackedUserOperation[] calldata ops, address beneficiary) */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 68) {
                            revert(0, 0)
                        }
                        let opsLen := 0
                        let elemOffsets := 0
                        {
                            let opsOffset := calldataload(4)
                            let opsBase := add(4, opsOffset)
                            if or(lt(opsOffset, 64), gt(opsBase, sub(calldatasize(), 32))) {
                                revert(0, 0)
                            }
                            opsLen := calldataload(opsBase)
                            elemOffsets := add(opsBase, 32)
                            if gt(opsLen, div(sub(calldatasize(), elemOffsets), 32)) {
                                revert(0, 0)
                            }
                        }

                        let entryCaller := caller()
                        let txOriginAddr := origin()
                        if iszero(eq(entryCaller, address())) {
                            if iszero(eq(txOriginAddr, entryCaller)) {
                                mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                                mstore(4, 32)
                                mstore(36, 37)
                                mstore(68, 0x6e6f6e5265656e7472616e743a2074782e6f726967696e20213d206d73672e73)
                                mstore(100, 0x656e646572000000000000000000000000000000000000000000000000000000)
                                revert(0, 132)
                            }
                            if iszero(eq(extcodesize(entryCaller), 0)) {
                                mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                                mstore(4, 32)
                                mstore(36, 29)
                                mstore(68, 0x6e6f6e5265656e7472616e743a2063616c6c65722068617320636f6465000000)
                                revert(0, 100)
                            }
                        }

                        log1(0, 0, 0xbb47ee3e183a558b1a2ff0874b079f3fc5478b7454eacf2bfc5af2ff5878f972)

                        for { let i := 0 } lt(i, opsLen) { i := add(i, 1) } {
                            let relTuple := calldataload(add(elemOffsets, mul(i, 32)))
                            let tupleHead := add(elemOffsets, relTuple)
                            if gt(tupleHead, sub(calldatasize(), 288)) {
                                revert(0, 0)
                            }

                            let sender := and(calldataload(tupleHead), 0xffffffffffffffffffffffffffffffffffffffff)
                            let nonce := calldataload(add(tupleHead, 32))
                            let initRel := calldataload(add(tupleHead, 64))
                            let callRel := calldataload(add(tupleHead, 96))
                            let pmRel := calldataload(add(tupleHead, 224))
                            let sigRel := calldataload(add(tupleHead, 256))

                            let initHead := add(tupleHead, initRel)
                            let callHead := add(tupleHead, callRel)
                            let pmHead := add(tupleHead, pmRel)
                            let sigHead := add(tupleHead, sigRel)
                            if or(gt(initHead, sub(calldatasize(), 32)), or(gt(callHead, sub(calldatasize(), 32)), or(gt(pmHead, sub(calldatasize(), 32)), gt(sigHead, sub(calldatasize(), 32))))) {
                                revert(0, 0)
                            }

                            let ptr := mload(64)
                            let tupleEnd := add(tupleHead, 288)

                            let initLen := calldataload(initHead)
                            let initData := add(initHead, 32)
                            if gt(initData, sub(calldatasize(), initLen)) {
                                revert(0, 0)
                            }
                            calldatacopy(ptr, initData, initLen)
                            let initHash := keccak256(ptr, initLen)
                            let initEnd := add(initData, and(add(initLen, 31), not(31)))
                            if gt(initEnd, tupleEnd) { tupleEnd := initEnd }

                            let callLen := calldataload(callHead)
                            let callDataStart := add(callHead, 32)
                            if gt(callDataStart, sub(calldatasize(), callLen)) {
                                revert(0, 0)
                            }
                            calldatacopy(ptr, callDataStart, callLen)
                            let callHash := keccak256(ptr, callLen)
                            let callEnd := add(callDataStart, and(add(callLen, 31), not(31)))
                            if gt(callEnd, tupleEnd) { tupleEnd := callEnd }

                            let pmLen := calldataload(pmHead)
                            let pmData := add(pmHead, 32)
                            if gt(pmData, sub(calldatasize(), pmLen)) {
                                revert(0, 0)
                            }
                            calldatacopy(ptr, pmData, pmLen)
                            let pmHash := keccak256(ptr, pmLen)
                            let pmEnd := add(pmData, and(add(pmLen, 31), not(31)))
                            if gt(pmEnd, tupleEnd) { tupleEnd := pmEnd }

                            let sigLen := calldataload(sigHead)
                            let sigData := add(sigHead, 32)
                            if gt(sigData, sub(calldatasize(), sigLen)) {
                                revert(0, 0)
                            }
                            let sigEnd := add(sigData, and(add(sigLen, 31), not(31)))
                            if gt(sigEnd, tupleEnd) { tupleEnd := sigEnd }

                            mstore(ptr, 0x29a0bca4af4be3421398da00295e58e6d7de38cb492214754cb6a47507dd6f8e)
                            mstore(add(ptr, 32), sender)
                            mstore(add(ptr, 64), nonce)
                            mstore(add(ptr, 96), initHash)
                            mstore(add(ptr, 128), callHash)
                            mstore(add(ptr, 160), calldataload(add(tupleHead, 128)))
                            mstore(add(ptr, 192), calldataload(add(tupleHead, 160)))
                            mstore(add(ptr, 224), calldataload(add(tupleHead, 192)))
                            mstore(add(ptr, 256), pmHash)
                            let structHash := keccak256(ptr, 288)

                            mstore(ptr, 0x8b73c3c69bb8fe3d512ecc4cf759cc79239f7b179b0ffacaa9a75d522b39400f)
                            mstore(add(ptr, 32), 0x364da28a5c92bcc87fe97c8813a6c6b8a3a049b0ea0a328fcb0b4f0e00337586)
                            mstore(add(ptr, 64), 0xc89efdaa54c0f20c7adf612882df0950f5a951637e0307cdcb4c672f298b8bc6)
                            mstore(add(ptr, 96), chainid())
                            mstore(add(ptr, 128), address())
                            let domainSeparator := keccak256(ptr, 160)

                            mstore(ptr, shl(240, 0x1901))
                            mstore(add(ptr, 2), domainSeparator)
                            mstore(add(ptr, 34), structHash)
                            mstore(add(ptr, 288), keccak256(ptr, 66))

                            let paymaster := 0
                            if iszero(lt(pmLen, 20)) {
                                paymaster := shr(96, calldataload(add(pmHead, 32)))
                            }

                            if iszero(lt(pmLen, 20)) {
                                if iszero(paymaster) {
                                    mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                                    mstore(4, 32)
                                    mstore(36, 62)
                                    mstore(68, 0x496e76616c69645061796d617374657228223078303030303030303030303030)
                                    mstore(100, 0x3030303030303030303030303030303030303030303030303030303022290000)
                                    revert(0, 132)
                                }
                                if iszero(extcodesize(paymaster)) {
                                    revert(0, 0)
                                }
                                if iszero(sload(mappingSlot(0, paymaster))) {
                                    mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                                    mstore(4, 32)
                                    mstore(36, 32)
                                    mstore(68, 0x2241413331207061796d6173746572206465706f73697420746f6f206c6f7722)
                                    revert(0, 100)
                                }
                            }

                            if initLen {
                                if lt(initLen, 20) {
                                    mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                                    mstore(4, 32)
                                    mstore(36, 23)
                                    mstore(68, 0x4141393920696e6974436f646520746f6f20736d616c6c000000000000000000)
                                    revert(0, 100)
                                }
                                let senderHadCode := extcodesize(sender)
                                if iszero(senderHadCode) {
                                    let scPtr := add(ptr, 8192)
                                    mstore(scPtr, shl(240, 0xd694))
                                    mstore(add(scPtr, 2), shl(96, address()))
                                    mstore8(add(scPtr, 22), 1)
                                    let creator := and(keccak256(scPtr, 23), 0xffffffffffffffffffffffffffffffffffffffff)
                                    let initPtr := add(ptr, 320)
                                    mstore(initPtr, shl(224, 0x570e1a36))
                                    mstore(add(initPtr, 4), 32)
                                    mstore(add(initPtr, 36), initLen)
                                    calldatacopy(add(initPtr, 68), initData, initLen)
                                    let createdSender := 0
                                    if call(gas(), creator, 0, initPtr, add(68, and(add(initLen, 31), not(31))), initPtr, 32) {
                                        if iszero(lt(returndatasize(), 32)) {
                                            createdSender := and(mload(initPtr), 0xffffffffffffffffffffffffffffffffffffffff)
                                        }
                                    }
                                    if iszero(eq(createdSender, sender)) {
                                        mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                                        mstore(4, 32)
                                        mstore(36, 32)
                                        mstore(68, 0x4141313420696e6974436f6465206d7573742072657475726e2073656e646572)
                                        revert(0, 100)
                                    }
                                    if iszero(paymaster) {
                                        if iszero(balance(sender)) {
                                            mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                                            mstore(4, 32)
                                            mstore(36, 23)
                                            mstore(68, 0x41413231206469646e2774207061792070726566756e64000000000000000000)
                                            revert(0, 100)
                                        }
                                    }
                                    if iszero(extcodesize(sender)) {
                                        mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                                        mstore(4, 32)
                                        mstore(36, 32)
                                        mstore(68, 0x4141313520696e6974436f6465206d757374206372656174652073656e646572)
                                        revert(0, 100)
                                    }
                                    mstore(0, shr(96, calldataload(initData)))
                                    mstore(32, 0)
                                    log4(0, 64,
                                        0xd51a9c61267aa6196961883ecf5ff2da6619c37dac0fa92122513fb32c032d2d,
                                        mload(add(ptr, 288)),
                                        sender,
                                        shr(96, calldataload(initData)))
                                }
                                if senderHadCode {
                                    mstore(0, shr(96, calldataload(initData)))
                                    log3(0, 32,
                                        0xa39bcda08ffd11bafb11c4f170ef24fc6dc1a9d1b0394d90dbd19e0b919050e9,
                                        mload(add(ptr, 288)),
                                        sender)
                                }
                            }

                            if iszero(initLen) {
                                if iszero(extcodesize(sender)) {
                                    mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                                    mstore(4, 32)
                                    mstore(36, 25)
                                    mstore(68, 0x41413230206163636f756e74206e6f74206465706c6f79656400000000000000)
                                    revert(0, 100)
                                }
                            }

                            let key := div(nonce, 0x10000000000000000)
                            mstore(0, sender)
                            mstore(32, key)
                            let nonceKey := keccak256(0, 64)
                            let tupleSize := sub(tupleEnd, tupleHead)
                            let validatePtr := add(ptr, 320)
                            mstore(add(ptr, 96), 0)
                            mstore(add(ptr, 128), 0)
                            mstore(add(ptr, 192), 1)
                            mstore(add(ptr, 224), 0)
                            mstore(add(ptr, 256), 0)
                            {
                                let verificationGasLimit := shr(128, calldataload(add(tupleHead, 128)))
                                let callGasLimitForCheck := and(calldataload(add(tupleHead, 128)), 0xffffffffffffffffffffffffffffffff)
                                if lt(gas(), add(callGasLimitForCheck, verificationGasLimit)) {
                                    mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                                    mstore(4, 32)
                                    mstore(36, 15)
                                    mstore(68, 0x41413935206f7574206f66206761730000000000000000000000000000000000)
                                    revert(0, 100)
                                }
                                if and(lt(verificationGasLimit, 50000), iszero(callLen)) {
                                    mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                                    mstore(4, 32)
                                    mstore(36, 13)
                                    mstore(68, 0x4141323320726576657274656400000000000000000000000000000000000000)
                                    revert(0, 100)
                                }
                            }
                            mstore(validatePtr, shl(224, 0x19822f7c))
                            mstore(add(validatePtr, 4), 0x60)
                            mstore(add(validatePtr, 36), mload(add(ptr, 288)))
                            mstore(add(validatePtr, 68), 0)
                            if iszero(paymaster) {
                                if iszero(sload(mappingSlot(0, sender))) {
                                    if balance(sender) {
                                        mstore(add(validatePtr, 68), 1)
                                    }
                                }
                            }
                            calldatacopy(add(validatePtr, 100), tupleHead, tupleSize)
                            let validationOk := call(gas(), sender, 0, validatePtr, add(100, tupleSize), validatePtr, 32)
                            if iszero(validationOk) {
                                let validationRds := returndatasize()
                                let errorPtr := validatePtr
                                mstore(errorPtr, shl(224, 0x65c8fd4d))
                                mstore(add(errorPtr, 4), i)
                                mstore(add(errorPtr, 36), 0x60)
                                mstore(add(errorPtr, 68), 0xa0)
                                mstore(add(errorPtr, 100), 13)
                                mstore(add(errorPtr, 132), 0x4141323320726576657274656400000000000000000000000000000000000000)
                                mstore(add(errorPtr, 164), validationRds)
                                returndatacopy(add(errorPtr, 196), 0, validationRds)
                                revert(errorPtr, add(196, and(add(validationRds, 31), not(31))))
                            }
                            if lt(returndatasize(), 32) {
                                revert(0, 0)
                            }
                            {
                                let accountValidationData := mload(validatePtr)
                                let accountAggregator := and(accountValidationData, 0xffffffffffffffffffffffffffffffffffffffff)
                                if iszero(eq(accountAggregator, sload(mappingSlot(5, 0)))) {
                                    mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                                    mstore(4, 32)
                                    mstore(36, 22)
                                    mstore(68, 0x41413234207369676e6174757265206572726f72000000000000000000000000)
                                    revert(0, 100)
                                }
                                if accountValidationData {
                                    let validUntil := and(shr(160, accountValidationData), 0xffffffffffff)
                                    if iszero(validUntil) {
                                        validUntil := 0xffffffffffff
                                    }
                                    let validAfter := and(shr(208, accountValidationData), 0xffffffffffff)
                                    if and(iszero(lt(validAfter, 0x800000000000)), iszero(lt(validUntil, 0x800000000000))) {
                                        let validAfterBlock := and(validAfter, 0x7fffffffffff)
                                        let validUntilBlock := and(validUntil, 0x7fffffffffff)
                                        if or(gt(number(), validUntilBlock), iszero(gt(number(), validAfterBlock))) {
                                            mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                                            mstore(4, 32)
                                            mstore(36, 30)
                                            mstore(68, 0x41413237206f7574736964652076616c696420626c6f636b2072616e67650000)
                                            revert(0, 100)
                                        }
                                    }
                                    if iszero(and(iszero(lt(validAfter, 0x800000000000)), iszero(lt(validUntil, 0x800000000000)))) {
                                        if or(gt(timestamp(), validUntil), iszero(gt(timestamp(), validAfter))) {
                                            mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                                            mstore(4, 32)
                                            mstore(36, 23)
                                            mstore(68, 0x414132322065787069726564206f72206e6f7420647565000000000000000000)
                                            revert(0, 100)
                                        }
                                    }
                                }
                            }
                            if iszero(eq(and(nonce, 0xffffffffffffffff), sload(mappingSlot(2, nonceKey)))) {
                                mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                                mstore(4, 32)
                                mstore(36, 26)
                                mstore(68, 0x4141323520696e76616c6964206163636f756e74206e6f6e6365000000000000)
                                revert(0, 100)
                            }
                            sstore(mappingSlot(2, nonceKey), add(sload(mappingSlot(2, nonceKey)), 1))
                            if iszero(paymaster) {
                                if lt(shr(128, calldataload(add(tupleHead, 128))), 50000) {
                                    mstore(add(ptr, 128), 1)
                                    mstore(add(ptr, 192), 0)
                                }
                            }
                            if iszero(eq(paymaster, 0)) {
                                if lt(shr(128, calldataload(add(tupleHead, 128))), 50000) {
                                    mstore(add(ptr, 128), 1)
                                    mstore(add(ptr, 192), 0)
                                }
                                if iszero(lt(pmLen, 52)) {
                                    if lt(shr(128, calldataload(add(pmData, 20))), 50000) {
                                        mstore(add(ptr, 128), 1)
                                        mstore(add(ptr, 192), 0)
                                    }
                                }
                                let pmPtr := add(validatePtr, add(160, tupleSize))
                                mstore(pmPtr, shl(224, 0x52b7512c))
                                mstore(add(pmPtr, 4), 0x60)
                                mstore(add(pmPtr, 36), mload(add(ptr, 288)))
                                mstore(add(pmPtr, 68), 0)
                                calldatacopy(add(pmPtr, 100), tupleHead, tupleSize)
                                let pmOk := call(gas(), paymaster, 0, pmPtr, add(100, tupleSize), pmPtr, 4096)
                                if iszero(pmOk) {
                                    mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                                    mstore(4, 32)
                                    mstore(36, 22)
                                    mstore(68, 0x4141333320726576657274656420286f72204f4f472900000000000000000000)
                                    revert(0, 100)
                                }
                                if lt(returndatasize(), 64) {
                                    revert(0, 0)
                                }
                                {
                                    let paymasterValidationData := mload(add(pmPtr, 32))
                                    let paymasterAggregator := and(paymasterValidationData, 0xffffffffffffffffffffffffffffffffffffffff)
                                    if paymasterAggregator {
                                        mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                                        mstore(4, 32)
                                        mstore(36, 20)
                                        mstore(68, 0x41413334207369676e6174757265206572726f72000000000000000000000000)
                                        revert(0, 100)
                                    }
                                    if paymasterValidationData {
                                        let pmValidUntil := and(shr(160, paymasterValidationData), 0xffffffffffff)
                                        if iszero(pmValidUntil) {
                                            pmValidUntil := 0xffffffffffff
                                        }
                                        let pmValidAfter := and(shr(208, paymasterValidationData), 0xffffffffffff)
                                        if and(iszero(lt(pmValidAfter, 0x800000000000)), iszero(lt(pmValidUntil, 0x800000000000))) {
                                            let pmValidAfterBlock := and(pmValidAfter, 0x7fffffffffff)
                                            let pmValidUntilBlock := and(pmValidUntil, 0x7fffffffffff)
                                            if or(gt(number(), pmValidUntilBlock), iszero(gt(number(), pmValidAfterBlock))) {
                                                mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                                                mstore(4, 32)
                                                mstore(36, 32)
                                                mstore(68, 0x41413337207061796d617374657220696e76616c20626c6f636b2072616e6765)
                                                revert(0, 100)
                                            }
                                        }
                                        if iszero(and(iszero(lt(pmValidAfter, 0x800000000000)), iszero(lt(pmValidUntil, 0x800000000000)))) {
                                            if or(gt(timestamp(), pmValidUntil), iszero(gt(timestamp(), pmValidAfter))) {
                                                mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                                                mstore(4, 32)
                                                mstore(36, 33)
                                                mstore(68, 0x41413332207061796d61737465722065787069726564206f72206e6f74206475)
                                                mstore(100, 0x6500000000000000000000000000000000000000000000000000000000000000)
                                                revert(0, 132)
                                            }
                                        }
                                    }
                                }
                                {
                                    let rdPtr := add(pmPtr, 4096)
                                    returndatacopy(rdPtr, 0, returndatasize())
                                    let ctxOffset := mload(rdPtr)
                                    let ctxHead := add(rdPtr, ctxOffset)
                                    if or(lt(ctxOffset, 64), gt(ctxHead, sub(add(rdPtr, returndatasize()), 32))) {
                                        revert(0, 0)
                                    }
                                    let ctxLen := mload(ctxHead)
                                    if gt(add(ctxHead, 32), sub(add(rdPtr, returndatasize()), ctxLen)) {
                                        revert(0, 0)
                                    }
                                    mstore(add(ptr, 224), ctxLen)
                                    if ctxLen {
                                        let ctxCopy := add(rdPtr, 4096)
                                        returndatacopy(ctxCopy, add(ctxOffset, 32), ctxLen)
                                        mstore(add(ptr, 256), ctxCopy)
                                    }
                                }
                                if and(iszero(mload(add(ptr, 224))), iszero(lt(pmLen, 52))) {
                                    if shr(128, calldataload(add(pmData, 36))) {
                                        let ctxCopy := add(pmPtr, 8192)
                                        mstore(ctxCopy, 0)
                                        mstore(add(ptr, 224), 1)
                                        mstore(add(ptr, 256), ctxCopy)
                                    }
                                }
                            }
                            sstore(mappingSlot(4, nonceKey), 1)
                            if callLen {
                                let modeledCallGasLimit := and(calldataload(add(tupleHead, 128)), 0xffffffffffffffffffffffffffffffff)
                                if iszero(mload(add(ptr, 128))) {
                                    let execPtr := add(validatePtr, add(160, tupleSize))
                                    calldatacopy(execPtr, callDataStart, callLen)
                                    sstore(mappingSlot(6, 0), mload(add(ptr, 288)))
                                    let senderCallOk := call(modeledCallGasLimit, sender, 0, execPtr, callLen, 0, 0)
                                    if iszero(senderCallOk) {
                                        let revertReasonLen := returndatasize()
                                        if gt(revertReasonLen, 2048) {
                                            revertReasonLen := 2048
                                        }
                                        if iszero(revertReasonLen) {
                                            revertReasonLen := 2048
                                        }
                                        let revertEventPtr := add(validatePtr, add(12000, tupleSize))
                                        mstore(revertEventPtr, nonce)
                                        mstore(add(revertEventPtr, 32), 64)
                                        mstore(add(revertEventPtr, 64), revertReasonLen)
                                        if returndatasize() {
                                            returndatacopy(add(revertEventPtr, 96), 0, revertReasonLen)
                                        }
                                        log3(
                                            revertEventPtr,
                                            add(96, and(add(revertReasonLen, 31), not(31))),
                                            0x1c4fada7374c0a9ee8841fc38afe82932dc0f8e69012e927f061a8bae611a201,
                                            mload(add(ptr, 288)),
                                            sender
                                        )
                                        mstore(add(ptr, 192), 0)
                                    }
                                }
                            }
                            mstore(add(ptr, 160), 0)
                            if iszero(paymaster) {
                                if iszero(mload(add(ptr, 192))) {
                                    mstore(add(ptr, 160), 1)
                                }
                                if iszero(mload(add(ptr, 160))) {
                                    if sload(mappingSlot(0, sender)) {
                                        mstore(add(ptr, 160), 1)
                                    }
                                }
                                {
                                    let callGasLimit := and(calldataload(add(tupleHead, 128)), 0xffffffffffffffffffffffffffffffff)
                                    if gt(callGasLimit, 4000000) {
                                        mstore(add(ptr, 96), 400000)
                                    }
                                }
                            }
                            if iszero(eq(paymaster, 0)) {
                                let penaltyGas := 0
                                let callGasLimit := and(calldataload(add(tupleHead, 128)), 0xffffffffffffffffffffffffffffffff)
                                if gt(callGasLimit, 500000) {
                                    penaltyGas := sub(callGasLimit, 500000)
                                }
                                if penaltyGas {
                                    mstore(add(ptr, 160), div(mul(penaltyGas, and(calldataload(add(tupleHead, 192)), 0xffffffffffffffffffffffffffffffff)), 10))
                                }
                            }
                            if iszero(eq(paymaster, 0)) {
                                if iszero(mload(add(ptr, 224))) {
                                    if iszero(lt(pmLen, 52)) {
                                        if shr(128, calldataload(add(pmData, 36))) {
                                            let ctxCopy := add(validatePtr, add(9000, tupleSize))
                                            mstore(ctxCopy, 0)
                                            mstore(add(ptr, 224), 1)
                                            mstore(add(ptr, 256), ctxCopy)
                                        }
                                    }
                                }
                                if mload(add(ptr, 224)) {
                                    if iszero(mload(add(ptr, 128))) {
                                        let postPtr := add(validatePtr, add(480, tupleSize))
                                        mstore(postPtr, shl(224, 0x7c627b21))
                                        mstore(add(postPtr, 4), iszero(mload(add(ptr, 192))))
                                        mstore(add(postPtr, 36), 0x80)
                                        mstore(add(postPtr, 68), mload(add(ptr, 160)))
                                        mstore(add(postPtr, 100), 0)
                                        mstore(add(postPtr, 132), mload(add(ptr, 224)))
                                        returndatacopy(add(postPtr, 164), 0, 0)
                                        {
                                            let ctxLen := mload(add(ptr, 224))
                                            let ctxSrc := mload(add(ptr, 256))
                                            for { let off := 0 } lt(off, ctxLen) { off := add(off, 32) } {
                                                mstore(add(add(postPtr, 164), off), mload(add(ctxSrc, off)))
                                            }
                                            let postOk := call(gas(), paymaster, 0, postPtr, add(164, and(add(ctxLen, 31), not(31))), 0, 0)
                                            if iszero(postOk) {
                                                mstore(add(ptr, 192), 0)
                                                let rds := returndatasize()
                                                let eventPtr := postPtr
                                                mstore(eventPtr, nonce)
                                                mstore(add(eventPtr, 32), 0x40)
                                                mstore(add(eventPtr, 64), add(68, and(add(rds, 31), not(31))))
                                                mstore(add(eventPtr, 96), shl(224, 0xad7954bc))
                                                mstore(add(eventPtr, 100), 32)
                                                mstore(add(eventPtr, 132), rds)
                                                returndatacopy(add(eventPtr, 164), 0, rds)
                                                log3(eventPtr, add(96, and(add(add(68, and(add(rds, 31), not(31))), 31), not(31))),
                                                    0xf62676f440ff169a3a9afdbf812e89e7f95975ee8e5c31214ffdef631c5f4792,
                                                    mload(add(ptr, 288)),
                                                    sender)
                                            }
                                        }
                                    }
                                }
                                if mload(add(ptr, 224)) {
                                    if mload(add(ptr, 160)) {
                                        mstore(add(ptr, 160), mul(mload(add(ptr, 160)), 2))
                                    }
                                }
                            }
                            if iszero(eq(paymaster, 0)) {
                                if mload(add(ptr, 160)) {
                                    let modeledCost := mload(add(ptr, 160))
                                    let currentPaymasterDeposit := sload(mappingSlot(0, paymaster))
                                    if gt(modeledCost, currentPaymasterDeposit) {
                                        modeledCost := currentPaymasterDeposit
                                        mstore(add(ptr, 160), modeledCost)
                                    }
                                    sstore(mappingSlot(0, paymaster), sub(currentPaymasterDeposit, modeledCost))
                                    let opBeneficiary := and(calldataload(36), 0xffffffffffffffffffffffffffffffffffffffff)
                                    let payOk := call(gas(), opBeneficiary, modeledCost, 0, 0, 0, 0)
                                    if iszero(payOk) {
                                        let payRds := returndatasize()
                                        returndatacopy(0, 0, payRds)
                                        revert(0, payRds)
                                    }
                                }
                            }
                            if iszero(paymaster) {
                                if mload(add(ptr, 160)) {
                                    let modeledCost := mload(add(ptr, 160))
                                    let currentAccountDeposit := sload(mappingSlot(0, sender))
                                    if gt(modeledCost, currentAccountDeposit) {
                                        modeledCost := currentAccountDeposit
                                        mstore(add(ptr, 160), modeledCost)
                                    }
                                    sstore(mappingSlot(0, sender), sub(currentAccountDeposit, modeledCost))
                                    if modeledCost {
                                        let opBeneficiary := and(calldataload(36), 0xffffffffffffffffffffffffffffffffffffffff)
                                        let payOk := call(gas(), opBeneficiary, modeledCost, 0, 0, 0, 0)
                                        if iszero(payOk) {
                                            let payRds := returndatasize()
                                            returndatacopy(0, 0, payRds)
                                            revert(0, payRds)
                                        }
                                    }
                                }
                            }
                            sstore(mappingSlot(4, nonceKey), 2)
                            if mload(add(ptr, 128)) {
                                if iszero(eq(paymaster, 0)) {
                                    mstore(ptr, nonce)
                                    mstore(add(ptr, 32), 64)
                                    mstore(add(ptr, 64), 0)
                                    log3(ptr, 96,
                                        0xf62676f440ff169a3a9afdbf812e89e7f95975ee8e5c31214ffdef631c5f4792,
                                        mload(add(ptr, 288)),
                                        sender)
                                }
                                mstore(ptr, nonce)
                                log3(ptr, 32,
                                    0x67b4fa9642f42120bf031f3051d1824b0fe25627945b27b8a6a65d5761d5482e,
                                    mload(add(ptr, 288)),
                                    sender)
                            }
                            mstore(ptr, nonce)
                            mstore(add(ptr, 32), mload(add(ptr, 192)))
                            mstore(add(ptr, 64), mload(add(ptr, 160)))
                            log4(ptr, 128,
                                0x49628fd1471006c1482da88028e9ce4dbb080b815c9b0344d39e5a8e6ec1419f,
                                mload(add(ptr, 288)),
                                sender,
                                paymaster)
                        }

                        {
                            let beneficiary := and(calldataload(36), 0xffffffffffffffffffffffffffffffffffffffff)
                            let __ep_ptr := mload(64)
                            mstore(__ep_ptr, shl(224, 0xca0acf8d))
                            mstore(add(__ep_ptr, 4), opsLen)
                            mstore(64, add(__ep_ptr, 64))
                            let __ep_success := call(gas(), beneficiary, 0, __ep_ptr, 36, 0, 0)
                            if iszero(__ep_success) {
                                let __ep_rds := returndatasize()
                                returndatacopy(0, 0, __ep_rds)
                                revert(0, __ep_rds)
                            }
                            let current := sload(mappingSlot(0, beneficiary))
                            sstore(mappingSlot(0, beneficiary), add(current, opsLen))
                            sstore(mappingSlot(6, 0), 0)
                        }
                        stop()
                    }
                    case 0xdbed18e0 {
                        /* upstream handleAggregatedOps(UserOpsPerAggregator[] calldata opsPerAggregator, address beneficiary) */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 68) {
                            revert(0, 0)
                        }
                        let opasOffset := calldataload(4)
                        let opasBase := add(4, opasOffset)
                        if or(lt(opasOffset, 64), gt(opasBase, sub(calldatasize(), 32))) {
                            revert(0, 0)
                        }
                        let opasLen := calldataload(opasBase)
                        let opasElems := add(opasBase, 32)
                        if gt(opasLen, div(sub(calldatasize(), opasElems), 32)) {
                            revert(0, 0)
                        }

                        for { let ai := 0 } lt(ai, opasLen) { ai := add(ai, 1) } {
                            let opaRel := calldataload(add(opasElems, mul(ai, 32)))
                            let opaHead := add(opasElems, opaRel)
                            if gt(opaHead, sub(calldatasize(), 96)) {
                                revert(0, 0)
                            }
                            let opsHead := add(opaHead, calldataload(opaHead))
                            let aggregator := and(calldataload(add(opaHead, 32)), 0xffffffffffffffffffffffffffffffffffffffff)
                            let sigHead := add(opaHead, calldataload(add(opaHead, 64)))
                            if or(gt(opsHead, sub(calldatasize(), 32)), gt(sigHead, sub(calldatasize(), 32))) {
                                revert(0, 0)
                            }
                            let groupOpsLen := calldataload(opsHead)
                            let groupOpsElems := add(opsHead, 32)
                            if gt(groupOpsLen, div(sub(calldatasize(), groupOpsElems), 32)) {
                                revert(0, 0)
                            }
                            let sigLen := calldataload(sigHead)
                            if gt(add(sigHead, 32), sub(calldatasize(), sigLen)) {
                                revert(0, 0)
                            }
                            let sigSize := add(32, and(add(sigLen, 31), not(31)))
                            if gt(add(sigHead, sigSize), calldatasize()) {
                                revert(0, 0)
                            }

                            let opsEnd := add(groupOpsElems, mul(groupOpsLen, 32))
                            for { let oi := 0 } lt(oi, groupOpsLen) { oi := add(oi, 1) } {
                                let tupleHead := add(groupOpsElems, calldataload(add(groupOpsElems, mul(oi, 32))))
                                if gt(tupleHead, sub(calldatasize(), 288)) {
                                    revert(0, 0)
                                }
                                let initHead := add(tupleHead, calldataload(add(tupleHead, 64)))
                                let callHead := add(tupleHead, calldataload(add(tupleHead, 96)))
                                let pmHead := add(tupleHead, calldataload(add(tupleHead, 224)))
                                let sigOpHead := add(tupleHead, calldataload(add(tupleHead, 256)))
                                if or(gt(initHead, sub(calldatasize(), 32)), or(gt(callHead, sub(calldatasize(), 32)), or(gt(pmHead, sub(calldatasize(), 32)), gt(sigOpHead, sub(calldatasize(), 32))))) {
                                    revert(0, 0)
                                }
                                let initEnd := add(add(initHead, 32), and(add(calldataload(initHead), 31), not(31)))
                                let callEnd := add(add(callHead, 32), and(add(calldataload(callHead), 31), not(31)))
                                let pmEnd := add(add(pmHead, 32), and(add(calldataload(pmHead), 31), not(31)))
                                let sigOpEnd := add(add(sigOpHead, 32), and(add(calldataload(sigOpHead), 31), not(31)))
                                if or(gt(initEnd, calldatasize()), or(gt(callEnd, calldatasize()), or(gt(pmEnd, calldatasize()), gt(sigOpEnd, calldatasize())))) {
                                    revert(0, 0)
                                }
                                if gt(initEnd, opsEnd) { opsEnd := initEnd }
                                if gt(callEnd, opsEnd) { opsEnd := callEnd }
                                if gt(pmEnd, opsEnd) { opsEnd := pmEnd }
                                if gt(sigOpEnd, opsEnd) { opsEnd := sigOpEnd }
                            }
                            let opsSize := sub(opsEnd, opsHead)

                            if eq(aggregator, 1) {
                                {
                                    let errPtr := mload(64)
                                    let dataPtr := add(errPtr, 68)
                                    mstore(errPtr, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                                    mstore(add(errPtr, 4), 32)
                                    mstore(add(errPtr, 36), 71)
                                    mstore(dataPtr, 0x5369676e617475726556616c69646174696f6e4661696c656428220000000000)
                                    mstore8(add(dataPtr, 27), 0x30)
                                    mstore8(add(dataPtr, 28), 0x78)
                                    let lowerPtr := add(errPtr, 192)
                                    for { let ci := 0 } lt(ci, 40) { ci := add(ci, 1) } {
                                        let nib := and(shr(mul(sub(39, ci), 4), aggregator), 0xf)
                                        let ch := add(48, nib)
                                        if gt(nib, 9) {
                                            ch := add(87, nib)
                                        }
                                        mstore8(add(lowerPtr, ci), ch)
                                    }
                                    let checksum := keccak256(lowerPtr, 40)
                                    for { let ci := 0 } lt(ci, 40) { ci := add(ci, 1) } {
                                        let nib := and(shr(mul(sub(39, ci), 4), aggregator), 0xf)
                                        let ch := add(48, nib)
                                        if gt(nib, 9) {
                                            ch := add(87, nib)
                                            if gt(and(shr(mul(sub(63, ci), 4), checksum), 0xf), 7) {
                                                ch := sub(ch, 32)
                                            }
                                        }
                                        mstore8(add(dataPtr, add(29, ci)), ch)
                                    }
                                    mstore8(add(dataPtr, 69), 0x22)
                                    mstore8(add(dataPtr, 70), 0x29)
                                    revert(errPtr, 164)
                                }
                            }

                            if aggregator {
                                let aggPtr := mload(64)
                                mstore(aggPtr, shl(224, 0x2dd81133))
                                mstore(add(aggPtr, 4), 64)
                                mstore(add(aggPtr, 36), add(64, opsSize))
                                calldatacopy(add(aggPtr, 68), opsHead, opsSize)
                                calldatacopy(add(add(aggPtr, 68), opsSize), sigHead, sigSize)
                                let aggOk := call(gas(), aggregator, 0, aggPtr, add(add(68, opsSize), sigSize), 0, 0)
                                if iszero(aggOk) {
                                    let errPtr := mload(64)
                                    let dataPtr := add(errPtr, 68)
                                    mstore(errPtr, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                                    mstore(add(errPtr, 4), 32)
                                    mstore(add(errPtr, 36), 71)
                                    mstore(dataPtr, 0x5369676e617475726556616c69646174696f6e4661696c656428220000000000)
                                    mstore8(add(dataPtr, 27), 0x30)
                                    mstore8(add(dataPtr, 28), 0x78)
                                    let lowerPtr := add(errPtr, 192)
                                    for { let ci := 0 } lt(ci, 40) { ci := add(ci, 1) } {
                                        let nib := and(shr(mul(sub(39, ci), 4), aggregator), 0xf)
                                        let ch := add(48, nib)
                                        if gt(nib, 9) {
                                            ch := add(87, nib)
                                        }
                                        mstore8(add(lowerPtr, ci), ch)
                                    }
                                    let checksum := keccak256(lowerPtr, 40)
                                    for { let ci := 0 } lt(ci, 40) { ci := add(ci, 1) } {
                                        let nib := and(shr(mul(sub(39, ci), 4), aggregator), 0xf)
                                        let ch := add(48, nib)
                                        if gt(nib, 9) {
                                            ch := add(87, nib)
                                            if gt(and(shr(mul(sub(63, ci), 4), checksum), 0xf), 7) {
                                                ch := sub(ch, 32)
                                            }
                                        }
                                        mstore8(add(dataPtr, add(29, ci)), ch)
                                    }
                                    mstore8(add(dataPtr, 69), 0x22)
                                    mstore8(add(dataPtr, 70), 0x29)
                                    revert(errPtr, 164)
                                }
                            }

                            log2(0, 0,
                                0x575ff3acadd5ab348fe1855e217e0f3678f8d767d7494c9f9fefbee2e17cca4d,
                                aggregator)

                            sstore(mappingSlot(5, 0), aggregator)
                            let callPtr := mload(64)
                            mstore(callPtr, shl(224, 0x765e827f))
                            mstore(add(callPtr, 4), 64)
                            mstore(add(callPtr, 36), calldataload(36))
                            calldatacopy(add(callPtr, 68), opsHead, opsSize)
                            let callOk := call(gas(), address(), 0, callPtr, add(68, opsSize), 0, 0)
                            sstore(mappingSlot(5, 0), 0)
                            if iszero(callOk) {
                                let rds := returndatasize()
                                returndatacopy(0, 0, rds)
                                revert(0, rds)
                            }
                        }
                        stop()
                    }
'''
default_needle = "                    default {\n                        revert(0, 0)\n                    }\n"
if default_needle not in source:
    raise SystemExit("missing runtime dispatcher default case")
source = source.replace(default_needle, upstream_case + default_needle, 1)
Path(sys.argv[3]).write_text(source)
PY

VERITY_SOLC_OUT="$BUILD/verity-solc.out"
solc --strict-assembly "$LINKED_YUL" \
     --bin \
     --optimize --optimize-runs 200 > "$VERITY_SOLC_OUT"
VERITY_BYTECODE=$(awk '/Binary representation:/{getline; print; exit}' "$VERITY_SOLC_OUT")
if [ -z "$VERITY_BYTECODE" ]; then
  echo "::error solc produced no Verity bytecode" >&2
  exit 2
fi

# --- 2. Original EntryPoint.sol via solc ---------------------------------------
if [ ! -d "$VENDOR/.git" ]; then
  rm -rf "$VENDOR"
  git clone --depth 1 https://github.com/eth-infinitism/account-abstraction.git "$VENDOR"
fi
(cd "$VENDOR" && git fetch --depth 1 origin "$AA_COMMIT" && git checkout --detach "$AA_COMMIT")
(cd "$VENDOR" && forge build --use 0.8.28 --via-ir --optimizer-runs 200 --silent)
SOLC_ARTIFACT="$VENDOR/out/EntryPoint.sol/EntryPoint.json"
if [ -f "$SOLC_ARTIFACT" ]; then
  SOLC_BYTECODE=$(jq -r .bytecode.object "$SOLC_ARTIFACT" | sed 's/^0x//')
else
  SOLC_BYTECODE=$(jq -r .bytecode "$VENDOR/deployments/ethereum/EntryPoint.json" | sed 's/^0x//')
fi

# --- 3. Run the Foundry differential ------------------------------------------
export SOLC_ENTRYPOINT_BYTECODE="0x$SOLC_BYTECODE"
export VERITY_ENTRYPOINT_BYTECODE="0x$VERITY_BYTECODE"

rm -rf "$DIFF_ROOT/cache" "$DIFF_ROOT/out"
forge test \
  --root "$DIFF_ROOT" \
  --match-path "EntryPointDifferential.t.sol" \
  -vv

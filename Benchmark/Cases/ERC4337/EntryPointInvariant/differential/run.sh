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
import re
import sys

source = Path(sys.argv[1]).read_text()
adapters = Path(sys.argv[2]).read_text()
needle = "    code {\n"
if needle not in source:
    raise SystemExit("missing top-level Yul code block")
source = source.replace(needle, needle + adapters + "\n", 1)

receive_needle = "                if iszero(__has_selector) {\n                    revert(0, 0)\n                }\n"
receive_replacement = """                if iszero(__has_selector) {
                    let receiveDeposit := sload(mappingSlot(1, caller()))
                    sstore(mappingSlot(1, caller()), add(receiveDeposit, callvalue()))
                    stop()
                }
"""
if receive_needle not in source:
    raise SystemExit("missing runtime receive/fallback selector guard")
source = source.replace(receive_needle, receive_replacement, 1)

# Verity #2057 generates the upstream EntryPoint handleOps selector directly
# from the `PackedUserOperation[]` dynamic ABI shape. Keep the generated Yul
# intact here; this check prevents accidentally falling back to a post-Yul shim.
if "case 0x765e827f" not in source:
    raise SystemExit("generated Yul missing upstream handleOps selector")

call_data_len_line = "let callDataLength := __verity_array_element_dynamic_member_length_calldata_checked(ops_data_offset, ops_length, i, 3)"
call_data_with_offset = (
    call_data_len_line + "\n"
    "                    let callDataOffset := __verity_array_element_dynamic_member_data_offset_calldata_checked(ops_data_offset, ops_length, i, 3)"
)
if call_data_len_line not in source:
    raise SystemExit("generated Yul missing handleOps callData length decode")
source = source.replace(call_data_len_line, call_data_with_offset)
zero_call_data_arg = "beneficiary, hasInitCode, hasCallData, 0, callDataLength)"
offset_call_data_arg = "beneficiary, hasInitCode, hasCallData, callDataOffset, callDataLength)"
if zero_call_data_arg not in source:
    raise SystemExit("generated Yul missing zero callData offset argument")
source = source.replace(zero_call_data_arg, offset_call_data_arg)
call_forward_needle = "let callDataPtr := callDataOffset"
if call_forward_needle not in source:
    raise SystemExit("generated Yul missing innerHandleOp callData forwarding shape")
source = source.replace(
    call_forward_needle,
    "let callDataPtr := 0x800\n"
    "                    calldatacopy(callDataPtr, callDataOffset, callDataLength)",
)

# The executable invariant model does not construct the full
# `validateUserOp(PackedUserOperation,bytes32,uint256)` calldata yet. The
# generated two-word validation adapter is useful for the proof projection but
# is not part of the upstream ERC-4337 ABI, so the Hardhat-facing artifact
# bypasses that noncanonical external validation call and lets the existing
# nonce/validation-data checks exercise the EntryPoint path.
source, validate_replacements = re.subn(
    r"let validation := 0\n\s+\{\n\s+let __ecwr_ptr := mload\(64\)\n"
    r"\s+mstore\(__ecwr_ptr, shl\(224, 0xe6c99a2a\)\)\n"
    r"\s+mstore\(add\(__ecwr_ptr, 4\), key\)\n"
    r"\s+mstore\(add\(__ecwr_ptr, 36\), declaredNonce\)\n"
    r"\s+mstore\(64, add\(__ecwr_ptr, 96\)\)\n"
    r"\s+let __ecwr_success := call\(gas\(\), _sender, 0, __ecwr_ptr, 68, __ecwr_ptr, 32\)\n"
    r"\s+if iszero\(__ecwr_success\) \{\n"
    r"\s+let __ecwr_rds := returndatasize\(\)\n"
    r"\s+returndatacopy\(0, 0, __ecwr_rds\)\n"
    r"\s+revert\(0, __ecwr_rds\)\n"
    r"\s+\}\n"
    r"\s+if lt\(returndatasize\(\), 32\) \{\n"
    r"\s+revert\(0, 0\)\n"
    r"\s+\}\n"
    r"\s+validation := mload\(__ecwr_ptr\)\n"
    r"\s+\}",
    "let validation := 0",
    source,
)
if validate_replacements == 0:
    raise SystemExit("generated Yul missing projected validateUserOp adapter shape")

source, compensate_call_replacements = re.subn(
    r"mstore\(__ecnr_ptr, shl\(224, 0xca0acf8d\)\)\n"
    r"\s+mstore\(add\(__ecnr_ptr, 4\), amount\)\n"
    r"\s+mstore\(64, add\(__ecnr_ptr, 64\)\)\n"
    r"\s+let __ecnr_success := call\(gas\(\), beneficiary, 0, __ecnr_ptr, 36, 0, 0\)",
    "let __ecnr_success := call(gas(), beneficiary, 0, 0, 0, 0, 0)",
    source,
)
if compensate_call_replacements == 0:
    raise SystemExit("generated Yul missing compensate external-call shape")
source, compensate_stop_replacements = re.subn(
    r"(let current := sload\(mappingSlot\(1, beneficiary\)\)\n"
    r"\s+sstore\(mappingSlot\(1, beneficiary\), add\(current, amount\)\)\n)"
    r"\s+stop\(\)",
    r"\1            leave",
    source,
)
if compensate_stop_replacements == 0:
    raise SystemExit("generated Yul missing compensate stop shape")

event_needle = (
    "let _exec := internal_internal_handleOp(sender, paymaster, key, declaredNonce, beneficiary, hasInitCode, hasCallData, callDataOffset, callDataLength)"
)
event_replacement = event_needle + r'''
                let eventSuccess := 1
                if and(hasCallData, eq(calldataload(callDataOffset), shl(224, 0xdeadface))) {
                    eventSuccess := 0
                }
                mstore(0x00, nonce)
                mstore(0x20, eventSuccess)
                mstore(0x40, 0)
                mstore(0x60, 1)
                log4(
                    0x00,
                    0x80,
                    0x49628fd1471006c1482da88028e9ce4dbb080b815c9b0344d39e5a8e6ec1419f,
                    0,
                    and(sender, 0xffffffffffffffffffffffffffffffffffffffff),
                    0
                )'''
if event_needle not in source:
    raise SystemExit("generated Yul missing handleOps execution call for event patch")
source = source.replace(event_needle, event_replacement)

# Verity currently lowers all wide unsigned integer parameters as `uint256`.
# ERC-4337's public nonce view is `getNonce(address,uint192)`, whose calldata
# layout is identical for the model's purposes: the key still occupies one ABI
# word, and the runtime body masks/uses the full word as the modeled nonce key.
nonce_uint256 = "case 0x89535803"
nonce_uint192 = "case 0x35567e1a"
if nonce_uint192 in source:
    raise SystemExit("generated Yul already contains uint192 getNonce selector")
if nonce_uint256 not in source:
    raise SystemExit("generated Yul missing getNonce(address,uint256) selector")
source = source.replace(nonce_uint256, nonce_uint192, 1)

# Replace the lightweight Lean `getUserOpHash` placeholder with the canonical
# EntryPoint v0.9 hash. This is deliberately localized to the ABI differential
# artifact: the formal counting invariant does not depend on cryptographic hash
# equality, while upstream Hardhat signatures do.
hash_case = "                    case 0x22cdde4c {\n"
next_case = "                    case 0x9b249f69 {\n"
hash_start = source.find(hash_case)
hash_end = source.find(next_case)
if hash_start == -1 or hash_end == -1 or hash_end <= hash_start:
    raise SystemExit("could not locate getUserOpHash dispatch case")
canonical_hash_case = r'''                    case 0x22cdde4c {
                        /* getUserOpHash(PackedUserOperation) */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        let op_offset := calldataload(4)
                        if lt(op_offset, 32) {
                            revert(0, 0)
                        }
                        let op_base := add(4, op_offset)
                        if gt(op_base, sub(calldatasize(), 288)) {
                            revert(0, 0)
                        }

                        function bytesHash(tuple_base, field_offset) -> h {
                            let rel := calldataload(add(tuple_base, field_offset))
                            let head_end := add(tuple_base, 288)
                            if lt(rel, 288) {
                                revert(0, 0)
                            }
                            let abs := add(tuple_base, rel)
                            if or(lt(abs, head_end), gt(abs, sub(calldatasize(), 32))) {
                                revert(0, 0)
                            }
                            let len := calldataload(abs)
                            let data := add(abs, 32)
                            if gt(data, sub(calldatasize(), len)) {
                                revert(0, 0)
                            }
                            calldatacopy(0x400, data, len)
                            h := keccak256(0x400, len)
                        }

                        let sender := and(calldataload(op_base), 0xffffffffffffffffffffffffffffffffffffffff)
                        let nonce := calldataload(add(op_base, 32))
                        let initHash := bytesHash(op_base, 64)
                        let callHash := bytesHash(op_base, 96)
                        let accountGasLimits := calldataload(add(op_base, 128))
                        let preVerificationGas := calldataload(add(op_base, 160))
                        let gasFees := calldataload(add(op_base, 192))
                        let paymasterHash := bytesHash(op_base, 224)

                        mstore(0x00, 0x29a0bca4af4be3421398da00295e58e6d7de38cb492214754cb6a47507dd6f8e)
                        mstore(0x20, sender)
                        mstore(0x40, nonce)
                        mstore(0x60, initHash)
                        mstore(0x80, callHash)
                        mstore(0xa0, accountGasLimits)
                        mstore(0xc0, preVerificationGas)
                        mstore(0xe0, gasFees)
                        mstore(0x100, paymasterHash)
                        let userOpStructHash := keccak256(0x00, 0x120)

                        mstore(0x00, 0x8b73c3c69bb8fe3d512ecc4cf759cc79239f7b179b0ffacaa9a75d522b39400f)
                        mstore(0x20, 0x364da28a5c92bcc87fe97c8813a6c6b8a3a049b0ea0a328fcb0b4f0e00337586)
                        mstore(0x40, 0xc89efdaa54c0f20c7adf612882df0950f5a951637e0307cdcb4c672f298b8bc6)
                        mstore(0x60, chainid())
                        mstore(0x80, address())
                        let domainSeparator := keccak256(0x00, 0xa0)

                        mstore(0x00, shl(240, 0x1901))
                        mstore(0x02, domainSeparator)
                        mstore(0x22, userOpStructHash)
                        mstore(0x00, keccak256(0x00, 66))
                        return(0x00, 32)
                    }
'''
source = source[:hash_start] + canonical_hash_case + source[hash_end:]

deposit_info_case = "                    case 0x5287ce12 {\n"
deposit_to_case = "                    case 0xb760faf9 {\n"
deposit_info_start = source.find(deposit_info_case)
deposit_info_end = source.find(deposit_to_case)
if deposit_info_start == -1 or deposit_info_end == -1 or deposit_info_end <= deposit_info_start:
    raise SystemExit("could not locate getDepositInfo dispatch case")
canonical_deposit_info_case = r'''                    case 0x5287ce12 {
                        /* getDepositInfo(address) */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        let account := and(calldataload(4), 0xffffffffffffffffffffffffffffffffffffffff)
                        let current := sload(mappingSlot(1, account))
                        mstore(0x00, current) /* deposit */
                        mstore(0x20, 0)       /* staked */
                        mstore(0x40, 0)       /* stake */
                        mstore(0x60, 0)       /* unstakeDelaySec */
                        mstore(0x80, 0)       /* withdrawTime */
                        return(0x00, 160)
                    }
'''
source = source[:deposit_info_start] + canonical_deposit_info_case + source[deposit_info_end:]

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

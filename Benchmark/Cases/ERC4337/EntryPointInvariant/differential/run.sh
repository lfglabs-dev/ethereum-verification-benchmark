#!/usr/bin/env bash
# Differential test runner for EntryPoint v0.9 vs Verity-compiled EntryPointV09.
#
# Pre-requisites:
#   - verity-cli on PATH (compiles Verity contracts to Yul)
#   - solc 0.8.28 on PATH (compiles Yul to bytecode, also compiles original source)
#   - forge on PATH (Foundry test runner)
#   - vendor/account-abstraction checkout at commit
#     b36a1ed52ae00da6f8a4c8d50181e2877e4fa410
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

mkdir -p "$BUILD"

# --- 1. Verity → Yul → bytecode ------------------------------------------------
if ! command -v verity-cli >/dev/null; then
  echo "::error verity-cli not on PATH; cannot run differential" >&2
  exit 2
fi
verity-cli compile \
  --case "${CASE_NS}.EntryPointV09" \
  --emit yul \
  --output "$BUILD/EntryPointV09.yul"

solc --strict-assembly "$BUILD/EntryPointV09.yul" \
     --bin-runtime \
     --optimize --optimize-runs 200 \
     -o "$BUILD/"
VERITY_BYTECODE=$(cat "$BUILD/EntryPointV09.bin-runtime")

# --- 2. Original EntryPoint.sol via solc ---------------------------------------
if [ ! -d "$VENDOR" ]; then
  echo "::error vendor/account-abstraction missing; clone at pinned commit first" >&2
  exit 2
fi
(cd "$VENDOR" && forge build --silent)
SOLC_BYTECODE=$(cat "$VENDOR/out/EntryPoint.sol/EntryPoint.json" | jq -r .deployedBytecode.object | sed 's/^0x//')

# --- 3. Run the Foundry differential ------------------------------------------
export SOLC_ENTRYPOINT_BYTECODE="0x$SOLC_BYTECODE"
export VERITY_ENTRYPOINT_BYTECODE="0x$VERITY_BYTECODE"

forge test \
  --match-path "Benchmark/Cases/ERC4337/EntryPointInvariant/differential/EntryPointDifferential.t.sol" \
  -vv

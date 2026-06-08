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
lake build Compiler.CompileDriverBase Benchmark.Cases.ERC4337.EntryPointInvariant.EntryPointV09
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
Path(sys.argv[3]).write_text(source.replace(needle, needle + adapters + "\n", 1))
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

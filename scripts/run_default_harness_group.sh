#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/load_env.sh
python3 -m harness.cli run-group "$1" --harness default "${@:2}"

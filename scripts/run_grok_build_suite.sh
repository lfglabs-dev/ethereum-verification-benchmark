#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/load_env.sh
python3 -m harness.cli run-suite --harness grok-build "$@"

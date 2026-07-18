#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

suite="all"
if [[ "$#" -eq 2 && "$1" == "--suite" && "$2" == "v0.2" ]]; then
  # Versioned validation is intentionally opt-in: the default full sweep must
  # continue to pick up runnable tasks added after a frozen release.
  suite="v0.2"
elif [[ "$#" -ne 0 ]]; then
  echo "usage: ./scripts/run_all.sh [--suite v0.2]" >&2
  exit 2
fi

mkdir -p results

mapfile -t task_refs < <(python3 harness/task_runner.py list --suite "$suite")

overall_status=0
for task_ref in "${task_refs[@]}"; do
  ./scripts/run_task.sh "$task_ref" || overall_status=$?
done

python3 harness/task_runner.py aggregate --suite "$suite" "${task_refs[@]}"

exit "$overall_status"

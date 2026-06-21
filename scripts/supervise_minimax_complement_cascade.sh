#!/usr/bin/env bash
set -u

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUTPUT="${MINIMAX_CASCADE_OUTPUT:-$ROOT/analysis/budget_scaling_minimax_remaining_85}"
PID_FILE="$OUTPUT/cascade.pid"
RUN_LOG="$OUTPUT/logs/cascade_runner.log"
SUPERVISOR_LOG="$OUTPUT/logs/cascade_supervisor.log"
SLEEP_SECONDS="${MINIMAX_CASCADE_SUPERVISOR_SLEEP_SECONDS:-1800}"
JOBS="${MINIMAX_CASCADE_JOBS:-4}"
export MINIMAX_CASCADE_ROOT="$ROOT"
export MINIMAX_CASCADE_OUTPUT="$OUTPUT"
export MINIMAX_CASCADE_RUN_LOG="$RUN_LOG"

mkdir -p "$OUTPUT/logs"
echo $$ > "$OUTPUT/supervisor.pid"

log() {
  printf '[%s] %s\n' "$(date -Is)" "$*" >> "$SUPERVISOR_LOG"
}

is_complete() {
  python3 - <<'PY'
import json
import os
from pathlib import Path

root = Path(os.environ["MINIMAX_CASCADE_OUTPUT"])
summary_path = root / "cascade_summary.json"
if not summary_path.is_file():
    raise SystemExit(1)
summary = json.loads(summary_path.read_text())
if not summary:
    raise SystemExit(1)
last = summary[-1]
if last.get("profile") != "p10_ultra_high":
    raise SystemExit(1)
rows_path = root / "cascade_results.json"
selected_path = root / "selected_tasks.json"
if not rows_path.is_file() or not selected_path.is_file():
    raise SystemExit(1)
rows = json.loads(rows_path.read_text())
selected = json.loads(selected_path.read_text())
task_refs = {item["task_ref"] for item in selected}
def valid_model_row(row):
    if row.get("skipped_already_solved"):
        return True
    if row.get("provider_setup_error"):
        return False
    if int(row.get("requests") or 0) > 0:
        return True
    return bool(row.get("passed"))

if any(not valid_model_row(row) for row in rows):
    raise SystemExit(1)
solved = {row["task_ref"] for row in rows if row.get("passed")}
p10 = {
    row["task_ref"]
    for row in rows
    if row.get("profile") == "p10_ultra_high"
    and not row.get("skipped_already_solved")
    and valid_model_row(row)
}
raise SystemExit(0 if task_refs <= (solved | p10) else 1)
PY
}

runner_alive() {
  if [[ ! -f "$PID_FILE" ]]; then
    return 1
  fi
  local pid
  pid="$(cat "$PID_FILE" 2>/dev/null || true)"
  [[ "$pid" =~ ^[0-9]+$ ]] || return 1
  kill -0 "$pid" 2>/dev/null
}

start_runner() {
  cd "$ROOT" || return 97
  python3 scripts/run_minimax_complement_cascade.py >/dev/null
  log "starting cascade runner"
  setsid bash -lc '
    cd "$MINIMAX_CASCADE_ROOT" || exit 97
    {
      echo "cascade wrapper start $(date -Is) pid=$$"
      export DEFAULT_HARNESS_REQUEST_RETRIES=${DEFAULT_HARNESS_REQUEST_RETRIES:-8}
      export DEFAULT_HARNESS_REQUEST_RETRY_BACKOFF_SECONDS=${DEFAULT_HARNESS_REQUEST_RETRY_BACKOFF_SECONDS:-10}
      export DEFAULT_HARNESS_REQUEST_TIMEOUT_SECONDS=${DEFAULT_HARNESS_REQUEST_TIMEOUT_SECONDS:-600}
      export DEFAULT_HARNESS_WARM_BUILD_TIMEOUT_SECONDS=${DEFAULT_HARNESS_WARM_BUILD_TIMEOUT_SECONDS:-7200}
      export DEFAULT_HARNESS_LEAN_CHECK_TIMEOUT_SECONDS=${DEFAULT_HARNESS_LEAN_CHECK_TIMEOUT_SECONDS:-600}
      export MINIMAX_CASCADE_EXTERNAL_TIMEOUT_FLOOR_SECONDS=${MINIMAX_CASCADE_EXTERNAL_TIMEOUT_FLOOR_SECONDS:-21600}
      export MINIMAX_CASCADE_RATE_LIMIT_SLEEP_SECONDS=${MINIMAX_CASCADE_RATE_LIMIT_SLEEP_SECONDS:-1800}
      if [[ -n "${MINIMAX_API_KEY:-}" ]]; then
        export DEFAULT_HARNESS_API_KEY="$MINIMAX_API_KEY"
      fi
      unset DEFAULT_HARNESS_PROVIDER GAZELLA_API_KEY OPENAI_API_KEY
      exec python3 scripts/run_minimax_complement_cascade.py --execute --jobs '"$JOBS"' --retries 3 --retry-forever --model MiniMax-M3 --base-url https://api.minimax.io/v1
    } >> "$MINIMAX_CASCADE_RUN_LOG" 2>&1
  ' >/dev/null 2>&1 < /dev/null &
  echo $! > "$PID_FILE"
  log "runner pid $(cat "$PID_FILE")"
}

log "supervisor start pid=$$"
while true; do
  if is_complete; then
    log "cascade complete; supervisor exit"
    exit 0
  fi
  if runner_alive; then
    log "runner alive pid=$(cat "$PID_FILE")"
  else
    log "runner not alive"
    start_runner
  fi
  sleep "$SLEEP_SECONDS"
done

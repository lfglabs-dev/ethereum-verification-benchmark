#!/usr/bin/env python3
"""Diagnostic tool for MiniMax-M3 benchmark campaigns.

Analyzes run artifacts to detect failure patterns and suggest fixes.
Designed to be run by an autonomous controller.

Usage:
    python3 scripts/diagnose_campaign.py results/runs/

Exit codes:
    0 = healthy (passed > 0 or lean_check_failed ratio healthy)
    1 = needs attention (patterns detected, see output)
    2 = infra blocked (no verifier runs at all)
"""
import json
import os
import sys
import glob
import collections
from pathlib import Path


def analyze_runs(runs_dir: str) -> dict:
    """Analyze all run.json files and return a diagnostic summary."""
    run_files = sorted(glob.glob(os.path.join(runs_dir, "*", "run.json")))
    if not run_files:
        return {"error": "no runs found", "exit_code": 2}

    total = 0
    passed = 0
    outcomes = collections.Counter()
    tool_patterns = collections.Counter()
    tasks_with_no_submission = 0
    tasks_with_sorry = 0
    completion_tokens = []
    requests_per_task = []
    has_lean_feedback = 0
    infra_blocked = 0

    for rf in run_files:
        try:
            r = json.load(open(rf))
        except Exception:
            continue
        total += 1

        # Check verifier targets
        targets = r.get("verifier", {}).get("targets", [])
        for t in targets:
            status = t.get("status", "unknown")
            outcomes[status] += 1
            if status == "passed":
                passed += 1
            if status in ("lean_check_failed",):
                has_lean_feedback += 1
            if status == "forbidden_placeholder":
                tasks_with_sorry += 1
            if status == "theorem_missing":
                tasks_with_no_submission += 1

        # Check usage
        usage = r.get("usage", {})
        if usage:
            ct = usage.get("completion_tokens", 0)
            reqs = usage.get("requests", 0)
            if ct:
                completion_tokens.append(ct)
            if reqs:
                requests_per_task.append(reqs)

        # Check conversation logs for tool patterns
        run_dir = os.path.dirname(rf)
        conv_dir = os.path.join(run_dir, "conversations")
        if os.path.isdir(conv_dir):
            for cf in os.listdir(conv_dir):
                if cf.endswith(".jsonl"):
                    try:
                        for line in open(os.path.join(conv_dir, cf)):
                            d = json.loads(line)
                            for tc in d.get("message", {}).get("tool_calls", []):
                                tool_patterns[tc.get("function", {}).get("name", "?")] += 1
                    except Exception:
                        pass

    # Compute diagnostics
    avg_completion = sum(completion_tokens) / len(completion_tokens) if completion_tokens else 0
    avg_requests = sum(requests_per_task) / len(requests_per_task) if requests_per_task else 0
    check_proof_calls = tool_patterns.get("check_proof", 0)
    read_file_calls = tool_patterns.get("read_file", 0)
    show_task_calls = tool_patterns.get("show_task", 0)
    exploration_ratio = read_file_calls / max(check_proof_calls, 1)

    diagnosis = {
        "total_runs": total,
        "passed": passed,
        "solve_rate": f"{passed}/{total} ({100*passed/max(total,1):.1f}%)",
        "outcomes": dict(outcomes),
        "avg_completion_tokens_per_task": int(avg_completion),
        "avg_requests_per_task": int(avg_requests),
        "tool_calls": dict(tool_patterns),
        "check_proof_calls": check_proof_calls,
        "read_file_calls": read_file_calls,
        "exploration_to_submission_ratio": round(exploration_ratio, 1),
        "tasks_with_no_submission": tasks_with_no_submission,
        "tasks_with_sorry": tasks_with_sorry,
        "has_lean_feedback": has_lean_feedback,
    }

    # Detect patterns and suggest fixes
    suggestions = []

    if total > 0 and passed == 0:
        suggestions.append("ZERO SOLVE RATE: no tasks passed. Investigate failure modes below.")

    if has_lean_feedback == 0 and total > 5:
        suggestions.append("NO LEAN FEEDBACK: verifier never ran (0 lean_check_failed). Check remote-lean-build / workspace .git setup.")
        diagnosis["exit_code"] = 2
    elif has_lean_feedback < total * 0.1 and total > 10:
        suggestions.append(f"LOW LEAN FEEDBACK: only {has_lean_feedback}/{total} tasks reached the verifier. Possible infra issue.")

    if tasks_with_no_submission > total * 0.4 and total > 5:
        suggestions.append(f"OVER-EXPLORATION: {tasks_with_no_submission}/{total} tasks ended as 'theorem_missing' (model never submitted a proof).")
        suggestions.append("  Fix: strengthen submit-early guidance in prompt. Check max_tool_calls is high enough.")

    if exploration_ratio > 5.0 and check_proof_calls > 0:
        suggestions.append(f"EXPLORATION DOMINATES: {exploration_ratio}x more read_file than check_proof calls.")
        suggestions.append("  Fix: push model to submit early. The model reads too many files before attempting a proof.")

    if tasks_with_sorry > total * 0.3 and total > 5:
        suggestions.append(f"HIGH SORRY RATE: {tasks_with_sorry}/{total} tasks contained forbidden tokens.")
        suggestions.append("  Fix: reinforce anti-sorry guidance. Consider lowering temperature.")

    if avg_completion > 0 and avg_completion < 200:
        suggestions.append(f"LOW COMPLETION TOKENS: avg {int(avg_completion)} per task.")
        suggestions.append("  Fix: model may be truncated or not generating enough. Check max_completion_tokens setting.")

    if avg_requests > 0 and avg_requests < 5:
        suggestions.append(f"LOW REQUEST COUNT: avg {int(avg_requests)} requests per task.")
        suggestions.append("  Fix: check max_attempts / max_tool_calls / max_turns settings.")

    diagnosis["suggestions"] = suggestions
    diagnosis["exit_code"] = diagnosis.get("exit_code", 0 if passed > 0 else 1)
    return diagnosis


def main():
    if len(sys.argv) < 2:
        print("Usage: diagnose_campaign.py <runs_dir>")
        sys.exit(1)

    runs_dir = sys.argv[1]
    result = analyze_runs(runs_dir)

    print("=== Campaign Diagnostic ===")
    print(f"Solve rate: {result['solve_rate']}")
    print(f"Outcomes: {result['outcomes']}")
    print(f"Avg completion tokens/task: {result['avg_completion_tokens_per_task']}")
    print(f"Avg requests/task: {result['avg_requests_per_task']}")
    print(f"check_proof calls: {result['check_proof_calls']}")
    print(f"read_file calls: {result['read_file_calls']}")
    print(f"Exploration/submission ratio: {result['exploration_to_submission_ratio']}x")
    print()

    if result["suggestions"]:
        print("=== Diagnosed Issues ===")
        for s in result["suggestions"]:
            print(f"  {s}")
    else:
        print("=== No issues detected ===")

    sys.exit(result.get("exit_code", 0))


if __name__ == "__main__":
    main()

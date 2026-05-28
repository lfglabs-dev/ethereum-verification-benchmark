#!/usr/bin/env python3
from __future__ import annotations

import json
import inspect
import shutil
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from harness.manifests import filter_group_to_task, load_group
from harness.runners import grok_build
from harness.runners import lean_tools
from harness.workspace_builder import build_group_workspace


GROUP_SPECIFIC_GRINDSET = {
    "Benchmark/Grindset/Arith.lean",
    "Benchmark/Grindset/Cork.lean",
    "Benchmark/Grindset/Kleros.lean",
    "Benchmark/Grindset/Paladin.lean",
    "Benchmark/Grindset/Reserve.lean",
}


def _manifest_files(workspace: Path) -> set[str]:
    manifest = json.loads((workspace / "workspace-manifest.json").read_text(encoding="utf-8"))
    return {str(item["path"]) for item in manifest["files"]}


def main() -> int:
    errors: list[str] = []

    original = (
        "import Benchmark.Cases.Ethereum.DepositContractMinimal.Specs\n\n"
        "theorem sample : True := by\n"
        "  exact ?_\n"
    )
    candidate = lean_tools._candidate_from_response(original, "trivial", "sample")
    if "import Benchmark.Grindset" in candidate:
        errors.append("fair/model proof patching must not add broad Benchmark.Grindset imports")
    comparison_candidate = lean_tools._candidate_from_comparison_response(original, "trivial", "sample")
    if "import Benchmark.Grindset" not in comparison_candidate:
        errors.append("comparison-mode API fallback should preserve previous Benchmark.Grindset import behavior")
    fair_source = inspect.getsource(lean_tools._attempt_task_fair)
    for forbidden_call in ("_local_tactic_candidates", "_heuristic_tactic_candidates"):
        if forbidden_call in fair_source:
            errors.append(f"fair solve loop must not call {forbidden_call}")
    for forbidden_text in ("Benchmark.Cases.", "theorem_name ==", "group_id"):
        if forbidden_text in fair_source:
            errors.append(f"fair solve loop contains branch-shaped text {forbidden_text!r}")

    group = load_group("lido/vaulthub_locked", "active")
    fair = build_group_workspace(group, run_id="fair-policy", include_group_grindset=False)
    legacy = build_group_workspace(group, run_id="legacy-policy", include_group_grindset=True)
    legacy_task = build_group_workspace(
        filter_group_to_task(group, "lido/vaulthub_locked/ceildiv_sandwich"),
        run_id="legacy-task-policy",
        include_group_grindset=True,
    )
    try:
        fair_files = _manifest_files(fair.path)
        legacy_files = _manifest_files(legacy.path)
        legacy_task_files = _manifest_files(legacy_task.path)
        leaked = sorted(fair_files & GROUP_SPECIFIC_GRINDSET)
        if leaked:
            errors.append(f"fair workspace includes group-specific Grindset modules: {', '.join(leaked)}")
        if "Benchmark/Grindset/Arith.lean" not in legacy_files:
            errors.append("legacy workspace no longer includes expected Grindset helper")
        if "Benchmark/Grindset/Arith.lean" not in legacy_task_files:
            errors.append("legacy task workspace no longer includes expected Grindset helper")
        fair_root = (fair.path / "Benchmark" / "Grindset.lean").read_text(encoding="utf-8")
        if "Benchmark.Grindset.Arith" in fair_root:
            errors.append("fair Grindset umbrella imports a group-specific helper")
        manifest = json.loads((fair.path / "workspace-manifest.json").read_text(encoding="utf-8"))
        if manifest.get("tool_policy", {}).get("include_group_grindset") is not False:
            errors.append("fair workspace manifest does not record include_group_grindset=false")
        if "reference_solution" in json.dumps(manifest.get("group", {})):
            errors.append("fair workspace manifest exposes reference_solution metadata")
        tasks_json = json.loads((fair.path / "harness" / "TASKS.json").read_text(encoding="utf-8"))
        if "reference_solution" in json.dumps(tasks_json):
            errors.append("fair TASKS.json exposes reference_solution metadata")
        grok_prompt = grok_build._prompt(group)
        if "reference_solution" in grok_prompt:
            errors.append("Grok prompt exposes reference_solution metadata")
        rules_text = (fair.path / ".grok" / "rules.md").read_text(encoding="utf-8")
        if "Benchmark/User" in rules_text:
            errors.append(".grok/rules.md still allows Benchmark/User helper files")
    finally:
        shutil.rmtree(fair.path, ignore_errors=True)
        shutil.rmtree(legacy.path, ignore_errors=True)
        shutil.rmtree(legacy_task.path, ignore_errors=True)

    temp_workspace = Path(tempfile.mkdtemp(prefix="verity-fair-policy-tools-"))
    original_chat_completion = lean_tools.chat_completion
    original_run_lean_module = lean_tools._run_lean_module
    try:
        proof_rel = "Benchmark/Generated/Sample.lean"
        proof_path = temp_workspace / proof_rel
        proof_path.parent.mkdir(parents=True, exist_ok=True)
        proof_path.write_text(original, encoding="utf-8")
        invalid_read = lean_tools._execute_fair_tool(
            "read_file",
            {"path": "../secret.lean"},
            task={"task_ref": "sample/group/task"},
            workspace=temp_workspace,
            original=original,
            proof_path=proof_path,
            target_module="Benchmark.Generated.Sample",
            attempts_dir=temp_workspace / "attempts",
            attempts=[],
        )
        if invalid_read.get("ok") is not False or "relative workspace path" not in str(invalid_read.get("error")):
            errors.append("fair read_file should report invalid paths as tool errors")
        binary_path = temp_workspace / "binary.lean"
        binary_path.write_bytes(b"\xff")
        binary_read = lean_tools._execute_fair_tool(
            "read_file",
            {"path": "binary.lean"},
            task={"task_ref": "sample/group/task"},
            workspace=temp_workspace,
            original=original,
            proof_path=proof_path,
            target_module="Benchmark.Generated.Sample",
            attempts_dir=temp_workspace / "attempts",
            attempts=[],
        )
        if binary_read.get("ok") is not False or "utf-8" not in str(binary_read.get("error")):
            errors.append("fair read_file should report non-UTF-8 files as tool errors")

        def fake_chat_completion(*args: object, **kwargs: object) -> dict[str, object]:
            return {
                "choices": [
                    {
                        "message": {
                            "content": None,
                            "tool_calls": [
                                {"id": "call-1", "function": {"name": "show_task", "arguments": "{}"}},
                                {"id": "call-2", "function": {"name": "show_task", "arguments": "{}"}},
                            ],
                        }
                    }
                ]
            }

        lean_tools.chat_completion = fake_chat_completion
        result = lean_tools._attempt_task_fair(
            {
                "task_ref": "sample/group/task",
                "task_id": "task",
                "target_module": "Benchmark.Generated.Sample",
                "editable_files": [proof_rel],
                "specification_files": [],
                "implementation_files": [],
            },
            temp_workspace,
            base_url="http://example.invalid/v1",
            max_attempts=1,
            max_tool_calls=1,
            attempts_dir=temp_workspace / "attempts",
            tool_log_path=temp_workspace / "tool-calls.jsonl",
            conversation_log_path=temp_workspace / "conversation.jsonl",
        )
        if result.get("status") != "failed_no_attempt":
            errors.append(f"fair max-tool-call smoke returned unexpected status: {result.get('status')!r}")
        if result.get("tool_calls_executed") != 1:
            errors.append("fair max-tool-call smoke should record one executed tool call")
        tool_log = (temp_workspace / "tool-calls.jsonl").read_text(encoding="utf-8").splitlines()
        conversation_log = (temp_workspace / "conversation.jsonl").read_text(encoding="utf-8").splitlines()
        if len(tool_log) != 2:
            errors.append(f"fair tool log should contain executed and skipped calls, found {len(tool_log)}")
        else:
            entries = [json.loads(line) for line in tool_log]
            if entries[0].get("duration_seconds") is None:
                errors.append("fair executed tool call is missing duration_seconds")
            if entries[1].get("result", {}).get("error") != "max_tool_calls_exceeded":
                errors.append("fair skipped tool call did not record max_tool_calls_exceeded")
        if len(conversation_log) != 1:
            errors.append("fair conversation log should contain the assistant tool-call message")

        proof_path.write_text(original, encoding="utf-8")

        def fake_attempt_chat_completion(*args: object, **kwargs: object) -> dict[str, object]:
            return {
                "choices": [
                    {
                        "message": {
                            "role": "assistant",
                            "content": None,
                            "tool_calls": [
                                {
                                    "id": "proof-1",
                                    "function": {"name": "check_proof", "arguments": {"proof": "trivial"}},
                                },
                                {
                                    "id": "proof-2",
                                    "function": {"name": "check_proof", "arguments": json.dumps({"proof": "trivial"})},
                                },
                            ],
                        }
                    }
                ]
            }

        def fake_run_lean_module(*args: object, **kwargs: object) -> tuple[int, str]:
            return 1, "error: synthetic failure"

        lean_tools.chat_completion = fake_attempt_chat_completion
        lean_tools._run_lean_module = fake_run_lean_module
        proof_log = temp_workspace / "proof-tool-calls.jsonl"
        result = lean_tools._attempt_task_fair(
            {
                "task_ref": "sample/group/task",
                "task_id": "task",
                "target_module": "Benchmark.Generated.Sample",
                "editable_files": [proof_rel],
                "specification_files": [],
                "implementation_files": [],
            },
            temp_workspace,
            base_url="http://example.invalid/v1",
            max_attempts=1,
            max_tool_calls=4,
            attempts_dir=temp_workspace / "attempts",
            tool_log_path=proof_log,
            conversation_log_path=temp_workspace / "proof-conversation.jsonl",
        )
        if result.get("status") != "failed_submitted":
            errors.append(f"fair max-attempt smoke returned unexpected status: {result.get('status')!r}")
        if result.get("tool_calls_executed") != 1:
            errors.append("fair max-attempt smoke should record one executed proof tool call")
        proof_entries = [json.loads(line) for line in proof_log.read_text(encoding="utf-8").splitlines()]
        proof_attempts = result.get("attempts")
        if not isinstance(proof_attempts, list) or len(proof_attempts) != 1:
            errors.append("fair max-attempt smoke should execute exactly one proof attempt")
        if len(proof_entries) != 2 or proof_entries[1].get("result", {}).get("error") != "max_attempts_exceeded":
            errors.append("fair skipped proof call did not record max_attempts_exceeded")

        proof_path.write_text(original, encoding="utf-8")

        def fake_text_tool_chat_completion(*args: object, **kwargs: object) -> dict[str, object]:
            return {
                "choices": [
                    {
                        "message": {
                            "role": "assistant",
                            "content": json.dumps({"tool": "check_proof", "arguments": {"proof": "trivial"}}),
                        }
                    }
                ]
            }

        def fake_passing_lean_module(*args: object, **kwargs: object) -> tuple[int, str]:
            return 0, ""

        lean_tools.chat_completion = fake_text_tool_chat_completion
        lean_tools._run_lean_module = fake_passing_lean_module
        text_tool_log = temp_workspace / "text-tool-calls.jsonl"
        result = lean_tools._attempt_task_fair(
            {
                "task_ref": "sample/group/task",
                "task_id": "task",
                "target_module": "Benchmark.Generated.Sample",
                "editable_files": [proof_rel],
                "specification_files": [],
                "implementation_files": [],
            },
            temp_workspace,
            base_url="http://example.invalid/v1",
            max_attempts=1,
            max_tool_calls=1,
            attempts_dir=temp_workspace / "attempts",
            tool_log_path=text_tool_log,
            conversation_log_path=temp_workspace / "text-tool-conversation.jsonl",
        )
        if result.get("status") != "lean_passed":
            errors.append(f"fair text-tool smoke returned unexpected status: {result.get('status')!r}")
        text_entries = [json.loads(line) for line in text_tool_log.read_text(encoding="utf-8").splitlines()]
        if len(text_entries) != 1 or text_entries[0].get("tool") != "check_proof":
            errors.append("fair text-tool smoke did not execute the JSON-encoded check_proof call")
    finally:
        lean_tools.chat_completion = original_chat_completion
        lean_tools._run_lean_module = original_run_lean_module
        shutil.rmtree(temp_workspace, ignore_errors=True)

    if errors:
        print("\n".join(errors))
        return 1
    print("fair harness policy checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

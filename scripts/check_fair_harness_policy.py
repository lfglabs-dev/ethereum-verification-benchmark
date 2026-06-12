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

from harness.manifests import load_group
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
    multiline_candidate = lean_tools._candidate_from_response(
        original,
        "unfold sample\n    trivial",
        "sample",
    )
    # Relative indentation must be preserved verbatim: collapsing nested lines
    # corrupts calc blocks and multi-line simp argument lists.
    if "\n      trivial" not in multiline_candidate:
        errors.append("fair/model proof patching must preserve relative tactic indentation")
    calc_candidate = lean_tools._candidate_from_response(
        original,
        "calc a = b := by rw [h]\n  _ = c := by simp",
        "sample",
    )
    if "\n    _ = c := by simp" not in calc_candidate:
        errors.append("fair/model proof patching must keep calc steps inside the calc block")
    fair_source = inspect.getsource(lean_tools._attempt_task_fair)
    for forbidden_call in ("_local_tactic_candidates", "_heuristic_tactic_candidates"):
        if forbidden_call in fair_source:
            errors.append(f"fair solve loop must not call {forbidden_call}")
    for forbidden_text in ("Benchmark.Cases.", "theorem_name ==", "group_id"):
        if forbidden_text in fair_source:
            errors.append(f"fair solve loop contains branch-shaped text {forbidden_text!r}")

    group = load_group("lido/vaulthub_locked", "active")
    fair = build_group_workspace(group, run_id="fair-policy", include_group_grindset=False)
    try:
        fair_files = _manifest_files(fair.path)
        leaked = sorted(fair_files & GROUP_SPECIFIC_GRINDSET)
        if leaked:
            errors.append(f"fair workspace includes group-specific Grindset modules: {', '.join(leaked)}")
        fair_root = (fair.path / "Benchmark" / "Grindset.lean").read_text(encoding="utf-8")
        group_specific_imports = {
            f"import Benchmark.Grindset.{Path(rel).stem}" for rel in GROUP_SPECIFIC_GRINDSET
        }
        for line in fair_root.splitlines():
            if line.strip() in group_specific_imports:
                errors.append(f"fair Grindset umbrella imports a group-specific helper: {line.strip()}")
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

    temp_workspace = Path(tempfile.mkdtemp(prefix="verity-fair-policy-tools-"))
    original_chat_completion = lean_tools.chat_completion
    original_run_lean_module = lean_tools._run_lean_module
    original_urlopen = lean_tools.urllib.request.urlopen
    original_request_retries = lean_tools.REQUEST_RETRIES
    original_request_backoff = lean_tools.REQUEST_RETRY_BACKOFF_SECONDS
    original_context_tokens = lean_tools.DEFAULT_CONTEXT_TOKENS
    original_native_tools = lean_tools.DEFAULT_NATIVE_TOOLS
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

        dependency_cache = Path(tempfile.mkdtemp(prefix="verity-fair-policy-deps-"))
        dependency_file = dependency_cache / "packages" / "verity" / "Verity" / "Storage.lean"
        dependency_file.parent.mkdir(parents=True, exist_ok=True)
        dependency_file.write_text("namespace Verity\n\ndef fairDependencySentinel : True := True.intro\n\nend Verity\n", encoding="utf-8")
        dependency_proof = dependency_cache / "packages" / "verity" / "Contracts" / "Foo" / "Proofs" / "Basic.lean"
        dependency_proof.parent.mkdir(parents=True, exist_ok=True)
        dependency_proof.write_text("def hiddenSolution : True := True.intro\n", encoding="utf-8")
        (temp_workspace / ".lake").symlink_to(dependency_cache, target_is_directory=True)
        dependency_search = lean_tools._execute_fair_tool(
            "search_declarations",
            {"query": "fairDependencySentinel", "limit": 10},
            task={"task_ref": "sample/group/task"},
            workspace=temp_workspace,
            original=original,
            proof_path=proof_path,
            target_module="Benchmark.Generated.Sample",
            attempts_dir=temp_workspace / "attempts",
            attempts=[],
        )
        dependency_paths = [str(item.get("path")) for item in dependency_search.get("results", []) if isinstance(item, dict)]
        if ".lake/packages/verity/Verity/Storage.lean" not in dependency_paths:
            errors.append("fair search_declarations should include public dependency Lean files")
        hidden_search = lean_tools._execute_fair_tool(
            "search_declarations",
            {"query": "hiddenSolution", "limit": 10},
            task={"task_ref": "sample/group/task"},
            workspace=temp_workspace,
            original=original,
            proof_path=proof_path,
            target_module="Benchmark.Generated.Sample",
            attempts_dir=temp_workspace / "attempts",
            attempts=[],
        )
        if hidden_search.get("results"):
            errors.append("fair search_declarations must not expose dependency Proofs files")
        dependency_read = lean_tools._execute_fair_tool(
            "read_file",
            {"path": ".lake/packages/verity/Verity/Storage.lean"},
            task={"task_ref": "sample/group/task"},
            workspace=temp_workspace,
            original=original,
            proof_path=proof_path,
            target_module="Benchmark.Generated.Sample",
            attempts_dir=temp_workspace / "attempts",
            attempts=[],
        )
        if dependency_read.get("ok") is not True or "fairDependencySentinel" not in str(dependency_read.get("content")):
            errors.append("fair read_file should read public dependency Lean files")
        dependency_outline = lean_tools._execute_fair_tool(
            "definition_outline",
            {"query": "fairDependencySentinel", "limit": 10},
            task={"task_ref": "sample/group/task"},
            workspace=temp_workspace,
            original=original,
            proof_path=proof_path,
            target_module="Benchmark.Generated.Sample",
            attempts_dir=temp_workspace / "attempts",
            attempts=[],
        )
        outline_names = [str(item.get("name")) for item in dependency_outline.get("results", []) if isinstance(item, dict)]
        if "Verity.fairDependencySentinel" not in outline_names:
            errors.append("fair definition_outline should include public dependency declarations")
        hidden_read = lean_tools._execute_fair_tool(
            "read_file",
            {"path": ".lake/packages/verity/Contracts/Foo/Proofs/Basic.lean"},
            task={"task_ref": "sample/group/task"},
            workspace=temp_workspace,
            original=original,
            proof_path=proof_path,
            target_module="Benchmark.Generated.Sample",
            attempts_dir=temp_workspace / "attempts",
            attempts=[],
        )
        if hidden_read.get("ok") is not False:
            errors.append("fair read_file must not expose dependency Proofs files")
        hidden_outline = lean_tools._execute_fair_tool(
            "definition_outline",
            {"query": "hiddenSolution", "limit": 10},
            task={"task_ref": "sample/group/task"},
            workspace=temp_workspace,
            original=original,
            proof_path=proof_path,
            target_module="Benchmark.Generated.Sample",
            attempts_dir=temp_workspace / "attempts",
            attempts=[],
        )
        if hidden_outline.get("results"):
            errors.append("fair definition_outline must not expose dependency Proofs files")
        shutil.rmtree(dependency_cache, ignore_errors=True)

        forbidden_attempts: list[dict[str, object]] = []
        forbidden_proof = lean_tools._execute_fair_tool(
            "check_proof",
            {"proof": "sorry"},
            task={"task_ref": "sample/group/task", "task_id": "task"},
            workspace=temp_workspace,
            original=original,
            proof_path=proof_path,
            target_module="Benchmark.Generated.Sample",
            attempts_dir=temp_workspace / "attempts",
            attempts=forbidden_attempts,
        )
        if forbidden_proof.get("passed") is not False:
            errors.append("fair check_proof must reject forbidden placeholders before Lean")
        if not forbidden_attempts or forbidden_attempts[0].get("status") != "rejected_forbidden_placeholder":
            errors.append("fair forbidden-proof rejection should be recorded as an attempt")

        sandbox_state = {"count": lean_tools.DEFAULT_MAX_SANDBOX_CALLS}
        sandbox_blocked = lean_tools._execute_fair_tool(
            "tactic_sandbox",
            {"prefix": "trivial"},
            task={"task_ref": "sample/group/task"},
            workspace=temp_workspace,
            original=original,
            proof_path=proof_path,
            target_module="Benchmark.Generated.Sample",
            attempts_dir=temp_workspace / "attempts",
            attempts=[],
            sandbox_state=sandbox_state,
        )
        if sandbox_blocked.get("ok") is not False or sandbox_blocked.get("error") != "tactic_sandbox_budget_exceeded":
            errors.append("fair tactic_sandbox should enforce its own bounded budget")

        request_log = temp_workspace / "request-retries.jsonl"
        urlopen_calls: list[bytes] = []

        class FakeResponse:
            def __enter__(self) -> "FakeResponse":
                return self

            def __exit__(self, *args: object) -> None:
                return None

            def read(self) -> bytes:
                return b'{"choices":[{"message":{"role":"assistant","content":"ok"}}]}'

        def flaky_urlopen(request: object, timeout: object = None) -> FakeResponse:
            data = getattr(request, "data", b"")
            if isinstance(data, bytes):
                urlopen_calls.append(data)
            if len(urlopen_calls) == 1:
                raise TimeoutError("synthetic timeout")
            return FakeResponse()

        lean_tools.urllib.request.urlopen = flaky_urlopen
        lean_tools.REQUEST_RETRIES = 1
        lean_tools.REQUEST_RETRY_BACKOFF_SECONDS = 0
        lean_tools.DEFAULT_CONTEXT_TOKENS = None
        retry_response = lean_tools.chat_completion(
            [{"role": "user", "content": "hello"}],
            base_url="http://example.invalid/v1",
            request_log_path=request_log,
            request_index=7,
        )
        if retry_response.get("choices") is None or len(urlopen_calls) != 2:
            errors.append("chat_completion should retry a transient timeout and return the later response")
        request_payload = json.loads(urlopen_calls[0].decode("utf-8"))
        if "n_ctx" in request_payload:
            errors.append("chat_completion should not send provider-specific n_ctx unless configured")
        request_events = [json.loads(line) for line in request_log.read_text(encoding="utf-8").splitlines()]
        if [event.get("status") for event in request_events] != ["request_retry", "request_retry_succeeded"]:
            errors.append("chat_completion retry log should record retry and success events")
        lean_tools.urllib.request.urlopen = original_urlopen
        lean_tools.DEFAULT_CONTEXT_TOKENS = original_context_tokens
        lean_tools.DEFAULT_NATIVE_TOOLS = True

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
        lean_tools.DEFAULT_NATIVE_TOOLS = True
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
        lean_tools.urllib.request.urlopen = original_urlopen
        lean_tools.REQUEST_RETRIES = original_request_retries
        lean_tools.REQUEST_RETRY_BACKOFF_SECONDS = original_request_backoff
        lean_tools.DEFAULT_CONTEXT_TOKENS = original_context_tokens
        lean_tools.DEFAULT_NATIVE_TOOLS = original_native_tools
        shutil.rmtree(temp_workspace, ignore_errors=True)

    if errors:
        print("\n".join(errors))
        return 1
    print("fair harness policy checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

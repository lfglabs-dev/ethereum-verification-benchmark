from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path
from unittest import mock

import harness.lean_lsp_mcp_client as lean_lsp_mcp_client
from harness.lean_lsp_mcp_client import (
    ALLOWED_TOOLS,
    LeanLspMcpCompatibilityError,
    LeanLspMcpError,
    LeanLspMcpSession,
    LeanLspMcpTransportError,
    _openai_tool,
    assert_compatible_lean_toolchain,
    lean_toolchain_version,
    normalize_call_result,
    normalize_tool_arguments,
)
from harness.classification import classify_target
from harness.runners import lean_tools
from scripts import aggregate_runs
from scripts.check_run_artifacts import check_run


class _FakeMcpSession:
    def __init__(self) -> None:
        self.tools = [
            {
                "type": "function",
                "function": {
                    "name": "lean_goal",
                    "description": "Get proof goals",
                    "parameters": {
                        "type": "object",
                        "properties": {
                            "file_path": {"type": "string"},
                            "line": {"type": "integer"},
                        },
                        "required": ["file_path", "line"],
                    },
                },
            }
        ]
        self.calls: list[tuple[str, dict[str, object]]] = []
        self.files_changed = False

    def call_tool(self, name: str, arguments: dict[str, object]) -> dict[str, object]:
        self.calls.append((name, arguments))
        return {"ok": True, "mcp_tool": name, "content": "⊢ True"}

    def mark_workspace_files_changed(self) -> None:
        self.files_changed = True


class _SemanticFakeMcpSession(_FakeMcpSession):
    """Local MCP fixture: no model/provider transport is ever opened."""

    def __init__(self) -> None:
        super().__init__()
        self.tools = [
            {"type": "function", "function": {"name": name, "parameters": {"type": "object"}}}
            for name in ("lean_declaration_file", "lean_diagnostic_messages", "lean_goal")
        ]

    def call_tool(self, name: str, arguments: dict[str, object]) -> dict[str, object]:
        self.calls.append((name, arguments))
        contents = {
            "lean_declaration_file": "Benchmark/Generated/Sample.lean:1",
            "lean_diagnostic_messages": "no diagnostics",
            "lean_goal": "⊢ True",
        }
        return {"ok": True, "mcp_tool": name, "content": contents[name]}


class BuiltinLeanLspMcpTests(unittest.TestCase):
    def test_mcp_028_requires_lean_424(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            workspace = Path(tmp)
            toolchain = workspace / "lean-toolchain"
            toolchain.write_text("leanprover/lean4:v4.22.0\n", encoding="utf-8")
            self.assertEqual(lean_toolchain_version(workspace), (4, 22, 0))
            with self.assertRaisesRegex(
                LeanLspMcpCompatibilityError,
                r"lean-lsp-mcp==0\.28\.0 requires Lean >= 4\.24\.0",
            ):
                assert_compatible_lean_toolchain(workspace)

            toolchain.write_text("leanprover/lean4:v4.24.0\n", encoding="utf-8")
            self.assertEqual(
                assert_compatible_lean_toolchain(workspace), (4, 24, 0)
            )

            toolchain.unlink()
            self.assertIsNone(
                LeanLspMcpSession(workspace).metadata()["workspace_lean_version"]
            )

    def test_mcp_descriptor_is_forwarded_without_schema_rewriting(self) -> None:
        schema = {
            "type": "object",
            "properties": {"file_path": {"type": "string"}},
            "required": ["file_path"],
        }
        converted = _openai_tool(
            {"name": "lean_goal", "description": "goal", "inputSchema": schema}
        )
        self.assertEqual(converted["function"]["name"], "lean_goal")
        self.assertIs(converted["function"]["parameters"], schema)

    def test_argument_policy_blocks_hidden_and_escaping_files(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            workspace = Path(tmp)
            public = workspace / "Public.lean"
            hidden = workspace / "Proofs.lean"
            public.write_text("theorem ok : True := by trivial\n", encoding="utf-8")
            hidden.write_text("theorem secret : True := by trivial\n", encoding="utf-8")
            normalized = normalize_tool_arguments(
                "lean_goal",
                {"file_path": "Public.lean", "line": 1},
                workspace=workspace,
            )
            self.assertEqual(normalized["file_path"], str(public.resolve()))
            with self.assertRaisesRegex(LeanLspMcpError, "does not expose"):
                normalize_tool_arguments(
                    "lean_goal",
                    {"file_path": "Proofs.lean", "line": 1},
                    workspace=workspace,
                )
            with self.assertRaisesRegex(LeanLspMcpError, "not found|escapes"):
                normalize_tool_arguments(
                    "lean_goal",
                    {"file_path": "../outside.lean", "line": 1},
                    workspace=workspace,
                )

    def test_argument_policy_allows_resolved_public_package_files(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            workspace = Path(tmp) / "workspace"
            workspace.mkdir()
            root = Path(tmp) / "root"
            dependency = root / ".lake" / "packages" / "mathlib" / "Public.lean"
            dependency.parent.mkdir(parents=True)
            dependency.write_text("theorem public_ok : True := by trivial\n", encoding="utf-8")
            lake = workspace / ".lake"
            lake.mkdir()
            (lake / "packages").symlink_to(dependency.parent.parent)

            with mock.patch.object(lean_lsp_mcp_client, "ROOT", root):
                normalized = normalize_tool_arguments(
                    "lean_goal",
                    {"file_path": ".lake/packages/mathlib/Public.lean", "line": 1},
                    workspace=workspace,
                )

        self.assertEqual(normalized["file_path"], str(dependency.resolve()))

    def test_local_search_root_and_multi_attempt_are_bounded(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            workspace = Path(tmp)
            search = normalize_tool_arguments(
                "lean_local_search",
                {"query": "Nat.add", "project_root": "/"},
                workspace=workspace,
            )
            self.assertEqual(search["project_root"], str(workspace.resolve()))
            lean_file = workspace / "Main.lean"
            lean_file.write_text("example : True := by trivial\n", encoding="utf-8")
            attempts = normalize_tool_arguments(
                "lean_multi_attempt",
                {
                    "file_path": "Main.lean",
                    "line": 1,
                    "snippets": [f"tactic_{index}" for index in range(8)],
                },
                workspace=workspace,
            )
            self.assertEqual(len(attempts["snippets"]), 5)

    def test_error_result_remains_structured_for_model_feedback(self) -> None:
        result = normalize_call_result(
            "lean_goal",
            {
                "isError": True,
                "content": [{"type": "text", "text": "LSP timeout"}],
            },
        )
        self.assertFalse(result["ok"])
        self.assertEqual(result["error"], "LSP timeout")

    def test_builtin_loop_routes_mcp_tool_and_keeps_attempt_metering(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            workspace = Path(tmp)
            editable = "Benchmark/Generated/Sample.lean"
            proof_path = workspace / editable
            proof_path.parent.mkdir(parents=True)
            proof_path.write_text(
                "theorem sample : True := by\n  exact ?_\n", encoding="utf-8"
            )
            session = _FakeMcpSession()
            responses = [
                {
                    "choices": [
                        {
                            "message": {
                                "role": "assistant",
                                "content": None,
                                "tool_calls": [
                                    {
                                        "id": "goal-1",
                                        "type": "function",
                                        "function": {
                                            "name": "lean_goal",
                                            "arguments": '{"file_path":"Benchmark/Generated/Sample.lean","line":1}',
                                        },
                                    }
                                ],
                            }
                        }
                    ],
                    "usage": {"prompt_tokens": 10, "completion_tokens": 2, "total_tokens": 12},
                },
                {
                    "choices": [
                        {
                            "message": {
                                "role": "assistant",
                                "content": None,
                                "tool_calls": [
                                    {
                                        "id": "proof-1",
                                        "type": "function",
                                        "function": {
                                            "name": "check_proof",
                                            "arguments": '{"proof":"trivial"}',
                                        },
                                    }
                                ],
                            }
                        }
                    ],
                    "usage": {"prompt_tokens": 15, "completion_tokens": 3, "total_tokens": 18},
                },
            ]
            advertised: list[list[dict[str, object]]] = []

            def fake_chat(*_args: object, **kwargs: object) -> dict[str, object]:
                advertised.append(kwargs["tools"])
                return responses.pop(0)

            task = {
                "task_ref": "sample/group/task",
                "task_id": "task",
                "editable_files": [editable],
                "target_module": "Benchmark.Generated.Sample",
                "theorem_name": "sample",
            }
            with mock.patch.object(lean_tools, "chat_completion", fake_chat), mock.patch.object(
                lean_tools, "_run_lean_module", return_value=(0, "")
            ):
                result = lean_tools._attempt_task_fair(
                    task,
                    workspace,
                    base_url="http://localhost:8000/v1",
                    max_attempts=1,
                    max_tool_calls=4,
                    attempts_dir=workspace / "attempts",
                    tool_log_path=workspace / "tools.jsonl",
                    conversation_log_path=workspace / "conversation.jsonl",
                    native_tools=True,
                    mcp_session=session,
                )

        self.assertEqual(result["status"], "lean_passed")
        self.assertEqual(result["tool_calls_executed"], 2)
        self.assertEqual(result["usage"]["requests"], 2)
        self.assertEqual(session.calls[0][0], "lean_goal")
        advertised_names = {
            tool["function"]["name"] for tool in advertised[0]
        }
        self.assertIn("lean_goal", advertised_names)
        self.assertIn("check_proof", advertised_names)
        self.assertNotIn("show_goal", advertised_names)
        self.assertTrue(session.files_changed)

    def test_semantic_mcp_smoke_resumes_after_declaration_diagnostics_and_goal_results(self) -> None:
        """A local fake transport proves structured MCP result resumption without providers."""
        with tempfile.TemporaryDirectory() as tmp:
            workspace = Path(tmp)
            editable = "Benchmark/Generated/Sample.lean"
            proof_path = workspace / editable
            proof_path.parent.mkdir(parents=True)
            proof_path.write_text("theorem sample : True := by\n  exact ?_\n", encoding="utf-8")
            session = _SemanticFakeMcpSession()
            responses = []
            for call_id, name, arguments in (
                ("decl-1", "lean_declaration_file", '{"declaration":"sample"}'),
                ("diag-1", "lean_diagnostic_messages", '{"file_path":"Benchmark/Generated/Sample.lean"}'),
                ("goal-1", "lean_goal", '{"file_path":"Benchmark/Generated/Sample.lean","line":1}'),
                ("proof-1", "check_proof", '{"proof":"trivial"}'),
            ):
                responses.append({"choices": [{"message": {"role": "assistant", "content": None, "tool_calls": [{"id": call_id, "type": "function", "function": {"name": name, "arguments": arguments}}]}}], "usage": {"prompt_tokens": 1, "completion_tokens": 1, "total_tokens": 2}})
            observed_messages: list[list[dict[str, object]]] = []

            def fake_chat(messages: list[dict[str, object]], **_kwargs: object) -> dict[str, object]:
                observed_messages.append(list(messages))
                return responses.pop(0)

            with mock.patch.object(lean_tools, "chat_completion", fake_chat), mock.patch.object(
                lean_tools, "_run_lean_module", return_value=(0, "")
            ):
                result = lean_tools._attempt_task_fair(
                    {"task_ref": "sample/group/task", "task_id": "task", "editable_files": [editable], "target_module": "Benchmark.Generated.Sample", "theorem_name": "sample"},
                    workspace, base_url="http://127.0.0.1:9/v1", max_attempts=1,
                    max_tool_calls=8, attempts_dir=workspace / "attempts",
                    tool_log_path=workspace / "tools.jsonl", conversation_log_path=workspace / "conversation.jsonl",
                    native_tools=True, mcp_session=session,
                )

        self.assertEqual(result["status"], "lean_passed")
        self.assertEqual([name for name, _ in session.calls], ["lean_declaration_file", "lean_diagnostic_messages", "lean_goal"])
        self.assertEqual(result["tool_calls_executed"], 4)
        self.assertTrue(all(any(message.get("role") == "tool" for message in messages) for messages in observed_messages[1:]))

    def test_json_fallback_prompt_contains_mcp_schemas_and_default_briefing(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            workspace = Path(tmp)
            editable = "Benchmark/Generated/Sample.lean"
            proof_path = workspace / editable
            proof_path.parent.mkdir(parents=True)
            proof_path.write_text(
                "theorem sample : True := by\n  exact ?_\n", encoding="utf-8"
            )
            session = _FakeMcpSession()
            captured_messages: list[dict[str, object]] = []

            def fake_chat(messages: list[dict[str, object]], **_kwargs: object) -> dict[str, object]:
                captured_messages.extend(messages)
                return {
                    "choices": [
                        {
                            "message": {
                                "role": "assistant",
                                "content": '{"tool":"check_proof","arguments":{"proof":"trivial"}}',
                            }
                        }
                    ],
                    "usage": {"prompt_tokens": 10, "completion_tokens": 2, "total_tokens": 12},
                }

            with mock.patch.object(lean_tools, "chat_completion", fake_chat), mock.patch.object(
                lean_tools, "_run_lean_module", return_value=(0, "")
            ):
                result = lean_tools._attempt_task_fair(
                    {
                        "task_ref": "sample/group/task",
                        "task_id": "task",
                        "editable_files": [editable],
                        "target_module": "Benchmark.Generated.Sample",
                        "theorem_name": "sample",
                    },
                    workspace,
                    base_url="http://localhost:8000/v1",
                    max_attempts=1,
                    max_tool_calls=4,
                    attempts_dir=workspace / "attempts",
                    tool_log_path=workspace / "tools.jsonl",
                    conversation_log_path=workspace / "conversation.jsonl",
                    native_tools=False,
                    mcp_session=session,
                )

        self.assertEqual(result["status"], "lean_passed")
        system = str(captured_messages[0]["content"])
        self.assertIn('"name":"lean_goal"', system)
        self.assertIn('"file_path"', system)
        self.assertIn("proof_patterns guide", system)
        self.assertIn("the theorem statement must stay byte-identical", system)

    def test_mcp_setup_precedes_and_short_circuits_provider_preflight(self) -> None:
        with tempfile.TemporaryDirectory() as tmp, mock.patch.object(
            lean_tools, "RESULTS_DIR", Path(tmp) / "results"
        ), mock.patch.object(lean_tools, "_api_key", return_value="test-key"), mock.patch.object(
            lean_tools, "warm_public_dependencies", return_value=[]
        ), mock.patch.object(lean_tools, "_warm_target_modules", return_value=[]), mock.patch.object(
            LeanLspMcpSession,
            "start",
            side_effect=LeanLspMcpCompatibilityError("incompatible test toolchain"),
        ), mock.patch.object(
            lean_tools, "_role_provider_preflight"
        ) as provider_preflight:
            code, run_dir = lean_tools.run_group(
                "ethereum/deposit_contract_minimal",
                task_ref="ethereum/deposit_contract_minimal/deposit_count",
                max_attempts=1,
                max_tool_calls=4,
                harness_id="builtin-lean-lsp",
                run_slug="builtin-lean-lsp-test",
                track="group/lean_tools_mcp",
                tool_backend="lean-lsp-mcp",
            )
            response = json.loads(
                (run_dir / "harness-response.json").read_text(encoding="utf-8")
            )
            run = json.loads(
                (run_dir / "run.json").read_text(encoding="utf-8")
            )
            artifact_errors = check_run(run_dir)
            aggregate_rows = aggregate_runs.collect_runs(Path(tmp))

        self.assertEqual(code, 1)
        provider_preflight.assert_not_called()
        self.assertEqual(response["status"], "completed_with_failures")
        self.assertTrue(response["mcp_setup_error"])
        self.assertFalse(response["provider_setup_error"])
        self.assertEqual(response["failure_class"], "mcp_setup_error")
        self.assertEqual(run["classification"]["run_class"], "INFRA_INVALID")
        self.assertFalse(run["classification"]["reusable"])
        self.assertEqual(artifact_errors, [])
        self.assertEqual(len(aggregate_rows), 1)
        self.assertTrue(aggregate_rows[0]["valid"])
        self.assertEqual(aggregate_rows[0]["final_class"], "INFRA_INVALID")
        self.assertFalse(aggregate_rows[0]["reusable"])

    def test_pre_mcp_warm_failure_does_not_require_mcp_artifacts(self) -> None:
        with tempfile.TemporaryDirectory() as tmp, mock.patch.object(
            lean_tools, "RESULTS_DIR", Path(tmp) / "results"
        ), mock.patch.object(lean_tools, "_api_key", return_value="test-key"), mock.patch.object(
            lean_tools,
            "warm_public_dependencies",
            return_value=[{"exit_code": 1, "module": "Mathlib"}],
        ), mock.patch.object(lean_tools, "LeanLspMcpSession") as mcp_session:
            code, run_dir = lean_tools.run_group(
                "ethereum/deposit_contract_minimal",
                task_ref="ethereum/deposit_contract_minimal/deposit_count",
                max_attempts=1,
                max_tool_calls=4,
                harness_id="builtin-lean-lsp",
                run_slug="builtin-lean-lsp-test",
                track="group/lean_tools_mcp",
                tool_backend="lean-lsp-mcp",
            )
            run = json.loads((run_dir / "run.json").read_text(encoding="utf-8"))
            artifact_errors = check_run(run_dir)

        self.assertEqual(code, 1)
        mcp_session.assert_not_called()
        self.assertEqual(run["harness_status"], "completed_with_failures")
        self.assertIsNone(run["mcp_preflight"])
        self.assertIn("MCP-backed fair run missing MCP lifecycle metadata", "\n".join(artifact_errors))
        self.assertIn("MCP-backed fair run missing MCP preflight result", "\n".join(artifact_errors))

    def test_missing_credentials_artifact_does_not_require_unstarted_mcp_metadata(self) -> None:
        with tempfile.TemporaryDirectory() as tmp, mock.patch.object(
            lean_tools, "RESULTS_DIR", Path(tmp) / "results"
        ), mock.patch.object(lean_tools, "_api_key", return_value=None), mock.patch.object(
            lean_tools, "_local_no_auth_endpoint", return_value=False
        ), mock.patch.object(lean_tools, "LeanLspMcpSession") as mcp_session:
            code, run_dir = lean_tools.run_group(
                "ethereum/deposit_contract_minimal",
                task_ref="ethereum/deposit_contract_minimal/deposit_count",
                max_attempts=1,
                max_tool_calls=4,
                harness_id="builtin-lean-lsp",
                run_slug="builtin-lean-lsp-test",
                track="group/lean_tools_mcp",
                tool_backend="lean-lsp-mcp",
            )
            run = json.loads((run_dir / "run.json").read_text(encoding="utf-8"))
            artifact_errors = check_run(run_dir)

        self.assertEqual(code, 1)
        mcp_session.assert_not_called()
        self.assertEqual(run["harness_status"], "missing_credentials")
        self.assertEqual(run["tool_backend"], "lean-lsp-mcp")
        self.assertEqual(run["failure_class"], "provider_setup_error")
        self.assertIsNone(run["lean_lsp_mcp"])
        self.assertIsNone(run["mcp_preflight"])
        self.assertEqual(artifact_errors, [])

    def test_aggregate_accepts_multi_task_mcp_preflight_failure(self) -> None:
        budget = {
            "max_attempts": 1,
            "max_tool_calls": 4,
            "max_turns": None,
            "completion_token_budget": 32768,
        }
        with tempfile.TemporaryDirectory() as tmp:
            run_dir = Path(tmp) / "run"
            run_dir.mkdir()
            (run_dir / "run.json").write_text(
                json.dumps(
                    {
                        "run_id": "mcp-group-preflight-failure",
                        "harness_id": "builtin-lean-lsp",
                        "model": "local",
                        "group_id": "case/group",
                        "harness_status": "completed_with_failures",
                        "benchmark_budget": budget,
                        "failure_counts": {"mcp_setup_error": 2},
                        "classification": {
                            "run_class": "INFRA_INVALID",
                            "reusable": False,
                        },
                        "verifier": {
                            "score": {"passed_targets": 0, "total_targets": 2}
                        },
                    }
                ),
                encoding="utf-8",
            )
            (run_dir / "harness-response.json").write_text(
                json.dumps(
                    {
                        "mcp_preflight": {"status": "failed"},
                        "tasks": [
                            {
                                "task_ref": "case/group/one",
                                "status": "request_failed",
                                "failure_class": "mcp_setup_error",
                                "attempts": [],
                                "usage": {"requests": 0, "total_tokens": 0},
                                "benchmark_budget": budget,
                            },
                            {
                                "task_ref": "case/group/two",
                                "status": "request_failed",
                                "failure_class": "mcp_setup_error",
                                "attempts": [],
                                "usage": {"requests": 0, "total_tokens": 0},
                                "benchmark_budget": budget,
                            },
                        ],
                    }
                ),
                encoding="utf-8",
            )
            rows = aggregate_runs.collect_runs(Path(tmp))

        self.assertEqual(len(rows), 1)
        self.assertTrue(rows[0]["valid"])
        self.assertFalse(rows[0]["passed"])
        self.assertEqual(rows[0]["final_class"], "INFRA_INVALID")
        self.assertFalse(rows[0]["reusable"])
        self.assertNotIn("terminal status", " ".join(rows[0]["validity_errors"]))

    def test_session_metadata_records_effective_calls_and_shutdown(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            workspace = Path(tmp)
            (workspace / "lean-toolchain").write_text(
                "leanprover/lean4:v4.24.0\n", encoding="utf-8"
            )
            session = LeanLspMcpSession(workspace)
            listed_tools = [
                {
                    "name": name,
                    "description": name,
                    "inputSchema": {"type": "object", "properties": {}},
                }
                for name in sorted(ALLOWED_TOOLS)
            ]
            with mock.patch.object(
                session,
                "_request",
                side_effect=[
                    {
                        "serverInfo": {"name": "Lean LSP", "version": "test"},
                        "instructions": "test",
                    },
                    {"tools": listed_tools},
                ],
            ), mock.patch.object(session, "_notify"):
                session._initialize()
            with mock.patch.object(
                session,
                "_request",
                return_value={
                    "isError": False,
                    "content": [{"type": "text", "text": '{"items":[]}'}],
                },
            ):
                result = session.call_tool("lean_local_search", {"query": "Nat.add"})

            class _StoppedProcess:
                pid = 987654
                stdin = None

                @staticmethod
                def poll() -> None:
                    return None

                @staticmethod
                def wait(timeout: int) -> int:
                    return 0

            session.process = _StoppedProcess()  # type: ignore[assignment]
            session.close()
            metadata = session.metadata()

        self.assertTrue(result["ok"])
        self.assertEqual(metadata["initialization_count"], 1)
        self.assertEqual(metadata["tool_call_count"], 1)
        self.assertEqual(metadata["tool_call_counts"], {"lean_local_search": 1})
        self.assertGreaterEqual(metadata["tool_call_duration_seconds"], 0)
        self.assertTrue(metadata["clean_shutdown"])
        self.assertEqual(metadata["shutdown_signal"], "stdin_eof")

    def test_mcp_transport_failure_is_non_reusable_without_submission(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            workspace = Path(tmp)
            editable = "Benchmark/Generated/Sample.lean"
            proof_path = workspace / editable
            proof_path.parent.mkdir(parents=True)
            proof_path.write_text(
                "theorem sample : True := by\n  exact ?_\n", encoding="utf-8"
            )
            session = _FakeMcpSession()

            def fail_tool(_name: str, _arguments: dict[str, object]) -> dict[str, object]:
                raise LeanLspMcpTransportError("MCP process exited")

            session.call_tool = fail_tool  # type: ignore[method-assign]
            response = {
                "choices": [
                    {
                        "message": {
                            "role": "assistant",
                            "content": None,
                            "tool_calls": [
                                {
                                    "id": "goal-1",
                                    "type": "function",
                                    "function": {
                                        "name": "lean_goal",
                                        "arguments": '{"file_path":"Benchmark/Generated/Sample.lean","line":1}',
                                    },
                                }
                            ],
                        }
                    }
                ],
                "usage": {"prompt_tokens": 10, "completion_tokens": 2, "total_tokens": 12},
            }
            with mock.patch.object(lean_tools, "chat_completion", return_value=response):
                result = lean_tools._attempt_task_fair(
                    {
                        "task_ref": "sample/group/task",
                        "task_id": "task",
                        "editable_files": [editable],
                        "target_module": "Benchmark.Generated.Sample",
                        "theorem_name": "sample",
                    },
                    workspace,
                    base_url="http://localhost:8000/v1",
                    max_attempts=1,
                    max_tool_calls=4,
                    attempts_dir=workspace / "attempts",
                    tool_log_path=workspace / "tools.jsonl",
                    conversation_log_path=workspace / "conversation.jsonl",
                    native_tools=True,
                    mcp_session=session,
                )

        self.assertEqual(result["status"], "request_failed")
        self.assertEqual(result["failure_class"], "transport_error")
        classification = classify_target(
            {"task_ref": "sample/group/task", "status": "lean_check_failed"},
            result,
        )
        self.assertEqual(classification["final_class"], "INFRA_INVALID")
        self.assertFalse(classification["reusable"])


if __name__ == "__main__":
    unittest.main()

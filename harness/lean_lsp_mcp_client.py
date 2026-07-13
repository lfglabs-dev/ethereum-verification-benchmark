from __future__ import annotations

import json
import os
import select
import signal
import subprocess
import threading
import time
from collections import deque
from pathlib import Path


# 0.28.0's leanclient requires Lean >= 4.24.  The benchmark intentionally pins
# Lean 4.22, while 0.27.0 exposes the same selected tool schemas and supports
# this project toolchain.
LEAN_LSP_MCP_VERSION = "0.27.0"
PROTOCOL_VERSION = "2025-06-18"

# Keep the same local, non-networked Lean surface as the Vibe profile.  The
# benchmark runner owns file mutation and final verification, so code execution,
# builds, remote search, widgets, profiling, and verifier-like tools stay out of
# the model-visible MCP surface.
DISABLED_TOOLS = {
    "lean_build",
    "lean_get_widget_source",
    "lean_get_widgets",
    "lean_hammer_premise",
    "lean_leanfinder",
    "lean_leansearch",
    "lean_loogle",
    "lean_minimal_hypotheses",
    "lean_profile_proof",
    "lean_run_code",
    "lean_state_search",
    "lean_verify",
}

ALLOWED_TOOLS = {
    "lean_code_actions",
    "lean_completions",
    "lean_declaration_file",
    "lean_diagnostic_messages",
    "lean_file_outline",
    "lean_goal",
    "lean_hover_info",
    "lean_local_search",
    "lean_multi_attempt",
    "lean_references",
    "lean_term_goal",
}


class LeanLspMcpError(RuntimeError):
    pass


class LeanLspMcpTransportError(LeanLspMcpError):
    """MCP process/protocol failure, as opposed to rejected model arguments."""

    pass


def _openai_tool(tool: dict[str, object]) -> dict[str, object]:
    """Convert one MCP tool descriptor to the chat-completions tool shape."""
    name = tool.get("name")
    schema = tool.get("inputSchema")
    if not isinstance(name, str) or not isinstance(schema, dict):
        raise LeanLspMcpError("invalid tools/list entry from lean-lsp-mcp")
    return {
        "type": "function",
        "function": {
            "name": name,
            "description": str(tool.get("description") or ""),
            "parameters": schema,
        },
    }


def _public_path(workspace: Path, raw_path: str) -> str:
    if not raw_path.strip():
        raise LeanLspMcpError("file_path must not be empty")
    supplied = Path(raw_path)
    candidate = supplied if supplied.is_absolute() else workspace / supplied
    try:
        resolved = candidate.resolve(strict=True)
    except OSError as exc:
        raise LeanLspMcpError(f"Lean file not found: {raw_path}") from exc

    roots: list[Path] = [workspace.resolve()]
    lake = workspace / ".lake"
    try:
        if lake.exists():
            roots.append(lake.resolve())
    except OSError:
        pass
    if not any(resolved == root or root in resolved.parents for root in roots):
        raise LeanLspMcpError("file_path escapes the isolated benchmark workspace")

    normalized = resolved.as_posix()
    blocked_parts = {".env", "GeneratedPreview", "Proofs"}
    if any(part in blocked_parts for part in resolved.parts) or resolved.name == "Proofs.lean":
        raise LeanLspMcpError(
            "fair mode does not expose hidden proof, GeneratedPreview, or .env files"
        )
    if resolved.suffix != ".lean":
        raise LeanLspMcpError("lean-lsp-mcp tools may only inspect .lean files")
    return normalized


def normalize_tool_arguments(
    name: str,
    arguments: dict[str, object],
    *,
    workspace: Path,
) -> dict[str, object]:
    """Apply the benchmark's public-file policy before forwarding to MCP."""
    if name not in ALLOWED_TOOLS:
        raise LeanLspMcpError(f"lean-lsp-mcp tool is not allowed: {name}")
    normalized = dict(arguments)
    file_path = normalized.get("file_path")
    if file_path is not None:
        if not isinstance(file_path, str):
            raise LeanLspMcpError("file_path must be a string")
        normalized["file_path"] = _public_path(workspace, file_path)
    if name == "lean_local_search":
        # Never let a model redirect the search index to another checkout.
        normalized["project_root"] = str(workspace.resolve())
    if name == "lean_multi_attempt":
        snippets = normalized.get("snippets")
        if isinstance(snippets, list):
            normalized["snippets"] = snippets[:5]
    return normalized


def normalize_call_result(name: str, result: dict[str, object]) -> dict[str, object]:
    content = result.get("content")
    structured = result.get("structuredContent")
    payload: dict[str, object] = {
        "ok": not bool(result.get("isError")),
        "mcp_tool": name,
    }
    if structured is not None:
        payload["structured_content"] = structured
    if isinstance(content, list):
        text_items = [
            str(item.get("text"))
            for item in content
            if isinstance(item, dict) and item.get("type") == "text" and item.get("text") is not None
        ]
        if text_items:
            payload["content"] = "\n".join(text_items)
        non_text = [item for item in content if not (isinstance(item, dict) and item.get("type") == "text")]
        if non_text:
            payload["other_content"] = non_text
    if result.get("isError"):
        payload["error"] = payload.get("content") or structured or "lean-lsp-mcp tool failed"
    return payload


class LeanLspMcpSession:
    """Small synchronous MCP stdio client for one isolated Lean workspace."""

    def __init__(
        self,
        workspace: Path,
        *,
        startup_timeout_seconds: float | None = None,
        tool_timeout_seconds: float | None = None,
    ) -> None:
        self.workspace = workspace.resolve()
        self.startup_timeout_seconds = startup_timeout_seconds or float(
            os.environ.get("DEFAULT_HARNESS_LEAN_MCP_STARTUP_TIMEOUT_SECONDS", "180")
        )
        self.tool_timeout_seconds = tool_timeout_seconds or float(
            os.environ.get("DEFAULT_HARNESS_LEAN_MCP_TOOL_TIMEOUT_SECONDS", "600")
        )
        self.process: subprocess.Popen[str] | None = None
        self._request_id = 0
        self._stderr_tail: deque[str] = deque(maxlen=40)
        self.server_info: dict[str, object] = {}
        self.instructions = ""
        self.tools: list[dict[str, object]] = []
        self._workspace_files_changed = False

    @property
    def command(self) -> list[str]:
        return [
            "uvx",
            "--from",
            f"lean-lsp-mcp=={LEAN_LSP_MCP_VERSION}",
            "lean-lsp-mcp",
            "--transport",
            "stdio",
            "--lean-project-path",
            str(self.workspace),
            "--disable-tools",
            ",".join(sorted(DISABLED_TOOLS)),
        ]

    def __enter__(self) -> LeanLspMcpSession:
        self.start()
        return self

    def __exit__(self, _exc_type: object, _exc: object, _tb: object) -> None:
        self.close()

    def _drain_stderr(self) -> None:
        process = self.process
        if process is None or process.stderr is None:
            return
        for line in process.stderr:
            self._stderr_tail.append(line.rstrip())

    def start(self) -> None:
        if self.process is not None:
            return
        env = {
            **os.environ,
            "LEAN_PROJECT_PATH": str(self.workspace),
            "LEAN_LOG_LEVEL": "NONE",
            "LEAN_BUILD_CONCURRENCY": "share",
        }
        try:
            self.process = subprocess.Popen(
                self.command,
                cwd=self.workspace,
                env=env,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                bufsize=1,
                start_new_session=True,
            )
        except OSError as exc:
            raise LeanLspMcpTransportError(f"failed to start lean-lsp-mcp: {exc}") from exc
        threading.Thread(target=self._drain_stderr, daemon=True).start()
        try:
            self._initialize()
        except Exception:
            self.close()
            raise

    def _initialize(self) -> None:
        initialized = self._request(
            "initialize",
            {
                "protocolVersion": PROTOCOL_VERSION,
                "capabilities": {},
                "clientInfo": {
                    "name": "ethereum-verification-benchmark",
                    "version": "1",
                },
            },
            timeout_seconds=self.startup_timeout_seconds,
        )
        self.server_info = (
            dict(initialized.get("serverInfo", {}))
            if isinstance(initialized.get("serverInfo"), dict)
            else {}
        )
        self.instructions = str(initialized.get("instructions") or "")
        self._notify("notifications/initialized", {})
        listed = self._request("tools/list", {}, timeout_seconds=self.startup_timeout_seconds)
        raw_tools = listed.get("tools")
        if not isinstance(raw_tools, list):
            raise LeanLspMcpError("lean-lsp-mcp tools/list returned no tools")
        by_name = {
            str(tool.get("name")): tool
            for tool in raw_tools
            if isinstance(tool, dict) and tool.get("name") in ALLOWED_TOOLS
        }
        missing = sorted(ALLOWED_TOOLS - set(by_name))
        if missing:
            raise LeanLspMcpError(
                "lean-lsp-mcp is missing required tools: " + ", ".join(missing)
            )
        self.tools = [_openai_tool(by_name[name]) for name in sorted(by_name)]
        self._workspace_files_changed = False

    def mark_workspace_files_changed(self) -> None:
        """Ensure the next IDE call observes a proof written outside the LSP."""
        self._workspace_files_changed = True

    def restart(self) -> None:
        self.close()
        self.start()

    def metadata(self) -> dict[str, object]:
        return {
            "package": "lean-lsp-mcp",
            "package_version": LEAN_LSP_MCP_VERSION,
            "protocol_version": PROTOCOL_VERSION,
            "server_info": self.server_info,
            "tools": [
                str(tool.get("function", {}).get("name"))
                for tool in self.tools
                if isinstance(tool.get("function"), dict)
            ],
        }

    def call_tool(self, name: str, arguments: dict[str, object]) -> dict[str, object]:
        if self._workspace_files_changed:
            # leanclient keeps opened document contents in memory. check_proof
            # writes directly to disk, so a fresh server is the reliable way to
            # keep later goals/diagnostics synchronized with the submitted file.
            self.restart()
        normalized = normalize_tool_arguments(name, arguments, workspace=self.workspace)
        result = self._request(
            "tools/call",
            {"name": name, "arguments": normalized},
            timeout_seconds=self.tool_timeout_seconds,
        )
        return normalize_call_result(name, result)

    def _send(self, payload: dict[str, object]) -> None:
        process = self.process
        if process is None or process.stdin is None:
            raise LeanLspMcpError("lean-lsp-mcp is not running")
        try:
            process.stdin.write(json.dumps(payload, separators=(",", ":")) + "\n")
            process.stdin.flush()
        except (BrokenPipeError, OSError) as exc:
            raise LeanLspMcpTransportError(
                self._process_error("lean-lsp-mcp pipe closed")
            ) from exc

    def _notify(self, method: str, params: dict[str, object]) -> None:
        self._send({"jsonrpc": "2.0", "method": method, "params": params})

    def _request(
        self,
        method: str,
        params: dict[str, object],
        *,
        timeout_seconds: float,
    ) -> dict[str, object]:
        self._request_id += 1
        request_id = self._request_id
        self._send(
            {
                "jsonrpc": "2.0",
                "id": request_id,
                "method": method,
                "params": params,
            }
        )
        process = self.process
        if process is None or process.stdout is None:
            raise LeanLspMcpError("lean-lsp-mcp is not running")
        deadline = time.monotonic() + timeout_seconds
        while True:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise LeanLspMcpTransportError(
                    f"lean-lsp-mcp {method} timed out after {timeout_seconds:g}s"
                )
            if process.poll() is not None:
                raise LeanLspMcpTransportError(self._process_error("lean-lsp-mcp exited"))
            readable, _, _ = select.select([process.stdout], [], [], min(remaining, 0.25))
            if not readable:
                continue
            line = process.stdout.readline()
            if not line:
                raise LeanLspMcpTransportError(
                    self._process_error("lean-lsp-mcp closed stdout")
                )
            try:
                message = json.loads(line)
            except json.JSONDecodeError:
                continue
            if not isinstance(message, dict):
                continue
            # The selected tools do not use client-side sampling or roots, but
            # fail unknown reverse requests promptly instead of deadlocking.
            if "method" in message and "id" in message:
                self._send(
                    {
                        "jsonrpc": "2.0",
                        "id": message["id"],
                        "error": {"code": -32601, "message": "client method not supported"},
                    }
                )
                continue
            if message.get("id") != request_id:
                continue
            error = message.get("error")
            if isinstance(error, dict):
                raise LeanLspMcpTransportError(
                    f"lean-lsp-mcp {method} failed: {error.get('message') or error}"
                )
            result = message.get("result")
            if not isinstance(result, dict):
                raise LeanLspMcpTransportError(
                    f"lean-lsp-mcp {method} returned an invalid result"
                )
            return result

    def _process_error(self, prefix: str) -> str:
        detail = "\n".join(self._stderr_tail).strip()
        return f"{prefix}: {detail}" if detail else prefix

    def close(self) -> None:
        process, self.process = self.process, None
        if process is None:
            return
        try:
            os.killpg(process.pid, signal.SIGTERM)
            process.wait(timeout=5)
        except (OSError, subprocess.TimeoutExpired):
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except OSError:
                pass
            try:
                process.wait(timeout=2)
            except subprocess.TimeoutExpired:
                pass

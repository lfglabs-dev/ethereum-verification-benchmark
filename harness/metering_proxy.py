"""Local OpenAI-compatible metering proxy for shell-agent harnesses.

Spawns an HTTP server on 127.0.0.1 that forwards /v1/* requests to an
upstream OpenAI-compatible endpoint, injecting the real API key. Every
response (JSON or SSE stream) is scanned for `usage` objects, which are
accumulated and written to a usage.json artifact. This gives all shell
harnesses (opencode, codex, ...) the same token accounting as the builtin
harness, measured at the API boundary rather than self-reported.

Optionally enforces a completion-token budget: once exceeded, further
chat requests get HTTP 429 so budgets mean the same thing across harnesses.
"""
from __future__ import annotations

import json
import re
import secrets
import threading
import time
import urllib.error
import urllib.request
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

from harness.identity import HARNESS_USER_AGENT


_TEXT_TOOL_ALIASES = {
    "read": ("read", "read_file"),
    "write": ("write", "write_file"),
    "search_replace": ("search_replace", "edit"),
}
_SAMPLING_FIELDS = ("temperature", "top_p", "reasoning_effort")


def omit_sampling_fields(request_data: bytes | None) -> bytes | None:
    """Drop sampling overrides at the API boundary while preserving the request."""
    if not request_data:
        return request_data
    try:
        payload = json.loads(request_data.decode("utf-8"))
    except (UnicodeDecodeError, ValueError):
        return request_data
    if not isinstance(payload, dict):
        return request_data
    for key in _SAMPLING_FIELDS:
        payload.pop(key, None)
    return json.dumps(payload, ensure_ascii=False).encode("utf-8")


def _available_tool_names(request_payload: dict[str, object]) -> set[str]:
    names: set[str] = set()
    tools = request_payload.get("tools")
    if not isinstance(tools, list):
        return names
    for tool in tools:
        function = tool.get("function") if isinstance(tool, dict) else None
        name = function.get("name") if isinstance(function, dict) else None
        if isinstance(name, str):
            names.add(name)
    return names


def _text_tool_calls(content: str, available_names: set[str]) -> tuple[list[dict[str, object]], int | None]:
    """Recover Vibe-style ``read{...}`` calls from a text-only model turn."""
    calls: list[dict[str, object]] = []
    first_start: int | None = None
    decoder = json.JSONDecoder()
    for match in re.finditer(r"(?<![\w-])([A-Za-z_][\w.-]*)\s*(?=\{)", content):
        emitted_name = match.group(1)
        emitted_candidates = (emitted_name, emitted_name.rsplit(".", 1)[-1])
        resolved = next(
            (
                (emitted, candidate)
                for emitted in emitted_candidates
                for candidate in _TEXT_TOOL_ALIASES.get(emitted, (emitted,))
                if candidate in available_names
            ),
            None,
        )
        if resolved is None:
            continue
        matched_emitted, name = resolved
        try:
            arguments, _ = decoder.raw_decode(content, match.end())
        except json.JSONDecodeError:
            continue
        if not isinstance(arguments, dict):
            continue
        if first_start is None:
            first_start = match.end(1) - len(matched_emitted)
        calls.append(
            {
                "id": f"text-fallback-{len(calls) + 1}",
                "type": "function",
                "function": {
                    "name": name,
                    "arguments": json.dumps(arguments, separators=(",", ":")),
                },
            }
        )
    return calls, first_start


def adapt_text_tool_response(response_data: bytes, request_data: bytes | None) -> bytes:
    """Translate text-only Vibe tool syntax into OpenAI ``tool_calls``."""
    if not request_data:
        return response_data
    try:
        request_payload = json.loads(request_data.decode("utf-8"))
        response_payload = json.loads(response_data.decode("utf-8"))
    except (UnicodeDecodeError, ValueError):
        return response_data
    if not isinstance(request_payload, dict) or not isinstance(response_payload, dict):
        return response_data
    available_names = _available_tool_names(request_payload)
    if not available_names:
        return response_data
    choices = response_payload.get("choices")
    if not isinstance(choices, list) or not choices or not isinstance(choices[0], dict):
        return response_data
    message = choices[0].get("message")
    if not isinstance(message, dict) or message.get("tool_calls"):
        return response_data
    content = message.get("content")
    if not isinstance(content, str):
        return response_data
    calls, first_start = _text_tool_calls(content, available_names)
    if not calls:
        return response_data
    prefix = content[:first_start].rstrip() if first_start is not None else ""
    message["content"] = prefix or None
    message["tool_calls"] = calls
    choices[0]["finish_reason"] = "tool_calls"
    return json.dumps(response_payload, ensure_ascii=False).encode("utf-8")


class MeteringProxy:
    def __init__(
        self,
        upstream_base_url: str,
        api_key: str | None,
        *,
        usage_path: Path | None = None,
        completion_token_budget: int = 0,
        user_agent: str = HARNESS_USER_AGENT,
        text_tool_fallback: bool = False,
        omit_sampling: bool = False,
    ) -> None:
        self.upstream = upstream_base_url.rstrip("/")
        self.api_key = api_key
        self.usage_path = usage_path
        self.completion_token_budget = completion_token_budget
        self.user_agent = user_agent
        self.text_tool_fallback = text_tool_fallback
        self.omit_sampling = omit_sampling
        self.local_key = "verity-proxy-" + secrets.token_hex(16)
        self.lock = threading.Lock()
        self.usage = {"prompt_tokens": 0, "completion_tokens": 0, "total_tokens": 0, "requests": 0}
        self.requests_log: list[dict[str, object]] = []
        self._server: ThreadingHTTPServer | None = None
        self._thread: threading.Thread | None = None

    @property
    def port(self) -> int:
        assert self._server is not None
        return self._server.server_address[1]

    @property
    def base_url(self) -> str:
        return f"http://127.0.0.1:{self.port}/v1"

    def record_usage(self, usage: dict[str, object]) -> None:
        with self.lock:
            self.usage["requests"] += 1
            for key in ("prompt_tokens", "completion_tokens", "total_tokens"):
                value = usage.get(key)
                if isinstance(value, (int, float)):
                    self.usage[key] += int(value)
            self._flush_locked()

    def budget_exhausted(self) -> bool:
        # Soft cap: checked between requests, so concurrent in-flight
        # completions can overshoot by at most one response each.
        if not self.completion_token_budget:
            return False
        with self.lock:
            return self.usage["completion_tokens"] >= self.completion_token_budget

    def _flush_locked(self) -> None:
        if self.usage_path is not None:
            payload = dict(self.usage)
            payload["completion_token_budget"] = self.completion_token_budget
            self.usage_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    def start(self) -> None:
        proxy = self

        class Handler(BaseHTTPRequestHandler):
            protocol_version = "HTTP/1.1"

            def log_message(self, fmt: str, *args: object) -> None:
                pass

            def _forward(self) -> None:
                started = time.time()
                length = int(self.headers.get("Content-Length") or 0)
                body = self.rfile.read(length) if length else None
                path = self.path
                if not path.startswith("/v1/"):
                    path = "/v1" + path if not path.startswith("/v1") else path
                upstream_url = proxy.upstream.removesuffix("/v1") + path
                if self.command == "POST" and "chat/completions" in path and proxy.budget_exhausted():
                    payload = json.dumps(
                        {"error": {"message": "ethereum verification benchmark completion-token budget exhausted", "type": "error", "code": "budget_exhausted"}}
                    ).encode("utf-8")
                    self.send_response(429)
                    self.send_header("Content-Type", "application/json")
                    self.send_header("Content-Length", str(len(payload)))
                    self.end_headers()
                    self.wfile.write(payload)
                    return
                if self.command == "POST" and "chat/completions" in path and proxy.omit_sampling:
                    body = omit_sampling_fields(body)
                request = urllib.request.Request(upstream_url, data=body, method=self.command)
                request.add_header("Content-Type", self.headers.get("Content-Type") or "application/json")
                request.add_header("User-Agent", proxy.user_agent)
                accept = self.headers.get("Accept")
                if accept:
                    request.add_header("Accept", accept)
                if proxy.api_key:
                    request.add_header("Authorization", f"Bearer {proxy.api_key}")
                try:
                    response = urllib.request.urlopen(request, timeout=600)
                except urllib.error.HTTPError as exc:
                    detail = exc.read()
                    self.send_response(exc.code)
                    self.send_header("Content-Type", exc.headers.get("Content-Type") or "application/json")
                    self.send_header("Content-Length", str(len(detail)))
                    self.end_headers()
                    self.wfile.write(detail)
                    return
                except Exception as exc:  # noqa: BLE001 - report upstream transport failures to the client
                    payload = json.dumps({"error": {"message": f"proxy upstream error: {exc}", "type": "error"}}).encode("utf-8")
                    self.send_response(502)
                    self.send_header("Content-Type", "application/json")
                    self.send_header("Content-Length", str(len(payload)))
                    self.end_headers()
                    self.wfile.write(payload)
                    return
                content_type = response.headers.get("Content-Type") or ""
                self.send_response(response.status)
                self.send_header("Content-Type", content_type)
                if "text/event-stream" in content_type:
                    self.send_header("Cache-Control", "no-cache")
                    self.send_header("Transfer-Encoding", "chunked")
                    self.end_headers()
                    buffer = b""
                    self._last_stream_usage = None
                    while True:
                        chunk = response.read(4096)
                        if not chunk:
                            break
                        self.wfile.write(f"{len(chunk):x}\r\n".encode("ascii") + chunk + b"\r\n")
                        self.wfile.flush()
                        buffer += chunk
                        while b"\n" in buffer:
                            line, buffer = buffer.split(b"\n", 1)
                            self._scan_sse_line(line)
                    self._scan_sse_line(buffer)
                    # Providers send cumulative usage chunks; record only the
                    # final one so a stream counts exactly once.
                    if isinstance(self._last_stream_usage, dict):
                        proxy.record_usage(self._last_stream_usage)
                    self.wfile.write(b"0\r\n\r\n")
                else:
                    data = response.read()
                    if proxy.text_tool_fallback:
                        data = adapt_text_tool_response(data, body)
                    self.send_header("Content-Length", str(len(data)))
                    self.end_headers()
                    self.wfile.write(data)
                    try:
                        decoded = json.loads(data.decode("utf-8"))
                        usage = decoded.get("usage")
                        if isinstance(usage, dict):
                            proxy.record_usage(usage)
                    except (ValueError, UnicodeDecodeError):
                        pass
                with proxy.lock:
                    proxy.requests_log.append(
                        {"path": path, "status": response.status, "duration_seconds": round(time.time() - started, 3)}
                    )

            def _scan_sse_line(self, line: bytes) -> None:
                line = line.strip()
                if not line.startswith(b"data:"):
                    return
                payload = line[len(b"data:") :].strip()
                if not payload or payload == b"[DONE]":
                    return
                try:
                    decoded = json.loads(payload.decode("utf-8"))
                except (ValueError, UnicodeDecodeError):
                    return
                usage = decoded.get("usage") if isinstance(decoded, dict) else None
                if isinstance(usage, dict) and any(
                    isinstance(usage.get(key), (int, float)) and usage.get(key)
                    for key in ("total_tokens", "completion_tokens", "prompt_tokens")
                ):
                    self._last_stream_usage = usage

            do_POST = _forward
            do_GET = _forward

        self._server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
        self._thread = threading.Thread(target=self._server.serve_forever, daemon=True)
        self._thread.start()

    def stop(self) -> None:
        if self._server is not None:
            self._server.shutdown()
            self._server.server_close()
        with self.lock:
            self._flush_locked()

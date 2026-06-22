"""Compatibility facade for OpenAI-compatible chat transport.

The implementation is split by concern:
- transport_request: request construction, retries, response helpers.
- transport_backoff: retry classification and delay calculation.
- transport_preflight: endpoint smoke tests.
- transport_errors: protocol/transport exceptions.
"""

from __future__ import annotations

import urllib.error
import urllib.request

from harness.transport_errors import ChatCompletionError
from harness.transport_preflight import endpoint_smoke, local_no_auth_endpoint as _local_no_auth_endpoint
from harness.transport_request import (
    DEFAULT_BASE_URL,
    DEFAULT_CONTEXT_TOKENS,
    DEFAULT_MAX_RESPONSE_TOKENS,
    DEFAULT_MODEL,
    DEFAULT_PROVIDER,
    DEFAULT_TOOL_RESULT_CHARS,
    HTTP_USER_AGENT,
    PROVIDER_DEFAULTS,
    REQUEST_RETRIES,
    REQUEST_RETRY_BACKOFF_SECONDS,
    REQUEST_TIMEOUT_SECONDS,
    active_provider as _active_provider,
    api_key as _api_key,
    append_jsonl as _append_jsonl,
    chat_completion,
    harness_env as _harness_env,
    logged_response_message as _logged_response_message,
    provider_default as _provider_default,
    provider_env as _provider_env,
    response_text as _response_text,
)

__all__ = [
    "ChatCompletionError",
    "DEFAULT_BASE_URL",
    "DEFAULT_CONTEXT_TOKENS",
    "DEFAULT_MAX_RESPONSE_TOKENS",
    "DEFAULT_MODEL",
    "DEFAULT_PROVIDER",
    "DEFAULT_TOOL_RESULT_CHARS",
    "HTTP_USER_AGENT",
    "PROVIDER_DEFAULTS",
    "REQUEST_RETRIES",
    "REQUEST_RETRY_BACKOFF_SECONDS",
    "REQUEST_TIMEOUT_SECONDS",
    "_active_provider",
    "_api_key",
    "_append_jsonl",
    "_harness_env",
    "_local_no_auth_endpoint",
    "_logged_response_message",
    "_provider_default",
    "_provider_env",
    "_response_text",
    "chat_completion",
    "endpoint_smoke",
    "urllib",
]

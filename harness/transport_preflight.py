"""Provider preflight checks for OpenAI-compatible chat endpoints."""

from __future__ import annotations

import json
import urllib.request
from urllib.parse import urlparse

from harness.transport_request import DEFAULT_BASE_URL, DEFAULT_MODEL, build_chat_request


def endpoint_smoke(base_url: str = DEFAULT_BASE_URL, model: str = DEFAULT_MODEL) -> dict[str, object]:
    body = json.dumps(
        {
            "model": model,
            "messages": [{"role": "user", "content": "Dis moi tres brievement qui est Vasco de Gama (2 phrases)"}],
            "max_tokens": 500,
            "temperature": 0,
        }
    ).encode("utf-8")
    request = build_chat_request(base_url, body)
    with urllib.request.urlopen(request, timeout=60) as response:
        return json.loads(response.read().decode("utf-8"))


def local_no_auth_endpoint(base_url: str) -> bool:
    host = urlparse(base_url).hostname
    return host in {"127.0.0.1", "localhost", "::1"}


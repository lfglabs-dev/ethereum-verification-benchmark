"""Transport-level exception types."""

from __future__ import annotations


class ChatCompletionError(RuntimeError):
    def __init__(
        self,
        message: str,
        *,
        kind: str,
        attempts: int,
        timeout_seconds: int,
        transient: bool,
        last_status: int | None = None,
    ) -> None:
        super().__init__(message)
        self.kind = kind
        self.attempts = attempts
        self.timeout_seconds = timeout_seconds
        self.transient = transient
        self.last_status = last_status

    def to_dict(self) -> dict[str, object]:
        return {
            "message": str(self),
            "kind": self.kind,
            "attempts": self.attempts,
            "timeout_seconds": self.timeout_seconds,
            "transient": self.transient,
            "last_status": self.last_status,
        }


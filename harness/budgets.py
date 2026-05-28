from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class BudgetProfile:
    max_attempts: int
    max_tool_calls: int
    max_turns: int
    grok_timeout_seconds: int


BUDGET_PROFILES: dict[str, BudgetProfile] = {
    "quick": BudgetProfile(max_attempts=1, max_tool_calls=24, max_turns=20, grok_timeout_seconds=900),
    "normal": BudgetProfile(max_attempts=4, max_tool_calls=80, max_turns=50, grok_timeout_seconds=2400),
    "deep": BudgetProfile(max_attempts=12, max_tool_calls=200, max_turns=100, grok_timeout_seconds=7200),
}


def budget_profile(name: str) -> BudgetProfile:
    try:
        return BUDGET_PROFILES[name]
    except KeyError as exc:
        expected = ", ".join(sorted(BUDGET_PROFILES))
        raise ValueError(f"unknown budget profile: {name} (expected one of {expected})") from exc

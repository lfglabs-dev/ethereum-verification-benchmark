from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class BudgetProfile:
    max_attempts: int
    max_tool_calls: int
    max_turns: int
    shell_timeout_seconds: int


BUDGET_PROFILES: dict[str, BudgetProfile] = {
    "quick": BudgetProfile(max_attempts=4, max_tool_calls=40, max_turns=20, shell_timeout_seconds=900),
    "normal": BudgetProfile(max_attempts=16, max_tool_calls=120, max_turns=50, shell_timeout_seconds=2400),
    "deep": BudgetProfile(max_attempts=48, max_tool_calls=400, max_turns=100, shell_timeout_seconds=7200),
}


def budget_profile(name: str) -> BudgetProfile:
    try:
        return BUDGET_PROFILES[name]
    except KeyError as exc:
        expected = ", ".join(sorted(BUDGET_PROFILES))
        raise ValueError(f"unknown budget profile: {name} (expected one of {expected})") from exc

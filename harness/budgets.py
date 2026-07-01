from __future__ import annotations

import os
from dataclasses import asdict, dataclass


@dataclass(frozen=True)
class BudgetProfile:
    max_attempts: int
    max_tool_calls: int
    max_turns: int
    shell_timeout_seconds: int


@dataclass(frozen=True)
class OperationalBudget:
    provider_retries: int
    infra_restarts: int
    request_timeout_seconds: int
    warm_build_timeout_seconds: int


def operational_budget() -> OperationalBudget:
    return OperationalBudget(
        provider_retries=int(os.environ.get("DEFAULT_HARNESS_REQUEST_RETRIES", os.environ.get("GAZELLA_REQUEST_RETRIES", "5"))),
        infra_restarts=int(os.environ.get("DEFAULT_HARNESS_INFRA_RESTARTS", "0")),
        request_timeout_seconds=int(os.environ.get("DEFAULT_HARNESS_REQUEST_TIMEOUT_SECONDS", os.environ.get("GAZELLA_REQUEST_TIMEOUT_SECONDS", "180"))),
        warm_build_timeout_seconds=int(os.environ.get("DEFAULT_HARNESS_WARM_BUILD_TIMEOUT_SECONDS", "1800")),
    )


def budget_artifact(profile: BudgetProfile, *, token_budget: int = 0) -> dict[str, object]:
    return {
        "benchmark_budget": {
            "max_attempts": profile.max_attempts,
            "max_tool_calls": profile.max_tool_calls,
            "max_turns": profile.max_turns,
            "completion_token_budget": token_budget,
        },
        "operational_budget": asdict(operational_budget()),
    }


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

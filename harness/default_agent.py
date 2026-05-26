#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import random
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any
from urllib import error, request

from benchmark_config import load_benchmark_agent_defaults
from interactive_runtime import (
    TaskProofRuntime,
    classify_failure,
    extract_contract_simp_terms,
    prebuild_task_modules,
    tool_result_json,
    _PREFLIGHT_FAILURE_MODES as _RUNTIME_PREFLIGHT_FAILURE_MODES,
)
from task_runner import ROOT, load_task_record, resolve_task_manifest

AGENT_RESULTS_DIR = ROOT / "results" / "agent_runs"
SCHEMA_PATH = ROOT / "schemas" / "agent-config.schema.json"
RUN_SCHEMA_PATH = ROOT / "schemas" / "agent-run.schema.json"
BENCHMARK_DEFAULTS = load_benchmark_agent_defaults()
DEFAULT_PROFILE = BENCHMARK_DEFAULTS.default_agent_default_profile
AGENT_PROFILES_DIR = ROOT / BENCHMARK_DEFAULTS.default_agent_profiles_dir
DEFAULT_AGENT_CONFIG_PATH = ROOT / BENCHMARK_DEFAULTS.default_agent_config
PLACEHOLDER_PATTERN = re.compile(r"\b(sorry|admit|axiom)\b")
MAX_ERROR_FEEDBACK_CHARS = 6000
MAX_REASONING_SNIPPET_CHARS = 4000
ADAPTER_PROTOCOL_VERSION = 1
THINK_BLOCK_PATTERN = re.compile(r"(?s)<think>(.*?)</think>\s*")


@dataclass(frozen=True)
class ResolvedAgentConfig:
    profile: str | None
    agent_id: str
    track: str
    run_slug: str
    adapter: str
    config_path: str
    base_url: str
    base_url_env: str | None
    model: str
    model_env: str | None
    api_key: str
    api_key_env: str | None
    chat_completions_path: str
    models_path: str
    system_prompt_files: list[str]
    mode: str
    temperature: float
    max_completion_tokens: int
    max_attempts: int
    max_tool_calls: int
    headers: dict[str, str]
    header_envs: dict[str, str]
    env_contract: dict[str, list[str]]
    extra_body: dict[str, Any]
    request_timeout_seconds: int
    command: list[str]


def load_json(path: Path) -> object:
    return json.loads(path.read_text(encoding="utf-8"))


def type_matches(value: object, expected: str) -> bool:
    if expected == "object":
        return isinstance(value, dict)
    if expected == "array":
        return isinstance(value, list)
    if expected == "string":
        return isinstance(value, str)
    if expected == "integer":
        return isinstance(value, int) and not isinstance(value, bool)
    if expected == "number":
        return isinstance(value, (int, float)) and not isinstance(value, bool)
    if expected == "boolean":
        return isinstance(value, bool)
    if expected == "null":
        return value is None
    raise ValueError(f"unsupported schema type {expected!r}")


def validate(value: object, schema: dict[str, Any], path: str) -> list[str]:
    errors: list[str] = []

    schema_type = schema.get("type")
    if schema_type is not None:
        if isinstance(schema_type, list):
            if not any(type_matches(value, item) for item in schema_type):
                errors.append(f"{path}: expected one of {schema_type}, got {type(value).__name__}")
                return errors
        elif not type_matches(value, schema_type):
            errors.append(f"{path}: expected {schema_type}, got {type(value).__name__}")
            return errors

    if "const" in schema and value != schema["const"]:
        errors.append(f"{path}: expected constant {schema['const']!r}, got {value!r}")

    if "enum" in schema and value not in schema["enum"]:
        errors.append(f"{path}: expected one of {schema['enum']}, got {value!r}")

    if isinstance(value, dict):
        required = schema.get("required", [])
        for key in required:
            if key not in value:
                errors.append(f"{path}: missing required key {key!r}")

        properties = schema.get("properties", {})
        additional = schema.get("additionalProperties", True)
        for key, item in value.items():
            if key in properties:
                errors.extend(validate(item, properties[key], f"{path}.{key}"))
            elif additional is False:
                errors.append(f"{path}: unexpected key {key!r}")
            elif isinstance(additional, dict):
                errors.extend(validate(item, additional, f"{path}.{key}"))

    if isinstance(value, list) and "items" in schema:
        for index, item in enumerate(value):
            errors.extend(validate(item, schema["items"], f"{path}[{index}]"))

    if isinstance(value, str):
        min_length = schema.get("minLength")
        if min_length is not None and len(value) < min_length:
            errors.append(f"{path}: expected string length >= {min_length}, got {len(value)}")

    if isinstance(value, list):
        min_items = schema.get("minItems")
        if min_items is not None and len(value) < min_items:
            errors.append(f"{path}: expected at least {min_items} item(s), got {len(value)}")
        if schema.get("uniqueItems"):
            duplicates: list[object] = []
            for item in value:
                if item in duplicates:
                    continue
                if value.count(item) > 1:
                    duplicates.append(item)
            if duplicates:
                errors.append(f"{path}: expected unique items, got duplicates {duplicates!r}")

    if isinstance(value, (int, float)) and not isinstance(value, bool):
        minimum = schema.get("minimum")
        if minimum is not None and value < minimum:
            errors.append(f"{path}: expected >= {minimum}, got {value}")

    return errors


def validate_config_data(data: object, label: str) -> dict[str, Any]:
    schema = load_json(SCHEMA_PATH)
    if not isinstance(data, dict):
        raise SystemExit(f"{label}: config must decode to an object")
    errors = validate(data, schema, label)
    errors.extend(validate_agent_contract(data, label))
    if errors:
        raise SystemExit("\n".join(errors))
    return data


def load_config(path: Path) -> dict[str, Any]:
    return validate_config_data(load_json(path), config_label(path))


def config_label(path: Path) -> str:
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)


def explicit_config_path(config_path: str) -> Path:
    candidate = Path(config_path)
    if not candidate.is_absolute():
        candidate = ROOT / candidate
    if candidate.is_file():
        return candidate
    raise SystemExit(f"agent config file not found: {config_label(candidate)}")


def profile_path(profile: str) -> Path:
    name = profile.strip()
    if not name:
        raise SystemExit("profile name must not be empty")
    if "/" in name or name.startswith("."):
        raise SystemExit(f"invalid profile name {profile!r}")
    return AGENT_PROFILES_DIR / f"{name}.json"


def resolve_config_path(config_or_profile: str | None, profile: str | None) -> Path:
    if config_or_profile and profile:
        raise SystemExit("pass either --config or --profile, not both")
    if profile:
        path = profile_path(profile)
        if not path.is_file():
            raise SystemExit(f"agent profile not found: {config_label(path)}")
        return path
    if config_or_profile:
        candidate = Path(config_or_profile)
        if not candidate.is_absolute():
            candidate = ROOT / candidate
        if candidate.is_file():
            return candidate
        fallback = profile_path(config_or_profile)
        if fallback.is_file():
            return fallback
        raise SystemExit(
            f"agent config not found: {config_or_profile!r} "
            f"(checked file {config_label(candidate)} and profile {config_label(fallback)})"
        )
    if DEFAULT_AGENT_CONFIG_PATH.is_file():
        return DEFAULT_AGENT_CONFIG_PATH
    default_path = profile_path(DEFAULT_PROFILE)
    if default_path.is_file():
        return default_path
    raise SystemExit(
        "default agent config not found: "
        f"{config_label(DEFAULT_AGENT_CONFIG_PATH)} "
        f"(fallback profile {config_label(default_path)})"
    )


def discover_profiles() -> list[str]:
    if not AGENT_PROFILES_DIR.is_dir():
        return []
    return sorted(path.stem for path in AGENT_PROFILES_DIR.glob("*.json") if path.is_file())


def normalize_string(value: object) -> str | None:
    if value is None:
        return None
    text = str(value).strip()
    return text or None


def validate_agent_contract(config: dict[str, Any], label: str) -> list[str]:
    errors: list[str] = []
    mode = normalize_string(config.get("mode"))
    adapter = normalize_string(config.get("adapter"))

    for field in ("agent_id", "run_slug"):
        if not normalize_string(config.get(field)):
            errors.append(f"{label}: {field!r} must be a non-empty string")

    if mode not in {"strict", "interactive", "custom"}:
        errors.append(f"{label}: 'mode' must be one of ['strict', 'interactive', 'custom']")

    if adapter == "openai_compatible":
        for field in ("base_url", "model", "api_key"):
            direct_value = normalize_string(config.get(field))
            env_name = normalize_string(config.get(f"{field}_env"))
            if direct_value or env_name:
                continue
            errors.append(f"{label}: set either {field!r} or {field + '_env'!r}")
        for field in ("chat_completions_path", "models_path"):
            value = normalize_string(config.get(field))
            if not value:
                errors.append(f"{label}: {field!r} must be a non-empty string")
            elif not value.startswith("/"):
                errors.append(f"{label}: {field!r} must start with '/' for openai_compatible adapters")
    elif adapter == "command":
        raw_command = config.get("command")
        if not isinstance(raw_command, list) or not raw_command:
            errors.append(f"{label}: 'command' must be a non-empty array for command adapters")
        else:
            for index, item in enumerate(raw_command):
                if not normalize_string(item):
                    errors.append(f"{label}: command[{index}] must be a non-empty string")
            if command_requires_openai_connection(raw_command):
                for field in ("base_url", "model", "api_key"):
                    direct_value = normalize_string(config.get(field))
                    env_name = normalize_string(config.get(f"{field}_env"))
                    if direct_value or env_name:
                        continue
                    errors.append(
                        f"{label}: bundled openai-compatible command adapter requires "
                        f"either {field!r} or {field + '_env'!r}"
                    )
                for field in ("chat_completions_path", "models_path"):
                    value = normalize_string(config.get(field))
                    if not value:
                        errors.append(f"{label}: {field!r} must be a non-empty string")
                    elif not value.startswith("/"):
                        errors.append(f"{label}: {field!r} must start with '/'")
    else:
        errors.append(f"{label}: unsupported adapter {adapter!r}")

    if mode in {"strict", "interactive"} and adapter != "openai_compatible":
        errors.append(f"{label}: mode {mode!r} requires adapter 'openai_compatible'")
    if mode == "custom" and adapter != "command":
        errors.append(f"{label}: mode 'custom' requires adapter 'command'")

    prompt_files = config.get("system_prompt_files", [])
    if isinstance(prompt_files, list):
        for index, item in enumerate(prompt_files):
            if not normalize_string(item):
                errors.append(f"{label}: system_prompt_files[{index}] must be a non-empty string")

    raw_header_envs = config.get("header_envs", {})
    if isinstance(raw_header_envs, dict):
        for header_name, env_name in raw_header_envs.items():
            if not normalize_string(header_name):
                errors.append(f"{label}: header_envs contains a blank header name")
            if not normalize_string(env_name):
                errors.append(f"{label}: header_envs[{header_name!r}] must be a non-empty env var name")

    return errors


def slugify(value: str) -> str:
    slug_chars: list[str] = []
    previous_dash = False
    for char in value.strip().lower():
        if char.isalnum():
            slug_chars.append(char)
            previous_dash = False
            continue
        if not previous_dash:
            slug_chars.append("-")
            previous_dash = True
    slug = "".join(slug_chars).strip("-")
    return slug or "agent"


def resolve_track(config: dict[str, Any], *, profile: str | None) -> str:
    explicit = normalize_string(config.get("track"))
    if explicit:
        return explicit
    if profile == DEFAULT_PROFILE:
        return "reference"
    return "custom"


def resolve_mode(config: dict[str, Any], *, profile: str | None) -> str:
    explicit = normalize_string(config.get("mode"))
    if explicit:
        return explicit
    if profile == DEFAULT_PROFILE:
        return "strict"
    return "custom"


def resolve_run_slug(config: dict[str, Any], *, agent_id: str, profile: str | None) -> str:
    explicit = normalize_string(config.get("run_slug"))
    if explicit:
        base = slugify(explicit)
    elif profile:
        base = slugify(profile)
    else:
        base = slugify(agent_id)
    # Support repeat-index disambiguation for parallel benchmark runs
    repeat_idx = os.environ.get("VERITY_REPEAT_INDEX", "")
    # Sanitize: only allow digits to prevent path traversal
    repeat_idx = repeat_idx if repeat_idx.isdigit() else ""
    if repeat_idx and repeat_idx != "1":
        return f"{base}-r{repeat_idx}"
    return base


def resolve_field(config: dict[str, Any], field: str, *, required: bool) -> str | None:
    direct_value = normalize_string(config.get(field))
    if direct_value:
        return direct_value
    env_name = normalize_string(config.get(f"{field}_env"))
    if env_name:
        env_value = normalize_string(os.environ.get(env_name))
        if env_value:
            return env_value
        if required:
            raise SystemExit(f"missing required environment variable {env_name!r} for {field}")
        return None
    if required:
        raise SystemExit(f"missing required config value for {field}")
    return None


def resolve_headers(config: dict[str, Any]) -> dict[str, str]:
    headers: dict[str, str] = {}
    raw_headers = config.get("headers", {})
    if isinstance(raw_headers, dict):
        headers.update({str(key): str(value) for key, value in raw_headers.items()})

    raw_header_envs = config.get("header_envs", {})
    if isinstance(raw_header_envs, dict):
        for header_name, env_name in raw_header_envs.items():
            env_value = normalize_string(os.environ.get(str(env_name)))
            if env_value:
                headers[str(header_name)] = env_value

    return headers


def redact_headers(headers: dict[str, str]) -> dict[str, str]:
    return {str(header_name): "<redacted>" for header_name in headers}


def resolve_command(config: dict[str, Any]) -> list[str]:
    raw_command = config.get("command", [])
    if not isinstance(raw_command, list):
        return []
    return [str(item) for item in raw_command]


def command_requires_openai_connection(command: list[object]) -> bool:
    command_text = " ".join(str(item) for item in command)
    return "openai_compatible_adapter.py" in command_text


def resolve_config(path: Path, *, require_secrets: bool, profile: str | None = None) -> ResolvedAgentConfig:
    config = load_config(path)
    agent_id = str(config["agent_id"])
    adapter = str(config["adapter"])
    mode = resolve_mode(config, profile=profile)
    command = resolve_command(config)
    requires_openai_connection = adapter == "openai_compatible" or command_requires_openai_connection(command)
    prompt_files = [str(item) for item in config["system_prompt_files"]]
    missing_files = [item for item in prompt_files if not (ROOT / item).is_file()]
    if missing_files:
        raise SystemExit(f"missing system prompt files: {', '.join(missing_files)}")

    return ResolvedAgentConfig(
        profile=profile,
        agent_id=agent_id,
        track=resolve_track(config, profile=profile),
        run_slug=resolve_run_slug(config, agent_id=agent_id, profile=profile),
        adapter=adapter,
        config_path=config_label(path),
        base_url=(resolve_field(config, "base_url", required=require_secrets and requires_openai_connection) or "").rstrip("/"),
        base_url_env=normalize_string(config.get("base_url_env")),
        model=resolve_field(config, "model", required=require_secrets and requires_openai_connection) or "",
        model_env=normalize_string(config.get("model_env")),
        api_key=resolve_field(config, "api_key", required=require_secrets and requires_openai_connection) or "",
        api_key_env=normalize_string(config.get("api_key_env")),
        chat_completions_path=str(config.get("chat_completions_path") or ""),
        models_path=str(config.get("models_path") or ""),
        system_prompt_files=prompt_files,
        mode=mode,
        temperature=float(config["temperature"]),
        max_completion_tokens=int(config["max_completion_tokens"]),
        max_attempts=int(config.get("max_attempts", 5)),
        max_tool_calls=int(config.get("max_tool_calls", 24)),
        headers=resolve_headers(config),
        header_envs={str(key): str(value) for key, value in dict(config.get("header_envs", {})).items()},
        env_contract=env_contract(config),
        extra_body=dict(config.get("extra_body", {})),
        request_timeout_seconds=int(config.get("request_timeout_seconds", 120)),
        command=command,
    )


def _synthesized_interactive_tools_prompt() -> str:
    """Render the real interactive tool surface from TaskProofRuntime.tool_specs().

    Replaces the static harness/TOOLS.md which advertises `lake build`, `scripts/run_task.sh`,
    and `scripts/run_all.sh` — none of which are actually callable in interactive mode.
    """
    lines = [
        "# Interactive Tool Surface",
        "",
        "You have exactly these function tools. Call them; do NOT call shell commands:",
        "",
    ]
    # Build a minimal task shim to get tool_specs without instantiating a real task.
    # Note: tool_specs() uses self.paths.public_files for the read_public_file enum,
    # so we enumerate generic names here instead of calling tool_specs() directly.
    surface = [
        ("read_public_file(path)", "Read one of the task's public Lean files (impl/spec/editable)."),
        ("write_editable_proof(content)", "Replace the editable proof file AND automatically run the Lean check. Response reports status (passed/failed), failure_mode, details, failure_class, and repair_hints. A separate run_lean_check call is not needed after this."),
        ("run_lean_check()", "Re-run `lake env lean` without changing the file (redundant immediately after write_editable_proof)."),
        ("inspect_lean_goals()", "Inspect goal state at explicit `?_` holes. Unsupported if no hole present."),
        ("try_tactic_at_hole(tactic)", "Replace all `?_` holes with a tactic and check. Pass a raw tactic (e.g. `omega`, `simp_all`, `decide`); substitution auto-wraps as `(by tac)` at term positions like `exact ?_`. Preserves original proof on failure."),
        ("search_public_defs(query)", "Search the task's public impl/spec files for def/theorem/lemma names. Does NOT search Lean core / Batteries / Mathlib — use `exact?`/`apply?`/`rw?` via `try_tactic_at_hole` for standard-library lemmas."),
    ]
    for name, desc in surface:
        lines.append(f"- `{name}` — {desc}")
    lines.extend([
        "",
        "Typical loop: write_editable_proof (which runs Lean) → read repair_hints → iterate.",
        "`?_` is a PROBE for `inspect_lean_goals` / `try_tactic_at_hole`, never a final proof — Lean rejects every submission containing `?_`.",
        "Do NOT emit `lake build` or `scripts/...`; there is no shell tool.",
    ])
    return "\n".join(lines)


def build_system_prompt(config: ResolvedAgentConfig) -> str:
    sections = []
    for rel_path in config.system_prompt_files:
        # In interactive mode, replace the static TOOLS.md (which advertises shell
        # commands that don't exist) with a synthesized description of the real
        # function-tool surface.
        if config.mode == "interactive" and rel_path.endswith("TOOLS.md"):
            sections.append(f"[{rel_path}]\n{_synthesized_interactive_tools_prompt()}")
            continue
        path = ROOT / rel_path
        sections.append(f"[{rel_path}]\n{path.read_text(encoding='utf-8').strip()}")
    return "\n\n".join(sections).strip()


def render_file_bundle(paths: list[str]) -> str:
    sections = []
    for rel_path in paths:
        path = ROOT / rel_path
        if not path.is_file():
            sections.append(f"[{rel_path}]\n<missing>")
            continue
        contents = path.read_text(encoding="utf-8").strip()
        lines = [line.strip() for line in contents.splitlines() if line.strip()]
        if len(lines) == 1 and lines[0].startswith("import "):
            continue
        sections.append(f"[{rel_path}]\n{contents}")
    return "\n\n".join(sections).strip()



def extract_contract_branches(task: dict[str, Any]) -> list[str]:
    """Extract conditional branch conditions from contract implementation files."""
    branches: list[str] = []
    for rel_path in task.get("implementation_files", []):
        path = ROOT / rel_path
        if not path.is_file():
            continue
        content = path.read_text(encoding="utf-8")
        # Match 'if <condition> then' patterns in contract code
        for m in re.finditer(r"if\s+(.+?)\s+then", content):
            cond = m.group(1).strip()
            if cond not in branches:
                branches.append(cond)
        # Match 'ite (<condition>)' patterns (e.g., ite (nodeIndex == 3) ...)
        for m in re.finditer(r"\bite\s+\((.+?)\)", content):
            cond = m.group(1).strip()
            if cond not in branches:
                branches.append(cond)
    return branches


def build_proof_hints(task: dict[str, Any]) -> str:
    family = str(task.get("proof_family", ""))
    # Extract concrete simp terms from contract files
    contract_terms = extract_contract_simp_terms(task)
    shared = [
        "Verity execution proofs often need `simp` with the operational definitions, not just the theorem spec.",
        "Useful simplification symbols are often: `getStorage`, `setStorage`, `getMapping`, `setMapping`, `getMappingUint`, `setMappingUint`, `msgSender`, `Verity.require`, `Verity.bind`, `Bind.bind`, `Verity.pure`, `Pure.pure`, `Contract.run`, and `ContractResult.snd`.",
        "CRITICAL: Include ALL storage field definitions (e.g., `ContractName.depositCount`, `ContractName.chainStarted`) in the simp set so that `.slot` reduces to concrete slot numbers. Without these, simp leaves unresolved `if` expressions.",
        "CRITICAL: Pass ALL precondition hypotheses (`hCount`, `hMin`, etc.) to simp so it can evaluate `if` branches. Simp needs the hypotheses to reduce conditional execution paths.",
        "For mapping storage, the contract may use `setMappingUint`/`getMappingUint`. Include `setMappingUint`/`getMappingUint` and the mapping field definitions in simp.",
        "If the contract has conditional branches (e.g., `if depositAmount >= threshold then ...`), use `by_cases` on each condition BEFORE calling `simp`, not `split` after. CRITICAL: In each `by_cases` branch, repeat the FULL simp set PLUS the case hypothesis. Do NOT use bare `simp [hBig]` - you must include ALL contract definitions, storage fields, and operational symbols in every simp call. Example pattern:\n  ```\n  by_cases hBig : depositAmount >= 32000000000\n  · by_cases hThresh : add (s.storage 1) 1 = 65536\n    · simp [ContractName.fn, ContractName.field1, ContractName.field2, getStorage, setStorage, Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd, hCount, hMin, hBig, hThresh]\n    · simp [ContractName.fn, ContractName.field1, ContractName.field2, getStorage, setStorage, Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd, hCount, hMin, hBig, hThresh]\n  · simp [ContractName.fn, ContractName.field1, getStorage, setStorage, Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd, hCount, hMin, hBig]\n  ```",
        "If `simp` leaves unsolved goals because a hypothesis (e.g., `hBound`) uses a spec helper name while the goal has it unfolded, use `simp_all` instead of `simp`. `simp_all` rewrites hypotheses into the goal context, allowing it to match and discharge conditions that `simp` alone cannot.",
        "IMPORTANT: Verity contracts compile conditions like `x < y` into `decide (x < y) = true`. Do NOT use `decide_True` or `decide_False` - these identifiers do not exist. Instead, pass the precondition hypotheses (e.g., `hCount`, `hMin`) directly to `simp` and it will handle the `decide` reduction automatically.",
        "For negated branch conditions in `by_cases`: when `h : ¬ (x >= c)`, you can derive `have hLt : x < c := Nat.lt_of_not_ge h` and vice versa with `Nat.not_le_of_lt`. But usually just passing `h` to `simp` is sufficient.",
        "If helpful, add imports required for proof automation, for example `import Verity.Proofs.Stdlib.Automation`.",
    ]
    family_specific: list[str] = []
    if family == "state_preservation_local_effects":
        family_specific = [
            "For local-effect theorems, unfold the spec, split on branch conditions, prove concrete slot-write equalities, then finish with `simpa`.",
        ]
    elif family == "protocol_transition_correctness":
        family_specific = [
            "For transition theorems, use `by_cases` on threshold guards before simplifying the execution trace.",
            "For hypotheses of the form `hSmall : x < c`, the negated branch fact is often `have hNotBranch : ¬ c ≤ x := Nat.not_le_of_lt hSmall`.",
        ]
    elif family == "authorization_enablement":
        family_specific = [
            "For authorization theorems, unfold the spec then use `simp_all` (NOT `simp`) with the full simp set including all spec helpers. `simp_all` rewrites hypotheses into the goal, resolving require-guard conditions automatically. Do NOT use `dsimp` + `simp only` - use a single `simp_all` call.",
        ]
    elif family == "refinement_equivalence":
        family_specific = [
            "For refinement/equivalence theorems, normalize both sides into the same post-state shape before comparing observables.",
        ]
    elif family == "functional_correctness":
        family_specific = [
            "For functional-correctness theorems, unfold the spec to the mathematical target form before simplifying the execution result.",
        ]
    lines = ["Public proof hints:"] + [f"- {item}" for item in [*shared, *family_specific]]
    full_simp_set = ", ".join(contract_terms) if contract_terms else ""
    if full_simp_set:
        full_simp_set += ", "
    full_simp_set += "getStorage, setStorage, getMapping, setMapping, getMappingUint, setMappingUint, msgSender, Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd"
    if contract_terms:
        lines.append(f"\nFull simp set for this task (copy-paste this into EVERY simp call, including inside by_cases branches):")
        lines.append(f"  [{full_simp_set}]")
        lines.append(f"  IMPORTANT: Inside each `by_cases` branch, use `simp [{full_simp_set}, <all_hypotheses>]`. Never use bare `simp [h]`.")
    # Extract and show branch conditions
    branches = extract_contract_branches(task)
    if branches:
        lines.append(f"\nConditional branches in this contract (use `by_cases` on each relevant condition before simp):")
        for i, branch in enumerate(branches):
            lines.append(f"  {i+1}. `{branch}`")
    return "\n".join(lines)


def build_user_prompt(task: dict[str, Any], *, interactive: bool) -> str:
    editable_file = task["editable_files"][0]
    mode_instructions = (
        "You are in interactive mode with verification tools.\n"
        "All implementation, specification, and editable proof files are already provided below. "
        "Do NOT re-read them with read_public_file — start working immediately.\n"
        "Workflow: call write_editable_proof with your complete proof file — it returns the Lean check result directly, you do NOT need a separate run_lean_check call afterward.\n"
        "If the check fails, read the failure_class and repair_hints in the result.\n"
        "For unknown_identifier errors: read the repair_hints before searching — the missing name may be a tactic in term position (wrap in `by`), a local binder (call inspect_lean_goals instead), or a Mathlib lemma (this workspace has NO Mathlib; use `omega`/`ring`/`simp arith`). Only call search_public_defs for a genuine project-defined name from the implementation or spec file.\n"
        "For unsolved_goals: use inspect_lean_goals with a ?_ hole to see the exact goal, then write targeted tactics.\n"
        "Fix the specific error, write the corrected proof, and re-check. Do not rewrite from scratch unless the approach is fundamentally wrong.\n"
        "Only use read_public_file or search_public_defs if you need a definition not shown below.\n"
        "Do not ask for or attempt arbitrary shell access, arbitrary filesystem access, or files outside this task.\n"
    ) if interactive else (
        "The harness may give you several bounded repair rounds for the same task.\n"
        "On every round, return the complete editable Lean proof file, not a patch or explanation.\n"
    )
    return (
        "You are running the default benchmark agent for verity-benchmark.\n"
        "Treat this as a strict proof-generation benchmark.\n"
        "Do not invent specs, modify implementations, or rely on hidden reference proofs.\n\n"
        f"{mode_instructions}\n"
        "Do not claim that you will inspect more files or run commands.\n"
        "Reason only from the task payload and the file contents included below.\n"
        "Return Lean code only if you answer with a final proof file.\n"
        f"Task ref: {task['task_ref']}\n"
        f"Theorem name: {task['theorem_name']}\n"
        f"Proof family: {task['proof_family']}\n"
        f"Editable file: {editable_file}\n\n"
        "Implementation file contents:\n"
        f"{render_file_bundle(task['implementation_files'])}\n\n"
        "Specification file contents:\n"
        f"{render_file_bundle(task['specification_files'])}\n\n"
        "Editable proof template contents:\n"
        f"{render_file_bundle(task['editable_files'])}\n\n"
        f"{build_proof_hints(task)}\n"
    )


def build_messages(config: ResolvedAgentConfig, task: dict[str, Any]) -> list[dict[str, str]]:
    return [
        {"role": "system", "content": build_system_prompt(config)},
        {"role": "user", "content": build_user_prompt(task, interactive=config.mode == "interactive")},
    ]




def build_repair_guidance(details: str, failure_mode: str | None = None) -> str:
    hints: list[str] = []
    failure_class = classify_failure(details)

    # Failure-mode-specific hints (from main)
    if failure_mode == "empty_response":
        hints.append(
            "- Your previous reply did not include a usable Lean file. Return only the complete Lean proof file."
        )
    if failure_mode == "placeholder_detected":
        hints.append(
            "- Do not use `sorry`, `admit`, or `axiom`. Replace every placeholder with a real proof term or tactic."
        )
    if failure_mode == "theorem_statement_mismatch":
        hints.append(
            "- Keep the editable theorem statement byte-for-byte identical to the original. Only change the proof body."
        )
    if failure_mode == "hidden_proof_import_detected":
        hints.append(
            "- Remove any `Benchmark.Cases.*.Proofs` imports. Only import task-public modules."
        )
    if failure_mode == "hidden_case_import_detected":
        hints.append(
            "- Only import task-public modules. Remove any non-public `Benchmark.Cases` imports."
        )

    # Failure-class-specific hints (from our branch, more targeted)
    if failure_class == "split_failed":
        hints.append(
            "- Do not `split` the final post-state blindly. Prove branch-specific helper theorems first, then use `by_cases` plus `simpa`."
        )
    if failure_class == "no_goals":
        hints.append(
            "- A previous `simp` likely closed the goal already. Remove trailing tactics after the goal is solved."
        )
    if failure_class == "free_variables":
        hints.append(
            "- Do not use `native_decide` or `decide` on goals that still contain parameters. First reduce to concrete equalities."
        )
    if failure_class == "unknown_identifier":
        hints.append(
            "- You are referencing a lemma or constant that does not exist in this Lean 4 environment. "
            "Do not guess lemma names. Instead, use `simp` with the relevant definitions, `omega` for arithmetic, "
            "or `decide`/`native_decide` for decidable propositions. Remove all references to unknown names."
        )
        hints.append(
            "- Use the `search_public_defs` tool to find correct definition names from the specification and implementation files."
        )
    if failure_class == "unsolved_goals":
        if "match" in details:
            hints.append(
                "- The remaining goal contains a `match` expression. Use `split` to case-split on the match, "
                "then solve each branch separately. If the match is on a ContractResult, try "
                "`simp only [...]` to reduce it first, or use `cases` on the matched expression."
            )
        if "if " in details:
            hints.append(
                "- The remaining goal contains an `if` expression. Use `by_cases h : <condition>` to split on the condition, "
                "then `simp [h, ...]` in each branch. Do NOT use `split` after simp or `native_decide`/`decide` on goals with free variables."
            )
        if "match" not in details and "if " not in details:
            hints.append(
                "- Unsolved goals remain. Check that `simp` is given all necessary definitions and hypotheses."
            )
        hints.append(
            "- Try `inspect_lean_goals` with a `?_` hole to see the exact goal state, then write targeted tactics."
        )
    if failure_class == "rfl_failed":
        if "match" in details or "if " in details:
            hints.append(
                "- rfl failed because the goal has unresolved `if`/`match` expressions. Use `by_cases` on each unresolved condition BEFORE simp, not `split` after. Pass all case hypotheses to simp. For nested conditions, nest `by_cases`."
            )
        else:
            hints.append(
                "- rfl failed. Try replacing `rfl` with `simp` or adding more definitions to the simp set."
            )
    if failure_class == "type_mismatch":
        hints.append(
            "- Check that your proof term has the expected type. Unfold definitions to align both sides."
        )
    if failure_class == "unknown_tactic":
        hints.append(
            "- Use standard Lean 4 / Mathlib tactics. Remove any tactic the checker does not recognize."
        )
    if failure_class == "simp_no_progress":
        hints.append(
            "- `simp` made no progress with the given arguments. Add more definitions to unfold, "
            "or the simp arguments may already be fully reduced. Try removing the unproductive simp call."
        )
    # Additional hints from main for patterns not covered by failure_class
    if "failed to infer binder type" in details:
        hints.append(
            "- Lean cannot infer a binder type. Add explicit type annotations to your helper lemma parameters."
        )
    if "unexpected token" in details or "expected 'by'" in details:
        hints.append(
            "- Syntax error. Ensure the theorem body uses `:= by` followed by tactics. "
            "Do not use `:=` with a term-mode proof unless you are certain of the syntax."
        )
    if "Function expected at" in details:
        hints.append(
            "- Use `s.storage 0` (function application) not `s.storage[0]` or `s.storage.0`. "
            "ContractState.storage is a function `Nat → Uint256`."
        )
    return "\n".join(hints)


def build_repair_messages(
    base_messages: list[dict[str, Any]],
    candidate_text: str,
    evaluation: dict[str, Any],
    *,
    attempt_index: int,
    max_attempts: int,
) -> list[dict[str, Any]]:
    failure_mode = str(evaluation.get("failure_mode") or "").strip() or None
    details = str(evaluation.get("details", "")).strip()
    trimmed_details = details[:MAX_ERROR_FEEDBACK_CHARS]
    guidance = build_repair_guidance(trimmed_details, failure_mode=failure_mode)
    failure_summary = f"Failure mode: {failure_mode}\n" if failure_mode else ""
    repair_prompt = (
        f"The previous Lean file did not pass the checker (attempt {attempt_index} of {max_attempts}).\n"
        f"{failure_summary}"
        "Return a corrected complete replacement for the editable Lean proof file.\n"
        "Return Lean code only, with no markdown fences or extra explanation.\n\n"
        "Previous candidate file:\n"
        f"{candidate_text.rstrip()}\n\n"
        "Lean checker output:\n"
        f"{trimmed_details}\n"
    )
    if guidance:
        repair_prompt += f"\nGeneric repair guidance:\n{guidance}\n"
    return [
        *base_messages,
        {"role": "assistant", "content": candidate_text},
        {"role": "user", "content": repair_prompt},
    ]


def reasoning_excerpt(response: dict[str, Any]) -> str:
    reasoning = extract_response_content(response)["provider_reasoning_text"]
    return reasoning[:MAX_REASONING_SNIPPET_CHARS]


def response_message(response: dict[str, Any]) -> dict[str, Any]:
    choices = response.get("choices")
    if not isinstance(choices, list) or not choices:
        return {}
    message = choices[0].get("message", {})
    return message if isinstance(message, dict) else {}


def extract_response_content(response: dict[str, Any]) -> dict[str, str]:
    message = response_message(response)
    reasoning_parts: list[str] = []
    reasoning_content = message.get("reasoning_content")
    if isinstance(reasoning_content, str) and reasoning_content.strip():
        reasoning_parts.append(reasoning_content.strip())

    raw_segments: list[str] = []
    content = message.get("content")
    if isinstance(content, str):
        raw_segments.append(content.strip())
        reasoning_parts.extend(match.strip() for match in THINK_BLOCK_PATTERN.findall(content) if match.strip())
    elif isinstance(content, list):
        for item in content:
            if not isinstance(item, dict):
                continue
            item_type = item.get("type")
            text = item.get("text")
            if item_type == "text" and isinstance(text, str):
                raw_segments.append(text.strip())
                reasoning_parts.extend(match.strip() for match in THINK_BLOCK_PATTERN.findall(text) if match.strip())
            elif isinstance(text, str) and item_type in {"reasoning", "thinking"} and text.strip():
                reasoning_parts.append(text.strip())

    raw_text = "\n".join(segment for segment in raw_segments if segment).strip()
    return {
        "response_text_raw": raw_text,
        "response_text": THINK_BLOCK_PATTERN.sub("", raw_text).strip(),
        "provider_reasoning_text": "\n\n".join(part for part in reasoning_parts if part).strip(),
    }


def first_choice(response: dict[str, Any]) -> dict[str, Any]:
    choices = response.get("choices")
    if not isinstance(choices, list) or not choices:
        return {}
    choice = choices[0]
    return choice if isinstance(choice, dict) else {}


def stable_digest(payload: object) -> str:
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def prompt_chars(messages: list[dict[str, Any]]) -> int:
    total = 0
    for message in messages:
        content = message.get("content")
        if isinstance(content, str):
            total += len(content)
    return total


def attempt_has_candidate_state(attempt: dict[str, Any] | None) -> bool:
    if not isinstance(attempt, dict):
        return False
    candidate_text = attempt.get("candidate_file_contents")
    if isinstance(candidate_text, str) and candidate_text.strip():
        return True
    evaluation = attempt.get("evaluation")
    if not isinstance(evaluation, dict):
        return False
    status = evaluation.get("status")
    failure_mode = evaluation.get("failure_mode")
    return bool((isinstance(status, str) and status) or (isinstance(failure_mode, str) and failure_mode))


def latest_candidate_attempt(attempts: list[dict[str, Any]]) -> dict[str, Any] | None:
    for attempt in reversed(attempts):
        if attempt_has_candidate_state(attempt):
            return attempt
    return None


def build_attempt_trace(
    *,
    messages: list[dict[str, Any]],
    response: dict[str, Any],
    response_content: dict[str, str],
    candidate_text: str,
    evaluation: dict[str, Any] | None,
    previous_attempt: dict[str, Any] | None,
    latency_seconds: float | None,
) -> dict[str, Any]:
    choice = first_choice(response)
    usage = response.get("usage")
    usage_payload = usage if isinstance(usage, dict) else {}
    previous_trace = previous_attempt.get("trace", {}) if isinstance(previous_attempt, dict) else {}
    previous_candidate = str(previous_attempt.get("candidate_file_contents", "")) if isinstance(previous_attempt, dict) else ""
    failure_mode = evaluation.get("failure_mode") if isinstance(evaluation, dict) else None
    status = evaluation.get("status") if isinstance(evaluation, dict) else None
    return {
        "prompt_message_count": len(messages),
        "prompt_chars": prompt_chars(messages),
        "prompt_sha256": stable_digest(messages),
        "response_model": response.get("model"),
        "finish_reason": choice.get("finish_reason"),
        "usage": usage_payload,
        "latency_seconds": round(latency_seconds, 3) if isinstance(latency_seconds, (int, float)) else None,
        "response_text_chars": len(response_content["response_text"]),
        "response_text_raw_chars": len(response_content["response_text_raw"]),
        "provider_reasoning_chars": len(response_content["provider_reasoning_text"]),
        "candidate_chars": len(candidate_text),
        "candidate_sha256": stable_digest(candidate_text),
        "status": status,
        "failure_mode": failure_mode,
        # Treat the first non-empty candidate as a change (previously was None, which
        # broke candidate_change_count analytics — every successful run showed 0).
        "candidate_changed_from_previous": (
            bool(candidate_text.strip())
            if previous_attempt is None
            else candidate_text != previous_candidate
        ),
        "failure_mode_changed_from_previous": (
            None if previous_attempt is None else failure_mode != previous_trace.get("failure_mode")
        ),
    }


def build_attempt_record(
    *,
    attempt_index: int,
    mode: str,
    messages: list[dict[str, Any]],
    response: dict[str, Any],
    candidate_text: str,
    evaluation: dict[str, Any] | None,
    previous_attempt: dict[str, Any] | None,
    latency_seconds: float | None,
) -> dict[str, Any]:
    response_content = extract_response_content(response)
    return {
        "attempt": attempt_index,
        "mode": mode,
        "messages": list(messages),
        "response": response,
        "response_text": response_content["response_text"],
        "response_text_raw": response_content["response_text_raw"],
        "provider_reasoning_text": response_content["provider_reasoning_text"],
        "candidate_file_contents": candidate_text,
        "evaluation": evaluation or {},
        "trace": build_attempt_trace(
            messages=list(messages),
            response=response,
            response_content=response_content,
            candidate_text=candidate_text,
            evaluation=evaluation,
            previous_attempt=previous_attempt,
            latency_seconds=latency_seconds,
        ),
    }


def refresh_attempt_record(
    attempt: dict[str, Any],
    *,
    candidate_text: str,
    evaluation: dict[str, Any],
    previous_attempt: dict[str, Any] | None,
    latency_seconds: float | None = None,
) -> None:
    attempt["candidate_file_contents"] = candidate_text
    attempt["evaluation"] = evaluation
    prior_trace = attempt.get("trace")
    attempt["trace"] = build_attempt_trace(
        messages=list(attempt.get("messages", [])),
        response=attempt.get("response", {}) if isinstance(attempt.get("response"), dict) else {},
        response_content={
            "response_text": str(attempt.get("response_text", "")),
            "response_text_raw": str(attempt.get("response_text_raw", "")),
            "provider_reasoning_text": str(attempt.get("provider_reasoning_text", "")),
        },
        candidate_text=candidate_text,
        evaluation=evaluation,
        previous_attempt=previous_attempt,
        latency_seconds=(
            latency_seconds
            if latency_seconds is not None
            else prior_trace.get("latency_seconds")
            if isinstance(prior_trace, dict)
            else None
        ),
    )


def build_run_analysis(
    *,
    attempts: list[dict[str, Any]],
    evaluation: dict[str, Any],
    tool_calls_used: int,
) -> dict[str, Any]:
    reasoning_attempts = 0
    candidate_change_count = 0
    failure_mode_change_count = 0
    distinct_candidate_hashes: set[str] = set()
    previous_candidate = ""
    for attempt in attempts:
        trace = attempt.get("trace", {}) or {}
        if isinstance(trace, dict):
            if int(trace.get("provider_reasoning_chars") or 0) > 0:
                reasoning_attempts += 1
            if trace.get("candidate_changed_from_previous") is True:
                candidate_change_count += 1
            if trace.get("failure_mode_changed_from_previous") is True:
                failure_mode_change_count += 1
            candidate_hash = trace.get("candidate_sha256")
            if isinstance(candidate_hash, str) and candidate_hash and int(trace.get("candidate_chars") or 0) > 0:
                distinct_candidate_hashes.add(candidate_hash)
        # Fallback for interactive-mode attempts that do not populate `trace`:
        # derive candidate changes/hashes directly from candidate_file_contents.
        # Count every transition (incl. reverts like A -> B -> A), and record
        # each distinct hash separately. Skip this block entirely when `trace`
        # is already populated, so non-interactive traces are not redundantly
        # re-hashed (which would be harmless while digests match but fragile
        # if the two derivation paths ever diverge).
        trace_has_hash = isinstance(trace, dict) and bool(trace.get("candidate_sha256"))
        if not trace_has_hash:
            candidate_text = str(attempt.get("candidate_file_contents", ""))
            if candidate_text.strip():
                candidate_hash = stable_digest(candidate_text)
                distinct_candidate_hashes.add(candidate_hash)
                if candidate_text != previous_candidate:
                    candidate_change_count += 1
                previous_candidate = candidate_text
    return {
        "attempt_count": len(attempts),
        "tool_calls_used": tool_calls_used,
        "reasoning_attempt_count": reasoning_attempts,
        "candidate_change_count": candidate_change_count,
        "distinct_candidate_count": len(distinct_candidate_hashes),
        "failure_mode_change_count": failure_mode_change_count,
        "final_failure_mode": evaluation.get("failure_mode"),
        "final_status": evaluation.get("status"),
    }


def build_finalization_messages(
    base_messages: list[dict[str, Any]],
    response: dict[str, Any],
    *,
    attempt_index: int,
    max_attempts: int,
) -> list[dict[str, Any]]:
    reasoning = reasoning_excerpt(response)
    prompt = (
        f"Your previous reply did not include a final Lean file (attempt {attempt_index} of {max_attempts}).\n"
        "Stop reasoning and return the complete contents of the editable Lean proof file now.\n"
        "Return Lean code only, with no markdown fences or extra explanation.\n"
    )
    if reasoning:
        prompt += f"\nPrevious internal draft excerpt:\n{reasoning}\n"
    return [
        *base_messages,
        {"role": "user", "content": prompt},
    ]


RETRY_STATUS_CODES = frozenset({408, 409, 425, 429, 500, 502, 503, 504})
MAX_CHAT_COMPLETION_RETRIES = 6


def _parse_retry_after(value: str | None) -> float | None:
    """Parse an HTTP `Retry-After` header.

    Accepts both forms permitted by RFC 7231:
    - delta-seconds (e.g. "120")
    - HTTP-date (e.g. "Wed, 21 Oct 2015 07:28:00 GMT")

    Returns the number of seconds to wait, or None if the value cannot be
    parsed. A date in the past is clamped to 0.
    """
    if not value:
        return None
    value = value.strip()
    if not value:
        return None
    try:
        return max(0.0, float(value))
    except ValueError:
        pass
    try:
        from email.utils import parsedate_to_datetime
        import datetime as _dt

        parsed = parsedate_to_datetime(value)
        if parsed is None:
            return None
        if parsed.tzinfo is None:
            parsed = parsed.replace(tzinfo=_dt.timezone.utc)
        delta = (parsed - _dt.datetime.now(_dt.timezone.utc)).total_seconds()
        return max(0.0, delta)
    except (TypeError, ValueError):
        return None


def _backoff_delay(attempt: int, retry_after: float | None) -> float:
    if retry_after is not None:
        # Honour the provider-requested wait. Clamp only at a safety ceiling
        # (10 minutes) so a pathological header cannot stall the run
        # indefinitely; the previous 60s clamp was too aggressive and caused
        # retries to fire while the rate limit was still in force. Add a
        # small additive jitter (up to 1s) so concurrent workers hitting the
        # same Retry-After do not thunder back in lockstep.
        clamped = min(retry_after, 600.0)
        return clamped + random.random()
    # Exponential backoff with jitter, capped at 30s.
    base = min(30.0, 2.0 ** attempt)
    return base * (0.5 + random.random() * 0.5)


def _post_chat_completion(
    config: ResolvedAgentConfig,
    payload: dict[str, Any],
    model: str,
) -> dict[str, Any]:
    """POST one chat completion request with retries on transient failures.

    Retries on HTTP 408/409/425/429/500/502/503/504 and URL-level errors (timeouts)
    using exponential backoff with jitter, respecting Retry-After when present.
    """
    url = f"{config.base_url}{config.chat_completions_path}"
    body_payload = dict(payload)
    body_payload["model"] = model
    req_body = json.dumps(body_payload).encode("utf-8")
    headers = {
        "Authorization": f"Bearer {config.api_key}",
        "Content-Type": "application/json",
        "User-Agent": "verity-benchmark/0.1",
        **config.headers,
    }
    last_error: str | None = None
    for attempt in range(MAX_CHAT_COMPLETION_RETRIES):
        req = request.Request(url, data=req_body, headers=headers, method="POST")
        try:
            with request.urlopen(req, timeout=config.request_timeout_seconds) as response:
                body = response.read().decode("utf-8")
            try:
                return json.loads(body)
            except json.JSONDecodeError as exc:
                # Non-JSON 200 responses (HTML error pages from a CDN or load
                # balancer mid-deploy are common) must be treated as transient
                # failures so the retry loop and fallback-model chain can take
                # over, not as SystemExit which aborts the whole task.
                last_error = f"non-JSON response: {body[:200]!r}"
                if attempt == MAX_CHAT_COMPLETION_RETRIES - 1:
                    raise _ChatCompletionError(status=0, detail=last_error, model=model) from exc
                time.sleep(_backoff_delay(attempt, None))
                continue
        except error.HTTPError as exc:
            detail = exc.read().decode("utf-8", errors="replace")
            last_error = f"HTTP {exc.code}: {detail[:400]}"
            if exc.code not in RETRY_STATUS_CODES or attempt == MAX_CHAT_COMPLETION_RETRIES - 1:
                raise _ChatCompletionError(status=exc.code, detail=detail, model=model) from exc
            retry_after = _parse_retry_after(exc.headers.get("Retry-After") if exc.headers else None)
            time.sleep(_backoff_delay(attempt, retry_after))
            continue
        except error.URLError as exc:
            last_error = f"URL error: {exc}"
            if attempt == MAX_CHAT_COMPLETION_RETRIES - 1:
                raise _ChatCompletionError(status=0, detail=str(exc), model=model) from exc
            time.sleep(_backoff_delay(attempt, None))
            continue
        except TimeoutError as exc:
            # Python 3.10+: socket.timeout during SSL read surfaces as
            # TimeoutError rather than urllib.error.URLError. Treat it as
            # a transient network failure and retry with backoff.
            last_error = f"Read timeout: {exc}"
            if attempt == MAX_CHAT_COMPLETION_RETRIES - 1:
                raise _ChatCompletionError(status=0, detail=str(exc), model=model) from exc
            time.sleep(_backoff_delay(attempt, None))
            continue
    raise _ChatCompletionError(status=0, detail=last_error or "unknown", model=model)


class _ChatCompletionError(Exception):
    def __init__(self, *, status: int, detail: str, model: str) -> None:
        super().__init__(f"chat completion failed with status {status}: {detail[:400]}")
        self.status = status
        self.detail = detail
        self.model = model


def send_chat_completion(
    config: ResolvedAgentConfig,
    messages: list[dict[str, Any]],
    *,
    tools: list[dict[str, Any]] | None = None,
    max_tokens_override: int | None = None,
    temperature_override: float | None = None,
) -> dict[str, Any]:
    payload: dict[str, Any] = {"messages": messages}
    if tools:
        payload["tools"] = tools
        payload["tool_choice"] = "auto"
    # Apply extra_body first so computed overrides below win over any
    # temperature/max_tokens keys the user may have stashed in extra_body.
    payload.update(config.extra_body)
    payload["temperature"] = (
        config.temperature if temperature_override is None else temperature_override
    )
    payload["max_tokens"] = max_tokens_override or config.max_completion_tokens
    # Allow configuring a fallback chain via extra_body.fallback_models (list of model ids).
    # This lets a rate-limited primary (e.g. "opus") degrade gracefully instead of failing the run.
    # Normalize fallback_models: accept a list of strings (standard) or a
    # single string (common operator shorthand). A bare string must not be
    # iterated character-by-character, which would produce single-letter
    # "models" like "g", "p", "t".
    raw_fallback = config.extra_body.get("fallback_models") or []
    if isinstance(raw_fallback, str):
        raw_fallback = [raw_fallback]
    elif not isinstance(raw_fallback, (list, tuple)):
        # extra_body is schema-free operator input; a truthy non-iterable
        # (bool, int, dict, ...) must not blow up the iteration below.
        raw_fallback = []
    # Trim each entry: the guard below already gates on `item.strip()`
    # truthiness, but store the stripped form so leading/trailing whitespace
    # in a config like `" gpt-4o-mini"` does not survive into the outbound
    # request body (providers reject model ids they do not recognize, so an
    # otherwise-valid fallback would fail with a 404 model-not-found).
    fallback_models = [
        item.strip()
        for item in raw_fallback
        if isinstance(item, str) and item.strip()
    ]
    payload.pop("fallback_models", None)
    # Benchmark-only knob consumed in execute_interactive_agent_task; strip
    # it so providers don't reject the request with an unknown-field error.
    payload.pop("length_retry_token_cap", None)
    models_to_try: list[str] = [config.model, *fallback_models]
    last_exc: _ChatCompletionError | None = None
    # Status codes that are fatal for the whole chain — every model would
    # get the same error, so no point in continuing to try fallbacks.
    # 401 (bad/expired API key) and 403 (forbidden) are auth-level and
    # apply account-wide; retrying a different model would just produce
    # the same error. Every other non-transient 4xx is model-specific
    # (404 model-not-found, 400 model-rejected-payload, 422 bad params
    # for a model, 429 model-specific quota is in RETRY_STATUS_CODES
    # already) and should fall through to the next fallback model.
    _FATAL_AUTH_STATUSES = {401, 403}
    for model in models_to_try:
        try:
            return _post_chat_completion(config, payload, model)
        except _ChatCompletionError as exc:
            last_exc = exc
            # Fall back on the same transient statuses `_post_chat_completion`
            # retries internally (plus status 0 for network/read errors), so a
            # primary that keeps returning 408/409/425/429/5xx gets routed to
            # the configured fallback chain instead of hard-failing. For a
            # non-transient, non-auth error (e.g. 404 model-not-found on a
            # typo'd fallback entry) keep trying later models — one bad
            # fallback should not prevent subsequent configured backups.
            if exc.status in _FATAL_AUTH_STATUSES:
                break
            continue
    if last_exc is None:
        raise SystemExit("chat completion request failed with no attempts")
    raise SystemExit(
        f"chat completion request failed with HTTP {last_exc.status} (model={last_exc.model}): {last_exc.detail[:400]}"
    )


def list_models(config: ResolvedAgentConfig) -> dict[str, Any]:
    url = f"{config.base_url}{config.models_path}"
    headers = {
        "User-Agent": "verity-benchmark/0.1",
        **config.headers,
    }
    if config.api_key:
        headers["Authorization"] = f"Bearer {config.api_key}"
    req = request.Request(url, headers=headers, method="GET")
    try:
        with request.urlopen(req, timeout=config.request_timeout_seconds) as response:
            body = response.read().decode("utf-8")
    except error.HTTPError as exc:
        detail = exc.read().decode("utf-8", errors="replace")
        raise SystemExit(f"model probe failed with HTTP {exc.code}: {detail}") from exc
    except error.URLError as exc:
        raise SystemExit(f"model probe failed: {exc}") from exc
    try:
        return json.loads(body)
    except json.JSONDecodeError as exc:
        raise SystemExit(f"model probe returned non-JSON response: {body[:400]!r}") from exc


def extract_model_ids(models_payload: dict[str, Any]) -> list[str]:
    data = models_payload.get("data")
    if not isinstance(data, list):
        return []
    model_ids: list[str] = []
    for item in data:
        if isinstance(item, dict):
                model_id = item.get("id")
                if isinstance(model_id, str):
                    model_ids.append(model_id)
    return model_ids


def ensure_configured_model_available(config: ResolvedAgentConfig, model_ids: list[str]) -> None:
    if not model_ids:
        raise SystemExit(
            "model probe could not confirm configured model "
            f"{config.model!r}: {config.models_path} returned no parseable model ids"
        )
    if config.model not in model_ids:
        raise SystemExit(
            "model probe could not confirm configured model "
            f"{config.model!r}: not present in {config.models_path} response"
        )


def extract_text(response: dict[str, Any]) -> str:
    return extract_response_content(response)["response_text"]


def extract_tool_calls(response: dict[str, Any]) -> list[dict[str, Any]]:
    message = response_message(response)
    tool_calls = message.get("tool_calls")
    if isinstance(tool_calls, list):
        return [item for item in tool_calls if isinstance(item, dict)]
    return []


def _looks_like_lean(text: str) -> bool:
    """Check if text looks like Lean code rather than natural-language explanation."""
    # Use word-boundary-aware patterns to avoid matching English words like "simple", "exactly"
    lean_keywords = ("import ", "theorem ", "def ", "lemma ", "namespace ", "open ", ":= by", "simp [", "simp\n", "exact ")
    return any(kw in text for kw in lean_keywords)


def extract_candidate_file(response_text: str) -> str:
    text = response_text.strip()
    fenced = re.findall(r"```(?:lean)?\s*\n(.*?)```", text, flags=re.DOTALL)
    if len(fenced) == 1:
        return fenced[0].strip() + "\n"
    return text + ("\n" if text and not text.endswith("\n") else "")


def evaluate_candidate_submission(task: dict[str, Any], candidate_text: str) -> dict[str, Any]:
    try:
        runtime = TaskProofRuntime(task)
    except ValueError as exc:
        return {
            "status": "failed",
            "failure_mode": "editable_file_contract_invalid",
            "details": str(exc),
        }
    return runtime.evaluate_candidate(candidate_text)


def parse_tool_arguments(raw_arguments: object) -> dict[str, Any]:
    if isinstance(raw_arguments, dict):
        return raw_arguments
    if not isinstance(raw_arguments, str):
        return {}
    text = raw_arguments.strip()
    if not text:
        return {}
    try:
        parsed = json.loads(text)
    except json.JSONDecodeError:
        return {}
    return parsed if isinstance(parsed, dict) else {}


def build_task_payload(task: dict[str, Any]) -> dict[str, Any]:
    return {
        "task_ref": task["task_ref"],
        "task_id": task["task_id"],
        "case_id": task["case_id"],
        "track": task["track"],
        "property_class": task["property_class"],
        "category": task["category"],
        "difficulty": task["difficulty"],
        "theorem_name": task["theorem_name"],
        "proof_family": task["proof_family"],
        "implementation_files": task["implementation_files"],
        "specification_files": task["specification_files"],
        "editable_files": task["editable_files"],
        "targets": task["targets"],
        "evaluation": task["evaluation"],
        "readiness": task["readiness"],
        "manifest_path": task["manifest_path"],
        "case_manifest_path": task["case_manifest_path"],
    }


def load_public_task_files(task: dict[str, Any]) -> list[dict[str, str]]:
    rel_paths = [
        *[str(item) for item in task["implementation_files"]],
        *[str(item) for item in task["specification_files"]],
        *[str(item) for item in task["editable_files"]],
    ]
    files: list[dict[str, str]] = []
    for rel_path in rel_paths:
        path = ROOT / rel_path
        files.append(
            {
                "path": rel_path,
                "content": path.read_text(encoding="utf-8") if path.is_file() else "",
            }
        )
    return files


def build_command_adapter_request(
    config: ResolvedAgentConfig,
    task: dict[str, Any],
    messages: list[dict[str, Any]],
    *,
    kind: str,
) -> dict[str, Any]:
    return {
        "protocol_version": ADAPTER_PROTOCOL_VERSION,
        "kind": kind,
        "mode": config.mode,
        "task_ref": task["task_ref"],
        "task": build_task_payload(task),
        "public_files": load_public_task_files(task),
        "editable_file": task["editable_files"][0] if task["editable_files"] else None,
        "input": {
            "messages": messages,
            "system_prompt": messages[0]["content"] if messages else "",
            "user_prompt": messages[1]["content"] if len(messages) > 1 else "",
        },
        "agent": {
            "agent_id": config.agent_id,
            "mode": config.mode,
            "track": config.track,
            "run_slug": config.run_slug,
            "adapter": config.adapter,
            "config_path": config.config_path,
            "base_url": config.base_url or None,
            "model": config.model or None,
            "api_key": config.api_key or None,
            "chat_completions_path": config.chat_completions_path or None,
            "models_path": config.models_path or None,
            "temperature": config.temperature,
            "max_completion_tokens": config.max_completion_tokens,
            "max_attempts": config.max_attempts,
            "max_tool_calls": config.max_tool_calls,
            "headers": config.headers,
            "extra_body": config.extra_body,
            "request_timeout_seconds": config.request_timeout_seconds,
            "command": config.command,
        },
    }


def invoke_command_adapter(config: ResolvedAgentConfig, payload: dict[str, Any]) -> dict[str, Any]:
    if not config.command:
        raise SystemExit("command adapter requires a non-empty command")
    try:
        completed = subprocess.run(
            config.command,
            input=json.dumps(payload),
            capture_output=True,
            text=True,
            timeout=config.request_timeout_seconds,
            check=False,
            cwd=ROOT,
        )
    except OSError as exc:
        raise SystemExit(f"command adapter failed to start: {exc}") from exc
    except subprocess.TimeoutExpired as exc:
        raise SystemExit(
            f"command adapter timed out after {config.request_timeout_seconds} seconds: {exc}"
        ) from exc

    if completed.returncode != 0:
        detail = completed.stderr.strip() or completed.stdout.strip() or f"exit code {completed.returncode}"
        raise SystemExit(f"command adapter failed: {detail}")
    try:
        response = json.loads(completed.stdout)
    except json.JSONDecodeError as exc:
        raise SystemExit(f"command adapter returned invalid JSON: {exc}") from exc
    if not isinstance(response, dict):
        raise SystemExit("command adapter response must be a JSON object")
    if response.get("protocol_version") != ADAPTER_PROTOCOL_VERSION:
        raise SystemExit(
            "command adapter protocol version mismatch: "
            f"expected {ADAPTER_PROTOCOL_VERSION}, got {response.get('protocol_version')!r}"
        )
    return response


def extract_command_candidate(response: dict[str, Any]) -> tuple[str, str]:
    response_text_raw = response.get("response_text_raw")
    response_text = response.get("response_text")
    candidate = response.get("candidate_file_contents")
    if isinstance(candidate, str) and candidate.strip():
        if isinstance(response_text, str):
            return response_text, candidate
        if isinstance(response_text_raw, str):
            return response_text_raw, candidate
        return candidate, candidate

    if isinstance(response_text, str):
        return response_text, extract_candidate_file(response_text)
    if isinstance(response_text_raw, str):
        return response_text_raw, extract_candidate_file(response_text_raw)
    return "", ""


def legacy_result_path(task_ref: str) -> Path:
    return AGENT_RESULTS_DIR / f"{task_ref.replace('/', '__')}.json"


def canonical_result_path(task_ref: str, config: ResolvedAgentConfig) -> Path:
    return AGENT_RESULTS_DIR / config.track / config.run_slug / f"{task_ref.replace('/', '__')}.json"


def canonical_summary_path(config: ResolvedAgentConfig) -> Path:
    return ROOT / "results" / "agent_summaries" / config.track / f"{config.run_slug}.json"


def scoped_summary_path(config: ResolvedAgentConfig, scope: str) -> Path:
    if scope.startswith("suite:"):
        return canonical_summary_path(config)
    slug = slugify(scope.replace(":", "-").replace("/", "-"))
    return ROOT / "results" / "agent_summaries" / config.track / config.run_slug / f"{slug}.json"


def uses_legacy_aliases(config: ResolvedAgentConfig) -> bool:
    return config.track == "reference" and config.config_path == config_label(DEFAULT_AGENT_CONFIG_PATH)


def write_result(task_ref: str, config: ResolvedAgentConfig, payload: dict[str, Any]) -> Path:
    result_path = canonical_result_path(task_ref, config)
    result_path.parent.mkdir(parents=True, exist_ok=True)
    result_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    if uses_legacy_aliases(config):
        legacy_path = legacy_result_path(task_ref)
        legacy_path.parent.mkdir(parents=True, exist_ok=True)
        legacy_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    return result_path


def build_result(
    task_ref: str,
    config: ResolvedAgentConfig,
    task: dict[str, Any],
    messages: list[dict[str, Any]],
    *,
    dry_run: bool,
    evaluation: dict[str, Any] | None = None,
    elapsed_seconds: float | None = None,
) -> dict[str, Any]:
    payload = {
        "schema_version": 1,
        "task_ref": task_ref,
        "task_id": task["task_id"],
        "case_id": task["case_id"],
        "timestamp": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "dry_run": dry_run,
        "status": "dry_run" if dry_run else str((evaluation or {}).get("status", "failed")),
        "theorem_name": task["theorem_name"],
        "proof_family": task["proof_family"],
        "implementation_files": task["implementation_files"],
        "specification_files": task["specification_files"],
        "editable_files": task["editable_files"],
        "agent": {
            "profile": config.profile,
            "agent_id": config.agent_id,
            "mode": config.mode,
            "track": config.track,
            "run_slug": config.run_slug,
            "adapter": config.adapter,
            "config_path": config.config_path,
            "base_url": config.base_url,
            "base_url_env": config.base_url_env,
            "model": config.model,
            "model_env": config.model_env,
            "api_key_env": config.api_key_env,
            "chat_completions_path": config.chat_completions_path,
            "models_path": config.models_path,
            "system_prompt_files": config.system_prompt_files,
            "temperature": config.temperature,
            "max_completion_tokens": config.max_completion_tokens,
            "max_attempts": config.max_attempts,
            "max_tool_calls": config.max_tool_calls,
            "request_timeout_seconds": config.request_timeout_seconds,
            "headers": redact_headers(config.headers),
            "header_envs": config.header_envs,
            "env_contract": config.env_contract,
            "extra_body": config.extra_body,
            "command": config.command,
        },
        "messages": messages,
    }
    if evaluation is not None:
        payload["evaluation"] = evaluation
    if elapsed_seconds is not None:
        payload["elapsed_seconds"] = round(elapsed_seconds, 3)
    return payload


def validate_result_payload(payload: dict[str, Any], label: str) -> None:
    schema = load_json(RUN_SCHEMA_PATH)
    errors = validate(payload, schema, label)
    if errors:
        raise SystemExit("\n".join(errors))


def resolve_task(task_ref: str) -> dict[str, Any]:
    return load_task_record(resolve_task_manifest(task_ref))


def validate_command(config_path: Path) -> int:
    resolve_config(config_path, require_secrets=False)
    print(config_label(config_path))
    return 0


def env_contract(config: dict[str, Any]) -> dict[str, list[str]]:
    required: list[str] = []
    optional: list[str] = []

    for field in ("base_url", "model", "api_key"):
        env_name = normalize_string(config.get(f"{field}_env"))
        if not env_name:
            continue
        if normalize_string(config.get(field)):
            optional.append(env_name)
        else:
            required.append(env_name)

    raw_header_envs = config.get("header_envs", {})
    if isinstance(raw_header_envs, dict):
        for env_name in raw_header_envs.values():
            normalized = normalize_string(env_name)
            if normalized:
                optional.append(normalized)

    return {
        "required": sorted(set(required)),
        "optional": sorted(set(optional)),
    }


def field_source(config: dict[str, Any], field: str) -> str:
    if normalize_string(config.get(field)):
        return "config"
    if normalize_string(config.get(f"{field}_env")):
        return "env"
    return "missing"


def describe_command(config_path: Path) -> int:
    config_data = load_config(config_path)
    config = resolve_config(config_path, require_secrets=False)
    print(
        json.dumps(
            {
                "adapter": config.adapter,
                "agent_id": config.agent_id,
                "mode": config.mode,
                "track": config.track,
                "run_slug": config.run_slug,
                "config_path": config.config_path,
                "base_url": config.base_url or None,
                "base_url_env": config_data.get("base_url_env"),
                "base_url_source": field_source(config_data, "base_url"),
                "model": config.model or None,
                "model_env": config_data.get("model_env"),
                "model_source": field_source(config_data, "model"),
                "api_key_source": field_source(config_data, "api_key"),
                "api_key_env": config_data.get("api_key_env"),
                "chat_completions_path": config.chat_completions_path,
                "models_path": config.models_path,
                "system_prompt_files": config.system_prompt_files,
                "temperature": config.temperature,
                "max_completion_tokens": config.max_completion_tokens,
                "max_attempts": config.max_attempts,
                "max_tool_calls": config.max_tool_calls,
                "headers": redact_headers(config.headers),
                "header_envs": config.header_envs,
                "env_contract": config.env_contract,
                "extra_body": config.extra_body,
                "request_timeout_seconds": config.request_timeout_seconds,
                "command": config.command,
                "api_key_present": bool(config.api_key),
            },
            indent=2,
        )
    )
    return 0


def prompt_command(config_path: Path, task_ref: str) -> int:
    config = resolve_config(config_path, require_secrets=False)
    task = resolve_task(task_ref)
    payload = {
        "task_ref": task_ref,
        "messages": build_messages(config, task),
    }
    print(json.dumps(payload, indent=2))
    return 0


def evaluate_candidate_command(task_ref: str, candidate_path: Path) -> int:
    task = resolve_task(task_ref)
    evaluation = evaluate_candidate_submission(task, candidate_path.read_text(encoding="utf-8"))
    print(json.dumps(evaluation, indent=2))
    return 0 if evaluation["status"] == "passed" else 1


def probe_command(config_path: Path, ensure_model: bool) -> int:
    config = resolve_config(config_path, require_secrets=True)
    if config.adapter == "openai_compatible":
        models_payload = list_models(config)
        model_ids = extract_model_ids(models_payload)
        configured_model_available = config.model in model_ids
        payload = {
            "adapter": config.adapter,
            "mode": config.mode,
            "base_url": config.base_url,
            "models_path": config.models_path,
            "configured_model": config.model,
            "model_count": len(model_ids),
            "models": model_ids,
            "configured_model_available": configured_model_available,
        }
        print(json.dumps(payload, indent=2))
        if ensure_model:
            ensure_configured_model_available(config, model_ids)
        return 0

    probe_task = {
        "task_ref": "__probe__",
        "task_id": "__probe__",
        "case_id": "__probe__",
        "track": config.track,
        "property_class": "",
        "category": "",
        "difficulty": "",
        "theorem_name": "",
        "proof_family": "",
        "implementation_files": [],
        "specification_files": [],
        "editable_files": [],
        "targets": {},
        "evaluation": {},
        "readiness": {},
        "manifest_path": "",
        "case_manifest_path": "",
    }
    payload = invoke_command_adapter(
        config,
        build_command_adapter_request(config, probe_task, [], kind="probe"),
    )
    print(json.dumps(payload, indent=2))
    if ensure_model and payload.get("configured_model_available") is not True:
        raise SystemExit(
            "command adapter probe could not confirm configured model "
            f"{config.model!r}"
        )
    return 0


def execute_strict_agent_task(
    config: ResolvedAgentConfig,
    task: dict[str, Any],
    messages: list[dict[str, Any]],
) -> tuple[dict[str, Any], str, dict[str, Any], list[dict[str, Any]]]:
    attempt_messages = list(messages)
    response: dict[str, Any] = {}
    response_text = ""
    candidate_text = ""
    evaluation: dict[str, Any] = {
        "status": "failed",
        "failure_mode": "agent_not_run",
        "details": "agent invocation did not start",
    }
    attempts: list[dict[str, Any]] = []

    for attempt_index in range(1, config.max_attempts + 1):
        attempt_start = time.perf_counter()
        response = send_chat_completion(config, attempt_messages)
        attempt_latency = time.perf_counter() - attempt_start
        response_text = extract_text(response)
        candidate_text = extract_candidate_file(response_text)
        evaluation = evaluate_candidate_submission(task, candidate_text)
        previous_attempt = latest_candidate_attempt(attempts)
        attempts.append(
            build_attempt_record(
                attempt_index=attempt_index,
                mode="strict",
                messages=attempt_messages,
                response=response,
                candidate_text=candidate_text,
                evaluation=evaluation,
                previous_attempt=previous_attempt,
                latency_seconds=attempt_latency,
            )
        )
        if evaluation.get("status") == "passed":
            break
        if attempt_index >= config.max_attempts:
            break
        # Build repair messages for the next attempt
        attempt_messages = build_repair_messages(
            messages,
            candidate_text,
            evaluation,
            attempt_index=attempt_index,
            max_attempts=config.max_attempts,
        )
    return response, response_text, evaluation, attempts


# Set of failure_modes produced by write_editable_proof's preflight checks
# (before Lean ever runs). These are deterministic formatting/import/semantic
# rejects whose human-readable `details` classify as `other`, collapsing
# distinct failure modes into the same temperature-history bucket. Surface
# each preflight mode as its own history class so the repeated-class bump
# can fire correctly (and only) when the *same* preflight keeps recurring.
# Authoritative preflight failure-mode set lives in
# harness/interactive_runtime.py::_PREFLIGHT_FAILURE_MODES and is re-exported
# here so `_failure_history_class` can't drift out of sync with the runtime
# that actually produces these modes. An earlier duplicate definition lost
# `empty_response` during a refactor; importing removes that whole class of
# bug entirely.
_PREFLIGHT_FAILURE_MODES = _RUNTIME_PREFLIGHT_FAILURE_MODES

# Canonical evaluation-contract keys, matching the top-level `evaluation`
# object in schemas/agent-run.schema.json (additionalProperties=false over
# {status, failure_mode, details, command, candidate_workspace}). Whenever
# the runtime returns a dict that will ultimately become a top-level or
# per-attempt `evaluation` record, filter it through these keys first so
# write-time metadata (path, bytes, lines, warnings, write_status,
# repair_hints) and tool-specific extras (e.g. try_tactic_at_hole's
# `tactic`) don't leak through and break JSON schema validation.
_EVAL_KEYS = ("status", "failure_mode", "details", "command", "candidate_workspace")


def _failure_history_class(result: dict) -> str:
    """Return the failure-class label to append to temperature history.

    Empty string means "do not append" (no failure, or infra noise we filter).
    Preflight failure_modes are surfaced with a `pf:` prefix so e.g.
    `pf:placeholder_detected` does not collide with Lean-check classes like
    `type_error`, while still allowing the repeated-class same-value
    comparison to trigger when the same preflight recurs.
    """
    if not isinstance(result, dict) or result.get("status") != "failed":
        return ""
    failure_mode = result.get("failure_mode") or ""
    if failure_mode in _PREFLIGHT_FAILURE_MODES:
        return f"pf:{failure_mode}"
    # Lean-check failure (or any unclassified failure): derive from details.
    fc = result.get("failure_class") or classify_failure(str(result.get("details", "")))
    fc = str(fc)
    # Environment errors are infra noise that would break the sliding-window
    # same-class check (["type_error","environment_error","type_error"] looks
    # like a class change). Filter out.
    if fc == "environment_error":
        return ""
    return fc


def _append_failure_class(
    history: list,
    fc_entry: str,
    candidate_text: str,
    last_key: list,
) -> None:
    """Append `fc_entry` to `history` unless it's empty or a same-candidate duplicate.

    Dedupe guards against double-counting when a single turn fires both
    `write_editable_proof` (which now runs the Lean check internally) and a
    follow-up `run_lean_check` against the same failed candidate — that
    would push two identical entries for one actual failure and prematurely
    trigger the same-class temperature bump.
    """
    if not fc_entry:
        return
    candidate_hash = hashlib.sha1(candidate_text.encode("utf-8", "replace")).hexdigest()[:16]
    key = (candidate_hash, fc_entry)
    if last_key and last_key[0] == key:
        return
    history.append(fc_entry)
    last_key[0] = key



def execute_interactive_agent_task(
    config: ResolvedAgentConfig,
    task: dict[str, Any],
    messages: list[dict[str, Any]],
) -> tuple[dict[str, Any], str, str, dict[str, Any], list[dict[str, Any]], int]:
    runtime = TaskProofRuntime(task)
    base_messages: list[dict[str, Any]] = list(messages)
    transcript: list[dict[str, Any]] = list(messages)
    attempts: list[dict[str, Any]] = []
    response: dict[str, Any] = {}
    response_text = ""
    tool_calls_used = 0
    proof_attempts = 0
    consecutive_search_turns = 0
    consecutive_length_stops = 0
    max_total_turns = config.max_attempts * 2  # hard cap to prevent infinite loops
    token_budget = config.max_completion_tokens
    # Ceiling for the length-retry silent bump. Read from config.extra_body so
    # operators can opt into larger bumps for providers that accept them, but
    # default to `max_completion_tokens` so models with a hard cap at that value
    # don't get HTTP 400 when the bump kicks in. Stripped from the request
    # payload in `send_chat_completion` so it never leaks to the provider.
    _cap_raw = config.extra_body.get("length_retry_token_cap", config.max_completion_tokens)
    try:
        length_retry_token_cap = int(_cap_raw)
    except (TypeError, ValueError):
        # Invalid operator-edited value (e.g. null, "12k", nested object).
        # Fall back silently rather than aborting the run.
        length_retry_token_cap = config.max_completion_tokens
    if length_retry_token_cap < config.max_completion_tokens:
        length_retry_token_cap = config.max_completion_tokens
    # Temperature schedule: escalate after repeated same-class failures to break out
    # of deterministic loops where temperature=0 reproduces byte-identical responses.
    current_temperature = config.temperature
    failure_class_history: list[str] = []
    # Dedupe key for `failure_class_history` appends: (candidate_hash, class).
    # When a model does write_editable_proof then run_lean_check in the same
    # turn against the same (failed) candidate, both tool calls produce the
    # same class entry for the same candidate. Without dedupe the history
    # gets two entries for one actual failure, and the repeated-class
    # temperature bump fires a turn too early.
    # Scope: reset at the top of each model turn (see loop below) so
    # cross-turn repeats on an unchanged candidate still register as genuine
    # failures for the repeated-class temperature escalation.
    _last_history_key: list = [None]  # mutable cell so helper can update
    # Track how many failures we have already applied the temperature-bump
    # schedule to, so we don't keep escalating temperature on every iteration
    # once the trigger condition is first met (it would otherwise run to the
    # cap within a few turns regardless of intervening search/write activity).
    temperature_schedule_applied_at = 0

    turn = 0
    while proof_attempts < config.max_attempts and turn < max_total_turns:
        turn += 1
        # Scope the failure-class dedupe to a single turn. The dedupe exists to
        # coalesce same-candidate same-class duplicates emitted within one
        # model turn (e.g. `write_editable_proof` + follow-up `run_lean_check`
        # on the same candidate); it must not silence genuine cross-turn
        # repeats where the candidate stays unchanged but the model tries
        # again. Resetting here bounds the dedupe window to the current turn.
        _last_history_key[0] = None
        # Adjust temperature once per new failure entry when the last two
        # proof attempts failed with the same class.
        if (
            len(failure_class_history) > temperature_schedule_applied_at
            and len(failure_class_history) >= 2
            and failure_class_history[-1] == failure_class_history[-2]
            and failure_class_history[-1] not in ("", "environment_error")
        ):
            # Escalate toward 0.7 to break deterministic loops, but never
            # DECREASE below the configured base temperature. A run with
            # `config.temperature = 1.0` should stay at 1.0 (or higher)
            # rather than dropping to 0.7 on the first stagnation trigger —
            # the cap exists only to stop unbounded growth, not to override
            # an operator who explicitly asked for a hotter sampler.
            escalated = max(current_temperature + 0.2, 0.2)
            current_temperature = max(min(0.7, escalated), config.temperature)
        temperature_schedule_applied_at = len(failure_class_history)
        response = send_chat_completion(
            config, transcript, tools=runtime.tool_specs(),
            max_tokens_override=token_budget if token_budget != config.max_completion_tokens else None,
            temperature_override=current_temperature if current_temperature != config.temperature else None,
        )
        response_text = extract_text(response)
        tool_calls = extract_tool_calls(response)

        # Detect finish_reason=length with no usable output (model hit token limit
        # during internal reasoning). Bump token budget and retry without counting
        # this as a proof attempt.
        finish_reason = ""
        choices = response.get("choices", [])
        if choices:
            finish_reason = choices[0].get("finish_reason", "")
        if finish_reason == "length" and not tool_calls and not response_text.strip():
            consecutive_length_stops += 1
            # Up to 3 silent budget bumps before nudging the model to simplify.
            # Cap bump at `config.max_completion_tokens` so we never exceed the
            # provider-enforced per-response limit (some models hard-cap at the
            # configured value and would return HTTP 400 on anything larger).
            if consecutive_length_stops <= 3:
                token_budget = min(int(token_budget * 1.5), length_retry_token_cap)
                continue
            # Subsequent length stops: inject a nudge to simplify and use tools
            transcript.append({"role": "assistant", "content": ""})
            transcript.append({
                "role": "user",
                "content": (
                    "Your response was cut off. Do not over-think. "
                    "Immediately call write_editable_proof with a simple proof attempt "
                    "(it runs the Lean check automatically). Keep the proof short."
                ),
            })
            # Reset budget back to configured value after persistent overruns
            token_budget = config.max_completion_tokens
            continue
        else:
            # Recovered from any length streak -- reset both the counter and
            # the (possibly-elevated) token budget so we don't leak state into
            # subsequent turns.
            consecutive_length_stops = 0
            token_budget = config.max_completion_tokens

        attempts.append(
            {
                "attempt": turn,
                "proof_attempt": proof_attempts + 1,
                "mode": "interactive",
                "messages": list(transcript),
                "response": response,
                "response_text": response_text,
                "tool_calls": tool_calls,
            }
        )
        attempts[-1]["tool_calls"] = tool_calls
        if not tool_calls:
            final_candidate = extract_candidate_file(response_text)
            # Only overwrite the stored proof if the response looks like Lean code,
            # not natural-language explanation.
            if final_candidate.strip() and _looks_like_lean(final_candidate):
                # `write_editable_proof` already runs the Lean check
                # internally (check=True default) and returns the merged
                # write-metadata + run_lean_check result. Reuse that dict
                # instead of calling `evaluate_current()` again — the
                # previous double-invocation cost a second `lake env lean`
                # per no-tool-calls attempt and pushed a spurious entry
                # onto `_check_history`, which could trigger premature
                # stagnation/temperature escalation.
                # NOTE: local name is `write_payload` (not `write_result`)
                # because `write_result` is a module-level function at
                # line ~1530 (`write_result(task_ref, config, payload)`),
                # and shadowing it with a local would silently break any
                # future code in this function that tried to call the
                # file-writer. The on-trace attempts record still exposes
                # this payload under the `"write_result"` key for
                # backward-compatible tooling.
                write_payload = runtime.write_editable_proof(final_candidate)
                proof_attempts += 1
                # `write_editable_proof` returns the full write payload
                # merged with `run_lean_check` output (path, bytes, lines,
                # warnings, write_status, repair_hints). These are not part
                # of the top-level `evaluation` schema (which is strict:
                # additionalProperties=false over {status, failure_mode,
                # details, command, candidate_workspace}). Returning the
                # raw dict upward — as was done before — made `build_result`
                # forward it to `validate_result_payload` and fail schema
                # validation with a SystemExit, aborting the entire run
                # every time the model produced Lean text without tool
                # calls (including successful proofs). Normalize here so
                # both the nested `attempts[-1]["evaluation"]` record and
                # the outward return have the contract shape, while
                # preserving the rich write-time payload under a separate
                # per-attempt key for debugging/analytics.
                evaluation = {
                    k: write_payload[k]
                    for k in _EVAL_KEYS
                    if k in write_payload
                }
                evaluation.setdefault("failure_mode", None)
                evaluation.setdefault("details", "")
                attempts[-1]["candidate_file_contents"] = runtime.current_proof_text
                attempts[-1]["evaluation"] = evaluation
                attempts[-1]["write_result"] = write_payload
                # Track model-driven failure classes for the temperature
                # schedule's sliding window. `_failure_history_class` maps
                # preflight modes (placeholder_detected, hidden_*_import,
                # theorem_statement_mismatch) to distinct `pf:<mode>` labels
                # so they don't all collapse into `other`, and filters out
                # infra-noise environment errors that would break
                # same-class detection.
                fc_entry = _failure_history_class(write_payload)
                _append_failure_class(
                    failure_class_history,
                    fc_entry,
                    runtime.current_proof_text,
                    _last_history_key,
                )
                if evaluation["status"] == "passed":
                    return response, response_text, runtime.current_proof_text, evaluation, attempts, tool_calls_used
                # Failed candidate without tool calls: feed error back
                failure_mode = evaluation.get("failure_mode", "")
                if failure_mode == "lean_check_failed":
                    details = str(evaluation.get("details", ""))[:MAX_ERROR_FEEDBACK_CHARS]
                    guidance = build_repair_guidance(details, failure_mode=failure_mode)
                    repair_msg = (
                        f"Your proof did not pass (attempt {proof_attempts} of {config.max_attempts}).\n"
                        f"Lean checker output:\n{details}\n"
                    )
                    if guidance:
                        repair_msg += f"\nRepair guidance:\n{guidance}\n"
                    repair_msg += "\nUse write_editable_proof to write a corrected proof (it runs the Lean check automatically; no separate run_lean_check needed)."
                    transcript.append({"role": "assistant", "content": response_text or ""})
                    transcript.append({"role": "user", "content": repair_msg})
                elif failure_mode in (
                    "placeholder_detected",
                    "theorem_statement_mismatch",
                    "hidden_proof_import_detected",
                    "hidden_case_import_detected",
                ):
                    # Preflight rejections (placeholder_detected,
                    # theorem_statement_mismatch, hidden_*_import_detected) are
                    # all recoverable by the model: the candidate file made it
                    # through the write path but was rejected before Lean saw
                    # it. Surface the rejection and give the model another
                    # turn to produce a clean candidate, instead of bailing
                    # out on the first hidden-import mistake.
                    extra_hint = ""
                    if failure_mode == "hidden_proof_import_detected":
                        extra_hint = (
                            "\nRemove any `import`, `open`, or `export` of a "
                            "`Benchmark.Cases.*.Proofs` module — those hold "
                            "held-out ground truth and are not available to "
                            "the model."
                        )
                    elif failure_mode == "hidden_case_import_detected":
                        extra_hint = (
                            "\nOnly the public specification / implementation "
                            "modules for this task may be imported. Drop any "
                            "other `Benchmark.Cases.*` imports."
                        )
                    retry_msg = (
                        f"Your response did not produce a valid proof candidate (proof attempt {proof_attempts} of {config.max_attempts}, "
                        f"failure: {failure_mode}).\n"
                        "Use the write_editable_proof tool to submit the complete editable Lean proof file "
                        "(it runs the Lean check automatically; no separate run_lean_check needed).\n"
                        "Do not explain or analyze. Use the tools directly." + extra_hint + "\n"
                    )
                    transcript.append({"role": "assistant", "content": response_text})
                    transcript.append({"role": "user", "content": retry_msg})
                else:
                    return response, response_text, runtime.current_proof_text, evaluation, attempts, tool_calls_used
            else:
                # Empty response or no valid candidate: nudge model to use tools
                nudge_msg = (
                    "You must use the write_editable_proof tool to submit your proof "
                    "(it runs the Lean check automatically). Do not respond with text only.\n"
                )
                transcript.append({"role": "assistant", "content": response_text or ""})
                transcript.append({"role": "user", "content": nudge_msg})
            continue

        transcript.append(
            {
                "role": "assistant",
                "content": response_text,
                "tool_calls": tool_calls,
            }
        )
        turn_had_proof_action = False
        for tool_call in tool_calls:
            if tool_calls_used >= config.max_tool_calls:
                evaluation = runtime.evaluate_current()
                if evaluation.get("failure_mode") == "empty_response":
                    evaluation = {
                        "status": "failed",
                        "failure_mode": "tool_budget_exhausted",
                        "details": f"interactive tool-call budget exhausted after {tool_calls_used} tool calls",
                    }
                attempts[-1]["budget_exhausted"] = True
                attempts[-1]["candidate_file_contents"] = runtime.current_proof_text
                attempts[-1]["evaluation"] = evaluation
                return response, response_text, runtime.current_proof_text, evaluation, attempts, tool_calls_used
            function_call = tool_call.get("function", {})
            tool_name = str(function_call.get("name", ""))
            arguments = parse_tool_arguments(function_call.get("arguments"))
            result = runtime.execute_tool(tool_name, arguments)
            tool_calls_used += 1
            if tool_name in ("write_editable_proof", "run_lean_check", "try_tactic_at_hole"):
                turn_had_proof_action = True
            transcript.append(
                {
                    "role": "tool",
                    "tool_call_id": str(tool_call.get("id", "")),
                    "content": tool_result_json(result),
                }
            )
            attempts[-1].setdefault("tool_results", []).append(
                {
                    "tool_call_id": str(tool_call.get("id", "")),
                    "name": tool_name,
                    "arguments": arguments,
                    "result": result,
                }
            )
            if tool_name in ("run_lean_check", "write_editable_proof") and result.get("status") == "failed":
                # Track any write/check failure (Lean-check *and* preflight
                # failures like placeholder_detected /
                # hidden_case_import_detected). Previously only
                # `failure_mode == "lean_check_failed"` was recorded, so a run
                # stuck on repeated preflight failures never tripped the
                # same-class temperature bump and stayed at deterministic
                # temperature until attempt exhaustion.
                fc_entry = _failure_history_class(result)
                _append_failure_class(
                    failure_class_history,
                    fc_entry,
                    runtime.current_proof_text,
                    _last_history_key,
                )
                # Persist candidate state even for failed proof-tool turns so
                # `build_run_analysis` can hash intermediate drafts for the
                # candidate_change_count / distinct_candidate_count analytics.
                # Without this, only the last (passed or budget-exhausted)
                # turn's candidate gets recorded and repeated unsuccessful
                # edits look like zero churn.
                attempts[-1]["candidate_file_contents"] = runtime.current_proof_text
                # Normalize to the evaluation schema (same _EVAL_KEYS filter as
                # the passed path below) so the nested per-attempt evaluation
                # records have a consistent shape across passed / failed /
                # budget-exhausted branches. The raw tool result carries
                # write-time metadata (path, bytes, lines, warnings,
                # repair_hints) that isn't part of the evaluation contract.
                _failed_eval = {
                    k: result[k]
                    for k in _EVAL_KEYS
                    if k in result
                }
                _failed_eval.setdefault("failure_mode", None)
                _failed_eval.setdefault("details", "")
                attempts[-1]["evaluation"] = _failed_eval
            elif tool_name in ("run_lean_check", "try_tactic_at_hole", "write_editable_proof") and result.get("status") == "passed":
                # Normalize to evaluation schema. `try_tactic_at_hole` returns
                # extra keys like `tactic` that must be stripped, otherwise the
                # final result fails schema validation (additionalProperties:
                # false) and the whole task aborts with no result file.
                evaluation = {k: result[k] for k in _EVAL_KEYS if k in result}
                evaluation.setdefault("failure_mode", None)
                evaluation.setdefault("details", "")
                attempts[-1]["candidate_file_contents"] = runtime.current_proof_text
                attempts[-1]["evaluation"] = evaluation
                return response, response_text, runtime.current_proof_text, evaluation, attempts, tool_calls_used

        if turn_had_proof_action:
            proof_attempts += 1
            consecutive_search_turns = 0
        else:
            consecutive_search_turns += 1
            if consecutive_search_turns >= 2:
                transcript.append(
                    {
                        "role": "user",
                        "content": (
                            "Stop searching and write a proof now. The search_public_defs tool only searches "
                            "this task's implementation and specification files, not the Lean standard library. "
                            "Use write_editable_proof to submit your best proof attempt (it runs the Lean check automatically)."
                        ),
                    }
                )
                consecutive_search_turns = 0

        # Tool results are already in the transcript from the tool-call loop above.
        # No transcript compaction — the model benefits from seeing its full history.

    evaluation = runtime.evaluate_current()
    if evaluation.get("failure_mode") == "empty_response":
        evaluation = {
            "status": "failed",
            "failure_mode": "attempt_budget_exhausted",
            "details": f"interactive attempt budget exhausted after {proof_attempts} proof attempts ({turn} total turns)",
        }
    attempts.append(
        {
            "attempt": turn,
            "proof_attempt": proof_attempts,
            "mode": "interactive",
            "budget_exhausted": True,
            "candidate_file_contents": runtime.current_proof_text,
            "evaluation": evaluation,
        }
    )
    attempts[-1]["budget_exhausted"] = True
    return response, response_text, runtime.current_proof_text, evaluation, attempts, tool_calls_used


def execute_agent_task(
    config_path: Path,
    task_ref: str,
    dry_run: bool,
    *,
    profile: str | None = None,
    resolved_config: ResolvedAgentConfig | None = None,
) -> tuple[int, Path]:
    config = resolved_config or resolve_config(config_path, require_secrets=not dry_run, profile=profile)
    task = resolve_task(task_ref)
    if task["translation_status"] != "generated":
        raise SystemExit(
            f"{task_ref}: translation_status must be 'generated' for Verity-executed harness runs "
            f"(got {task['translation_status']!r})"
        )
    messages = build_messages(config, task)
    if dry_run:
        result = build_result(task_ref, config, task, messages, dry_run=dry_run, elapsed_seconds=0.0)
        validate_result_payload(result, task_ref)
        result_path = write_result(task_ref, config, result)
        return 0, result_path

    start = time.perf_counter()
    # Pre-build implementation/specification modules so `lake env lean` inside
    # TaskProofRuntime.evaluate_candidate does not race against on-the-fly
    # compilation with fast agent retries.
    prebuild_reports: list[dict[str, Any]] = []
    if config.mode == "interactive":
        prebuild_reports = prebuild_task_modules(task)
        response, response_text, candidate_text, evaluation, attempts, tool_calls_used = execute_interactive_agent_task(
            config,
            task,
            messages,
        )
    elif config.mode == "custom":
        response = invoke_command_adapter(
            config,
            build_command_adapter_request(config, task, messages, kind="run"),
        )
        response_text, candidate_text = extract_command_candidate(response)
        evaluation = evaluate_candidate_submission(task, candidate_text)
        attempts = []
        tool_calls_used = 0
    else:
        response, response_text, evaluation, attempts = execute_strict_agent_task(config, task, messages)
        candidate_text = str(attempts[-1].get("candidate_file_contents", "")) if attempts else ""
        tool_calls_used = 0
    elapsed_seconds = time.perf_counter() - start
    result = build_result(
        task_ref,
        config,
        task,
        messages,
        dry_run=dry_run,
        evaluation=evaluation,
        elapsed_seconds=elapsed_seconds,
    )
    result["response"] = response
    result["response_text"] = response_text
    if config.mode == "custom":
        result["response_text_raw"] = str(response.get("response_text_raw", response_text))
        result["provider_reasoning_text"] = str(response.get("provider_reasoning_text", ""))
    else:
        response_content = extract_response_content(response)
        result["response_text_raw"] = response_content["response_text_raw"]
        result["provider_reasoning_text"] = response_content["provider_reasoning_text"]
    result["candidate_file_contents"] = candidate_text
    result["attempts"] = attempts
    result["tool_calls_used"] = tool_calls_used
    result["analysis"] = build_run_analysis(attempts=attempts, evaluation=evaluation, tool_calls_used=tool_calls_used)
    if prebuild_reports:
        result["prebuild_reports"] = prebuild_reports
    validate_result_payload(result, task_ref)
    result_path = write_result(task_ref, config, result)
    return (0 if evaluation["status"] == "passed" else 1), result_path


def run_command(config_path: Path, task_ref: str, dry_run: bool, *, profile: str | None = None) -> int:
    exit_code, result_path = execute_agent_task(config_path, task_ref, dry_run, profile=profile)
    print(result_path.relative_to(ROOT))
    return exit_code


def profiles_command() -> int:
    profiles: list[dict[str, Any]] = []
    for name in discover_profiles():
        path = profile_path(name)
        config = load_config(path)
        profiles.append(
            {
                "name": name,
                "agent_id": config["agent_id"],
                "mode": config.get("mode"),
                "track": config.get("track"),
                "run_slug": config.get("run_slug"),
                "adapter": config["adapter"],
                "config_path": config_label(path),
                "env_contract": env_contract(config),
            }
        )
    payload = {
        "profiles_dir": config_label(AGENT_PROFILES_DIR),
        "default_profile": DEFAULT_PROFILE,
        "profiles": profiles,
    }
    print(json.dumps(payload, indent=2))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description="Default benchmark agent adapter")
    subparsers = parser.add_subparsers(dest="command", required=True)

    validate_parser = subparsers.add_parser("validate-config", help="Validate an agent config file")
    validate_parser.add_argument("config")

    describe_parser = subparsers.add_parser("describe", help="Resolve and print a non-secret config summary")
    describe_parser.add_argument("--config")
    describe_parser.add_argument("--profile")

    prompt_parser = subparsers.add_parser("prompt", help="Render the default-agent prompt package for one task")
    prompt_parser.add_argument("task_ref")
    prompt_parser.add_argument("--config")
    prompt_parser.add_argument("--profile")

    evaluate_parser = subparsers.add_parser(
        "evaluate-candidate",
        help="Evaluate a candidate editable Lean file for one task",
    )
    evaluate_parser.add_argument("task_ref")
    evaluate_parser.add_argument("candidate_path")

    probe_parser = subparsers.add_parser("probe", help="Probe the configured OpenAI-compatible backend")
    probe_parser.add_argument("--config")
    probe_parser.add_argument("--profile")
    probe_parser.add_argument("--ensure-model", action="store_true")

    run_parser = subparsers.add_parser("run", help="Invoke the configured default agent for one task")
    run_parser.add_argument("task_ref")
    run_parser.add_argument("--config")
    run_parser.add_argument("--profile")
    run_parser.add_argument("--dry-run", action="store_true")

    subparsers.add_parser("profiles", help="List bundled default-agent profiles")

    args = parser.parse_args()

    if args.command == "validate-config":
        return validate_command(explicit_config_path(args.config))
    if args.command == "describe":
        return describe_command(resolve_config_path(args.config, args.profile))
    if args.command == "prompt":
        return prompt_command(resolve_config_path(args.config, args.profile), args.task_ref)
    if args.command == "evaluate-candidate":
        return evaluate_candidate_command(args.task_ref, Path(args.candidate_path))
    if args.command == "probe":
        return probe_command(resolve_config_path(args.config, args.profile), args.ensure_model)
    if args.command == "run":
        return run_command(
            resolve_config_path(args.config, args.profile),
            args.task_ref,
            args.dry_run,
            profile=args.profile,
        )
    if args.command == "profiles":
        return profiles_command()

    print(f"unsupported command: {args.command}", file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())

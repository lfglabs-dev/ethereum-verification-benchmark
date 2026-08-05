#!/usr/bin/env python3
"""Validate the portable manifests and files emitted by benchmark campaigns."""
from __future__ import annotations

import argparse
import json
import re
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parent.parent
SCHEMA_PATH = REPO_ROOT / "schemas" / "campaign_artifact_manifest.schema.json"
SHA = re.compile(r"^[0-9a-f]{40}$")
KNOWN_FIELDS = {
    "run_id", "model_id", "commit_sha", "lean_version", "task_set_id",
    "verity_commit", "artifacts",
}


@dataclass
class Result:
    manifest: str
    run_id: str
    errors: list[str]
    warnings: list[str]


def load_object(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError("expected a JSON object")
    return data


def schema_errors(data: dict[str, Any], schema: dict[str, Any], strict: bool) -> list[str]:
    """Validate the deliberately small schema vocabulary used by this manifest."""
    errors: list[str] = []
    for field in schema["required"]:
        if field not in data:
            errors.append(f"missing required field {field!r}")
    for field in ("run_id", "model_id", "commit_sha", "verity_commit"):
        value = data.get(field)
        if value is not None and not isinstance(value, str):
            errors.append(f"{field} must be a string")
    if isinstance(data.get("run_id"), str) and not data["run_id"]:
        errors.append("run_id must not be empty")
    for field in ("model_id", "commit_sha", "verity_commit"):
        value = data.get(field)
        if isinstance(value, str) and not SHA.fullmatch(value):
            errors.append(f"{field} must be a 40-character lowercase hexadecimal commit")
    if data.get("lean_version") != "4.31.0":
        errors.append("lean_version must be '4.31.0'")
    task_set_id = data.get("task_set_id")
    if task_set_id is not None and (not isinstance(task_set_id, str) or not task_set_id):
        errors.append("task_set_id must be a non-empty string")
    artifacts = data.get("artifacts")
    if not isinstance(artifacts, list) or not artifacts:
        errors.append("artifacts must be a non-empty array")
    else:
        for index, item in enumerate(artifacts):
            if isinstance(item, str) and item:
                continue
            if isinstance(item, dict) and isinstance(item.get("path"), str) and item["path"]:
                if "required" in item and not isinstance(item["required"], bool):
                    errors.append(f"artifacts[{index}].required must be boolean")
                continue
            errors.append(f"artifacts[{index}] must be a path or an object with a path")
    if strict:
        for field in sorted(set(data) - KNOWN_FIELDS):
            errors.append(f"unknown field in strict mode: {field!r}")
    return errors


def artifact_paths(data: dict[str, Any]) -> list[str]:
    paths: list[str] = []
    for item in data.get("artifacts", []):
        if isinstance(item, str):
            paths.append(item)
        elif isinstance(item, dict) and item.get("required", True) is not False:
            path = item.get("path")
            if isinstance(path, str):
                paths.append(path)
    return paths


def validate_manifest(path: Path, schema: dict[str, Any], strict: bool) -> Result:
    errors: list[str] = []
    warnings: list[str] = []
    try:
        data = load_object(path)
    except (OSError, json.JSONDecodeError, ValueError) as exc:
        return Result(str(path), path.parent.name, [f"invalid manifest: {exc}"], warnings)
    run_id = data.get("run_id") if isinstance(data.get("run_id"), str) else path.parent.name
    errors.extend(schema_errors(data, schema, strict))
    if isinstance(data.get("run_id"), str) and data["run_id"] != path.parent.name:
        errors.append(f"run_id does not match directory name {path.parent.name!r}")
    task_set_id = data.get("task_set_id")
    if isinstance(task_set_id, str):
        task_manifest = REPO_ROOT / "tasks" / task_set_id / "task_manifest.json"
        if not task_manifest.is_file():
            errors.append(f"task_set_id has no task manifest: {task_manifest}")
    base = path.parent.resolve()
    for relative in artifact_paths(data):
        candidate = (base / relative).resolve()
        if candidate != base and base not in candidate.parents:
            errors.append(f"artifact path escapes run directory: {relative!r}")
        elif not candidate.is_file():
            errors.append(f"required artifact is missing: {relative}")
        else:
            try:
                if candidate.stat().st_size == 0:
                    errors.append(f"required artifact is empty: {relative}")
            except OSError as exc:
                errors.append(f"cannot inspect artifact {relative!r}: {exc}")
    # check_verity_pin_staleness.py treats a pin as a lowercase hex Git SHA.
    # Staleness itself needs network state and is intentionally informational here.
    if isinstance(data.get("verity_commit"), str) and SHA.fullmatch(data["verity_commit"]):
        warnings.append("verity pin staleness not enforced (informational policy)")
    return Result(str(path), run_id, errors, warnings)


def validate_root(root: Path, strict: bool) -> list[Result]:
    schema = load_object(SCHEMA_PATH)
    paths = sorted(root.glob("*/manifest.json")) if root.is_dir() else []
    if not paths:
        return [Result(str(root), "-", ["no <run_id>/manifest.json files found"], [])]
    results = [validate_manifest(path, schema, strict) for path in paths]
    owners: dict[str, list[Result]] = {}
    for result in results:
        owners.setdefault(result.run_id, []).append(result)
    for run_id, duplicates in owners.items():
        if len(duplicates) > 1:
            for result in duplicates:
                result.errors.append(f"duplicate run_id: {run_id!r}")
    return results


def print_results(results: list[Result], as_json: bool) -> None:
    errors = sum(len(result.errors) for result in results)
    summary = {
        "ok": errors == 0,
        "runs": len(results),
        "error_count": errors,
        "results": [result.__dict__ for result in results],
    }
    if as_json:
        print(json.dumps(summary, indent=2, sort_keys=True))
        return
    print(f"{'RUN':<42} {'STATUS':<7} DETAILS")
    for result in results:
        details = result.errors or ["clean"]
        print(f"{result.run_id:<42} {'ERROR' if result.errors else 'OK':<7} {details[0]}")
        for detail in details[1:]:
            print(f"{'':<42} {'':<7} {detail}")
    print(f"Validated {len(results)} run(s): {errors} error(s)")


def self_test() -> int:
    with tempfile.TemporaryDirectory(prefix="campaign-artifact-validator-") as temporary:
        root = Path(temporary)
        # Two fixtures exercise both success and failure without adding repository files.
        good = root / ("a" * 40)
        good.mkdir()
        (good / "result.json").write_text("{}\n", encoding="utf-8")
        manifest = {
            "run_id": good.name, "model_id": "b" * 40, "commit_sha": "c" * 40,
            "lean_version": "4.31.0", "verity_commit": "d" * 40,
            "artifacts": [{"path": "result.json", "required": True}],
        }
        (good / "manifest.json").write_text(json.dumps(manifest), encoding="utf-8")
        good_results = validate_root(root, False)
        if any(result.errors for result in good_results):
            print("self-test good fixture failed", file=sys.stderr)
            return 1
        bad = root / ("e" * 40)
        bad.mkdir()
        manifest["run_id"] = bad.name
        manifest["lean_version"] = "4.30.0"
        (bad / "manifest.json").write_text(json.dumps(manifest), encoding="utf-8")
        bad_results = validate_root(root, False)
        if not any(result.errors for result in bad_results):
            print("self-test bad fixture was accepted", file=sys.stderr)
            return 1
    print("campaign artifact validator self-test passed")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate campaign artifact manifests and referenced files")
    parser.add_argument("--root", type=Path, default=Path("campaign_artifacts"))
    parser.add_argument("--strict", action="store_true")
    parser.add_argument("--json", action="store_true", dest="as_json")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        return self_test()
    try:
        results = validate_root(args.root, args.strict)
    except (OSError, json.JSONDecodeError, ValueError) as exc:
        parser.error(str(exc))
    print_results(results, args.as_json)
    return 1 if any(result.errors for result in results) else 0


if __name__ == "__main__":
    raise SystemExit(main())

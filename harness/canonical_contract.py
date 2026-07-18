"""Loading and fail-closed validation for frozen benchmark task contracts."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

try:
    from .paths import ROOT
except ImportError:
    from paths import ROOT


CANONICAL_V02_PATH = ROOT / "benchmark-versions" / "v0.2.json"


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_v02_task_refs() -> list[str]:
    """Return the frozen v0.2 sequence, rejecting any malformed or drifted input."""
    try:
        data = json.loads(CANONICAL_V02_PATH.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ValueError(f"cannot load canonical v0.2 contract: {exc}") from exc
    if data.get("schema_version") != 2 or data.get("benchmark_version") != "0.2":
        raise ValueError("canonical v0.2 contract has incompatible schema/version")
    source = data.get("source")
    if not isinstance(source, dict) or not isinstance(source.get("commit"), str):
        raise ValueError("canonical v0.2 contract has malformed source provenance")
    task_objects = data.get("tasks")
    hashes = data.get("task_manifest_sha256")
    if not isinstance(task_objects, list) or not all(isinstance(item, dict) for item in task_objects):
        raise ValueError("canonical v0.2 contract has malformed tasks")
    tasks = [item.get("task_ref") for item in task_objects]
    if not all(isinstance(item, str) and item for item in tasks):
        raise ValueError("canonical v0.2 contract has malformed task refs")
    if data.get("manifest_schema_version") != 1 or any(
        not isinstance(item.get("task_fingerprint"), str)
        or not isinstance(item.get("task_interface_id"), str)
        for item in task_objects
    ):
        raise ValueError("canonical v0.2 contract has malformed version task metadata")
    if not isinstance(hashes, dict) or set(hashes) != set(tasks):
        raise ValueError("canonical v0.2 contract has missing or duplicate task mappings")
    if len(tasks) != len(set(tasks)) or data.get("task_count") != len(tasks):
        raise ValueError("canonical v0.2 contract has duplicate task refs or incorrect count")
    task_set_hash = hashlib.sha256(("\n".join(tasks) + "\n").encode()).hexdigest()
    if data.get("task_set_sha256") != task_set_hash:
        raise ValueError("canonical v0.2 contract task ordering/hash drift")
    # This must be derived from the immutable source named by the contract.
    # Comparing to the working tree permits a coordinated source/manifest edit.
    from scripts.compute_fingerprints import baseline_task_metadata, task_metadata

    baseline_metadata = baseline_task_metadata(source["commit"])
    current_metadata = task_metadata("all")
    if set(baseline_metadata) != set(tasks):
        raise ValueError("canonical v0.2 contract pinned baseline task set drift")
    if not set(tasks).issubset(current_metadata):
        raise ValueError("canonical v0.2 contract current frozen task missing")
    for task_object, task_ref in zip(task_objects, tasks, strict=True):
        parts = task_ref.split("/")
        if len(parts) != 3:
            raise ValueError(f"canonical v0.2 contract has malformed task ref: {task_ref}")
        candidates = [
            ROOT / "cases" / parts[0] / parts[1] / "tasks" / f"{parts[2]}.yaml",
            ROOT / "backlog" / parts[0] / parts[1] / "tasks" / f"{parts[2]}.yaml",
        ]
        paths = [path for path in candidates if path.is_file()]
        if len(paths) != 1 or not isinstance(hashes[task_ref], str) or sha256_file(paths[0]) != hashes[task_ref]:
            raise ValueError(f"canonical v0.2 contract task source drift: {task_ref}")
        if baseline_metadata.get(task_ref) != (
            task_object["task_fingerprint"],
            task_object["task_interface_id"],
        ):
            raise ValueError(f"canonical v0.2 contract task fingerprint drift: {task_ref}")
        if current_metadata.get(task_ref) != baseline_metadata[task_ref]:
            raise ValueError(f"canonical v0.2 contract task source fingerprint drift: {task_ref}")
    return tasks

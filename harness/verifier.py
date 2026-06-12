from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import tempfile
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path

try:
    from .manifests import Group, Task, group_to_json
    from .paths import ROOT
    from .workspace_builder import _clone_tree, sha256_file
except ImportError:
    from manifests import Group, Task, group_to_json
    from paths import ROOT
    from workspace_builder import _clone_tree, sha256_file

FORBIDDEN_RE = re.compile(r"\b(sorry|admit|axiom)\b|\?_[A-Za-z0-9_']*")
IMPORT_RE = re.compile(r"^\s*import\s+(.+)$", re.MULTILINE)


@dataclass(frozen=True)
class TargetResult:
    task_ref: str
    theorem_name: str | None
    points: int
    status: str
    output: str = ""


def _run(command: list[str], cwd: Path, timeout: int) -> tuple[int, str]:
    try:
        completed = subprocess.run(command, cwd=cwd, capture_output=True, text=True, timeout=timeout, check=False)
    except subprocess.TimeoutExpired as exc:
        stdout = exc.stdout or ""
        stderr = exc.stderr or ""
        if isinstance(stdout, bytes):
            stdout = stdout.decode("utf-8", errors="replace")
        if isinstance(stderr, bytes):
            stderr = stderr.decode("utf-8", errors="replace")
        return 124, stdout + stderr + "\ntimeout"
    return completed.returncode, (completed.stdout + completed.stderr).strip()


def _compact_output(output: str, limit: int = 4000) -> str:
    lines = output.splitlines()
    error_lines: list[str] = []
    for index, line in enumerate(lines):
        if "error:" in line.lower():
            error_lines.extend(lines[index : min(len(lines), index + 8)])
    if error_lines:
        filtered = [line for line in error_lines if not line.startswith("trace: .>") and "LEAN_PATH=" not in line]
        return "\n".join(filtered)[-limit:]
    return output[-limit:]


def _decl_name(theorem_name: str | None) -> str | None:
    if not theorem_name:
        return None
    return theorem_name.split(".")[-1]


def _theorem_signature(text: str, theorem_name: str | None) -> str | None:
    name = _decl_name(theorem_name)
    if not name:
        return None
    pattern = re.compile(rf"\btheorem\s+{re.escape(name)}\b(?P<body>.*?)(?::=\s*by|:=)", re.DOTALL)
    match = pattern.search(text)
    if not match:
        return None
    return " ".join(match.group(0).split())


def _policy_failure(task: Task, submitted_file: Path, submitted_workspace: Path) -> str | None:
    if not submitted_file.is_file():
        return "theorem_missing"
    text = submitted_file.read_text(encoding="utf-8")
    for import_line in IMPORT_RE.findall(text):
        for import_module in import_line.strip().split():
            if "GeneratedPreview" in import_module or (
                import_module.startswith("Benchmark.Cases.") and import_module.split(".")[-1].endswith("Proofs")
            ):
                return "hidden_import"
            # Any project module the agent could not see in its workspace is
            # hidden by definition: the verifier repo has every source, so
            # compilation alone would not catch the smuggled import.
            if import_module.startswith("Benchmark"):
                rel = import_module.replace(".", "/") + ".lean"
                if not (submitted_workspace / rel).is_file():
                    return "hidden_import"
    original_file = ROOT / task.editable_files[0]
    original_sig = _theorem_signature(original_file.read_text(encoding="utf-8"), task.theorem_name)
    submitted_sig = _theorem_signature(text, task.theorem_name)
    if submitted_sig is None:
        return "theorem_missing"
    if original_sig is not None and submitted_sig != original_sig:
        return "theorem_statement_mismatch"
    if FORBIDDEN_RE.search(text):
        return "forbidden_placeholder"
    return None


def _copy_repo_for_verification() -> Path:
    temp_root = Path(tempfile.mkdtemp(prefix="verity-verifier-"))
    dst = temp_root / "repo"

    needed_roots = {
        "Benchmark", "Benchmark.lean", "cases", "families", "harness", "scripts",
        "lakefile.lean", "lake-manifest.json", "lean-toolchain", "benchmark.toml",
        "trusted-axioms.json", "schemas",
    }

    def ignore(dir_path: str, names: list[str]) -> set[str]:
        ignored = {name for name in names if name in {".git", ".lake", "results", "__pycache__"}}
        if Path(dir_path).resolve() == ROOT.resolve():
            ignored.update(name for name in names if name not in needed_roots)
        return ignored

    shutil.copytree(ROOT, dst, ignore=ignore, symlinks=True, ignore_dangling_symlinks=True)
    lake_cache = ROOT / ".lake"
    if lake_cache.exists():
        # Private build dir (cheap clone): verification builds must not write
        # into the repo cache, and the workspace umbrella overlay below would
        # otherwise be rebuilt into the shared .lake.
        (dst / ".lake").mkdir()
        if (lake_cache / "packages").exists():
            (dst / ".lake" / "packages").symlink_to(lake_cache / "packages", target_is_directory=True)
        if (lake_cache / "build").is_dir():
            _clone_tree(lake_cache / "build", dst / ".lake" / "build")
    return dst


def verify_group(
    group: Group,
    submitted_workspace: Path,
    *,
    artifact_dir: Path | None = None,
    timeout_seconds: int = 120,
) -> dict[str, object]:
    started = time.time()
    verifier_repo = _copy_repo_for_verification()
    # Mirror the workspace's generated Grindset umbrella: the repo umbrella
    # imports case-specific helper modules the agent never saw, and through
    # the skeleton's `import Benchmark.Grindset` those names would otherwise
    # be in scope during verification.
    workspace_umbrella = submitted_workspace / "Benchmark" / "Grindset.lean"
    if workspace_umbrella.is_file():
        shutil.copy2(workspace_umbrella, verifier_repo / "Benchmark" / "Grindset.lean")
    keep_verifier_workspace = os.environ.get("VERITY_KEEP_VERIFIER_WORKSPACE") == "1"
    targets: list[TargetResult] = []
    submitted_files: list[str] = []

    for task in group.tasks:
        if len(task.editable_files) != 1:
            targets.append(TargetResult(task.task_ref, task.theorem_name, task.points, "harness_error", "expected one editable file"))
            continue
        rel = task.editable_files[0]
        submitted = submitted_workspace / rel
        failure = _policy_failure(task, submitted, submitted_workspace)
        if failure:
            targets.append(TargetResult(task.task_ref, task.theorem_name, task.points, failure))
            continue
        dst = verifier_repo / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(submitted, dst)
        submitted_files.append(rel)
        module = task.target_module
        if not module:
            targets.append(TargetResult(task.task_ref, task.theorem_name, task.points, "harness_error", "missing target module"))
            continue
        code, output = _run(["lake", "build", module], verifier_repo, timeout_seconds)
        if code != 0 and "not up-to-date" in output:
            # Shared dependency cache corrupted (e.g. concurrent lake builds);
            # repair and retry once so infra noise never reads as a proof failure.
            _run(["lake", "exe", "cache", "get"], verifier_repo, 600)
            code, output = _run(["lake", "build", module], verifier_repo, timeout_seconds)
        if code != 0:
            if "not up-to-date" in output:
                status = "verifier_infra_error"
            else:
                status = "timeout" if code == 124 else "lean_check_failed"
            targets.append(TargetResult(task.task_ref, task.theorem_name, task.points, status, _compact_output(output)))
            continue
        if task.theorem_name:
            with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=verifier_repo, delete=False, encoding="utf-8") as check_file:
                check_file.write(f"import {module}\n#check {task.theorem_name}\n")
                check_path = Path(check_file.name)
            code, check_output = _run(["lake", "env", "lean", str(check_path)], verifier_repo, timeout_seconds)
            check_path.unlink(missing_ok=True)
            if code != 0:
                targets.append(TargetResult(task.task_ref, task.theorem_name, task.points, "theorem_missing", _compact_output(check_output)))
                continue
        targets.append(TargetResult(task.task_ref, task.theorem_name, task.points, "passed", _compact_output(output)))

    earned = sum(item.points for item in targets if item.status == "passed")
    possible = sum(item.points for item in targets)
    passed = sum(1 for item in targets if item.status == "passed")
    completed = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    result = {
        "schema_version": 1,
        "completed_at": completed,
        "group": group_to_json(group),
        "submitted_workspace": str(submitted_workspace),
        "verifier_workspace": str(verifier_repo) if keep_verifier_workspace else None,
        "submitted_files": [
            {"path": rel, "sha256": sha256_file(submitted_workspace / rel)}
            for rel in submitted_files
            if (submitted_workspace / rel).is_file()
        ],
        "score": {
            "points_earned": earned,
            "points_possible": possible,
            "passed_targets": passed,
            "total_targets": len(targets),
        },
        "targets": [item.__dict__ for item in targets],
        "duration_seconds": round(time.time() - started, 3),
    }
    if artifact_dir:
        artifact_dir.mkdir(parents=True, exist_ok=True)
        (artifact_dir / "verifier.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    if not keep_verifier_workspace:
        shutil.rmtree(verifier_repo.parent, ignore_errors=True)
    return result

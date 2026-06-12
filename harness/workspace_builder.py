from __future__ import annotations

import hashlib
import json
import os
import shutil
import tempfile
from dataclasses import dataclass
from pathlib import Path

try:
    from .manifests import Group, group_to_json
    from .paths import ROOT
except ImportError:
    from manifests import Group, group_to_json
    from paths import ROOT


@dataclass(frozen=True)
class BuiltWorkspace:
    path: Path
    manifest_path: Path


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def agent_group_to_json(group: Group) -> dict[str, object]:
    payload = group_to_json(group)
    tasks = payload.get("tasks")
    if isinstance(tasks, list):
        for task in tasks:
            if isinstance(task, dict):
                task.pop("reference_solution", None)
    return payload


def _read_if_present(workspace: Path, rel_path: str, *, limit: int = 6000) -> str:
    path = workspace / rel_path
    if not path.is_file():
        return ""
    text = path.read_text(encoding="utf-8")
    if len(text) > limit:
        return text[:limit] + "\n/- truncated in task summary -/\n"
    return text


def _symbol_lines(text: str, *, limit: int = 20) -> list[str]:
    symbols: list[str] = []
    namespace = ""
    for raw in text.splitlines():
        line = raw.strip()
        if not line:
            continue
        if line.startswith("namespace "):
            namespace = line.split(None, 1)[1]
            continue
        if line.startswith("end "):
            namespace = ""
            continue
        if line.startswith(("def ", "theorem ", "lemma ", "abbrev ", "structure ", "inductive ")):
            symbols.append(line.split(":=", 1)[0].strip()[:220])
        elif line.startswith("function "):
            symbols.append((f"{namespace}.{line}" if namespace else line)[:220])
        elif ":= slot " in line:
            symbols.append(("storage " + line)[:220])
        if len(symbols) >= limit:
            break
    return symbols


def _relevant_symbols_for_task(workspace: Path, task: object) -> list[str]:
    symbols: list[str] = []
    seen: set[str] = set()
    for rel in (*task.implementation_files, *task.specification_files):
        text = _read_if_present(workspace, rel, limit=10000)
        if not text:
            continue
        for symbol in _symbol_lines(text, limit=16):
            if symbol not in seen:
                seen.add(symbol)
                symbols.append(f"- `{rel}`: {symbol}")
            if len(symbols) >= 24:
                return symbols
    return symbols


def _task_summary_markdown(group: Group, workspace: Path) -> str:
    lines = [
        "# Verity Task Summary",
        "",
        f"- group: `{group.group_id}`",
        f"- suite: `{group.suite}`",
        f"- tasks: `{len(group.tasks)}`",
        "- check command: `./harness/check.sh`",
        "",
        "## Policy",
        "",
        "- Edit only files listed under editable files.",
        "- Do not import hidden Proofs modules or Benchmark/GeneratedPreview.",
        "- Do not use `sorry`, `admit`, or new `axiom` declarations.",
        "- In fair comparisons, do not rely on benchmark-specific Grindset helpers or task-name-specific proof knowledge.",
        "",
    ]
    for index, task in enumerate(group.tasks, start=1):
        lines.extend(
            [
                f"## Task {index}: `{task.task_ref}`",
                "",
                f"- theorem: `{task.theorem_name}`",
                f"- target module: `{task.target_module}`",
                f"- editable files: `{', '.join(task.editable_files)}`",
                f"- implementation files: `{', '.join(task.implementation_files)}`",
                f"- specification files: `{', '.join(task.specification_files)}`",
                "",
            ]
        )
        symbols = _relevant_symbols_for_task(workspace, task)
        if symbols:
            lines.extend(["### Relevant Symbols", "", *symbols, ""])
        for rel in task.editable_files:
            content = _read_if_present(workspace, rel)
            if content:
                lines.extend(["### Current Editable File", "", f"`{rel}`", "", "```lean", content.rstrip(), "```", ""])
    return "\n".join(lines).rstrip() + "\n"


def _copy_file(rel_path: str, workspace: Path, copied: dict[str, str]) -> None:
    if rel_path.startswith(".env") or "Benchmark/GeneratedPreview" in rel_path:
        raise ValueError(f"refusing to copy forbidden workspace path {rel_path}")
    src = ROOT / rel_path
    if not src.is_file():
        raise FileNotFoundError(rel_path)
    dst = workspace / rel_path
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(src, dst)
    copied[rel_path] = sha256_file(dst)


def _case_public_dirs(group: Group) -> list[str]:
    parts = group.group_id.split("/")
    if len(parts) < 2:
        raise ValueError(f"invalid group id {group.group_id!r}")
    project, case = parts[:2]
    dirs = [f"cases/{project}/{case}"]
    for task in group.tasks:
        for rel_path in (*task.implementation_files, *task.specification_files, *task.editable_files):
            parts = Path(rel_path).parts
            if len(parts) >= 4 and parts[0] == "Benchmark" and parts[1] == "Cases":
                dirs.append(str(Path(*parts[:4])))
    return sorted(set(dirs))



def _clone_tree(src: Path, dst: Path) -> None:
    """Cheap copy-on-write/hardlink clone of a directory tree."""
    import platform
    import subprocess

    dst.parent.mkdir(parents=True, exist_ok=True)
    if platform.system() == "Darwin":
        result = subprocess.run(["cp", "-Rc", str(src), str(dst)], capture_output=True)
        if result.returncode == 0:
            return
    else:
        result = subprocess.run(["cp", "-Rla", str(src), str(dst)], capture_output=True)
        if result.returncode == 0:
            return
    shutil.copytree(src, dst)


def setup_private_lake(root_dir: Path, *, prune_to_sources: bool = False) -> dict[str, str] | None:
    """Give `root_dir` a private .lake: dependency packages are shared via
    symlink (read-only caches), while the project's own build dir is cloned
    cheaply so builds never write into the repo cache.

    With `prune_to_sources`, every cloned artifact whose source .lean is
    absent from `root_dir` is removed. Sharing the repo build dir verbatim
    would leak compiled hidden reference proofs: they stay importable even
    though their sources never reach the workspace. Verifier copies carry
    all sources, so they clone without pruning."""
    lake_cache = ROOT / ".lake"
    if not lake_cache.exists() or (root_dir / ".lake").exists():
        return None
    (root_dir / ".lake").mkdir()
    dependency_cache: dict[str, str] | None = None
    if (lake_cache / "packages").exists():
        (root_dir / ".lake" / "packages").symlink_to(lake_cache / "packages", target_is_directory=True)
        dependency_cache = {"path": ".lake/packages", "target": str(lake_cache / "packages")}
    if (lake_cache / "build").is_dir():
        _clone_tree(lake_cache / "build", root_dir / ".lake" / "build")
        if prune_to_sources:
            _prune_build_to_sources(root_dir)
    return dependency_cache


def _prune_build_to_sources(workspace: Path) -> None:
    dst_build = workspace / ".lake" / "build"
    for tree in (dst_build / "lib" / "lean", dst_build / "ir"):
        if not tree.is_dir():
            continue
        for artifact in sorted(tree.rglob("*")):
            if not artifact.is_file():
                continue
            rel = artifact.relative_to(tree)
            stem = rel.as_posix()
            for suffix in (".olean", ".olean.hash", ".olean.trace", ".ilean", ".ilean.hash",
                           ".trace", ".c", ".c.hash", ".c.o", ".o", ".bc", ".json"):
                if stem.endswith(suffix):
                    stem = stem[: -len(suffix)]
                    break
            source = workspace / (stem + ".lean")
            if not source.is_file():
                artifact.unlink(missing_ok=True)
        for directory in sorted((d for d in tree.rglob("*") if d.is_dir()), reverse=True):
            try:
                directory.rmdir()
            except OSError:
                pass


def build_group_workspace(
    group: Group,
    *,
    workspace_dir: Path | None = None,
    run_id: str | None = None,
) -> BuiltWorkspace:
    workspace = workspace_dir or Path(tempfile.mkdtemp(prefix=f"verity-{group.group_id.replace('/', '__')}-"))
    workspace.mkdir(parents=True, exist_ok=True)
    copied: dict[str, str] = {}

    for rel in ("lakefile.lean", "lake-manifest.json", "lean-toolchain"):
        if (ROOT / rel).is_file():
            _copy_file(rel, workspace, copied)
    dependency_cache: dict[str, str] | None = None

    grindset_root = workspace / "Benchmark" / "Grindset.lean"
    grindset_root.parent.mkdir(parents=True, exist_ok=True)
    grindset_modules = {"Attr.lean", "Monad.lean", "Core.lean", "Reach.lean", "ArithCore.lean"}
    grindset_imports = [
        "import Benchmark.Grindset.Attr",
        "import Benchmark.Grindset.Monad",
        "import Benchmark.Grindset.Core",
        "import Benchmark.Grindset.Reach",
        "import Benchmark.Grindset.ArithCore",
    ]
    grindset_root.write_text(
        "\n".join(grindset_imports)
        + "\n\n/- Group-safe umbrella generated by harness/workspace_builder.py. -/\n",
        encoding="utf-8",
    )
    copied["Benchmark/Grindset.lean"] = sha256_file(grindset_root)
    for rel in sorted(
        str(path.relative_to(ROOT))
        for path in (ROOT / "Benchmark" / "Grindset").glob("*.lean")
        if path.name in grindset_modules
    ):
        _copy_file(rel, workspace, copied)

    for rel_dir in _case_public_dirs(group):
        src = ROOT / rel_dir
        if src.is_dir():
            for file_path in sorted(src.rglob("*")):
                if not file_path.is_file():
                    continue
                rel = file_path.relative_to(ROOT).as_posix()
                if rel.endswith("Proofs.lean") or "GeneratedPreview" in rel:
                    continue
                _copy_file(rel, workspace, copied)

    for task in group.tasks:
        for rel in (*task.implementation_files, *task.specification_files, *task.editable_files, task.manifest_path):
            _copy_file(rel, workspace, copied)
        case_manifest = Path(task.manifest_path).parent.parent / "case.yaml"
        _copy_file(case_manifest.as_posix(), workspace, copied)

    for rel in ("harness/PROMPT.md", "harness/POLICY.md", "harness/TOOLS.md", "harness/PROOF_PATTERNS.md"):
        _copy_file(rel, workspace, copied)

    harness_dir = workspace / "harness"
    harness_dir.mkdir(parents=True, exist_ok=True)
    (harness_dir / "TASKS.json").write_text(json.dumps(agent_group_to_json(group), indent=2) + "\n", encoding="utf-8")
    copied["harness/TASKS.json"] = sha256_file(harness_dir / "TASKS.json")
    (harness_dir / "TASK_SUMMARY.md").write_text(
        _task_summary_markdown(group, workspace),
        encoding="utf-8",
    )
    copied["harness/TASK_SUMMARY.md"] = sha256_file(harness_dir / "TASK_SUMMARY.md")
    check = "#!/usr/bin/env bash\nset -euo pipefail\nfor module in $(python3 - <<'PY'\nimport json\nfor task in json.load(open('harness/TASKS.json'))['tasks']:\n    print(task['target_module'])\nPY\n); do\n  lake build \"$module\"\ndone\n"
    (harness_dir / "check.sh").write_text(check, encoding="utf-8")
    os.chmod(harness_dir / "check.sh", 0o755)
    copied["harness/check.sh"] = sha256_file(harness_dir / "check.sh")

    grok_dir = workspace / ".grok"
    grok_dir.mkdir(exist_ok=True)
    (grok_dir / "rules.md").write_text("Edit only declared editable files.\n", encoding="utf-8")
    (grok_dir / "sandbox.toml").write_text("[sandbox]\nprofile = \"strict\"\n", encoding="utf-8")
    copied[".grok/rules.md"] = sha256_file(grok_dir / "rules.md")
    copied[".grok/sandbox.toml"] = sha256_file(grok_dir / "sandbox.toml")

    manifest = {
        "schema_version": 1,
        "run_id": run_id,
        "group": agent_group_to_json(group),
        "root": str(workspace),
        "files": [{"path": path, "sha256": digest} for path, digest in sorted(copied.items())],
        "dependency_cache": dependency_cache,
        "tool_policy": {
            "generic_grindset_only": True,
        },
        "forbidden_absent": [
            "Benchmark/Cases/**/*Proofs.lean",
            "Benchmark/GeneratedPreview",
            ".env",
        ],
    }
    dependency_cache = setup_private_lake(workspace, prune_to_sources=True)

    manifest_path = workspace / "workspace-manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    return BuiltWorkspace(path=workspace, manifest_path=manifest_path)


def assert_workspace_isolated(workspace: Path) -> None:
    forbidden = []
    if (workspace / ".env").exists():
        forbidden.append(".env")
    if (workspace / "Benchmark" / "GeneratedPreview").exists():
        forbidden.append("Benchmark/GeneratedPreview")
    forbidden.extend(str(path.relative_to(workspace)) for path in workspace.glob("Benchmark/Cases/**/*Proofs.lean"))
    if forbidden:
        raise AssertionError(f"workspace leaked forbidden files: {', '.join(forbidden)}")

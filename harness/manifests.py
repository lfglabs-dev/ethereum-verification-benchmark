from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any

try:
    from .paths import ROOT
    from .toml_compat import load_toml_file
except ImportError:
    from paths import ROOT
    from toml_compat import load_toml_file

from manifest_utils import load_manifest_data

RUNNABLE_STAGES = {"build_green", "proof_partial", "proof_complete"}
RUNNABLE_TRANSLATION_STATUSES = {"generated", "translated"}
PROOF_READY_STATUSES = {"partial", "complete"}


@dataclass(frozen=True)
class Task:
    task_ref: str
    task_id: str
    case_id: str
    suite: str
    theorem_name: str | None
    implementation_files: tuple[str, ...]
    specification_files: tuple[str, ...]
    editable_files: tuple[str, ...]
    reference_solution_module: str | None
    reference_solution_declaration: str | None
    manifest_path: str
    points: int = 1
    depends_on: tuple[str, ...] = ()

    @property
    def target_module(self) -> str | None:
        if len(self.editable_files) != 1:
            return None
        path = Path(self.editable_files[0])
        if path.suffix != ".lean":
            return None
        return ".".join(path.with_suffix("").parts)


@dataclass(frozen=True)
class Group:
    group_id: str
    suite: str
    tasks: tuple[Task, ...]
    default_points: int = 1

    @property
    def points_possible(self) -> int:
        return sum(task.points for task in self.tasks)


def _string(value: object) -> str | None:
    if value is None or isinstance(value, list):
        return None
    text = str(value).strip()
    return text or None


def _list(value: object) -> tuple[str, ...]:
    if value is None:
        return ()
    if not isinstance(value, list):
        raise ValueError(f"expected list, got {type(value).__name__}")
    return tuple(str(item).strip() for item in value if str(item).strip())


def _suite_for_manifest(path: Path) -> str:
    return "active" if "cases" in path.parts else "backlog"


def task_ref_from_manifest(path: Path) -> str:
    case_dir = path.parent.parent
    return f"{case_dir.parent.name}/{case_dir.name}/{path.stem}"


def discover_task_manifests(suite: str = "active") -> list[Path]:
    roots: list[Path] = []
    if suite in {"active", "all"}:
        roots.append(ROOT / "cases")
    if suite in {"backlog", "all"}:
        roots.append(ROOT / "backlog")
    manifests: list[Path] = []
    for root in roots:
        if root.exists():
            manifests.extend(sorted(root.glob("*/*/tasks/*.yaml")))
    return manifests


def resolve_task_manifest(task_ref: str) -> Path:
    parts = task_ref.split("/")
    if len(parts) != 3:
        raise ValueError("task refs must be project/case/task")
    for base in (ROOT / "cases", ROOT / "backlog"):
        candidate = base / parts[0] / parts[1] / "tasks" / f"{parts[2]}.yaml"
        if candidate.is_file():
            return candidate
    raise FileNotFoundError(f"task manifest not found for {task_ref}")


def resolve_case_manifest(group_id: str, suite: str = "active") -> Path:
    parts = group_id.split("/")
    if len(parts) != 2:
        raise ValueError("group refs must be project/case")
    roots = [ROOT / "cases"] if suite == "active" else [ROOT / "backlog"] if suite == "backlog" else [ROOT / "cases", ROOT / "backlog"]
    for base in roots:
        candidate = base / parts[0] / parts[1] / "case.yaml"
        if candidate.is_file():
            return candidate
    raise FileNotFoundError(f"case manifest not found for {group_id}")


def load_task(path: Path) -> Task:
    raw = load_manifest_data(path)
    case_dir = path.parent.parent
    case_raw = load_manifest_data(case_dir / "case.yaml")
    case_id = f"{case_raw['project']}/{case_raw['case_id']}"
    task_id = _string(raw.get("task_id")) or path.stem
    theorem_name = _string(raw.get("theorem_name"))
    return Task(
        task_ref=f"{case_id}/{task_id}",
        task_id=task_id,
        case_id=case_id,
        suite=_suite_for_manifest(path),
        theorem_name=theorem_name,
        implementation_files=_list(raw.get("implementation_files")),
        specification_files=_list(raw.get("specification_files")),
        editable_files=_list(raw.get("editable_files")),
        reference_solution_module=_string(raw.get("reference_solution_module")),
        reference_solution_declaration=_string(raw.get("reference_solution_declaration")) or theorem_name,
        manifest_path=str(path.relative_to(ROOT)),
    )


def load_task_by_ref(task_ref: str) -> Task:
    return load_task(resolve_task_manifest(task_ref))


def _configured_groups(suite: str) -> list[Group]:
    benchmark_toml = ROOT / "benchmark.toml"
    if not benchmark_toml.is_file():
        return []
    data = load_toml_file(benchmark_toml)
    raw_groups = data.get("groups")
    if not isinstance(raw_groups, list):
        return []
    groups: list[Group] = []
    for raw_group in raw_groups:
        if not isinstance(raw_group, dict):
            continue
        group_id = _string(raw_group.get("id"))
        group_suite = _string(raw_group.get("suite")) or "active"
        if not group_id or (suite != "all" and group_suite != suite):
            continue
        default_points = int(raw_group.get("default_points", 1))
        raw_tasks = raw_group.get("tasks")
        if not isinstance(raw_tasks, list):
            continue
        tasks: list[Task] = []
        for raw_task in raw_tasks:
            if not isinstance(raw_task, dict):
                continue
            task_ref = _string(raw_task.get("task_ref"))
            if not task_ref:
                continue
            base = load_task_by_ref(task_ref)
            tasks.append(
                Task(
                    task_ref=base.task_ref,
                    task_id=base.task_id,
                    case_id=base.case_id,
                    suite=base.suite,
                    theorem_name=base.theorem_name,
                    implementation_files=base.implementation_files,
                    specification_files=base.specification_files,
                    editable_files=base.editable_files,
                    reference_solution_module=base.reference_solution_module,
                    reference_solution_declaration=base.reference_solution_declaration,
                    manifest_path=base.manifest_path,
                    points=int(raw_task.get("points", default_points)),
                    depends_on=_list(raw_task.get("depends_on")),
                )
            )
        if tasks:
            groups.append(Group(group_id=group_id, suite=group_suite, tasks=tuple(tasks), default_points=default_points))
    return groups


def task_is_runnable(task: Task) -> bool:
    raw = load_manifest_data(ROOT / task.manifest_path)
    case_raw = load_manifest_data((ROOT / task.manifest_path).parent.parent / "case.yaml")
    stage = _string(raw.get("stage")) or _string(case_raw.get("stage"))
    translation_status = _string(raw.get("translation_status")) or _string(case_raw.get("translation_status"))
    proof_status = _string(raw.get("proof_status")) or _string(case_raw.get("proof_status"))
    return (
        stage in RUNNABLE_STAGES
        and translation_status in RUNNABLE_TRANSLATION_STATUSES
        and proof_status in PROOF_READY_STATUSES
        and bool(task.theorem_name)
        and bool(task.editable_files)
    )


def list_groups(suite: str = "active", *, runnable_only: bool = True) -> list[Group]:
    configured = _configured_groups(suite)
    if configured:
        if runnable_only:
            configured = [
                Group(group.group_id, group.suite, tuple(task for task in group.tasks if task_is_runnable(task)), group.default_points)
                for group in configured
            ]
            configured = [group for group in configured if group.tasks]
        return sorted(configured, key=lambda group: group.group_id)

    groups: dict[str, list[Task]] = {}
    for manifest in discover_task_manifests(suite):
        task = load_task(manifest)
        if runnable_only and not task_is_runnable(task):
            continue
        groups.setdefault(task.case_id, []).append(task)
    return [
        Group(group_id=group_id, suite=tasks[0].suite, tasks=tuple(sorted(tasks, key=lambda item: item.task_id)))
        for group_id, tasks in sorted(groups.items())
    ]


def load_group(group_id: str, suite: str = "active", *, runnable_only: bool = True) -> Group:
    resolve_case_manifest(group_id, suite)
    groups = {group.group_id: group for group in list_groups(suite, runnable_only=runnable_only)}
    if group_id not in groups:
        raise FileNotFoundError(f"no runnable group found for {group_id} in suite {suite}")
    return groups[group_id]


def group_id_from_task_ref(task_ref: str) -> str:
    parts = task_ref.split("/")
    if len(parts) != 3:
        raise ValueError("task refs must be project/case/task")
    return "/".join(parts[:2])


def filter_group_to_task(group: Group, task_ref: str) -> Group:
    matches = tuple(task for task in group.tasks if task.task_ref == task_ref)
    if not matches:
        raise FileNotFoundError(f"task {task_ref} not found in group {group.group_id}")
    return Group(group_id=task_ref, suite=group.suite, tasks=matches, default_points=group.default_points)


def group_to_json(group: Group) -> dict[str, Any]:
    return {
        "id": group.group_id,
        "suite": group.suite,
        "default_points": group.default_points,
        "points_possible": group.points_possible,
        "tasks": [
            {
                "task_ref": task.task_ref,
                "task_id": task.task_id,
                "theorem_name": task.theorem_name,
                "target_module": task.target_module,
                "points": task.points,
                "depends_on": list(task.depends_on),
                "implementation_files": list(task.implementation_files),
                "specification_files": list(task.specification_files),
                "editable_files": list(task.editable_files),
                "manifest_path": task.manifest_path,
                "reference_solution": {
                    "module": task.reference_solution_module,
                    "declaration": task.reference_solution_declaration,
                },
            }
            for task in group.tasks
        ],
    }

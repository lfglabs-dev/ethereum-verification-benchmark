from __future__ import annotations

import hashlib
import json
import os
import signal
import shutil
import subprocess
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path

try:
    from .manifests import Group, group_to_json
    from .paths import ROOT
    from .verify_lease import verify_lease
except ImportError:
    from manifests import Group, group_to_json
    from paths import ROOT
    from verify_lease import verify_lease


@dataclass(frozen=True)
class BuiltWorkspace:
    path: Path
    manifest_path: Path


# Every generated fair/shell workspace gets this restricted, public Grindset
# surface. Warm the component modules in the repo cache up front; otherwise the
# first provider arm silently pays their multi-minute cold build even after a
# successful `warm-task`. Do not warm the repository's broader Grindset
# umbrella, whose imports intentionally differ from the generated workspace.
PUBLIC_WORKSPACE_GRINDSET_MODULES = (
    "Benchmark.Grindset.ArithCore",
    "Benchmark.Grindset.Attr",
    "Benchmark.Grindset.Core",
    "Benchmark.Grindset.Monad",
    "Benchmark.Grindset.Reach",
)


def declared_lean_toolchain() -> str:
    """Return the exact repository toolchain used by every setup command."""
    path = ROOT / "lean-toolchain"
    value = path.read_text(encoding="utf-8").strip()
    if not value or any(char.isspace() for char in value):
        raise RuntimeError(f"invalid lean-toolchain declaration: {value!r}")
    return value


def toolchain_command(program: str, *args: str) -> list[str]:
    """Run a Lean tool through the declared Elan toolchain, never host default."""
    return ["elan", "run", "--install", declared_lean_toolchain(), program, *args]


def toolchain_environment() -> dict[str, str]:
    env = os.environ.copy()
    # A workspace-level override must not silently beat the repository pin.
    override = env.pop("ELAN_TOOLCHAIN", None)
    declared = declared_lean_toolchain()
    if override is not None and override != declared:
        raise RuntimeError(
            f"ELAN_TOOLCHAIN={override!r} conflicts with repository pin {declared!r}"
        )
    return env


def _validate_effective_toolchain(
    log_path: Path, *, timeout_seconds: int
) -> dict[str, object]:
    """Validate the pinned toolchain within the enclosing warm budget.

    ``elan run --install`` may download a missing pinned toolchain, so this
    required preflight must use the same bounded cold-install allowance as the
    dependency warm phase rather than a separate short validation cap.
    """
    expected = declared_lean_toolchain().rsplit(":v", 1)[-1]
    command = toolchain_command("lean", "--version")
    started = time.monotonic()
    try:
        completed = subprocess.run(
            command,
            cwd=ROOT,
            env=toolchain_environment(),
            capture_output=True,
            text=True,
            timeout=timeout_seconds,
            check=False,
        )
        output = (completed.stdout + completed.stderr).strip()
        exit_code = completed.returncode
    except subprocess.TimeoutExpired:
        output = (
            f"toolchain validation timed out after {timeout_seconds} seconds "
            f"while running {' '.join(command)}"
        )
        exit_code = 124
    except (OSError, RuntimeError) as exc:
        output = str(exc)
        exit_code = 127
    matched = exit_code == 0 and f"version {expected}" in output
    status = "passed" if matched else "timeout" if exit_code == 124 else "failed"
    return {
        "kind": "lean_toolchain",
        "required": True,
        "status": status,
        "exit_code": 0 if matched else exit_code or 1,
        "duration_seconds": round(time.monotonic() - started, 3),
        "declared_toolchain": declared_lean_toolchain(),
        "effective_version": output.splitlines()[0] if output else "",
        "command": command,
        "log_path": str(log_path),
    }


def _invalid_package_checkouts() -> list[str]:
    packages = ROOT / ".lake" / "packages"
    if not packages.is_dir():
        return []
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    manifest_packages = {
        package["name"]
        for package in manifest.get("packages", [])
        if isinstance(package, dict) and isinstance(package.get("name"), str)
    }
    invalid = []
    for package in sorted(packages.iterdir()):
        if not package.is_dir() or package.name not in manifest_packages:
            continue
        try:
            top_level = subprocess.run(
                ["git", "-C", str(package), "rev-parse", "--show-toplevel"],
                env=toolchain_environment(),
                capture_output=True,
                text=True,
                timeout=10,
                check=False,
            )
            head = subprocess.run(
                ["git", "-C", str(package), "rev-parse", "--verify", "HEAD"],
                env=toolchain_environment(),
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                timeout=10,
                check=False,
            )
            owns_worktree = (
                top_level.returncode == 0
                and Path(top_level.stdout.strip()).resolve() == package.resolve()
            )
        except (OSError, subprocess.TimeoutExpired):
            owns_worktree = False
            head = None
        if not owns_worktree or head is None or head.returncode != 0:
            invalid.append(package.name)
    return invalid


def _wait_for_package_checkouts(log_path: Path) -> dict[str, object]:
    """Wait out a concurrent Lake checkout instead of observing partial Git state."""
    timeout = float(os.environ.get("VERITY_PACKAGE_CHECKOUT_TIMEOUT_SECONDS", "180"))
    started = time.monotonic()
    invalid = _invalid_package_checkouts()
    while invalid and time.monotonic() - started < timeout:
        time.sleep(1)
        invalid = _invalid_package_checkouts()
    return {
        "kind": "package_checkout_health",
        "required": True,
        "status": "passed" if not invalid else "failed",
        "exit_code": 0 if not invalid else 1,
        "duration_seconds": round(time.monotonic() - started, 3),
        "invalid_packages": invalid,
        "log_path": str(log_path),
    }


def warm_result_failed(item: dict[str, object]) -> bool:
    """Return whether a required warm step failed."""
    return item.get("required", True) is not False and item.get("exit_code") != 0


def _mathlib_cache_fingerprint() -> str:
    digest = hashlib.sha256()
    for name in ("lean-toolchain", "lake-manifest.json"):
        path = ROOT / name
        if path.is_file():
            digest.update(name.encode())
            digest.update(path.read_bytes())
    return digest.hexdigest()[:20]


def _prefetch_mathlib_cache(
    *, timeout_seconds: int, log, log_path: Path, heartbeat_seconds: float
) -> dict[str, object]:
    """Best-effort Mathlib binary-cache fetch before source compilation."""
    sentinel = ROOT / ".lake" / f".verity-mathlib-cache-{_mathlib_cache_fingerprint()}"
    if sentinel.is_file():
        print("[dependency-warm] cache=mathlib state=cached", flush=True)
        return {
            "kind": "mathlib_cache",
            "required": False,
            "status": "cached",
            "exit_code": 0,
            "duration_seconds": 0.0,
            "log_path": str(log_path),
        }

    queued_at = time.monotonic()
    print("[dependency-warm] cache=mathlib state=waiting_for_lease", flush=True)
    with verify_lease(label="dependency_cache_get") as lease_reason:
        if sentinel.is_file():
            return {
                "kind": "mathlib_cache",
                "required": False,
                "status": "cached",
                "exit_code": 0,
                "duration_seconds": 0.0,
                "lease": lease_reason,
                "lease_wait_seconds": round(time.monotonic() - queued_at, 3),
                "log_path": str(log_path),
            }
        started = time.monotonic()
        lease_wait_seconds = round(started - queued_at, 3)
        log.write("\n$ lake exe cache get\n")
        log.flush()
        try:
            process = subprocess.Popen(
                toolchain_command("lake", "exe", "cache", "get"),
                cwd=ROOT,
                env=toolchain_environment(),
                stdout=log,
                stderr=subprocess.STDOUT,
                text=True,
                start_new_session=True,
            )
        except OSError as exc:
            duration = round(time.monotonic() - started, 3)
            log.write(f"best-effort cache prefetch could not start: {exc}\n")
            log.flush()
            return {
                "kind": "mathlib_cache",
                "required": False,
                "status": "failed",
                "exit_code": 127,
                "duration_seconds": duration,
                "lease": lease_reason,
                "lease_wait_seconds": lease_wait_seconds,
                "log_path": str(log_path),
                "error": str(exc),
            }
        timed_out = False
        try:
            while process.poll() is None:
                elapsed = time.monotonic() - started
                remaining = timeout_seconds - elapsed
                if remaining <= 0:
                    timed_out = True
                    try:
                        os.killpg(process.pid, signal.SIGTERM)
                    except ProcessLookupError:
                        pass
                    try:
                        process.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        try:
                            os.killpg(process.pid, signal.SIGKILL)
                        except ProcessLookupError:
                            pass
                        process.wait()
                    break
                try:
                    process.wait(timeout=min(heartbeat_seconds, remaining))
                except subprocess.TimeoutExpired:
                    print(
                        f"[dependency-warm] cache=mathlib state=running elapsed_seconds={int(elapsed)}",
                        flush=True,
                    )
        except BaseException:
            if process.poll() is None:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                process.wait()
            raise

        duration = round(time.monotonic() - started, 3)
        exit_code = 124 if timed_out else int(process.returncode or 0)
        status = "timeout" if timed_out else "passed" if exit_code == 0 else "failed"
        if exit_code == 0:
            sentinel.parent.mkdir(parents=True, exist_ok=True)
            sentinel.write_text("ok\n", encoding="utf-8")
        print(
            f"[dependency-warm] cache=mathlib state={status} exit_code={exit_code} "
            f"duration_seconds={duration}",
            flush=True,
        )
        return {
            "kind": "mathlib_cache",
            "required": False,
            "status": status,
            "exit_code": exit_code,
            "duration_seconds": duration,
            "lease": lease_reason,
            "lease_wait_seconds": lease_wait_seconds,
            "log_path": str(log_path),
        }


def public_dependency_modules(group: Group) -> list[str]:
    """Return public, non-editable Lean modules worth warming once at repo scope."""
    modules: set[str] = set(PUBLIC_WORKSPACE_GRINDSET_MODULES)
    for task in group.tasks:
        for rel_path in (*task.implementation_files, *task.specification_files):
            path = Path(rel_path)
            if path.suffix != ".lean":
                continue
            if "Proofs.lean" in rel_path or "GeneratedPreview" in path.parts:
                raise ValueError(f"refusing to warm forbidden dependency {rel_path}")
            # The configured Lean library is rooted at Benchmark/. Lower-case
            # cases/** files are translation/context inputs, not Lake targets.
            if not path.parts or path.parts[0] != "Benchmark":
                continue
            modules.add(".".join(path.with_suffix("").parts))
    return sorted(modules)


def warm_public_dependencies(
    group: Group,
    *,
    timeout_seconds: int,
    log_path: Path,
    heartbeat_seconds: float = 10.0,
) -> list[dict[str, object]]:
    """Warm public implementation/spec modules in the persistent repo cache.

    Workspaces clone ``ROOT/.lake/build`` after this step, so repeated task
    runs do not recompile the same dependency graph. Output stays in a durable
    log while concise heartbeats make long cold builds externally observable.
    """
    log_path.parent.mkdir(parents=True, exist_ok=True)
    results: list[dict[str, object]] = []
    with log_path.open("a", encoding="utf-8") as log:
        toolchain_result = _validate_effective_toolchain(
            log_path, timeout_seconds=timeout_seconds
        )
        results.append(toolchain_result)
        log.write(
            "$ " + " ".join(toolchain_result["command"]) + "\n"
            + str(toolchain_result["effective_version"]) + "\n"
        )
        log.flush()
        if warm_result_failed(toolchain_result):
            print(
                f"[dependency-warm] toolchain state={toolchain_result['status']} "
                f"declared={toolchain_result['declared_toolchain']} "
                f"exit_code={toolchain_result['exit_code']}",
                flush=True,
            )
            return results
        cache_timeout = min(
            timeout_seconds,
            int(os.environ.get("VERITY_CACHE_GET_TIMEOUT_SECONDS", "1800")),
        )
        results.append(
            _prefetch_mathlib_cache(
                timeout_seconds=cache_timeout,
                log=log,
                log_path=log_path,
                heartbeat_seconds=heartbeat_seconds,
            )
        )
        for module in public_dependency_modules(group):
            queued_at = time.monotonic()
            print(f"[dependency-warm] module={module} state=waiting_for_lease", flush=True)
            log.write(f"\n$ lake build {module}\n")
            log.flush()
            timed_out = False
            with verify_lease(label="dependency_warm") as lease_reason:
                # Cache hydration shares this lease. Validate again after acquiring
                # it so another warmer cannot leave a partial checkout between the
                # earlier health check and this required build.
                checkout_result = _wait_for_package_checkouts(log_path)
                results.append(checkout_result)
                if warm_result_failed(checkout_result):
                    log.write(
                        "invalid package checkouts: "
                        + ", ".join(checkout_result["invalid_packages"])
                        + "\n"
                    )
                    log.flush()
                    print(
                        "[dependency-warm] package_checkout state=failed invalid="
                        + ",".join(checkout_result["invalid_packages"]),
                        flush=True,
                    )
                    return results
                started = time.monotonic()
                lease_wait_seconds = round(started - queued_at, 3)
                print(
                    f"[dependency-warm] module={module} state=starting "
                    f"lease={lease_reason} lease_wait_seconds={lease_wait_seconds}",
                    flush=True,
                )
                try:
                    process = subprocess.Popen(
                        toolchain_command("lake", "build", module),
                        cwd=ROOT,
                        env=toolchain_environment(),
                        stdout=log,
                        stderr=subprocess.STDOUT,
                        text=True,
                        start_new_session=True,
                    )
                except OSError as exc:
                    duration = round(time.monotonic() - started, 3)
                    message = f"failed to start lake build: {exc}"
                    log.write(f"{message}\n")
                    log.flush()
                    print(
                        f"[dependency-warm] module={module} state=failed "
                        f"exit_code=127 duration_seconds={duration}",
                        flush=True,
                    )
                    results.append(
                        {
                            "module": module,
                            "status": "failed",
                            "exit_code": 127,
                            "duration_seconds": duration,
                            "lease": lease_reason,
                            "lease_wait_seconds": lease_wait_seconds,
                            "log_path": str(log_path),
                            "error": message,
                        }
                    )
                    break
                try:
                    while process.poll() is None:
                        elapsed = time.monotonic() - started
                        remaining = timeout_seconds - elapsed
                        if remaining <= 0:
                            timed_out = True
                            try:
                                os.killpg(process.pid, signal.SIGTERM)
                            except ProcessLookupError:
                                pass
                            try:
                                process.wait(timeout=5)
                            except subprocess.TimeoutExpired:
                                try:
                                    os.killpg(process.pid, signal.SIGKILL)
                                except ProcessLookupError:
                                    pass
                                process.wait()
                            break
                        try:
                            process.wait(timeout=min(heartbeat_seconds, remaining))
                        except subprocess.TimeoutExpired:
                            print(
                                f"[dependency-warm] module={module} state=running elapsed_seconds={int(elapsed)}",
                                flush=True,
                            )
                except BaseException:
                    if process.poll() is None:
                        try:
                            os.killpg(process.pid, signal.SIGTERM)
                        except ProcessLookupError:
                            pass
                        try:
                            process.wait(timeout=5)
                        except subprocess.TimeoutExpired:
                            try:
                                os.killpg(process.pid, signal.SIGKILL)
                            except ProcessLookupError:
                                pass
                            process.wait()
                    raise
            duration = round(time.monotonic() - started, 3)
            exit_code = 124 if timed_out else int(process.returncode or 0)
            status = "timeout" if timed_out else "passed" if exit_code == 0 else "failed"
            print(
                f"[dependency-warm] module={module} state={status} exit_code={exit_code} "
                f"duration_seconds={duration}",
                flush=True,
            )
            results.append(
                {
                    "module": module,
                    "status": status,
                    "exit_code": exit_code,
                    "duration_seconds": duration,
                    "lease": lease_reason,
                    "lease_wait_seconds": lease_wait_seconds,
                    "log_path": str(log_path),
                }
            )
            if exit_code != 0:
                break
    return results


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
    if dst.exists():
        shutil.rmtree(dst)
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
        # Dependency warms mutate the shared repo build cache under this same
        # lease. Reacquire it for the complete clone so another runner cannot
        # change the source tree halfway through our copy and produce a mixed
        # workspace cache.
        with verify_lease(label="dependency_cache_clone"):
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

    dependency_cache = setup_private_lake(workspace, prune_to_sources=True)

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

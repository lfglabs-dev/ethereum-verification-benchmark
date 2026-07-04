#!/usr/bin/env python3
import argparse
import hashlib
import json
import re
import shutil
import subprocess
import sys
import tarfile
from pathlib import Path

from release_config import GITHUB_REPO_URL


def slug(value: str) -> str:
    value = value.strip().lower()
    value = re.sub(r"[^a-z0-9]+", "-", value)
    return value.strip("-") or "unknown"


def load_json(path: Path) -> dict:
    try:
        return json.loads(path.read_text())
    except Exception:
        return {}


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def selected_run_ids_by_model(results_manifest: dict) -> dict[str, set[str]]:
    """Return selected run/artifact ids indexed by the published result manifest."""
    selected: dict[str, set[str]] = {}
    for model in results_manifest.get("models", []):
        if not isinstance(model, dict):
            continue
        model_id = model.get("model_id")
        if not isinstance(model_id, str) or not model_id:
            continue
        run_ids: set[str] = set()
        for task in model.get("task_results", []):
            if not isinstance(task, dict):
                continue
            run_id = task.get("run_id") or task.get("artifact_id")
            if isinstance(run_id, str) and run_id:
                run_ids.add(run_id)
        selected[model_id] = run_ids
    return selected


def filter_dirs_by_result_manifest(
    by_model: dict[str, list[Path]],
    results_manifest: dict,
) -> tuple[dict[str, list[Path]], list[str]]:
    """Keep only selected manifest artifacts and fail closed on missing run directories."""
    selected = selected_run_ids_by_model(results_manifest)
    filtered: dict[str, list[Path]] = {}
    errors: list[str] = []
    for model, run_ids in sorted(selected.items()):
        dirs_by_id = {path.name: path for path in by_model.get(model, [])}
        missing = sorted(run_id for run_id in run_ids if run_id not in dirs_by_id)
        if missing:
            for run_id in missing:
                errors.append(f"{model}: selected manifest run_id is missing from runs-dir: {run_id}")
        filtered[model] = [dirs_by_id[run_id] for run_id in sorted(run_ids) if run_id in dirs_by_id]
    return filtered, errors


def run_zstd_tar(output: Path, rel_dirs: list[str], cwd: Path, compression_level: int) -> None:
    list_file = output.with_suffix(output.suffix + ".files")
    list_file.write_text("".join(f"{name}\n" for name in rel_dirs))
    try:
        subprocess.run(
            [
                "tar",
                "--use-compress-program",
                f"zstd -T0 -{compression_level}",
                "-cf",
                str(output),
                "-C",
                str(cwd),
                "--files-from",
                str(list_file),
            ],
            check=True,
        )
    finally:
        list_file.unlink(missing_ok=True)


def tarfile_fallback(output: Path, rel_dirs: list[str], cwd: Path) -> None:
    gzip_output = output.with_suffix(".tar.gz")
    with tarfile.open(gzip_output, "w:gz") as tf:
        for rel_dir in rel_dirs:
            tf.add(cwd / rel_dir, arcname=rel_dir)
    output.unlink(missing_ok=True)
    gzip_output.rename(output.with_suffix(".tar.gz"))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--runs-dir", type=Path, default=Path("results/runs"))
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument(
        "--results-manifest",
        type=Path,
        help="optional published result manifest; package exactly its selected run_ids and fail if any are missing",
    )
    parser.add_argument("--tag", default="v0.1")
    parser.add_argument("--compression-level", type=int, default=10)
    args = parser.parse_args()

    runs_dir = args.runs_dir.resolve()
    out_dir = args.out_dir.resolve()
    archives_dir = out_dir / "archives"
    archives_dir.mkdir(parents=True, exist_ok=True)

    by_model: dict[str, list[Path]] = {}
    skipped: list[str] = []
    for run_dir in sorted(p for p in runs_dir.iterdir() if p.is_dir()):
        data = load_json(run_dir / "run.json")
        model = data.get("model")
        if not isinstance(model, str) or not model:
            skipped.append(run_dir.name)
            continue
        by_model.setdefault(model, []).append(run_dir)

    selected_by_manifest = False
    if args.results_manifest:
        selected_by_manifest = True
        results_manifest = load_json(args.results_manifest)
        if not isinstance(results_manifest.get("models"), list):
            print(f"error: results manifest has no models array: {args.results_manifest}", file=sys.stderr)
            return 1
        by_model, selection_errors = filter_dirs_by_result_manifest(by_model, results_manifest)
        if selection_errors:
            for error in selection_errors:
                print(f"error: {error}", file=sys.stderr)
            return 1

    manifest = {
        "schema_version": 1,
        "tag": args.tag,
        "repository_url": GITHUB_REPO_URL,
        "runs_dir": str(runs_dir),
        "selected_by_results_manifest": selected_by_manifest,
        "archives": [],
        "skipped_without_model": skipped,
    }

    for model, dirs in sorted(by_model.items()):
        model_slug = slug(model)
        archive = archives_dir / f"benchmark-{args.tag}-{model_slug}.tar.zst"
        rel_dirs = [str(p.relative_to(runs_dir.parent)) for p in dirs]

        archive.unlink(missing_ok=True)
        if shutil.which("zstd"):
            run_zstd_tar(archive, rel_dirs, runs_dir.parent, args.compression_level)
            final_archive = archive
        else:
            tarfile_fallback(archive, rel_dirs, runs_dir.parent)
            final_archive = archive.with_suffix(".tar.gz")

        total_prompt = 0
        total_completion = 0
        total_requests = 0
        nonzero_usage = 0
        completed = 0
        passed = 0
        failed = 0
        errored = 0
        tasks = []

        for run_dir in dirs:
            data = load_json(run_dir / "run.json")
            usage = data.get("usage") if isinstance(data.get("usage"), dict) else {}
            prompt = int(usage.get("prompt_tokens") or 0)
            completion = int(usage.get("completion_tokens") or 0)
            requests = int(usage.get("requests") or 0)
            total_prompt += prompt
            total_completion += completion
            total_requests += requests
            if prompt > 0 or completion > 0 or requests > 0:
                nonzero_usage += 1
            if data.get("harness_status") == "completed":
                completed += 1

            score = (((data.get("verifier") or {}).get("score") or {}))
            earned = score.get("points_earned")
            possible = score.get("points_possible")
            is_pass = isinstance(earned, (int, float)) and isinstance(possible, (int, float)) and possible > 0 and earned >= possible
            if is_pass:
                passed += 1
            elif data.get("harness_status") == "completed" and possible:
                failed += 1
            elif data.get("harness_status") not in (None, "completed"):
                errored += 1

            tasks.append(
                {
                    "run_id": data.get("run_id") or run_dir.name,
                    "task_ref": data.get("task_ref"),
                    "group_id": data.get("group_id"),
                    "harness_status": data.get("harness_status"),
                    "passed": is_pass,
                    "prompt_tokens": prompt,
                    "completion_tokens": completion,
                    "requests": requests,
                }
            )

        manifest["archives"].append(
            {
                "model": model,
                "archive": str(final_archive.relative_to(out_dir)),
                "sha256": sha256(final_archive),
                "bytes": final_archive.stat().st_size,
                "run_dirs": len(dirs),
                "run_ids": sorted(str(task["run_id"]) for task in tasks if task.get("run_id")),
                "completed": completed,
                "nonzero_usage": nonzero_usage,
                "passed": passed,
                "failed": failed,
                "errored_or_incomplete": errored + (len(dirs) - completed),
                "prompt_tokens": total_prompt,
                "completion_tokens": total_completion,
                "requests": total_requests,
                "tasks": tasks,
            }
        )

    manifest_path = out_dir / f"benchmark-{args.tag}-artifacts-manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(manifest_path)
    for item in manifest["archives"]:
        print(f"{item['model']}: {item['run_dirs']} dirs -> {item['archive']} ({item['bytes']} bytes)")
    return 0


if __name__ == "__main__":
    sys.exit(main())

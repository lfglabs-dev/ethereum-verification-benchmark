#!/usr/bin/env python3
"""Build coverage-aware task clustering artifacts from a version manifest.

The script intentionally uses only the Python standard library. It produces
SVGs directly so the analysis is reproducible in the benchmark repo without a
scientific Python stack.
"""

from __future__ import annotations

import argparse
import csv
import html
import json
import math
from collections import Counter, defaultdict
from pathlib import Path


PASS = 1.0
FAIL = 0.0
MISSING = None


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", default="results/manifests/v0.1.json")
    parser.add_argument("--taxonomy", default="analysis/task_taxonomy.json")
    parser.add_argument("--matrix", default="analysis/model_task_matrix.csv")
    parser.add_argument("--features", default="analysis/task_features.json")
    parser.add_argument("--out-dir", default="analysis/task_map")
    parser.add_argument("--min-task-coverage", type=int, default=4)
    parser.add_argument("--cluster-count", type=int, default=8)
    return parser.parse_args()


def read_manifest(path: Path) -> dict:
    return json.loads(path.read_text())


def read_taxonomy(path: Path) -> dict[str, dict]:
    if not path.exists():
        return {}
    data = json.loads(path.read_text())
    labels = data.get("labels", [])
    return {row["task_ref"]: row for row in labels}


def read_matrix_metadata(path: Path) -> dict[str, dict]:
    if not path.exists():
        return {}
    metadata: dict[str, dict] = {}
    with path.open(newline="") as f:
        reader = csv.DictReader(f)
        for row in reader:
            metadata[row["task_ref"]] = row
    return metadata


def read_feature_metadata(path: Path) -> dict[str, dict]:
    if not path.exists():
        return {}
    data = json.loads(path.read_text())
    cohort = data.get("cohort", [])
    metadata = {}
    for row in data.get("tasks", []):
        signature = ""
        per_model = row.get("per_model", {})
        for model_id in cohort:
            value = per_model.get(model_id, {})
            if "passed" not in value:
                signature += "?"
            else:
                signature += "P" if value.get("passed") else "F"
        metadata[row["task_ref"]] = {
            "cohort": cohort,
            "cohort_signature": signature or None,
            "cohort_pass_rate": row.get("cohort_pass_rate"),
            "divisiveness": row.get("divisiveness"),
            "category": row.get("category"),
        }
    return metadata


def build_matrix(manifest: dict) -> tuple[list[str], list[str], dict[str, dict[str, float | None]], dict[str, dict]]:
    task_refs = sorted(
        {
            result["task_ref"]
            for model in manifest["models"]
            for result in model.get("task_results", [])
        }
    )
    model_ids = [model["model_id"] for model in manifest["models"]]
    by_task = {task_ref: {model_id: MISSING for model_id in model_ids} for task_ref in task_refs}
    model_meta = {}
    for model in manifest["models"]:
        model_id = model["model_id"]
        model_meta[model_id] = {
            "display_name": model.get("display_name", model_id),
            "task_count": model.get("task_count", 0),
            "passed": model.get("passed", 0),
            "failed": model.get("failed", 0),
            "status": model.get("status", "unknown"),
        }
        for result in model.get("task_results", []):
            by_task[result["task_ref"]][model_id] = PASS if result.get("passed") else FAIL
    return task_refs, model_ids, by_task, model_meta


def observed(values: dict[str, float | None]) -> list[float]:
    return [v for v in values.values() if v is not None]


def task_distance(a: dict[str, float | None], b: dict[str, float | None]) -> float:
    overlap = [m for m in a if a[m] is not None and b[m] is not None]
    if not overlap:
        return 1.0
    mismatches = sum(1 for m in overlap if a[m] != b[m])
    # Downweight very small overlaps so partial-model coincidences do not dominate.
    coverage_penalty = 1.0 - min(1.0, len(overlap) / max(6, len(a)))
    return min(1.0, mismatches / len(overlap) + 0.35 * coverage_penalty)


def distance_matrix(task_refs: list[str], by_task: dict[str, dict[str, float | None]]) -> list[list[float]]:
    matrix: list[list[float]] = []
    for task_a in task_refs:
        row = []
        for task_b in task_refs:
            row.append(0.0 if task_a == task_b else task_distance(by_task[task_a], by_task[task_b]))
        matrix.append(row)
    return matrix


def mat_vec_mul(matrix: list[list[float]], vector: list[float]) -> list[float]:
    return [sum(a * b for a, b in zip(row, vector)) for row in matrix]


def dot(a: list[float], b: list[float]) -> float:
    return sum(x * y for x, y in zip(a, b))


def norm(vector: list[float]) -> float:
    return math.sqrt(max(0.0, dot(vector, vector)))


def top_eigenpair(matrix: list[list[float]], seed: int) -> tuple[float, list[float]]:
    n = len(matrix)
    vector = [math.sin((i + 1) * (seed + 1)) + 0.3 * math.cos((i + 3) * (seed + 2)) for i in range(n)]
    length = norm(vector) or 1.0
    vector = [x / length for x in vector]
    for _ in range(250):
        nxt = mat_vec_mul(matrix, vector)
        length = norm(nxt)
        if length < 1e-12:
            break
        nxt = [x / length for x in nxt]
        if norm([a - b for a, b in zip(nxt, vector)]) < 1e-10:
            vector = nxt
            break
        vector = nxt
    mv = mat_vec_mul(matrix, vector)
    eigenvalue = dot(vector, mv)
    return eigenvalue, vector


def classical_mds(distances: list[list[float]], dimensions: int = 2) -> tuple[list[tuple[float, float]], list[float]]:
    n = len(distances)
    if n == 0:
        return [], []
    d2 = [[distances[i][j] ** 2 for j in range(n)] for i in range(n)]
    row_mean = [sum(row) / n for row in d2]
    col_mean = [sum(d2[i][j] for i in range(n)) / n for j in range(n)]
    total_mean = sum(row_mean) / n
    gram = [
        [-0.5 * (d2[i][j] - row_mean[i] - col_mean[j] + total_mean) for j in range(n)]
        for i in range(n)
    ]
    working = [row[:] for row in gram]
    axes: list[list[float]] = []
    eigenvalues: list[float] = []
    for axis in range(dimensions):
        value, vector = top_eigenpair(working, axis)
        if value <= 1e-12:
            axes.append([0.0] * n)
            eigenvalues.append(0.0)
            continue
        scale = math.sqrt(value)
        axes.append([scale * x for x in vector])
        eigenvalues.append(value)
        for i in range(n):
            for j in range(n):
                working[i][j] -= value * vector[i] * vector[j]
    coords = list(zip(axes[0], axes[1] if len(axes) > 1 else [0.0] * n))
    total_positive = sum(max(0.0, v) for v in eigenvalues) or 1.0
    explained = [max(0.0, v) / total_positive for v in eigenvalues]
    return coords, explained


def agglomerative_clusters(task_refs: list[str], distances: list[list[float]], k: int) -> tuple[dict[str, int], list[str]]:
    n = len(task_refs)
    clusters: dict[int, list[int]] = {i: [i] for i in range(n)}
    next_id = n
    while len(clusters) > max(1, k):
        ids = list(clusters)
        best_pair = None
        best_distance = float("inf")
        for pos, a in enumerate(ids):
            for b in ids[pos + 1 :]:
                pairs = [(i, j) for i in clusters[a] for j in clusters[b]]
                dist = sum(distances[i][j] for i, j in pairs) / len(pairs)
                if dist < best_distance:
                    best_distance = dist
                    best_pair = (a, b)
        assert best_pair is not None
        a, b = best_pair
        clusters[next_id] = clusters.pop(a) + clusters.pop(b)
        next_id += 1
    sorted_clusters = sorted(clusters.values(), key=lambda rows: (len(rows), min(rows)), reverse=True)
    assignment = {}
    order = []
    for cluster_id, rows in enumerate(sorted_clusters, start=1):
        rows_sorted = sorted(rows, key=lambda i: task_refs[i])
        for i in rows_sorted:
            assignment[task_refs[i]] = cluster_id
            order.append(task_refs[i])
    return assignment, order


def task_stats(task_ref: str, values: dict[str, float | None]) -> dict:
    seen = observed(values)
    passes = sum(1 for v in seen if v == PASS)
    fails = sum(1 for v in seen if v == FAIL)
    attempts = len(seen)
    pass_rate = passes / attempts if attempts else 0.0
    return {
        "task_ref": task_ref,
        "attempts": attempts,
        "passes": passes,
        "fails": fails,
        "pass_rate": pass_rate,
        "difficulty": 1.0 - pass_rate,
    }


def category_for(task_ref: str, taxonomy: dict[str, dict], matrix_meta: dict[str, dict]) -> tuple[str, str]:
    row = taxonomy.get(task_ref) or matrix_meta.get(task_ref) or {}
    proof = row.get("proof_family") or "unknown"
    prop = row.get("property_class") or "unknown"
    return proof, prop


def color_for_property(prop: str) -> str:
    palette = [
        "#3b82f6",
        "#ef4444",
        "#22c55e",
        "#f59e0b",
        "#8b5cf6",
        "#06b6d4",
        "#ec4899",
        "#64748b",
        "#84cc16",
        "#f97316",
    ]
    return palette[abs(hash(prop)) % len(palette)]


def scale_points(coords: list[tuple[float, float]], width: int, height: int, margin: int) -> list[tuple[float, float]]:
    if not coords:
        return []
    xs, ys = zip(*coords)
    min_x, max_x = min(xs), max(xs)
    min_y, max_y = min(ys), max(ys)
    span_x = max(max_x - min_x, 1e-9)
    span_y = max(max_y - min_y, 1e-9)
    return [
        (
            margin + (x - min_x) / span_x * (width - 2 * margin),
            height - margin - (y - min_y) / span_y * (height - 2 * margin),
        )
        for x, y in coords
    ]


def write_task_map_svg(path: Path, rows: list[dict], explained: list[float]) -> None:
    width, height, margin = 1200, 850, 70
    points = scale_points([(r["x"], r["y"]) for r in rows], width, height, margin)
    props = sorted({r["property_class"] for r in rows})
    legend_x = width - 330
    legend_y = 35
    parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">',
        '<rect width="100%" height="100%" fill="#ffffff"/>',
        f'<text x="40" y="38" font-family="Arial" font-size="24" font-weight="700">Task map by model pass/fail profile</text>',
        f'<text x="40" y="66" font-family="Arial" font-size="13" fill="#475569">MDS over coverage-aware Hamming distances. Axis shares: x={explained[0]:.0%}, y={explained[1]:.0%}. Dot size = failure rate.</text>',
        f'<line x1="{margin}" y1="{height-margin}" x2="{width-margin}" y2="{height-margin}" stroke="#cbd5e1"/>',
        f'<line x1="{margin}" y1="{margin}" x2="{margin}" y2="{height-margin}" stroke="#cbd5e1"/>',
        f'<text x="{width/2-80:.0f}" y="{height-20}" font-family="Arial" font-size="13" fill="#334155">Axis 1: dominant difficulty / solvability contrast</text>',
        f'<text transform="translate(22 {height/2+110:.0f}) rotate(-90)" font-family="Arial" font-size="13" fill="#334155">Axis 2: model-specialization contrast</text>',
    ]
    for row, (x, y) in zip(rows, points):
        radius = 4 + 10 * row["difficulty"]
        color = color_for_property(row["property_class"])
        title = (
            f'{row["task_ref"]}\\n'
            f'property={row["property_class"]}\\n'
            f'proof={row["proof_family"]}\\n'
            f'cluster={row["cluster"]}, pass_rate={row["pass_rate"]:.2f}, attempts={row["attempts"]}'
        )
        parts.append(f'<circle cx="{x:.1f}" cy="{y:.1f}" r="{radius:.1f}" fill="{color}" fill-opacity="0.72" stroke="#0f172a" stroke-opacity="0.25"><title>{html.escape(title)}</title></circle>')
    label_rows = sorted(rows, key=lambda r: (r["difficulty"], r["attempts"]), reverse=True)[:12]
    label_refs = {r["task_ref"] for r in label_rows}
    for row, (x, y) in zip(rows, points):
        if row["task_ref"] not in label_refs:
            continue
        label = row["task_ref"].split("/")[-1]
        parts.append(f'<text x="{x+8:.1f}" y="{y-8:.1f}" font-family="Arial" font-size="10" fill="#111827">{html.escape(label)}</text>')
    parts.append(f'<rect x="{legend_x-16}" y="{legend_y-24}" width="310" height="{min(390, 32+20*len(props))}" fill="#f8fafc" stroke="#e2e8f0"/>')
    parts.append(f'<text x="{legend_x}" y="{legend_y}" font-family="Arial" font-size="13" font-weight="700">Property class</text>')
    for i, prop in enumerate(props[:16]):
        y = legend_y + 24 + 20 * i
        parts.append(f'<circle cx="{legend_x+6}" cy="{y-4}" r="6" fill="{color_for_property(prop)}" fill-opacity="0.75"/>')
        parts.append(f'<text x="{legend_x+20}" y="{y}" font-family="Arial" font-size="11" fill="#334155">{html.escape(prop)}</text>')
    parts.append("</svg>")
    path.write_text("\n".join(parts) + "\n")


def write_heatmap_svg(path: Path, order: list[str], model_ids: list[str], by_task: dict[str, dict[str, float | None]], rows_by_ref: dict[str, dict]) -> None:
    cell = 14
    left = 430
    top = 145
    width = left + cell * len(model_ids) + 260
    height = top + cell * len(order) + 60
    parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">',
        '<rect width="100%" height="100%" fill="#ffffff"/>',
        '<text x="35" y="36" font-family="Arial" font-size="24" font-weight="700">Clustered task-model pass/fail heatmap</text>',
        '<text x="35" y="64" font-family="Arial" font-size="13" fill="#475569">Rows are clustered by behavior. Green=pass, red=fail, gray=missing/no artifact.</text>',
    ]
    for j, model in enumerate(model_ids):
        x = left + j * cell + 10
        label = model.replace("virtuals/", "v/").replace("openai-", "oai-")
        parts.append(f'<text transform="translate({x} {top-10}) rotate(-60)" font-family="Arial" font-size="10" fill="#334155">{html.escape(label)}</text>')
    last_cluster = None
    for i, task_ref in enumerate(order):
        y = top + i * cell
        row = rows_by_ref[task_ref]
        if row["cluster"] != last_cluster:
            parts.append(f'<line x1="24" y1="{y}" x2="{width-24}" y2="{y}" stroke="#94a3b8" stroke-width="1"/>')
            parts.append(f'<text x="35" y="{y+11}" font-family="Arial" font-size="10" font-weight="700" fill="#0f172a">C{row["cluster"]}</text>')
            last_cluster = row["cluster"]
        label = task_ref if len(task_ref) <= 54 else "..." + task_ref[-51:]
        parts.append(f'<text x="70" y="{y+11}" font-family="Arial" font-size="10" fill="#334155">{html.escape(label)}</text>')
        parts.append(f'<rect x="{left-24}" y="{y+2}" width="12" height="10" fill="{color_for_property(row["property_class"])}" fill-opacity="0.8"><title>{html.escape(row["property_class"])}</title></rect>')
        for j, model in enumerate(model_ids):
            value = by_task[task_ref].get(model)
            color = "#16a34a" if value == PASS else "#dc2626" if value == FAIL else "#e2e8f0"
            parts.append(f'<rect x="{left + j * cell}" y="{y}" width="{cell-1}" height="{cell-1}" fill="{color}"><title>{html.escape(task_ref)} / {html.escape(model)}</title></rect>')
    legend_x = left + cell * len(model_ids) + 40
    for idx, (label, color) in enumerate([("pass", "#16a34a"), ("fail", "#dc2626"), ("missing", "#e2e8f0")]):
        y = top + 24 * idx
        parts.append(f'<rect x="{legend_x}" y="{y}" width="14" height="14" fill="{color}"/>')
        parts.append(f'<text x="{legend_x+22}" y="{y+12}" font-family="Arial" font-size="12" fill="#334155">{label}</text>')
    parts.append("</svg>")
    path.write_text("\n".join(parts) + "\n")


def cluster_summaries(rows: list[dict]) -> list[dict]:
    grouped: dict[int, list[dict]] = defaultdict(list)
    for row in rows:
        grouped[row["cluster"]].append(row)
    summaries = []
    for cluster_id in sorted(grouped):
        items = grouped[cluster_id]
        props = Counter(item["property_class"] for item in items)
        proofs = Counter(item["proof_family"] for item in items)
        signatures = Counter(item.get("cohort_signature") or "unknown" for item in items)
        avg_pass = sum(item["pass_rate"] for item in items) / len(items)
        avg_attempts = sum(item["attempts"] for item in items) / len(items)
        summaries.append(
            {
                "cluster": cluster_id,
                "task_count": len(items),
                "avg_pass_rate": avg_pass,
                "avg_attempts": avg_attempts,
                "dominant_property_classes": props.most_common(3),
                "dominant_proof_families": proofs.most_common(3),
                "dominant_cohort_signatures": signatures.most_common(3),
                "example_tasks": [item["task_ref"] for item in sorted(items, key=lambda r: (r["difficulty"], r["task_ref"]), reverse=True)[:5]],
            }
        )
    return summaries


def write_report(path: Path, rows: list[dict], clusters: list[dict], model_meta: dict[str, dict], explained: list[float]) -> None:
    completeish = [m for m, meta in model_meta.items() if meta["task_count"] >= 80]
    partial = [m for m, meta in model_meta.items() if meta["task_count"] < 80]
    signatures = Counter(row.get("cohort_signature") or "unknown" for row in rows)
    lines = [
        "# Task Clustering Analysis",
        "",
        "Generated from `results/manifests/v0.1.json`.",
        "",
        "## Recommended Approach",
        "",
        "Use a two-layer categorization:",
        "",
        "1. Keep the human taxonomy (`proof_family`, `property_class`, skills) as the canonical explanation layer.",
        "2. Add behavior-derived clusters from the task-model pass/fail matrix as the empirical layer.",
        "",
        "The best default visualization is the SVG task map plus the clustered heatmap. The map is good for discovering axes; the heatmap is better for auditing whether the clusters are real.",
        "",
        "For current v0.1 data, the most stable empirical cluster key is the cohort signature derived from the full-coverage cohort in `analysis/task_features.json`. It is tied to that comparison cohort, so it should be shown as a behavior profile, not as a permanent taxonomy.",
        "",
        "## Axis Interpretation",
        "",
        f"- Axis 1 explains {explained[0]:.1%} of the two-axis embedding signal and mostly tracks global task difficulty.",
        f"- Axis 2 explains {explained[1]:.1%} of the two-axis embedding signal and mostly tracks model-specialization differences.",
        "- Dot size is failure rate; color is `property_class`; tooltips carry task, cluster, attempts, and pass rate.",
        "",
        "## Coverage Caveat",
        "",
        f"High-coverage models in this manifest: {', '.join(completeish) or 'none'}.",
        f"Low-coverage models are retained but distances are coverage-penalized: {', '.join(partial) or 'none'}.",
        "When the backfilled full-result manifest is regenerated, rerun this script; the cluster assignments should be treated as provisional until then.",
        "",
        "## Cohort Signatures",
        "",
        "The full-coverage cohort signature is the cleanest behavior-derived category today:",
        "",
    ]
    for signature, count in signatures.most_common():
        if signature == "unknown":
            name = "unknown coverage"
        elif set(signature) <= {"F"}:
            name = "cohort-universal hard"
        elif set(signature) <= {"P"}:
            name = "cohort-universal solved"
        elif signature.count("P") == 1:
            name = "single-model solvable"
        elif signature.count("P") == 2:
            name = "divisive 2-of-4"
        elif signature.count("F") == 1:
            name = "mostly solved, one-model gap"
        else:
            name = "mixed profile"
        lines.append(f"- `{signature}`: {count} tasks, {name}")
    lines.extend(
        [
            "",
        "## Cluster Summaries",
        "",
        ]
    )
    for cluster in clusters:
        props = ", ".join(f"{name} ({count})" for name, count in cluster["dominant_property_classes"])
        proofs = ", ".join(f"{name} ({count})" for name, count in cluster["dominant_proof_families"])
        signatures_text = ", ".join(f"{name} ({count})" for name, count in cluster["dominant_cohort_signatures"])
        examples = ", ".join(cluster["example_tasks"][:3])
        lines.extend(
            [
                f"### Cluster {cluster['cluster']}",
                "",
                f"- tasks: {cluster['task_count']}",
                f"- average pass rate: {cluster['avg_pass_rate']:.1%}",
                f"- average observed models: {cluster['avg_attempts']:.1f}",
                f"- dominant property classes: {props}",
                f"- dominant proof families: {proofs}",
                f"- dominant cohort signatures: {signatures_text}",
                f"- examples: `{examples}`",
                "",
            ]
        )
    lines.extend(
        [
            "## Method Comparison",
            "",
            "- PCA/SVD on the raw binary matrix is useful for a quick biplot, but it handles missing coverage poorly unless imputed.",
            "- Coverage-aware MDS over pairwise task distances is a better first artifact for the current partial manifest.",
            "- Hierarchical clustering plus a heatmap is the best audit view because it shows the exact pass/fail pattern behind each cluster.",
            "- UMAP/t-SNE may reveal visual neighborhoods, but should not define canonical categories because the axes are unstable and hard to explain.",
            "- Multidimensional IRT is the cleanest later statistical model once all selected models have full coverage; it can separate model ability from task difficulty and latent skill axes.",
            "",
            "## Website Data Model",
            "",
            "Expose `analysis/task_map/task_map.json` for the website. It contains task coordinates, clusters, pass rates, taxonomy labels, model coverage, and cluster summaries. Keep `results/summaries/v0.1.json` as the leaderboard input and `results/manifests/v0.1.json` as the full audit input.",
            "",
        ]
    )
    path.write_text("\n".join(lines))


def main() -> None:
    args = parse_args()
    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    manifest = read_manifest(Path(args.manifest))
    taxonomy = read_taxonomy(Path(args.taxonomy))
    matrix_meta = read_matrix_metadata(Path(args.matrix))
    feature_meta = read_feature_metadata(Path(args.features))
    all_task_refs, model_ids, by_task, model_meta = build_matrix(manifest)
    task_refs = [task_ref for task_ref in all_task_refs if len(observed(by_task[task_ref])) >= args.min_task_coverage]
    distances = distance_matrix(task_refs, by_task)
    coords, explained = classical_mds(distances, 2)
    cluster_assignments, order = agglomerative_clusters(task_refs, distances, args.cluster_count)
    rows = []
    for task_ref, (x, y) in zip(task_refs, coords):
        proof, prop = category_for(task_ref, taxonomy, matrix_meta)
        meta = {**matrix_meta.get(task_ref, {}), **feature_meta.get(task_ref, {})}
        stats = task_stats(task_ref, by_task[task_ref])
        rows.append(
            {
                **stats,
                "x": x,
                "y": y,
                "cluster": cluster_assignments[task_ref],
                "proof_family": proof,
                "property_class": prop,
                "cohort_signature": meta.get("cohort_signature"),
                "cohort_pass_rate": float(meta["cohort_pass_rate"]) if meta.get("cohort_pass_rate") not in (None, "") else None,
                "divisiveness": float(meta["divisiveness"]) if meta.get("divisiveness") not in (None, "") else None,
            }
        )
    rows_by_ref = {row["task_ref"]: row for row in rows}
    clusters = cluster_summaries(rows)
    output = {
        "schema_version": 1,
        "benchmark_version": manifest.get("benchmark_version"),
        "source_manifest": args.manifest,
        "method": "coverage_aware_hamming_mds_average_linkage",
        "coverage": {
            "min_task_coverage": args.min_task_coverage,
            "included_tasks": len(task_refs),
            "total_tasks": len(all_task_refs),
        },
        "axis_interpretation": {
            "x": "dominant difficulty / solvability contrast",
            "y": "model-specialization contrast",
            "explained_two_axis_share": explained,
        },
        "models": model_meta,
        "tasks": sorted(rows, key=lambda r: r["task_ref"]),
        "clusters": clusters,
        "artifacts": {
            "task_map_svg": "analysis/task_map/task_map.svg",
            "heatmap_svg": "analysis/task_map/clustered_heatmap.svg",
            "report": "analysis/task_map/task_clustering_report.md",
        },
    }
    (out_dir / "task_map.json").write_text(json.dumps(output, indent=2, sort_keys=True) + "\n")
    write_task_map_svg(out_dir / "task_map.svg", rows, explained)
    write_heatmap_svg(out_dir / "clustered_heatmap.svg", order, model_ids, by_task, rows_by_ref)
    write_report(out_dir / "task_clustering_report.md", rows, clusters, model_meta, explained)


if __name__ == "__main__":
    main()

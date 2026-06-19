#!/usr/bin/env python3
"""Generate a scatter-plot gallery for task taxonomy review.

The script intentionally uses only the Python standard library so it can run in
minimal benchmark workspaces.
"""

from __future__ import annotations

import csv
import html
import json
import math
from collections import Counter, defaultdict
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ANALYSIS = ROOT / "analysis"
OUT = ANALYSIS / "taxonomy_scatter_gallery"

W = 1180
H = 820
ML = 105
MR = 285
MT = 74
MB = 92

PALETTE = [
    "#2563eb",
    "#dc2626",
    "#16a34a",
    "#9333ea",
    "#ea580c",
    "#0891b2",
    "#be123c",
    "#4f46e5",
    "#65a30d",
    "#c026d3",
    "#0f766e",
    "#a16207",
    "#7c3aed",
    "#0284c7",
    "#b91c1c",
]


def load_json(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def safe_float(value, default=None):
    if value in ("", None):
        return default
    try:
        return float(value)
    except (TypeError, ValueError):
        return default


def slug(value: str) -> str:
    return "".join(ch.lower() if ch.isalnum() else "_" for ch in value).strip("_")


def nice_label(value: str) -> str:
    return value.replace("_", " ")


def log1p_tokens(value):
    value = safe_float(value, 0.0) or 0.0
    return math.log10(max(value, 0.0) + 1.0)


def quantile(values, q):
    values = sorted(v for v in values if v is not None and math.isfinite(v))
    if not values:
        return None
    idx = (len(values) - 1) * q
    lo = math.floor(idx)
    hi = math.ceil(idx)
    if lo == hi:
        return values[lo]
    return values[lo] * (hi - idx) + values[hi] * (idx - lo)


def extent(values, pad=0.08):
    values = [v for v in values if v is not None and math.isfinite(v)]
    if not values:
        return (0.0, 1.0)
    lo, hi = min(values), max(values)
    if lo == hi:
        lo -= 1
        hi += 1
    p = (hi - lo) * pad
    return lo - p, hi + p


def color_map(values):
    ordered = [v for v, _ in Counter(values).most_common()]
    return {v: PALETTE[i % len(PALETTE)] for i, v in enumerate(ordered)}


def svg_escape(value):
    return html.escape(str(value), quote=True)


def wrap_label(value, width=28):
    words = str(value).replace("_", " ").split()
    lines = []
    cur = ""
    for word in words:
        nxt = word if not cur else f"{cur} {word}"
        if len(nxt) <= width:
            cur = nxt
        else:
            if cur:
                lines.append(cur)
            cur = word
    if cur:
        lines.append(cur)
    return lines[:3]


def render_plot(
    rows,
    *,
    filename,
    title,
    subtitle,
    x_key,
    y_key,
    color_key,
    size_key=None,
    marker_key=None,
    label_key="task_ref",
    x_label=None,
    y_label=None,
    annotate_centroids=False,
    draw_category_hulls=False,
):
    rows = [
        r
        for r in rows
        if r.get(x_key) is not None
        and r.get(y_key) is not None
        and math.isfinite(r.get(x_key))
        and math.isfinite(r.get(y_key))
    ]
    if not rows:
        return None
    x_min, x_max = extent([r[x_key] for r in rows])
    y_min, y_max = extent([r[y_key] for r in rows])
    colors = color_map([str(r.get(color_key, "unknown")) for r in rows])
    size_vals = [safe_float(r.get(size_key), 0.0) for r in rows] if size_key else []
    s_lo = quantile(size_vals, 0.05) if size_vals else 0
    s_hi = quantile(size_vals, 0.95) if size_vals else 1
    if s_lo == s_hi:
        s_hi = (s_lo or 0) + 1

    def sx(x):
        return ML + (x - x_min) / (x_max - x_min) * (W - ML - MR)

    def sy(y):
        return H - MB - (y - y_min) / (y_max - y_min) * (H - MT - MB)

    def radius(row):
        if not size_key:
            return 5.2
        v = safe_float(row.get(size_key), 0.0) or 0.0
        t = max(0.0, min(1.0, (v - s_lo) / (s_hi - s_lo)))
        return 3.5 + 8.5 * math.sqrt(t)

    def marker(row):
        if not marker_key:
            return "circle"
        value = str(row.get(marker_key, ""))
        if value in ("pass", "passed", "True", "true", "resolved"):
            return "triangle"
        if value in ("review", "needs_review", "True"):
            return "diamond"
        return "circle"

    out = []
    out.append(f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" viewBox="0 0 {W} {H}">')
    out.append("<style>")
    out.append(
        "text{font-family:Inter,Arial,sans-serif;fill:#111827}"
        ".sub{fill:#4b5563}.axis{stroke:#374151;stroke-width:1.2}"
        ".grid{stroke:#e5e7eb;stroke-width:1}.pt{stroke:#111827;stroke-width:.55;opacity:.82}"
        ".legend{font-size:12px}.tick{font-size:11px;fill:#6b7280}.cent{font-size:11px;font-weight:700}"
    )
    out.append("</style>")
    out.append('<rect width="100%" height="100%" fill="#ffffff"/>')
    out.append(f'<text x="{ML}" y="34" font-size="24" font-weight="700">{svg_escape(title)}</text>')
    out.append(f'<text x="{ML}" y="57" font-size="13" class="sub">{svg_escape(subtitle)}</text>')

    for i in range(6):
        tx = ML + i * (W - ML - MR) / 5
        ty = MT + i * (H - MT - MB) / 5
        out.append(f'<line x1="{tx:.1f}" y1="{MT}" x2="{tx:.1f}" y2="{H-MB}" class="grid"/>')
        out.append(f'<line x1="{ML}" y1="{ty:.1f}" x2="{W-MR}" y2="{ty:.1f}" class="grid"/>')
        xv = x_min + i * (x_max - x_min) / 5
        yv = y_max - i * (y_max - y_min) / 5
        out.append(f'<text x="{tx:.1f}" y="{H-MB+20}" text-anchor="middle" class="tick">{xv:.2f}</text>')
        out.append(f'<text x="{ML-12}" y="{ty+4:.1f}" text-anchor="end" class="tick">{yv:.2f}</text>')
    out.append(f'<line x1="{ML}" y1="{H-MB}" x2="{W-MR}" y2="{H-MB}" class="axis"/>')
    out.append(f'<line x1="{ML}" y1="{MT}" x2="{ML}" y2="{H-MB}" class="axis"/>')
    out.append(f'<text x="{(ML+W-MR)/2:.1f}" y="{H-34}" font-size="14" font-weight="600">{svg_escape(x_label or x_key)}</text>')
    out.append(
        f'<text transform="translate(32 {(MT+H-MB)/2:.1f}) rotate(-90)" text-anchor="middle" font-size="14" font-weight="600">{svg_escape(y_label or y_key)}</text>'
    )

    if draw_category_hulls:
        groups = defaultdict(list)
        for r in rows:
            groups[str(r.get(color_key, "unknown"))].append(r)
        for group, pts in groups.items():
            if len(pts) < 4:
                continue
            xs = [sx(r[x_key]) for r in pts]
            ys = [sy(r[y_key]) for r in pts]
            out.append(
                f'<ellipse cx="{sum(xs)/len(xs):.1f}" cy="{sum(ys)/len(ys):.1f}" '
                f'rx="{max(20, (max(xs)-min(xs))/2+18):.1f}" ry="{max(16, (max(ys)-min(ys))/2+14):.1f}" '
                f'fill="{colors[group]}" opacity=".08" stroke="{colors[group]}" stroke-width="1.2" stroke-dasharray="5 4"/>'
            )

    for row in rows:
        x = sx(row[x_key])
        y = sy(row[y_key])
        r = radius(row)
        c = colors[str(row.get(color_key, "unknown"))]
        tip = f"{row.get(label_key, '')} | {color_key}={row.get(color_key, '')} | x={row[x_key]:.3g} y={row[y_key]:.3g}"
        mk = marker(row)
        if mk == "triangle":
            pts = f"{x:.1f},{y-r:.1f} {x-r:.1f},{y+r:.1f} {x+r:.1f},{y+r:.1f}"
            out.append(f'<polygon points="{pts}" fill="{c}" class="pt"><title>{svg_escape(tip)}</title></polygon>')
        elif mk == "diamond":
            pts = f"{x:.1f},{y-r:.1f} {x-r:.1f},{y:.1f} {x:.1f},{y+r:.1f} {x+r:.1f},{y:.1f}"
            out.append(f'<polygon points="{pts}" fill="{c}" class="pt"><title>{svg_escape(tip)}</title></polygon>')
        else:
            out.append(f'<circle cx="{x:.1f}" cy="{y:.1f}" r="{r:.1f}" fill="{c}" class="pt"><title>{svg_escape(tip)}</title></circle>')

    if annotate_centroids:
        groups = defaultdict(list)
        for r in rows:
            groups[str(r.get(color_key, "unknown"))].append(r)
        for group, pts in groups.items():
            if len(pts) < 2:
                continue
            cx = sum(sx(r[x_key]) for r in pts) / len(pts)
            cy = sum(sy(r[y_key]) for r in pts) / len(pts)
            out.append(f'<text x="{cx:.1f}" y="{cy:.1f}" class="cent" text-anchor="middle">{svg_escape(group[:24])}</text>')

    lx = W - MR + 26
    out.append(f'<text x="{lx}" y="{MT}" font-size="14" font-weight="700">Couleur: {svg_escape(color_key)}</text>')
    for i, (name, col) in enumerate(list(colors.items())[:18]):
        y = MT + 24 + i * 31
        out.append(f'<circle cx="{lx+7}" cy="{y-4}" r="6" fill="{col}" stroke="#111827" stroke-width=".5"/>')
        lines = wrap_label(name, 27)
        for j, line in enumerate(lines):
            out.append(f'<text x="{lx+22}" y="{y + j*13}" class="legend">{svg_escape(line)}</text>')
    if len(colors) > 18:
        out.append(f'<text x="{lx}" y="{MT+24+18*31}" class="legend sub">+ {len(colors)-18} autres</text>')
    if size_key:
        out.append(f'<text x="{lx}" y="{H-104}" class="legend" font-weight="700">Taille: {svg_escape(size_key)}</text>')
    if marker_key:
        out.append(f'<text x="{lx}" y="{H-82}" class="legend" font-weight="700">Forme: {svg_escape(marker_key)}</text>')
    out.append("</svg>")
    path = OUT / filename
    path.write_text("\n".join(out), encoding="utf-8")
    return path


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    cards_doc = load_json(ANALYSIS / "task_placement_cards.json")
    features_doc = load_json(ANALYSIS / "task_features.json")
    pca_doc = load_json(ANALYSIS / "task_map" / "task_pca.json")
    mds_doc = load_json(ANALYSIS / "task_map" / "task_map.json")

    cards = {t["task_ref"]: t for t in cards_doc["tasks"]}
    features = {t["task_ref"]: t for t in features_doc["tasks"]}
    pca = {t["task_ref"]: t for t in pca_doc["tasks"]}
    mds = {t["task_ref"]: t for t in mds_doc["tasks"]}

    rows = []
    for task_ref, card in cards.items():
        feat = features.get(task_ref, {})
        pr = pca.get(task_ref, {})
        mr = mds.get(task_ref, {})
        row = {
            "task_ref": task_ref,
            "stable_family": card.get("stable_family", "unknown"),
            "property_class": card.get("property_class", "unknown"),
            "empirical_family": card.get("empirical_family", "missing_empirical"),
            "proof_family": feat.get("proof_family") or pr.get("proof_family") or "unknown",
            "difficulty_label": feat.get("difficulty") or pr.get("difficulty") or "unknown",
            "confidence": safe_float(card.get("confidence"), 0.0) or 0.0,
            "needs_review_flag": "needs_review" if card.get("needs_review") else "auto",
            "proof_skill_count": len(card.get("proof_skills", [])),
            "spec_signal_count": len(card.get("spec_signals", [])),
            "neighbor_count": len(card.get("nearest_neighbors", [])),
            "pass_rate": safe_float(feat.get("pass_rate"), safe_float(pr.get("pass_rate"), 0.0)) or 0.0,
            "cohort_pass_rate": safe_float(feat.get("cohort_pass_rate"), safe_float(pr.get("cohort_pass_rate"), 0.0)) or 0.0,
            "passes": safe_float(feat.get("passes"), safe_float(pr.get("passes"), 0.0)) or 0.0,
            "attempts": safe_float(feat.get("attempts"), safe_float(pr.get("attempts"), 0.0)) or 0.0,
            "divisiveness": safe_float(feat.get("divisiveness"), safe_float(pr.get("divisiveness"), 0.0)) or 0.0,
            "mean_tokens_log": log1p_tokens(feat.get("mean_total_tokens")),
            "median_tokens_log": log1p_tokens(feat.get("median_total_tokens")),
            "mean_requests": safe_float(feat.get("mean_requests"), 0.0) or 0.0,
            "pc1": safe_float(pr.get("pc1")),
            "pc2": safe_float(pr.get("pc2")),
            "map_x": safe_float(mr.get("x")),
            "map_y": safe_float(mr.get("y")),
            "mds_cluster": f"cluster_{mr.get('cluster', 'missing')}",
            "resolved_flag": "resolved" if (safe_float(feat.get("passes"), safe_float(pr.get("passes"), 0.0)) or 0.0) > 0 else "unresolved",
        }
        rows.append(row)

    model_rows = []
    for row in rows:
        feat = features.get(row["task_ref"], {})
        for model, data in (feat.get("per_model") or {}).items():
            if not isinstance(data, dict):
                continue
            tokens = safe_float(data.get("total_tokens"), 0.0) or 0.0
            reqs = safe_float(data.get("requests"), 0.0) or 0.0
            model_rows.append(
                {
                    **row,
                    "model": model,
                    "model_tokens_log": log1p_tokens(tokens),
                    "model_requests": reqs,
                    "model_pass_numeric": 1.0 if data.get("passed") else 0.0,
                    "model_pass_flag": "pass" if data.get("passed") else "fail",
                }
            )

    plots = [
        ("01_pca_by_stable_family.svg", "PCA des tâches par famille stable", "Point=tâche, taille=log tokens moyens; PC1≈difficulté, PC2≈spécialisation", "pc1", "pc2", "stable_family", "mean_tokens_log", None, True, True),
        ("02_pca_by_empirical_family.svg", "PCA par famille empirique", "Point=tâche, taille=pass-rate; montre les clusters issus des runs", "pc1", "pc2", "empirical_family", "pass_rate", None, True, True),
        ("03_pca_by_property_class.svg", "PCA par property_class", "Point=tâche; catégories de preuve précises projetées sur le comportement modèle", "pc1", "pc2", "property_class", "mean_tokens_log", None, False, False),
        ("04_pca_by_review_status.svg", "PCA et revue humaine", "Diamant=tâche à revue; utile pour voir les zones taxonomiques incertaines", "pc1", "pc2", "needs_review_flag", "confidence", "needs_review_flag", True, True),
        ("05_mds_by_mds_cluster.svg", "Carte MDS par cluster comportemental", "Reprise de la carte pass/fail coverage-aware avec couleurs de clusters", "map_x", "map_y", "mds_cluster", "pass_rate", None, True, True),
        ("06_mds_by_stable_family.svg", "Carte MDS par famille stable", "Compare les familles sémantiques aux voisinages comportementaux", "map_x", "map_y", "stable_family", "mean_tokens_log", None, True, True),
        ("07_pass_rate_vs_tokens_stable.svg", "Pass-rate vs tokens par famille stable", "Les tâches chères mais non résolues ressortent en haut à gauche", "pass_rate", "mean_tokens_log", "stable_family", "attempts", None, False, False),
        ("08_cohort_pass_rate_vs_tokens_empirical.svg", "Cohort pass-rate vs tokens par famille empirique", "Vue centrée sur la cohorte de modèles comparables", "cohort_pass_rate", "mean_tokens_log", "empirical_family", "attempts", None, False, False),
        ("09_pc1_vs_tokens_stable.svg", "PC1 vs tokens", "PC1 mesure surtout la solvabilité; les tokens indiquent l'effort historique", "pc1", "mean_tokens_log", "stable_family", "attempts", None, False, False),
        ("10_pc2_vs_divisiveness_empirical.svg", "PC2 vs divisiveness", "Met en évidence les tâches qui séparent les modèles", "pc2", "divisiveness", "empirical_family", "pass_rate", None, False, False),
        ("11_confidence_vs_pass_rate_stable.svg", "Confiance taxonomique vs pass-rate", "Cherche les familles stables peu résolues mais bien identifiées", "confidence", "pass_rate", "stable_family", "mean_tokens_log", None, False, False),
        ("12_confidence_vs_tokens_review.svg", "Confiance vs tokens et revue", "Priorise la revue humaine: basse confiance + haut coût", "confidence", "mean_tokens_log", "needs_review_flag", "pass_rate", "needs_review_flag", False, False),
        ("13_skill_count_vs_pass_rate_stable.svg", "Nombre de skills de preuve vs pass-rate", "Complexité de preuve estimée contre succès historique", "proof_skill_count", "pass_rate", "stable_family", "mean_tokens_log", None, False, False),
        ("14_spec_signal_count_vs_pass_rate_stable.svg", "Signaux de spec vs pass-rate", "Les specs riches ne sont pas forcément faciles", "spec_signal_count", "pass_rate", "stable_family", "mean_tokens_log", None, False, False),
        ("15_neighbors_vs_confidence_stable.svg", "Voisins taxonomiques vs confiance", "Contrôle que les placements par similarité ont assez de voisins", "neighbor_count", "confidence", "stable_family", "pass_rate", None, False, False),
        ("16_resolved_vs_pca_stable.svg", "Tâches résolues et non résolues sur PCA", "Forme=résolution historique; couleur=famille stable", "pc1", "pc2", "stable_family", "mean_tokens_log", "resolved_flag", True, True),
        ("17_task_model_tokens_vs_pc1_model.svg", "Tâche-modèle: tokens vs PC1", "Point=paire tâche-modèle; triangle=pass, cercle=fail", "pc1", "model_tokens_log", "model", "model_requests", "model_pass_flag", False, False),
        ("18_task_model_pca_by_model.svg", "Tâche-modèle sur PCA par modèle", "Point=paire tâche-modèle; triangle=pass; montre les zones couvertes par chaque modèle", "pc1", "pc2", "model", "model_tokens_log", "model_pass_flag", False, False),
        ("19_task_model_pass_vs_tokens.svg", "Tâche-modèle: pass/fail vs tokens", "Chaque point est une tentative modèle; utile pour voir l'effort dépensé avant succès", "model_pass_numeric", "model_tokens_log", "model", "model_requests", "model_pass_flag", False, False),
        ("20_family_centroids_pca.svg", "Centres de familles stables sur PCA", "Point=tâche, ellipse=extension approximative, label=centroïde de famille", "pc1", "pc2", "stable_family", "pass_rate", None, True, True),
    ]

    manifest = []
    for args in plots:
        path = render_plot(
            rows if not args[0].startswith(("17_", "18_", "19_")) else model_rows,
            filename=args[0],
            title=args[1],
            subtitle=args[2],
            x_key=args[3],
            y_key=args[4],
            color_key=args[5],
            size_key=args[6],
            marker_key=args[7],
            annotate_centroids=args[8],
            draw_category_hulls=args[9],
            x_label=args[3],
            y_label=args[4],
        )
        if path:
            manifest.append({"file": path.name, "title": args[1], "subtitle": args[2]})

    # Category recommendation summaries.
    by_family = defaultdict(list)
    for row in rows:
        by_family[row["stable_family"]].append(row)
    csv_path = OUT / "category_summary.csv"
    with csv_path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow([
            "stable_family",
            "task_count",
            "avg_pass_rate",
            "avg_mean_tokens_log10",
            "needs_review",
            "top_property_classes",
            "top_empirical_families",
            "example_tasks",
        ])
        for fam, items in sorted(by_family.items(), key=lambda kv: (-len(kv[1]), kv[0])):
            writer.writerow([
                fam,
                len(items),
                f"{sum(r['pass_rate'] for r in items)/len(items):.3f}",
                f"{sum(r['mean_tokens_log'] for r in items)/len(items):.3f}",
                sum(1 for r in items if r["needs_review_flag"] == "needs_review"),
                "; ".join(f"{k}:{v}" for k, v in Counter(r["property_class"] for r in items).most_common(5)),
                "; ".join(f"{k}:{v}" for k, v in Counter(r["empirical_family"] for r in items).most_common(5)),
                "; ".join(r["task_ref"] for r in items[:5]),
            ])

    md = []
    md.append("# Taxonomy Scatter Gallery\n")
    md.append("## Recommended Stable Categories\n")
    for fam, items in sorted(by_family.items(), key=lambda kv: (-len(kv[1]), kv[0])):
        props = Counter(r["property_class"] for r in items).most_common(6)
        empir = Counter(r["empirical_family"] for r in items).most_common(4)
        avg_pass = sum(r["pass_rate"] for r in items) / len(items)
        md.append(f"### {fam}\n")
        md.append(f"- tasks: {len(items)}")
        md.append(f"- avg_pass_rate: {avg_pass:.3f}")
        md.append(f"- needs_review: {sum(1 for r in items if r['needs_review_flag'] == 'needs_review')}")
        md.append("- property_classes: " + ", ".join(f"{k} ({v})" for k, v in props))
        md.append("- empirical_families: " + ", ".join(f"{k} ({v})" for k, v in empir))
        md.append("- examples: " + ", ".join(r["task_ref"] for r in items[:6]))
        md.append("")
    md.append("## Plots\n")
    for item in manifest:
        md.append(f"- `{item['file']}`: {item['title']} - {item['subtitle']}")
    (OUT / "README.md").write_text("\n".join(md), encoding="utf-8")
    (OUT / "manifest.json").write_text(json.dumps({"plots": manifest}, indent=2), encoding="utf-8")
    print(f"wrote {len(manifest)} plots to {OUT}")


if __name__ == "__main__":
    main()

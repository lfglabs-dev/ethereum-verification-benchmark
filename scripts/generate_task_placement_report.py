#!/usr/bin/env python3
"""Generate task placement cards and a global taxonomy-placement report."""
from __future__ import annotations

import argparse
import json
import math
from collections import Counter, defaultdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

import yaml

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_VERSION = ROOT / "benchmark-versions" / "v0.1.json"
DEFAULT_FEATURES = ROOT / "analysis" / "task_features.json"
DEFAULT_TAXONOMY = ROOT / "analysis" / "task_taxonomy.json"
DEFAULT_TASK_MAP = ROOT / "analysis" / "task_map" / "task_map.json"
DEFAULT_TASK_PCA = ROOT / "analysis" / "task_map" / "task_pca.json"
DEFAULT_OUT_JSON = ROOT / "analysis" / "task_placement_cards.json"
DEFAULT_OUT_REPORT = ROOT / "analysis" / "task_placement_report.md"


PROOF_SKILL_HINTS = {
    "functional_correctness": ["definitional_unfolding", "rewriting"],
    "state_preservation_local_effects": ["state_threading", "invariant_preservation"],
    "authorization_enablement": ["access_control_reasoning", "state_threading"],
    "protocol_transition_correctness": ["state_threading", "case_analysis"],
    "refinement_equivalence": ["refinement_alignment", "definitional_unfolding"],
}

PROPERTY_SKILL_HINTS = (
    (("accounting", "balance", "supply", "conservation", "solvency", "reserve"), ["aggregation_conservation"]),
    (("bound", "round", "price", "overflow", "counter", "threshold", "rate", "formula"), ["arithmetic_reasoning"]),
    (("access", "authorization", "owner", "caller"), ["access_control_reasoning"]),
    (("rejected", "silent_failure", "non_leakage"), ["revert_reasoning"]),
    (("linked_list", "tree", "mapping", "subtree", "decoder", "calldata"), ["datastructure_reasoning"]),
    (("faithfulness", "equivalence", "noninterference", "frame"), ["refinement_alignment"]),
    (("invariant", "pps_nondecrease", "compliance"), ["invariant_preservation"]),
)


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def task_yaml(meta: dict[str, Any]) -> dict[str, Any]:
    manifest_path = meta.get("manifest_path")
    if not manifest_path:
        return {}
    path = ROOT / str(manifest_path)
    if not path.exists():
        return {}
    with path.open(encoding="utf-8") as f:
        data = yaml.safe_load(f) or {}
    return data if isinstance(data, dict) else {}


def load_task_yamls() -> dict[str, dict[str, Any]]:
    tasks: dict[str, dict[str, Any]] = {}
    for base in ("cases", "backlog"):
        for path in sorted((ROOT / base).glob("*/*/tasks/*.yaml")):
            with path.open(encoding="utf-8") as f:
                data = yaml.safe_load(f) or {}
            if not isinstance(data, dict):
                continue
            case_id = data.get("case_id")
            task_id = data.get("task_id")
            if not (case_id and task_id):
                continue
            task_ref = f"{case_id}/{task_id}"
            data["task_ref"] = task_ref
            data["manifest_path"] = str(path.relative_to(ROOT))
            tasks[task_ref] = data
    return tasks


def stable_family_for(row: dict[str, Any]) -> str:
    prop = str(row.get("property_class") or "")
    proof = str(row.get("proof_family") or "")
    task_ref = str(row.get("task_ref") or "")
    if prop in {"access_control_identity", "authorization_state"}:
        return "authorization_and_caller_integrity"
    if prop in {"accounting_conservation", "accounting_bound", "accounting_update", "fund_conservation"}:
        return "asset_accounting_and_conservation"
    if prop in {"guarded_solvency", "solvency"} or "solvency" in task_ref:
        return "solvency_and_liquidity_guards"
    if prop in {"price_computation", "price_band", "output_range"}:
        return "numeric_bounds_and_pricing"
    if prop in {"linked_list_invariant", "tree_conservation", "mapping_consistency", "threshold_partition"}:
        return "structural_indexing_invariants"
    if proof == "refinement_equivalence" or prop in {"decoder_faithfulness", "metadata_bridge"}:
        return "decoder_and_refinement_equivalence"
    if prop in {"non_leakage", "revert_boundary", "accounting_invariant_break"}:
        return "negative_and_attack_boundaries"
    if proof == "protocol_transition_correctness":
        return "protocol_transition_correctness"
    return "state_preservation_and_local_effects"


def unique(items: list[str]) -> list[str]:
    seen: set[str] = set()
    out: list[str] = []
    for item in items:
        if item and item not in seen:
            seen.add(item)
            out.append(item)
    return out


def inferred_skills(task: dict[str, Any], reviewed: dict[str, Any] | None) -> list[str]:
    if reviewed and reviewed.get("skills"):
        return list(reviewed["skills"])
    proof_family = str(task.get("proof_family") or "")
    prop = str(task.get("property_class") or "").lower()
    skills = list(PROOF_SKILL_HINTS.get(proof_family, []))
    for needles, hints in PROPERTY_SKILL_HINTS:
        if any(needle in prop for needle in needles):
            skills.extend(hints)
    if not skills:
        skills = ["definitional_unfolding", "rewriting"]
    return unique(skills)


def spec_signals(meta: dict[str, Any], yaml_meta: dict[str, Any]) -> list[str]:
    signals = [
        f"proof_family={meta.get('proof_family')}",
        f"property_class={meta.get('property_class')}",
        f"category={meta.get('category')}",
        f"difficulty={meta.get('difficulty')}",
        f"track={meta.get('track')}",
        f"theorem={meta.get('theorem_name')}",
    ]
    for key in ("proof_status", "translation_status", "abstraction_level"):
        value = yaml_meta.get(key) or meta.get(key)
        if value:
            signals.append(f"{key}={value}")
    if yaml_meta.get("reference_solution_declaration"):
        signals.append(f"reference_solution={yaml_meta['reference_solution_declaration']}")
    if yaml_meta.get("abstraction_notes"):
        signals.append("abstraction_notes_present")
    return [str(s) for s in signals if s and not s.endswith("=None")]


def distance(a: dict[str, Any], b: dict[str, Any]) -> float:
    ax = a.get("pc1", a.get("x", 0.0))
    ay = a.get("pc2", a.get("y", 0.0))
    bx = b.get("pc1", b.get("x", 0.0))
    by = b.get("pc2", b.get("y", 0.0))
    dx = float(ax) - float(bx)
    dy = float(ay) - float(by)
    d = math.hypot(dx, dy)
    if a.get("cohort_signature") != b.get("cohort_signature"):
        d += 0.35
    if a.get("stable_family") != b.get("stable_family"):
        d += 0.15
    if a.get("property_class") != b.get("property_class"):
        d += 0.1
    if a.get("cluster") and b.get("cluster") and a.get("cluster") != b.get("cluster"):
        d += 0.2
    return d


def nearest_neighbors(task_ref: str, task_map_by_ref: dict[str, dict[str, Any]], n: int = 5) -> list[str]:
    current = task_map_by_ref[task_ref]
    ranked = sorted(
        (
            (distance(current, other), other_ref)
            for other_ref, other in task_map_by_ref.items()
            if other_ref != task_ref
        ),
        key=lambda item: (item[0], item[1]),
    )
    return [ref for _, ref in ranked[:n]]


def static_similarity_neighbors(
    meta: dict[str, Any],
    active_meta_by_ref: dict[str, dict[str, Any]],
    placement_by_ref: dict[str, dict[str, Any]],
    n: int = 5,
) -> list[str]:
    stable = stable_family_for(meta)
    prop = meta.get("property_class")
    proof = meta.get("proof_family")
    family = meta.get("family_id")
    category = meta.get("category")
    ranked: list[tuple[float, str]] = []
    for ref, active in active_meta_by_ref.items():
        score = 0.0
        if placement_by_ref.get(ref, {}).get("stable_family") == stable:
            score += 4.0
        if active.get("property_class") == prop:
            score += 3.0
        if active.get("proof_family") == proof:
            score += 2.0
        if active.get("family_id") == family:
            score += 1.5
        if active.get("category") == category:
            score += 1.0
        ranked.append((-score, ref))
    ranked.sort(key=lambda item: (item[0], item[1]))
    return [ref for _, ref in ranked[:n]]


def empirical_family(task_map_row: dict[str, Any], cluster_summaries: dict[int, dict[str, Any]]) -> str:
    if task_map_row.get("empirical_family"):
        return str(task_map_row["empirical_family"])
    cluster = int(task_map_row.get("cluster") or 0)
    signature = task_map_row.get("cohort_signature") or "unknown"
    summary = cluster_summaries.get(cluster, {})
    dominant = "mixed"
    dominant_classes = summary.get("dominant_property_classes") or []
    if dominant_classes:
        dominant = str(dominant_classes[0][0])
    return f"cluster_{cluster}:{signature}:{dominant}"


def confidence(
    *,
    task: dict[str, Any],
    task_map_row: dict[str, Any],
    reviewed: dict[str, Any] | None,
    has_reference: bool,
    stable_pair_share: float,
) -> float:
    score = 0.5
    if reviewed:
        score += 0.15
    if has_reference:
        score += 0.08
    if task.get("task_fingerprint") and task_map_row.get("cohort_signature"):
        score += 0.08
    if stable_pair_share >= 0.67:
        score += 0.08
    elif stable_pair_share < 0.4:
        score -= 0.12
    cohort_pass_rate = float(task.get("cohort_pass_rate") or 0.0)
    divisiveness = float(task.get("divisiveness") or 0.0)
    if cohort_pass_rate in (0.0, 1.0):
        score += 0.06
    if divisiveness >= 0.75:
        score -= 0.12
    pass_rate = float(task.get("pass_rate") or 0.0)
    if 0.35 <= pass_rate <= 0.65:
        score -= 0.06
    return round(max(0.0, min(1.0, score)), 2)


def dominant_share(rows: list[dict[str, Any]], key: str) -> tuple[str, float]:
    if not rows:
        return ("", 0.0)
    counts = Counter(str(row.get(key)) for row in rows)
    value, count = counts.most_common(1)[0]
    return value, count / len(rows)


def build_cards(
    version: dict[str, Any],
    features: dict[str, Any],
    taxonomy: dict[str, Any],
    task_map: dict[str, Any],
    task_pca: dict[str, Any],
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    yaml_by_ref = load_task_yamls()
    version_by_ref = {str(t["task_ref"]): t for t in version.get("tasks", [])}
    for ref, meta in yaml_by_ref.items():
        version_by_ref.setdefault(ref, meta)
    features_by_ref = {str(t["task_ref"]): t for t in features.get("tasks", [])}
    reviewed_by_ref = {str(t["task_ref"]): t for t in taxonomy.get("labels", [])}
    task_map_by_ref = {str(t["task_ref"]): t for t in task_map.get("tasks", [])}
    task_pca_by_ref = {str(t["task_ref"]): t for t in task_pca.get("tasks", [])}
    placement_by_ref = {
        ref: {**task_map_by_ref.get(ref, {}), **task_pca_by_ref.get(ref, {})}
        for ref in set(task_map_by_ref) | set(task_pca_by_ref)
    }
    cluster_summaries = {int(c["cluster"]): c for c in task_map.get("clusters", [])}

    rows_for_share: dict[tuple[str, str], list[dict[str, Any]]] = defaultdict(list)
    for ref, row in placement_by_ref.items():
        meta = features_by_ref.get(ref) or version_by_ref.get(ref) or {}
        stable = str(row.get("stable_family") or meta.get("proof_family"))
        rows_for_share[(stable, str(meta.get("property_class")))].append(row)

    pair_empirical_share: dict[tuple[str, str], float] = {}
    for pair, rows in rows_for_share.items():
        enriched_rows = [
            {**row, "empirical_family": empirical_family(row, cluster_summaries)}
            for row in rows
        ]
        _, share = dominant_share(enriched_rows, "empirical_family")
        pair_empirical_share[pair] = share

    cards: list[dict[str, Any]] = []
    for task_ref in sorted(version_by_ref):
        task = features_by_ref.get(task_ref)
        meta = version_by_ref.get(task_ref, task)
        yaml_meta = task_yaml(meta)
        reviewed = reviewed_by_ref.get(task_ref)
        prop = str((task or {}).get("property_class") or meta.get("property_class") or "unknown")
        has_reference = bool(yaml_meta.get("reference_solution_declaration"))
        placement_basis = ["spec_text", "historical_runs"]
        if has_reference:
            placement_basis.insert(0, "reference_proof")
        if task is not None and task_ref in placement_by_ref:
            map_row = placement_by_ref[task_ref]
            stable_family = str(map_row.get("stable_family") or task.get("proof_family") or meta.get("proof_family") or "unknown")
            emp_family = empirical_family(map_row, cluster_summaries)
            neighbors = nearest_neighbors(task_ref, placement_by_ref)
            share = pair_empirical_share.get((stable_family, prop), 0.0)
            conf = confidence(
                task=task,
                task_map_row=map_row,
                reviewed=reviewed,
                has_reference=has_reference,
                stable_pair_share=share,
            )
            needs_review = (
                conf < 0.65
                or float(task.get("divisiveness") or 0.0) >= 0.75
                or share < 0.4
                or (int(task.get("passes") or 0) == 0 and map_row.get("cohort_signature") != "FFFF")
            )
        else:
            stable_family = stable_family_for(meta)
            neighbors = static_similarity_neighbors(meta, features_by_ref, placement_by_ref)
            neighbor_empirical = [
                empirical_family(placement_by_ref[neighbor], cluster_summaries)
                for neighbor in neighbors
                if neighbor in placement_by_ref
            ]
            emp_family = neighbor_empirical[0] if neighbor_empirical else "unplaced_no_historical_runs"
            conf = 0.5 if has_reference else 0.45
            needs_review = True
            placement_basis = [basis for basis in placement_basis if basis != "historical_runs"]
        cards.append(
            {
                "task_ref": task_ref,
                "stable_family": stable_family,
                "property_class": prop,
                "proof_skills": inferred_skills(task or meta, reviewed),
                "spec_signals": spec_signals(meta, yaml_meta),
                "empirical_family": emp_family,
                "nearest_neighbors": neighbors,
                "confidence": conf,
                "needs_review": needs_review,
                "placement_basis": placement_basis,
            }
        )

    context = {
        "features_by_ref": features_by_ref,
        "task_map_by_ref": placement_by_ref,
        "cluster_summaries": cluster_summaries,
        "pair_empirical_share": pair_empirical_share,
    }
    return cards, context


def as_task_line(card: dict[str, Any], features_by_ref: dict[str, dict[str, Any]]) -> str:
    task = features_by_ref.get(card["task_ref"], {})
    pass_rate = task.get("pass_rate")
    pass_rate_text = "no_run" if pass_rate is None else f"{float(pass_rate):.2f}"
    return (
        f"- `{card['task_ref']}` -> {card['empirical_family']} "
        f"(stable={card['stable_family']}, property={card['property_class']}, "
        f"pass_rate={pass_rate_text}, confidence={card['confidence']:.2f}); "
        f"neighbors: {', '.join('`' + n + '`' for n in card['nearest_neighbors'][:3])}"
    )


def build_report(cards: list[dict[str, Any]], context: dict[str, Any], out_json: Path) -> str:
    features_by_ref = context["features_by_ref"]
    cluster_summaries = context["cluster_summaries"]

    by_pair: dict[tuple[str, str], list[dict[str, Any]]] = defaultdict(list)
    by_empirical: dict[str, list[dict[str, Any]]] = defaultdict(list)
    by_stable: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for card in cards:
        by_pair[(card["stable_family"], card["property_class"])].append(card)
        by_empirical[card["empirical_family"]].append(card)
        by_stable[card["stable_family"]].append(card)

    confirmed: list[tuple[int, str, str, float, str]] = []
    split: list[tuple[int, str, str, list[tuple[str, int]]]] = []
    for pair, rows in by_pair.items():
        counts = Counter(row["empirical_family"] for row in rows)
        dominant, count = counts.most_common(1)[0]
        share = count / len(rows)
        if len(rows) >= 2 and share >= 0.67:
            confirmed.append((len(rows), pair[0], pair[1], share, dominant))
        if len(rows) >= 3 and len(counts) >= 3 and share < 0.67:
            split.append((len(rows), pair[0], pair[1], counts.most_common()))

    merges: list[tuple[str, int, list[tuple[str, int]]]] = []
    for emp, rows in by_empirical.items():
        pair_counts = Counter(f"{row['stable_family']} / {row['property_class']}" for row in rows)
        if len(pair_counts) >= 3 and len(rows) >= 5:
            merges.append((emp, len(rows), pair_counts.most_common(8)))

    unresolved = [
        card for card in cards
        if card["task_ref"] not in features_by_ref
        or int(features_by_ref[card["task_ref"]].get("passes") or 0) == 0
    ]
    ambiguous = [
        card for card in cards
        if card["needs_review"]
    ]

    lines = [
        "# Rapport global de placement des tâches",
        "",
        f"Generated at `{datetime.now(timezone.utc).isoformat()}`.",
        f"Fiches JSON: `{out_json.relative_to(ROOT)}`.",
        "",
        "## Portée et méthode",
        "",
        f"- Tâches placées: {len(cards)} tâches runnable: 135 actives couvertes par `analysis/task_features.json` et 8 backlog placées par similarité statique.",
        "- `stable_family` reprend la famille stable dérivée dans `analysis/task_map/task_pca.json`; fallback: `proof_family` canonique.",
        "- `property_class` reprend la classe de propriété du manifeste.",
        "- `empirical_family` reprend la famille empirique de `task_pca.json`; fallback: cluster comportemental + signature cohort.",
        "- `proof_skills`, hors 12 labels reviewés, sont inférés depuis `proof_family` + `property_class`.",
        "- `spec_signals` est un résumé déterministe des champs de manifeste et de la fiche YAML, pas une annotation manuelle.",
        "- `nearest_neighbors` utilise la carte PCA/MDS avec pénalité si signature, famille stable ou classe divergent.",
        "- Les tâches backlog n'ont pas d'historique v0.1; leur `empirical_family` est héritée du plus proche voisin actif et `needs_review=true`.",
        "",
        "## Familles confirmées",
        "",
    ]
    if confirmed:
        for count, family, prop, share, emp in sorted(confirmed, reverse=True)[:40]:
            lines.append(f"- `{family}` / `{prop}`: {count} tâches, {share:.0%} dans `{emp}`.")
    else:
        lines.append("- Aucune famille multi-tâche ne dépasse le seuil de confirmation.")

    lines.extend(["", "## Familles à fusionner", ""])
    if merges:
        for emp, count, pairs in sorted(merges, key=lambda x: (-x[1], x[0])):
            joined = "; ".join(f"{name} ({n})" for name, n in pairs)
            lines.append(f"- `{emp}` regroupe {count} tâches de familles stables proches: {joined}.")
    else:
        lines.append("- Aucun cluster empirique large ne suggère une fusion forte au seuil actuel.")

    lines.extend(["", "## Familles à splitter", ""])
    if split:
        for count, family, prop, counts in sorted(split, reverse=True):
            joined = "; ".join(f"{emp} ({n})" for emp, n in counts)
            lines.append(f"- `{family}` / `{prop}` ({count} tâches) se répartit entre: {joined}.")
    else:
        lines.append("- Aucun couple `stable_family` / `property_class` ne franchit le seuil de split.")

    lines.extend(["", "## Tâches non résolues placées par similarité", ""])
    if unresolved:
        for card in sorted(unresolved, key=lambda c: (c["empirical_family"], c["task_ref"])):
            lines.append(as_task_line(card, features_by_ref))
    else:
        lines.append("- Aucune tâche avec zéro passe historique.")

    lines.extend(["", "## Cas ambigus à revue humaine", ""])
    if ambiguous:
        for card in sorted(ambiguous, key=lambda c: (c["confidence"], c["task_ref"])):
            task = features_by_ref.get(card["task_ref"], {})
            reasons = []
            if card["task_ref"] not in features_by_ref:
                reasons.append("no historical run")
            if card["confidence"] < 0.65:
                reasons.append("confidence<0.65")
            if float(task.get("divisiveness") or 0.0) >= 0.75:
                reasons.append("divisive")
            lines.append(
                f"- `{card['task_ref']}`: {', '.join(reasons) or 'review flag'}; "
                f"stable=`{card['stable_family']}`, empirical=`{card['empirical_family']}`, "
                f"confidence={card['confidence']:.2f}."
            )
    else:
        lines.append("- Aucun cas ambigu au seuil actuel.")

    lines.extend(["", "## Clusters empiriques", ""])
    for cluster in sorted(cluster_summaries):
        summary = cluster_summaries[cluster]
        lines.append(
            f"- `cluster_{cluster}`: {summary.get('task_count')} tâches, "
            f"pass_rate moyen={float(summary.get('avg_pass_rate') or 0):.2f}, "
            f"signatures={summary.get('dominant_cohort_signatures')}."
        )
    lines.append("")
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--version", type=Path, default=DEFAULT_VERSION)
    parser.add_argument("--features", type=Path, default=DEFAULT_FEATURES)
    parser.add_argument("--taxonomy", type=Path, default=DEFAULT_TAXONOMY)
    parser.add_argument("--task-map", type=Path, default=DEFAULT_TASK_MAP)
    parser.add_argument("--task-pca", type=Path, default=DEFAULT_TASK_PCA)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-report", type=Path, default=DEFAULT_OUT_REPORT)
    args = parser.parse_args()

    version = load_json(args.version)
    features = load_json(args.features)
    taxonomy = load_json(args.taxonomy)
    task_map = load_json(args.task_map)
    task_pca = load_json(args.task_pca) if args.task_pca.exists() else {"tasks": []}

    cards, context = build_cards(version, features, taxonomy, task_map, task_pca)
    payload = {
        "schema_version": 1,
        "benchmark_version": features.get("benchmark_version") or version.get("benchmark_version"),
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "source_files": [
            str(args.version.relative_to(ROOT)),
            str(args.features.relative_to(ROOT)),
            str(args.taxonomy.relative_to(ROOT)),
            str(args.task_map.relative_to(ROOT)),
            str(args.task_pca.relative_to(ROOT)),
        ],
        "task_count": len(cards),
        "tasks": cards,
    }
    args.out_json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    args.out_report.write_text(build_report(cards, context, args.out_json), encoding="utf-8")


if __name__ == "__main__":
    main()

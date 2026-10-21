#!/usr/bin/env python3
"""Fit effort-scaling curves for the v0.3 STRAT-50 budget cascade.

PROVISIONAL: the cascade was run on a harness with a known repetition-guard bug.
Every number produced here is meant to be regenerated from the cascade output
directories with one command once the fixed-harness rerun lands:

    python -I analysis/budget_scaling_v03_strat50/fit_scaling.py --input <cascade_root>

<cascade_root>/<provider>__<model>/ must contain cascade_results.json (one row
per (profile, task) run) and cascade_summary.csv. Outputs (all in this
directory): fit_summary.json, cascade_points.csv, figures/*.svg|png and the
curated per-model copies under data/<provider>__<model>/.

Two complementary views of the same runs
----------------------------------------
1. Per-task survival model (the shared-shape test). For each task we accumulate
   the effort (total tokens, or requests) spent on it across cascade profiles.
   A task first solved at profile k is interval-censored between its cumulative
   spend before k and after k; a never-solved task is right-censored at its
   total spend. Per task:
       P(solved with cumulative effort <= e) = A * Phi((ln e - mu) / sigma)
   A ceiling, exp(mu) median per-task effort among reachable tasks, sigma the
   spread of task difficulty in log-effort. Nested hypotheses (LRT + AIC):
       H1 free:          A_m, mu_m, sigma_m per model
       H2 shared shape:  sigma shared; A_m, mu_m per model
       H3 pure scaling:  sigma and A shared; mu_m per model
2. Panel cascade curve (the parametrisation on veritylabs.dev/benchmark):
       S(E) = A / (1 + (kHalf / E)^alpha)
   with E the cumulative panel effort after each profile and S the cumulative
   solve rate over the 50 tasks, least squares on S. A = 1 is the site's form;
   an A-free variant and a panel log-normal A * Phi((ln E - mu) / sigma) are
   reported for comparison.

Confidence intervals: paired task bootstrap (the 50 tasks are the same for all
models, so one resample of task indices is applied to every model), refitting
every quantity on each replicate; percentile 95% intervals.
"""
from __future__ import annotations

import argparse
import csv
import json
import math
import os
import shutil
from pathlib import Path

# One BLAS thread per process: the bootstrap is parallelised over processes and
# tiny L-BFGS problems slow down badly with oversubscribed BLAS threads.
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ.setdefault(_v, "1")

import numpy as np
from scipy import optimize, special, stats

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
DEFAULT_INPUT = ROOT / "output" / "budget_scaling_v03_strat50"
DEFAULT_LEADERBOARD = ROOT / "analysis" / "v0.3_strat50" / "leaderboard.json"
DEFAULT_MINIMAX = ROOT / "analysis" / "budget_scaling_minimax_50" / "cascade_summary.csv"
DEFAULT_FINISHED = ["openai__gpt-6-astra", "openai__gpt-5.6-terra", "openai__gpt-6-luna"]
# Fixed display order (= categorical colour slot), never re-ranked.
DISPLAY_ORDER = [
    "openai__gpt-6-astra", "openai__gpt-5.6-terra", "openai__gpt-6-luna",
    "anthropic__claude-opus-5-5", "zai__glm-5.3", "google__gemini-4-argon-eap",
]
COLORS = ["#2a78d6", "#eb6834", "#1baf7a", "#eda100", "#e87ba4", "#008300", "#6250d6", "#e34948"]
PROFILE_ORDER = [
    "p01_ultra_tiny", "p02_tiny", "p03_ultra_cheap", "p04_cheap", "p05_quick_minus",
    "p06_quick", "p07_medium", "p08_normal", "p09_high", "p10_ultra_high",
]
LEADERBOARD_PROFILE = "p08_normal"  # 16 attempts / 120 tool calls = leaderboard p4_normal
UNITS = {"tokens": "total_tokens", "requests": "requests"}
EPS = 1e-12
LOGIT_BOUND = 12.0


# --------------------------------------------------------------------------- data

def load_model(path: Path) -> dict:
    rows = json.loads((path / "cascade_results.json").read_text())
    rows = [r for r in rows if r.get("profile") in PROFILE_ORDER and not r.get("skipped_already_solved")]
    profiles = sorted({r["profile"] for r in rows}, key=PROFILE_ORDER.index)
    tasks = sorted({r["task_ref"] for r in rows})
    ti = {t: i for i, t in enumerate(tasks)}
    P = len(profiles)
    spend = {u: np.zeros((len(tasks), P)) for u in UNITS}
    # Spend on runs of a task AFTER it was solved. The cascade should skip those,
    # but the v0.3 driver re-ran a few (task-leak bug). They count towards panel
    # cost (what was actually spent) but not towards the per-task solve effort.
    post_solve = {u: np.zeros((len(tasks), P)) for u in UNITS}
    post_solve_runs = []
    solved_at = np.full(len(tasks), -1)
    infra = np.zeros((len(tasks), P), int)
    rows.sort(key=lambda r: PROFILE_ORDER.index(r["profile"]))
    for r in rows:
        i, k = ti[r["task_ref"]], profiles.index(r["profile"])
        if 0 <= solved_at[i] < k:
            for u, field in UNITS.items():
                post_solve[u][i, k] += float(r.get(field) or 0)
            post_solve_runs.append({"task_ref": r["task_ref"], "solved_at": profiles[solved_at[i]],
                                    "rerun_profile": r["profile"], "final_class": r.get("final_class"),
                                    "total_tokens": int(r.get("total_tokens") or 0)})
            continue
        for u, field in UNITS.items():
            spend[u][i, k] += float(r.get(field) or 0)
        if r.get("final_class") == "INFRA_INVALID":
            infra[i, k] += 1
        if r.get("passed"):
            solved_at[i] = k
    summary = []
    with (path / "cascade_summary.csv").open() as fh:
        for row in csv.DictReader(fh):
            summary.append(row)
    return {"tasks": tasks, "profiles": profiles, "spend": spend, "post_solve": post_solve,
            "post_solve_runs": post_solve_runs, "solved_at": solved_at, "infra": infra, "summary_csv": summary}


def task_intervals(m: dict, unit: str, idx: np.ndarray | None = None):
    """(ln lo, ln hi, solved) per task; hi is unused for unsolved tasks."""
    sp, sa = m["spend"][unit], m["solved_at"]
    if idx is not None:
        sp, sa = sp[idx], sa[idx]
    cum = np.cumsum(sp, axis=1)
    before = np.concatenate([np.zeros((len(sa), 1)), cum[:, :-1]], axis=1)
    rows = np.arange(len(sa))
    k = np.where(sa >= 0, sa, 0)
    lo = np.where(sa >= 0, before[rows, k], cum[:, -1])
    hi = np.where(sa >= 0, cum[rows, k], 1.0)
    return np.log(np.maximum(lo, 1)), np.log(np.maximum(hi, 1)), sa >= 0


def panel_points(m: dict, unit: str, idx: np.ndarray | None = None):
    sp, sa = m["spend"][unit] + m["post_solve"][unit], m["solved_at"]
    if idx is not None:
        sp, sa = sp[idx], sa[idx]
    E = np.cumsum(sp.sum(axis=0))
    S = np.array([np.mean((sa >= 0) & (sa <= k)) for k in range(len(m["profiles"]))])
    return E, S


# ------------------------------------------------------------- per-task survival

def cdf(x, A, mu, sigma):
    return A * stats.norm.cdf((x - mu) / sigma)


def nll_model(A, mu, sigma, lo, hi, solved) -> float:
    g_lo = cdf(lo, A, mu, sigma)
    g_hi = cdf(hi, A, mu, sigma)
    p = np.where(solved, g_hi - g_lo, 1 - g_lo)
    return -float(np.sum(np.log(np.clip(p, EPS, 1))))


def _sig(v):
    return 1 / (1 + math.exp(-v))


def unpack(theta, hyp, n):
    if hyp == "H1":
        return [(_sig(theta[3 * i]), theta[3 * i + 1], math.exp(theta[3 * i + 2])) for i in range(n)]
    if hyp == "H2":
        s = math.exp(theta[0])
        return [(_sig(theta[1 + 2 * i]), theta[2 + 2 * i], s) for i in range(n)]
    s, a = math.exp(theta[0]), _sig(theta[1])
    return [(a, theta[2 + i], s) for i in range(n)]


def n_params(hyp, n):
    return {"H1": 3 * n, "H2": 1 + 2 * n, "H3": 2 + n}[hyp]


def bounds_for(hyp, n):
    A, MU, LS = (-LOGIT_BOUND, LOGIT_BOUND), (-5.0, 40.0), (math.log(0.05), math.log(20.0))
    if hyp == "H1":
        return [A, MU, LS] * n
    if hyp == "H2":
        return [LS] + [A, MU] * n
    return [LS, A] + [MU] * n


def default_starts(hyp, data):
    n = len(data)
    mu0 = [float(np.median(np.concatenate([d[0], d[1][d[2]]]))) + 1.0 for d in data]
    starts = []
    for a0, s0 in ((2.0, 0.7), (0.0, 0.3), (6.0, 1.0), (-1.0, 0.0)):
        if hyp == "H1":
            x = sum(([a0, mu0[i], s0] for i in range(n)), [])
        elif hyp == "H2":
            x = [s0] + sum(([a0, mu0[i]] for i in range(n)), [])
        else:
            x = [s0, a0] + mu0
        starts.append(np.array(x, float))
    return starts


def _vec_theta(theta, hyp, n):
    """Per-model (A, mu, sigma) arrays from the unconstrained parameter vector."""
    t = np.asarray(theta, float)
    if hyp == "H1":
        t = t.reshape(n, 3)
        return 1 / (1 + np.exp(-t[:, 0])), t[:, 1], np.exp(t[:, 2])
    if hyp == "H2":
        r = t[1:].reshape(n, 2)
        return 1 / (1 + np.exp(-r[:, 0])), r[:, 1], np.full(n, math.exp(t[0]))
    return np.full(n, _sig(t[1])), t[2:], np.full(n, math.exp(t[0]))


def fit_survival(data: list, hyp: str, starts=None):
    n = len(data)
    lo = np.concatenate([d[0] for d in data]); hi = np.concatenate([d[1] for d in data])
    sv = np.concatenate([d[2] for d in data]); gid = np.concatenate([np.full(len(d[0]), i) for i, d in enumerate(data)])

    def f(th):
        A, mu, s = _vec_theta(th, hyp, n)
        A, mu, s = A[gid], mu[gid], s[gid]
        g_lo = A * special.ndtr((lo - mu) / s)
        g_hi = A * special.ndtr((hi - mu) / s)
        p = np.where(sv, g_hi - g_lo, 1 - g_lo)
        return -float(np.sum(np.log(np.clip(p, EPS, 1))))

    best = None
    for x0 in starts if starts is not None else default_starts(hyp, data):
        res = optimize.minimize(f, x0, method="L-BFGS-B", bounds=bounds_for(hyp, n))
        if best is None or res.fun < best.fun:
            best = res
    return best.x, float(best.fun), unpack(best.x, hyp, n)


def survival_params_dict(names, params):
    return {m: {"A": p[0], "mu": p[1], "sigma": p[2], "median_effort": math.exp(p[1]),
                "A_at_bound": p[0] > _sig(LOGIT_BOUND - 1e-3)} for m, p in zip(names, params)}


# ----------------------------------------------------------- panel curve (site)

def loglogistic(E, A, k_half, alpha):
    return A / (1 + (k_half / E) ** alpha)


def fit_panel(E, S, form: str, starts=None):
    lE = np.log(E)
    if form == "loglogistic_A1":
        f = lambda th: np.sum((loglogistic(E, 1.0, math.exp(th[0]), math.exp(th[1])) - S) ** 2)
        x0s = [[float(np.median(lE)) + d, 0.0] for d in (0.0, 1.0, 2.0)]
        bnds = [(5.0, 40.0), (math.log(0.05), math.log(10.0))]
        out = lambda th: {"A": 1.0, "k_half": math.exp(th[0]), "alpha": math.exp(th[1])}
    elif form == "loglogistic_Afree":
        f = lambda th: np.sum((loglogistic(E, _sig(th[2]), math.exp(th[0]), math.exp(th[1])) - S) ** 2)
        x0s = [[float(np.median(lE)) + d, 0.0, a] for d in (0.0, 1.0, 2.0) for a in (0.0, 3.0)]
        bnds = [(5.0, 40.0), (math.log(0.05), math.log(10.0)), (-LOGIT_BOUND, LOGIT_BOUND)]
        out = lambda th: {"A": _sig(th[2]), "k_half": math.exp(th[0]), "alpha": math.exp(th[1])}
    else:  # lognormal_A1 on the panel axis
        f = lambda th: np.sum((special.ndtr((lE - th[0]) / math.exp(th[1])) - S) ** 2)
        x0s = [[float(np.median(lE)) + d, 0.0] for d in (0.0, 1.0, 2.0)]
        bnds = [(5.0, 40.0), (math.log(0.05), math.log(20.0))]
        out = lambda th: {"A": 1.0, "mu": th[0], "sigma": math.exp(th[1]), "median_effort": math.exp(th[0])}
    best = None
    for x0 in starts if starts is not None else x0s:
        res = optimize.minimize(f, np.array(x0, float), method="L-BFGS-B", bounds=bnds)
        if best is None or res.fun < best.fun:
            best = res
    o = out(best.x)
    o["sse"] = float(best.fun)
    o["rmse"] = math.sqrt(best.fun / len(S))
    o["theta"] = [float(v) for v in best.x]
    return o


PANEL_FORMS = ("loglogistic_A1", "loglogistic_Afree", "lognormal_A1")


# --------------------------------------------------------------------- bootstrap

def ci(vals):
    v = np.asarray([x for x in vals if x is not None and np.isfinite(x)], float)
    if len(v) == 0:
        return None
    return {"lo": float(np.percentile(v, 2.5)), "hi": float(np.percentile(v, 97.5)),
            "median": float(np.median(v)), "n": int(len(v))}


_CTX: dict = {}


def _boot_rep(idx):
    models, finished, unit, point = _CTX["models"], _CTX["finished"], _CTX["unit"], _CTX["point"]
    out = []
    for m in models:
        d = task_intervals(models[m], unit, idx)
        starts = [np.array(point["H1_single"][m]["theta"])] + default_starts("H1", [d])[:1]
        _, _, (p,) = fit_survival([d], "H1", starts)
        out += [(("H1", m, "A"), p[0]), (("H1", m, "median_effort"), math.exp(p[1])), (("H1", m, "sigma"), p[2])]
        E, S = panel_points(models[m], unit, idx)
        for form in PANEL_FORMS:
            pf = fit_panel(E, S, form, starts=[point["panel"][m][form]["theta"]])
            for k in ("A", "k_half", "alpha", "sigma", "median_effort"):
                if k in pf and not (form.endswith("A1") and k == "A"):
                    out.append(((form, m, k), pf[k]))
    data = [task_intervals(models[m], unit, idx) for m in finished]
    for hyp in ("H2", "H3"):
        starts = [np.array(point[hyp]["theta"])] + default_starts(hyp, data)[:1]
        _, _, params = fit_survival(data, hyp, starts)
        for m, p in zip(finished, params):
            out += [((hyp, m, "A"), p[0]), ((hyp, m, "median_effort"), math.exp(p[1])), ((hyp, m, "sigma"), p[2])]
        if hyp == "H3":
            med = {m: math.exp(p[1]) for m, p in zip(finished, params)}
            for m in finished[1:]:
                out.append((("H3", m, f"effort_ratio_vs_{short(finished[0])}"), med[m] / med[finished[0]]))
    return out


def bootstrap(models, finished, unit, reps, seed, point, jobs):
    import multiprocessing as mp
    rng = np.random.default_rng(seed)
    n_tasks = len(next(iter(models.values()))["tasks"])
    idxs = [rng.integers(0, n_tasks, n_tasks) for _ in range(reps)]
    _CTX.update(models=models, finished=finished, unit=unit, point=point)
    if jobs > 1:
        with mp.get_context("fork").Pool(jobs) as pool:
            results = pool.map(_boot_rep, idxs, chunksize=max(1, reps // (jobs * 8)))
    else:
        results = [_boot_rep(i) for i in idxs]
    acc: dict = {}
    for rep in results:
        for k, v in rep:
            acc.setdefault(k, []).append(v)
    return {k: ci(v) for k, v in acc.items()}


# ------------------------------------------------------------------- reporting

def mapping_note(sigma):
    return {"alpha_from_sigma_sd_match": math.pi / (sigma * math.sqrt(3)),
            "alpha_from_sigma_1702": 1.702 / sigma}


def marginal_steps(E, S, n_tasks, profiles):
    out, prevE, prevN = [], 0.0, 0
    for k, p in enumerate(profiles):
        N = int(round(S[k] * n_tasks))
        dE, dN = float(E[k] - prevE), N - prevN
        out.append({"profile": p, "cumulative_effort": float(E[k]), "delta_effort": dE, "newly_solved": dN,
                    "effort_per_extra_solve": dE / dN if dN > 0 else None})
        prevE, prevN = float(E[k]), N
    return out


def short(m):
    return m.split("__", 1)[1]


def plot(models, finished, partial, res, unit, out_dir):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    plt.rcParams.update({"font.size": 9, "axes.edgecolor": "#111827", "axes.labelcolor": "#404040",
                         "xtick.color": "#404040", "ytick.color": "#404040"})
    color = {m: COLORS[DISPLAY_ORDER.index(m) if m in DISPLAY_ORDER else 6] for m in models}
    label = lambda m: short(m) + (" (partial)" if m in partial else "")
    fig, axes = plt.subplots(1, 3, figsize=(18, 5.5))
    ax = axes[0]
    for m in models:
        E, S = panel_points(models[m], unit)
        ls = "--" if m in partial else "-"
        ax.plot(E, 100 * S, "o", color=color[m], ms=5, label=label(m))
        pf = res["panel_fits"][m]["loglogistic_A1"]
        xs = np.geomspace(E[0] / 2, max(E[-1] * 4, 1), 200)
        ax.plot(xs, 100 * loglogistic(xs, 1.0, pf["k_half"], pf["alpha"]), ls, color=color[m], lw=1.5, alpha=0.8)
    ax.set_xscale("log"); ax.set_xlabel(f"cumulative panel {unit} (cascade)"); ax.set_ylabel("solve rate (%)")
    ax.set_title("Cascade solve rate, fit S(E)=1/(1+(kHalf/E)^α)"); ax.grid(alpha=0.3, color="#e5e7eb"); ax.legend(fontsize=8)
    ax = axes[1]
    h3 = res["survival"]["finished"]["fits"]["H3"]["params"]
    solved_hi = np.concatenate([hi[sv] for _, hi, sv in (task_intervals(models[m], unit) for m in models)])
    xs = np.linspace(solved_hi.min() - 1.0, solved_hi.max() + 2.5, 300)
    for m in models:
        lo, hi, sv = task_intervals(models[m], unit)
        ev = np.sort(hi[sv]); n = len(sv)
        ax.step(np.exp(ev), 100 * np.arange(1, len(ev) + 1) / n, where="post", color=color[m], alpha=0.7, label=label(m))
        p = h3.get(m) or res["survival"]["H1_single"][m]["params"]
        ax.plot(np.exp(xs), 100 * cdf(xs, p["A"], p["mu"], p["sigma"]), "--" if m in partial else ":", color=color[m], lw=1.5)
    ax.set_xscale("log"); ax.set_xlabel(f"{unit} spent on the task (cumulative over profiles)"); ax.set_ylabel("tasks solved (%)")
    ax.set_title("Per-task effort: empirical vs H3 fit (partials: own H1 fit)"); ax.grid(alpha=0.3, color="#e5e7eb"); ax.legend(fontsize=7)
    ax = axes[2]
    z = np.linspace(-4, 4, 200)
    ax.plot(z, stats.norm.cdf(z), "-", color="#111827", lw=2, label="shared shape Φ")
    for m in finished:
        lo, hi, sv = task_intervals(models[m], unit)
        p = h3[m]
        ev = np.sort((hi[sv] - p["mu"]) / p["sigma"]); n = len(sv)
        ax.step(ev, np.arange(1, len(ev) + 1) / n / p["A"], where="post", color=color[m], alpha=0.8, label=label(m))
    ax.set_xlabel("(ln effort − μ_model) / σ"); ax.set_ylabel("solved / ceiling A")
    ax.set_title("Collapse onto one curve (H3)"); ax.grid(alpha=0.3, color="#e5e7eb"); ax.legend(fontsize=7)
    fig.suptitle("PROVISIONAL — EVB harness repetition-guard fix pending", color="#b91c1c", fontsize=10)
    fig.tight_layout()
    fig.savefig(out_dir / f"effort_scaling_{unit}.png", dpi=130)
    fig.savefig(out_dir / f"effort_scaling_{unit}.svg")
    plt.close(fig)


def curate(models_dirs, out: Path):
    """Small curated copies: summary CSV + results JSON with run_dir reduced to its basename."""
    data = out / "data"
    if data.exists():
        shutil.rmtree(data)
    for name, d in models_dirs.items():
        dst = data / name
        dst.mkdir(parents=True)
        shutil.copyfile(d / "cascade_summary.csv", dst / "cascade_summary.csv")
        rows = json.loads((d / "cascade_results.json").read_text())
        for r in rows:
            if r.get("run_dir"):
                r["run_dir"] = Path(r["run_dir"]).name
        (dst / "cascade_results.json").write_text(json.dumps(rows, separators=(",", ":")) + "\n")


def leaderboard_comparison(models, path: Path):
    if not path.is_file():
        return None
    lb = json.loads(path.read_text())
    by_model = {r["model"]: r for r in lb.get("results", [])}
    out = {}
    for m, v in models.items():
        key = m.replace("__", "/")
        r = by_model.get(key)
        last = v["profiles"][-1]
        reached = LEADERBOARD_PROFILE in v["profiles"]
        solved = {t for t, k in zip(v["tasks"], v["solved_at"]) if k >= 0}
        row = {"cascade_last_profile": last, "cascade_reached_leaderboard_budget": reached,
               "cascade_solved": len(solved),
               "cascade_cumulative_tokens": float(v["spend"]["tokens"].sum() + v["post_solve"]["tokens"].sum()),
               "leaderboard_solved": r["solved"] if r else None,
               "leaderboard_total_tokens": r.get("total_tokens") if r else None,
               "leaderboard_infra_invalid": r.get("infra_invalid") if r else None}
        if r and r.get("solved_tasks") is not None:
            ls = set(r["solved_tasks"])
            row.update({"both": len(solved & ls), "cascade_only": len(solved - ls), "leaderboard_only": len(ls - solved)})
        out[key] = row
    return {"source": str(path.relative_to(ROOT)) if path.is_relative_to(ROOT) else str(path),
            "leaderboard_profile": lb.get("effort", {}).get("profile"), "scope": lb.get("scope"), "models": out}


def minimax_check(path: Path):
    """Re-derive the site's v0.1 MiniMax fit (kHalf 4.6M, alpha 1.19) with the same fitting code."""
    if not path.is_file():
        return None
    rows = list(csv.DictReader(path.open()))
    E = np.array([float(r["cumulative_total_tokens"]) for r in rows])
    S = np.array([float(r["cumulative_solved"]) / float(r["task_count"]) for r in rows])
    f = fit_panel(E, S, "loglogistic_A1")
    return {"source": str(path.relative_to(ROOT)) if path.is_relative_to(ROOT) else str(path),
            "site_values": {"k_half": 4600000, "alpha": 1.19}, "refit": f}


def run_unit(models, finished, partial, unit, reps, seed, jobs):
    names = list(models)
    res = {"survival": {}, "panel_fits": {}, "panel_points": {}, "marginal": {}}
    # Per-model H1 fits (all models, partials flagged).
    single = {}
    for m in names:
        d = task_intervals(models[m], unit)
        theta, nll, (p,) = fit_survival([d], "H1")
        single[m] = {"theta": list(map(float, theta)), "nll": nll, "partial": m in partial,
                     "params": survival_params_dict([m], [p])[m], **mapping_note(p[2])}
    res["survival"]["H1_single"] = single

    def nested(group):
        data = [task_intervals(models[m], unit) for m in group]
        fits = {}
        for hyp in ("H1", "H2", "H3"):
            theta, nll, params = fit_survival(data, hyp)
            k = n_params(hyp, len(group))
            fits[hyp] = {"hypothesis": hyp, "nll": nll, "k": k, "aic": 2 * k + 2 * nll,
                         "theta": list(map(float, theta)), "params": survival_params_dict(group, params)}
        tests = {}
        for small, big in (("H2", "H1"), ("H3", "H2"), ("H3", "H1")):
            lr = 2 * (fits[small]["nll"] - fits[big]["nll"])
            df = fits[big]["k"] - fits[small]["k"]
            tests[f"{small}_vs_{big}"] = {"lr_stat": lr, "df": df, "p_value": float(stats.chi2.sf(max(lr, 0), df))}
        aics = {h: f["aic"] for h, f in fits.items()}
        best = min(aics, key=aics.get)
        return {"models": group, "fits": fits, "likelihood_ratio_tests": tests, "preferred_by_aic": best,
                "delta_aic": {h: a - aics[best] for h, a in aics.items()}}

    res["survival"]["finished"] = nested(finished)
    if partial:
        res["survival"]["sensitivity_all_models"] = nested(finished + partial)
    for m in names:
        E, S = panel_points(models[m], unit)
        res["panel_points"][m] = [{"profile": p, "cumulative_effort": float(e), "solve_rate": float(s),
                                   "cumulative_solved": int(round(s * len(models[m]["tasks"])))}
                                  for p, e, s in zip(models[m]["profiles"], E, S)]
        res["panel_fits"][m] = {form: fit_panel(E, S, form) for form in PANEL_FORMS}
        ln = res["panel_fits"][m]["lognormal_A1"]
        res["panel_fits"][m]["mapping_from_panel_lognormal"] = {"k_half_equiv": ln["median_effort"], **mapping_note(ln["sigma"])}
        res["marginal"][m] = marginal_steps(E, S, len(models[m]["tasks"]), models[m]["profiles"])
    point = {"H1_single": single, "H2": res["survival"]["finished"]["fits"]["H2"],
             "H3": res["survival"]["finished"]["fits"]["H3"], "panel": res["panel_fits"]}
    if reps > 0:
        boot = bootstrap(models, finished, unit, reps, seed, point, jobs)
        res["bootstrap_ci95"] = {}
        for (scope, m, k), v in sorted(boot.items()):
            res["bootstrap_ci95"].setdefault(scope, {}).setdefault(m, {})[k] = v
    return res


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--input", type=Path, default=DEFAULT_INPUT, help="cascade root with <provider>__<model>/ dirs")
    ap.add_argument("--finished", nargs="*", default=DEFAULT_FINISHED,
                    help="models whose cascade completed p01-p08 (shared-shape test set); others are 'partial'")
    ap.add_argument("--exclude", nargs="*", default=[], help="model dirs to ignore entirely")
    ap.add_argument("--bootstrap", type=int, default=1000)
    ap.add_argument("--seed", type=int, default=20261020)
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 1, help="bootstrap worker processes")
    ap.add_argument("--leaderboard", type=Path, default=DEFAULT_LEADERBOARD)
    ap.add_argument("--minimax-summary", type=Path, default=DEFAULT_MINIMAX)
    ap.add_argument("--out", type=Path, default=HERE)
    ap.add_argument("--no-curate", action="store_true", help="do not refresh data/ copies")
    args = ap.parse_args()

    dirs = {d.name: d for d in sorted(args.input.iterdir())
            if (d / "cascade_results.json").is_file() and d.name not in args.exclude}
    order = [m for m in DISPLAY_ORDER if m in dirs] + [m for m in dirs if m not in DISPLAY_ORDER]
    models = {m: load_model(dirs[m]) for m in order}
    task_sets = {tuple(v["tasks"]) for v in models.values()}
    if len(task_sets) != 1:
        raise SystemExit("models do not share one task panel; paired bootstrap needs identical panels")
    finished = [m for m in order if m in args.finished]
    partial = [m for m in order if m not in args.finished]
    for m in finished:
        if LEADERBOARD_PROFILE not in models[m]["profiles"]:
            raise SystemExit(f"{m} is listed as finished but has no {LEADERBOARD_PROFILE} rows")

    args.out.mkdir(parents=True, exist_ok=True)
    (args.out / "figures").mkdir(exist_ok=True)
    if not args.no_curate:
        curate(dirs, args.out)

    summary = {
        "provisional": True,
        "provisional_reason": "EVB harness repetition-guard bug; cascade to be rerun on the fixed harness",
        "input": str(args.input), "bootstrap_reps": args.bootstrap, "seed": args.seed,
        "finished_models": finished, "partial_models": partial, "task_count": len(models[order[0]]["tasks"]),
        "models": {}, "units": {},
        "leaderboard_comparison": leaderboard_comparison(models, args.leaderboard),
        "site_minimax_v01_check": minimax_check(args.minimax_summary),
        "notes": {
            "survival_median_effort": "exp(mu): per-TASK effort at which half of the reachable tasks are solved",
            "panel_k_half": "cumulative PANEL effort (all 50 tasks, cascade) at which S = A/2; the /benchmark unit",
            "alpha_sigma_mapping": "logistic with slope alpha in ln E vs normal with sd sigma: alpha = pi/(sigma*sqrt3) "
                                   "matches the sd, alpha = 1.702/sigma matches the CDF best; kHalf = exp(mu) when A = 1",
        },
    }
    for m in order:
        v = models[m]
        summary["models"][m] = {
            "partial": m in partial, "profiles_run": v["profiles"], "tasks": len(v["tasks"]),
            "solved": int((v["solved_at"] >= 0).sum()),
            "infra_invalid_runs_total": int(v["infra"].sum()),
            "post_solve_reruns": v["post_solve_runs"],
            "per_profile": [{"profile": r["profile"], "max_attempts": int(r["max_attempts"]),
                             "max_tool_calls": int(r["max_tool_calls"]), "executed_tasks": int(r["executed_tasks"]),
                             "infra_invalid_tasks": int(r["infra_invalid_tasks"]), "newly_solved": int(r["newly_solved"]),
                             "cumulative_solved": int(r["cumulative_solved"]),
                             "cumulative_total_tokens": int(r["cumulative_total_tokens"]),
                             "cumulative_requests": int(r["cumulative_requests"])}
                            for r in v["summary_csv"] if r["profile"] in v["profiles"]],
        }
    for unit in UNITS:
        print(f"[{unit}] fitting + {args.bootstrap} bootstrap reps ...", flush=True)
        res = run_unit(models, finished, partial, unit, args.bootstrap, args.seed, args.jobs)
        summary["units"][unit] = res
        plot(models, finished, partial, res, unit, args.out / "figures")
        fin = res["survival"]["finished"]
        print(f"  preferred by AIC: {fin['preferred_by_aic']}  LRT: " +
              ", ".join(f"{k} p={t['p_value']:.3f}" for k, t in fin["likelihood_ratio_tests"].items()))
        for m in order:
            p = res["survival"]["H1_single"][m]["params"]
            pf = res["panel_fits"][m]["loglogistic_A1"]
            print(f"  {short(m):24} H1 A={p['A']:.3f} med={p['median_effort']:.4g} sigma={p['sigma']:.3f} | "
                  f"panel kHalf={pf['k_half']:.4g} alpha={pf['alpha']:.3f}{'  (partial)' if m in partial else ''}")

    with (args.out / "cascade_points.csv").open("w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["model", "partial", "profile", "cumulative_total_tokens", "cumulative_requests",
                    "cumulative_solved", "solve_rate", "infra_invalid_tasks"])
        for m in order:
            pts_t = summary["units"]["tokens"]["panel_points"][m]
            pts_r = summary["units"]["requests"]["panel_points"][m]
            pp = summary["models"][m]["per_profile"]
            for a, b, c in zip(pts_t, pts_r, pp):
                w.writerow([m.replace("__", "/"), int(m in partial), a["profile"], int(a["cumulative_effort"]),
                            int(b["cumulative_effort"]), a["cumulative_solved"], round(a["solve_rate"], 4),
                            c["infra_invalid_tasks"]])
    (args.out / "fit_summary.json").write_text(json.dumps(summary, indent=1, default=float) + "\n")
    print("wrote", args.out / "fit_summary.json")


if __name__ == "__main__":
    main()

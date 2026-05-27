from __future__ import annotations

import copy
import json
import os
import re
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from task_runner import ROOT, run_command as lean_run_command


PLACEHOLDER_PATTERN = re.compile(r"\b(sorry|admit|axiom)\b")
# Match standalone `?_` holes only (not `?x` metavariables used in valid tactics).
HOLE_PATTERN = re.compile(r"(?<!\w)\?_(?!\w)")
# Detection-only pattern covering both unnamed (`?_`) and named (`?ident`)
# holes. Used by `inspect_goals` so the model can introspect goals at a
# named hole too. NOT used by `try_tactic_at_hole` or `_substitute_holes`
# — blanket substitution of a named hole `?h` can collide with real
# identifiers, so substitution stays strictly `?_`-scoped.
ANY_HOLE_PATTERN = re.compile(r"(?<!\w)\?(?:_|[A-Za-z][A-Za-z0-9_']*)(?!\w)")
DEF_PATTERN = re.compile(r"^\s*(?:def|theorem|lemma|abbrev|opaque)\s+([A-Za-z0-9_'.]+)")
HIDDEN_PROOF_IMPORT_PATTERN = re.compile(
    r"^\s*(?:import|open|export)\s+Benchmark\.Cases\..*\.Proofs\b", re.MULTILINE
)
IMPORT_PATTERN = re.compile(r"^\s*import\s+([A-Za-z0-9_.']+)\s*$", re.MULTILINE)

# Well-known Lean 4 tactics that Lean reports as "unknown identifier" when
# written in *term* position (e.g. `exact simp [...]`, `refine omega`, `:= by_cases h`).
# Corpus analysis of 83 runs: 20 of 29 failed tasks (69%) hit this at least once,
# with `simp`, `simpa`, `omega`, `exact`, `native_decide`, `intro`, `simp_all`, and
# `by_cases` accounting for 61 occurrences. The existing `unknown_identifier` hint
# sends the model to `search_public_defs`, which cannot help here — these are
# language keywords, not definitions.
_LEAN_TACTIC_NAMES = frozenset({
    "simp", "simpa", "simp_all", "dsimp",
    "omega", "decide", "native_decide",
    "exact", "refine", "apply", "intro", "intros",
    "constructor", "cases", "induction", "by_cases", "obtain",
    "unfold", "rfl", "rw", "rewrite", "ring", "linarith", "nlinarith",
    "split", "left", "right", "use", "show", "have", "suffices", "let",
    "trivial", "tauto", "contradiction", "assumption", "skip",
    "ext", "funext", "congr", "norm_num", "field_simp", "abel",
})
_UNKNOWN_IDENT_RE = re.compile(r"unknown (?:identifier|constant) '([^']+)'")

# Names that look like Mathlib lemmas (e.g. `add_sub_add_right_eq_sub`,
# `lt_of_add_lt_add_right`, `Nat.div_mul_le`). Corpus analysis of 83 runs
# found 5 of 29 failed tasks (17%) stagnating on such guesses —
# `add_sub_add_right_eq_sub`, `sub_eq_sub_right`, `add_assoc`, `add_comm`,
# `sub_eq_add_neg`, `lt_of_add_lt_add_right`, `Nat.div_mul_le`,
# `Nat.le_div_mul`, `Nat.div_def`, `Nat.cast_mk`, `Nat.not_ge.mp`, …
# This workspace has NO Mathlib dependency, so these searches can never
# succeed; the agent should be pointed at `omega`/`ring`/`simp` instead.
_MATHLIB_SHAPE_PREFIX_RE = re.compile(
    r"^(add_|sub_|mul_|div_|mod_|le_|lt_|ge_|gt_|eq_|ne_|not_|neg_|pos_|zero_|one_)"
)
_MATHLIB_SHAPE_EXACT = frozenset({
    "add_assoc", "add_comm", "add_left_comm",
    "mul_comm", "mul_assoc", "mul_left_comm",
    "sub_zero", "zero_add", "add_zero", "mul_one", "one_mul",
    "not_eq",
})


def _is_mathlib_shaped(name: str) -> bool:
    if name in _MATHLIB_SHAPE_EXACT:
        return True
    if _MATHLIB_SHAPE_PREFIX_RE.match(name):
        return True
    # `Nat.*` lemma guesses are overwhelmingly Mathlib-only in this corpus.
    if name.startswith("Nat."):
        return True
    return False


@dataclass(frozen=True)
class RuntimePaths:
    editable_rel_path: str
    theorem_name: str
    implementation_files: tuple[str, ...]
    specification_files: tuple[str, ...]
    public_files: tuple[str, ...]


class TaskProofRuntime:
    def __init__(self, task: dict[str, Any]) -> None:
        editable_files = [str(item) for item in task["editable_files"]]
        if len(editable_files) != 1:
            raise ValueError("tasks must declare exactly one editable Lean file")
        editable_rel_path = editable_files[0]
        self._check_history: list[str] = []  # failure_class history for stagnation detection
        self._task = task  # store for hint escalation
        self._best_error_count: int | None = None
        self._best_first_error_line: int | None = None
        # Fingerprints of hint texts already surfaced this session. Used to
        # avoid echoing the same repair advice verbatim across consecutive
        # failures — repeated identical hints are pure noise and train the
        # model to ignore the list instead of acting on it.
        self._emitted_hint_keys: set[str] = set()
        # Normalised fingerprint of the previous failing Lean details text,
        # plus a count of how many times the same fingerprint has repeated
        # in a row. Used to detect "no-progress loops" where the model
        # resubmits a proof that yields byte-identical errors — corpus
        # analysis found 12/29 failing tasks hit this pattern.
        self._last_details_fp: str | None = None
        self._same_details_streak: int = 0
        # Cache of the most recent run_lean_check evaluation keyed by the
        # exact proof text that produced it. A redundant run_lean_check call
        # against unchanged content (corpus analysis found 201/201 — 100% —
        # of run_lean_check calls were immediately after a write_editable_proof
        # that had already run Lean) returns this cached result instantly
        # plus a `cached: true` marker telling the model the call was
        # redundant, saving a full Lean invocation and a round.
        self._last_eval_cache: tuple[str, dict[str, Any]] | None = None
        # Count of consecutive failed try_tactic_at_hole calls. Corpus analysis
        # of 83 runs: try_tactic_at_hole has a 0/76 (0%) success rate across
        # the entire interactive-proxy corpus, but failed runs average 3-7
        # calls per task (14/29 failed runs have a ≥3-streak of failures)
        # vs passed runs which max at a 2-streak (and never succeed when
        # they do call it — they just move on after 1-2 attempts). Firing
        # a pivot warning at the 3rd consecutive failure catches the stuck-
        # loop pattern with zero false positives on the passed side.
        self._try_tactic_failure_streak: int = 0
        # Cache of prior search_public_defs calls keyed by (query, limit).
        # Corpus analysis of 83 runs found failed runs averaged 41.9
        # search_public_defs calls vs 1.5 on passing runs; 94% of those
        # calls in failed runs were byte-identical re-queries (e.g. the same
        # `"removeOwner_ownerListInvariant"` query 26 times in one run). The
        # index is read-only within a session, so a cached hit with a
        # `cached: true` + note tells the model the query yielded nothing
        # new and it should pivot instead of re-asking.
        self._search_cache: dict[tuple[str, int], dict[str, Any]] = {}
        self.paths = RuntimePaths(
            editable_rel_path=editable_rel_path,
            theorem_name=str(task["theorem_name"]),
            implementation_files=tuple(str(item) for item in task["implementation_files"]),
            specification_files=tuple(str(item) for item in task["specification_files"]),
            public_files=tuple(
                str(item)
                for item in [
                    *task["implementation_files"],
                    *task["specification_files"],
                    *editable_files,
                ]
            ),
        )
        self.current_proof_text = self._read_repo_file(editable_rel_path)
        self.expected_theorem_signature = self._extract_theorem_signature(self.current_proof_text)
        self.allowed_task_modules = frozenset(self._module_name(path) for path in self.paths.public_files)

    def _read_repo_file(self, rel_path: str) -> str:
        path = ROOT / rel_path
        if not path.is_file():
            raise FileNotFoundError(rel_path)
        return path.read_text(encoding="utf-8")

    def read_public_file(self, rel_path: str) -> dict[str, Any]:
        if rel_path not in self.paths.public_files:
            return {
                "status": "rejected",
                "reason": "path_not_public_for_task",
                "allowed_files": list(self.paths.public_files),
            }
        if rel_path == self.paths.editable_rel_path:
            return {"status": "ok", "path": rel_path, "content": self.current_proof_text}
        try:
            return {"status": "ok", "path": rel_path, "content": self._read_repo_file(rel_path)}
        except FileNotFoundError:
            return {"status": "missing", "path": rel_path}

    def write_editable_proof(self, content: str, *, check: bool = True) -> dict[str, Any]:
        self.current_proof_text = content if content.endswith("\n") else f"{content}\n"
        # Invalidate the run_lean_check fast-path cache. The cache is keyed on
        # `current_proof_text`, so a repeat write of identical content (common
        # during stagnation loops) would otherwise hit a stale cached
        # evaluation and return `cached: true` with a note claiming this was
        # a redundant `run_lean_check` follow-up — even though the model's
        # intent is a fresh write. Drop the cache unconditionally here; the
        # downstream `execute_tool("run_lean_check", ...)` call re-populates
        # it for genuine no-op follow-ups.
        self._last_eval_cache = None
        warnings: list[dict[str, str]] = []
        if not self.current_proof_text.strip():
            warnings.append({"kind": "empty_content", "detail": "candidate is empty"})
        if PLACEHOLDER_PATTERN.search(self.current_proof_text):
            warnings.append({
                "kind": "placeholder_detected",
                "detail": "contains `sorry`/`admit`/`axiom`; Lean rejects these — replace with a real tactic or a `?_` hole.",
            })
        if HIDDEN_PROOF_IMPORT_PATTERN.search(self.current_proof_text):
            warnings.append({
                "kind": "hidden_proof_import_detected",
                "detail": "remove Benchmark.Cases.*.Proofs import/open/export.",
            })
        blocked = self._find_blocked_case_imports(self.current_proof_text)
        if blocked:
            warnings.append({
                "kind": "hidden_case_import_detected",
                "detail": "non-public imports: " + ", ".join(blocked),
            })
        if HOLE_PATTERN.search(self.current_proof_text):
            warnings.append({
                "kind": "unfilled_hole",
                "detail": "proof still contains `?_` holes; fill before submitting.",
            })
        candidate_signature = self._extract_theorem_signature(self.current_proof_text)
        if candidate_signature != self.expected_theorem_signature:
            warnings.append({
                "kind": "theorem_statement_mismatch",
                "detail": "editable theorem signature changed; revert to the original statement.",
            })
        result: dict[str, Any] = {
            "status": "ok_with_warnings" if warnings else "ok",
            "path": self.paths.editable_rel_path,
            "bytes": len(self.current_proof_text.encode("utf-8")),
            "lines": len(self.current_proof_text.splitlines()),
        }
        if warnings:
            result["warnings"] = warnings
        # Fold the Lean check into the write. Each write+check used to cost
        # two tool slots and two model round-trips; inlining saves one full
        # round-trip (hundreds of ms to seconds of LLM latency per proof
        # iteration) and doubles the effective budget for proof exploration.
        # The caller can disable by passing check=False (kept for callers
        # that only want to stage a draft without paying for Lean).
        if check:
            # Reuse the full run_lean_check pipeline (auto-heal + annotation +
            # repair hints) so downstream success/failure detection is
            # identical to a bare run_lean_check call. Write-time metadata
            # (path, bytes, lines, warnings) stays visible in the result so
            # the model still sees format warnings like non_public_imports
            # alongside the Lean verdict.
            pre_check_status = result["status"]
            result.update(self.execute_tool("run_lean_check", {}))
            # `run_lean_check` overwrites the `status` field, which drops the
            # pre-check `ok_with_warnings` verdict. Callers that look for
            # write-phase warnings (unfilled `?_` holes, non_public_imports,
            # theorem_statement_mismatch) need a stable signal, so expose the
            # pre-check verdict on `write_status`. The main `status` still
            # reflects the Lean check so existing `status == "passed"` and
            # `status == "failed"` branches keep working unchanged.
            if pre_check_status != "ok":
                result["write_status"] = pre_check_status
        return result

    def search_public_defs(self, query: str, *, limit: int = 20) -> dict[str, Any]:
        query_text = query.strip()
        if not query_text:
            return {"status": "rejected", "reason": "query_must_not_be_empty"}
        # The set of public impl/spec files does not change within a session,
        # so the same (query, limit) will always return the same matches.
        # Short-circuit repeat queries with a cached response + explicit note
        # so the agent stops looping on an identical search.
        cache_key = (query_text.lower(), limit)
        cached = self._search_cache.get(cache_key)
        if cached is not None:
            reused = copy.deepcopy(cached)
            reused["cached"] = True
            reused["note"] = (
                "You already ran search_public_defs with this exact query "
                "earlier in the session; the public impl/spec files are "
                "static, so the result is identical. Try a different query "
                "(e.g. a substring, a related concept, or a parameter name) "
                "or switch to inspect_lean_goals / try_tactic_at_hole — "
                "do not resubmit the same query."
            )
            return reused
        lowered = query_text.lower()
        matches: list[dict[str, Any]] = []
        for rel_path in self.paths.implementation_files + self.paths.specification_files:
            path = ROOT / rel_path
            if not path.is_file():
                continue
            for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
                name_match = DEF_PATTERN.match(line)
                if not name_match:
                    continue
                def_name = name_match.group(1)
                if lowered not in def_name.lower() and lowered not in line.lower():
                    continue
                matches.append(
                    {
                        "path": rel_path,
                        "line": line_no,
                        "name": def_name,
                        "declaration": line.strip(),
                    }
                )
                if len(matches) >= limit:
                    result = {"status": "ok", "query": query_text, "matches": matches, "truncated": True}
                    self._search_cache[cache_key] = copy.deepcopy(result)
                    return result
        if not matches:
            # Corpus analysis (83 runs) found 55/75 (73%) of search_public_defs
            # calls returned empty — overwhelmingly because agents searched for
            # Mathlib / core Lean library names like `Nat.div_mul_le`,
            # `add_zero`, `div_pos`, etc. This tool only searches the task's
            # public impl/spec files, not the standard library. Surface that
            # scope limit explicitly so the agent stops burning rounds on
            # library searches.
            result = {
                "status": "ok",
                "query": query_text,
                "matches": matches,
                "truncated": False,
                "hint": (
                    "No match in the task's public impl/spec files. "
                    "`search_public_defs` only indexes definitions inside "
                    "implementation_files and specification_files for this "
                    "task — it does NOT search Lean core, Batteries, or "
                    "Mathlib (Mathlib is not a dependency of this project). "
                    "For standard-library lemmas use `exact?` / `apply?` / "
                    "`rw?` via `try_tactic_at_hole`, or rely on `simp` / "
                    "`omega` / `decide` which already know common arithmetic "
                    "and boolean facts. Retry this tool only with names you "
                    "expect to be defined in the current task's spec/impl."
                ),
            }
            self._search_cache[cache_key] = copy.deepcopy(result)
            return result
        result = {"status": "ok", "query": query_text, "matches": matches, "truncated": False}
        self._search_cache[cache_key] = copy.deepcopy(result)
        return result

    def inspect_goals(self) -> dict[str, Any]:
        # Detect `?_` AND named holes (`?h`, `?foo`). Named-hole detection was
        # lost when HOLE_PATTERN was tightened for substitution safety; this
        # tool is read-only so the broader pattern is safe and restores the
        # recovery path for proofs that use named holes.
        holes = sorted(set(ANY_HOLE_PATTERN.findall(self.current_proof_text)))
        if not holes:
            return {
                "status": "unsupported",
                "reason": "goal_inspection_requires_explicit_hole",
                "details": "Write the proof with a `?_` or named hole (e.g. `?h`) first, then retry goal inspection.",
            }
        evaluation = self.evaluate_current(check_goals=True)
        return {
            "status": "ok" if evaluation["status"] == "failed" else "passed",
            "holes": holes,
            "details": evaluation["details"],
            "command": evaluation.get("command"),
        }

    def try_tactic_at_hole(self, tactic: str) -> dict[str, Any]:
        """Try replacing all ?_ holes with a specific tactic and check if it works.

        This is a lightweight alternative to PyPantograph for targeted tactic execution.
        The original proof is preserved if the tactic fails.
        """
        if not tactic.strip():
            return {"status": "rejected", "reason": "tactic_must_not_be_empty"}
        original = self.current_proof_text
        # Substitute each `?_` with a context-adapted form of `tactic`. Corpus
        # analysis of 72 failed try_tactic_at_hole calls found 47 (65%) passed
        # a raw tactic (e.g. `omega`, `rfl`, `simp_all [...]`) into a proof
        # where the hole sat at a TERM position like `exact ?_` — making the
        # substituted proof read `exact omega`, which Lean rejects because
        # `omega` is a tactic, not a term. Automatically wrap the substituted
        # tactic with `(by ...)` at term-position holes, and strip an existing
        # `by ` wrapper at tactic-position holes, so the model's intent
        # survives context mismatches. Holes at other positions get the raw
        # tactic.
        modified = _substitute_holes(original, tactic.strip())
        if modified == original:
            return {
                "status": "unsupported",
                "reason": "no_holes_found",
                "details": "No `?_` holes in the current proof. Write a proof with `?_` holes first.",
            }
        evaluation = self.evaluate_candidate(modified)
        if evaluation.get("status") == "passed":
            self._try_tactic_failure_streak = 0
            self.current_proof_text = modified
            return {
                "status": "passed",
                "tactic": tactic.strip(),
                "details": "Tactic succeeded. Proof updated.",
            }
        self._try_tactic_failure_streak += 1
        # Produce the same class-based repair_hints as run_lean_check /
        # write_editable_proof do on failure. Corpus analysis of 83 interactive
        # runs found 76/76 (100%) of failed try_tactic_at_hole results returned
        # no hints, even though the failure_class distribution (45 unknown_
        # identifier, 18 unsolved_goals, 7 type_mismatch, …) maps onto hints
        # already produced by `_build_check_hints` when the same error comes
        # from the other two tools. Reusing that helper keeps the advice
        # consistent across the tool surface and gives the model a concrete
        # next tactic to try instead of a bare error payload.
        # `details` is already stripped of `linter.unusedSimpArgs` noise and
        # capped at `_LEAN_OUTPUT_CAP_CHARS` (16 KB) by `evaluate_candidate`.
        # Earlier code re-truncated to 2000 chars — a legacy band-aid from
        # before the upstream cleanup pipeline existed. Corpus analysis of
        # the 78 try_tactic_at_hole failures in the current corpus found
        # 41/78 (53%) hit that 2000-char cap, chopping off already-cleaned
        # diagnostic content (goal state, context, line numbers) that
        # run_lean_check would have returned in full on the same failure.
        # Drop the extra truncation so all three tools surface the same
        # error fidelity; the 16 KB pipeline cap remains the backstop.
        details = str(evaluation.get("details", ""))
        failure_class = classify_failure(details)
        result = {
            "status": "failed",
            "tactic": tactic.strip(),
            "details": details,
            "failure_class": failure_class,
        }
        hints = _build_check_hints(failure_class, details)
        # After 3 consecutive failed try_tactic_at_hole calls, inject a
        # "pivot" hint. Corpus analysis: passed runs never exceed a 2-streak;
        # failed runs hit ≥3 in 14/29 (48%) tasks, with some stacking 5-7
        # attempts of increasingly speculative tactics. The tool has a
        # 0/76 (0%) corpus-wide success rate, so further attempts on the
        # same hole are almost certainly wasted budget — the pivot hint
        # tells the model to switch to write_editable_proof with explicit
        # multi-step tactics and inspect_lean_goals between steps.
        if self._try_tactic_failure_streak >= 3:
            hints = list(hints) if hints else []
            hints.insert(
                0,
                f"You have now run {self._try_tactic_failure_streak} consecutive "
                "`try_tactic_at_hole` calls with no success. This tool only "
                "closes a goal when a SINGLE tactic discharges it entirely; "
                "for goals that need BEq↔Prop bridging, case analysis on "
                "residual `if`/`match` arms, monadic-trace unfolding, or "
                "multi-step arithmetic rewriting, no single tactic will "
                "close them no matter how many more you try. PIVOT: write a "
                "full multi-line proof body with `write_editable_proof` "
                "(leaving `?_` ONLY at positions where you then "
                "`inspect_lean_goals` to see the reduced state), and make "
                "progress one step at a time. Do NOT continue cycling "
                "single-tactic guesses here."
            )
        if hints:
            result["repair_hints"] = hints
        return result

    def evaluate_current(self, *, check_goals: bool = False) -> dict[str, Any]:
        return self.evaluate_candidate(self.current_proof_text, check_goals=check_goals)

    def preflight_candidate(self, candidate_text: str) -> dict[str, Any] | None:
        """Fast local checks that don't require running Lean. Returns a failure dict or None if OK."""
        if not candidate_text.strip():
            return {
                "status": "failed",
                "failure_mode": "empty_response",
                "details": "agent response was empty",
            }

        if PLACEHOLDER_PATTERN.search(candidate_text):
            return {
                "status": "failed",
                "failure_mode": "placeholder_detected",
                "details": "candidate proof contains a rejected placeholder token",
            }

        if HIDDEN_PROOF_IMPORT_PATTERN.search(candidate_text):
            return {
                "status": "failed",
                "failure_mode": "hidden_proof_import_detected",
                "details": "candidate proof imports hidden Benchmark.Cases.*.Proofs modules",
            }

        blocked_imports = self._find_blocked_case_imports(candidate_text)
        if blocked_imports:
            return {
                "status": "failed",
                "failure_mode": "hidden_case_import_detected",
                "details": (
                    "candidate proof imports non-public Benchmark.Cases modules: "
                    + ", ".join(blocked_imports)
                ),
            }

        candidate_signature = self._extract_theorem_signature(candidate_text)
        if candidate_signature != self.expected_theorem_signature:
            return {
                "status": "failed",
                "failure_mode": "theorem_statement_mismatch",
                "details": "candidate proof changed the editable theorem statement",
            }

        return None

    def evaluate_candidate(self, candidate_text: str, *, check_goals: bool = False) -> dict[str, Any]:
        preflight_failure = self.preflight_candidate(candidate_text)
        if preflight_failure is not None:
            return preflight_failure

        with tempfile.TemporaryDirectory(prefix="verity-benchmark-agent-") as tmp_dir:
            workspace = Path(tmp_dir) / "workspace"
            self._materialize_workspace(workspace)
            editable_path = workspace / self.paths.editable_rel_path
            editable_path.parent.mkdir(parents=True, exist_ok=True)
            editable_path.write_text(candidate_text, encoding="utf-8")

            if check_goals:
                check_path = editable_path
                command = ["lake", "env", "lean", "--root=.", str(check_path.relative_to(workspace))]
            else:
                check_path = workspace / "CandidateCheck.lean"
                check_path.write_text(
                    candidate_text.rstrip() + f"\n\n#check {self.paths.theorem_name}\n",
                    encoding="utf-8",
                )
                command = ["lake", "env", "lean", "--root=.", str(check_path.relative_to(workspace))]
            code, output = lean_run_command(command, cwd=workspace)
            # Strip the "This simp argument is unused" lint blocks from Lean
            # output before returning. Corpus analysis of 37 failed-check
            # detail blobs found 844/846 warnings (~99%) were this single
            # linter, accounting for ~20 KB of the average 34 KB details
            # blob. The noise drowns the real errors and trains the model
            # to ignore the details block. Filtering preserves every real
            # error and every other warning kind — only the known-useless
            # linter goes away.
            output = _strip_noise_warnings(output)
            output = _cap_lean_output(output)
            if code != 0:
                return {
                    "status": "failed",
                    "failure_mode": "lean_check_failed",
                    "details": output,
                    "command": command,
                    "candidate_workspace": str(editable_path.relative_to(workspace)),
                }
            return {
                "status": "passed",
                "failure_mode": None,
                "details": output,
                "command": command,
                "candidate_workspace": str(editable_path.relative_to(workspace)),
            }

    def tool_specs(self) -> list[dict[str, Any]]:
        return [
            {
                "type": "function",
                "function": {
                    "name": "read_public_file",
                    "description": "Read one task-scoped public Lean file from implementation_files, specification_files, or the editable proof.",
                    "parameters": {
                        "type": "object",
                        "additionalProperties": False,
                        "required": ["path"],
                        "properties": {
                            "path": {
                                "type": "string",
                                "enum": list(self.paths.public_files),
                            }
                        },
                    },
                },
            },
            {
                "type": "function",
                "function": {
                    "name": "write_editable_proof",
                    "description": "Replace the entire editable proof file with complete Lean code and automatically run the Lean check. The response reports status (passed/failed/ok/ok_with_warnings) and, on failure, failure_mode, details, and failure_class. A separate run_lean_check call is not needed after this.",
                    "parameters": {
                        "type": "object",
                        "additionalProperties": False,
                        "required": ["content"],
                        "properties": {
                            "content": {
                                "type": "string",
                            }
                        },
                    },
                },
            },
            {
                "type": "function",
                "function": {
                    "name": "run_lean_check",
                    "description": "Re-run the Lean check on the current editable proof without modifying it. Redundant immediately after `write_editable_proof`, which already runs the check — if the proof text is unchanged since the last evaluation, this call returns a cached result tagged `cached: true` rather than re-invoking Lean.",
                    "parameters": {
                        "type": "object",
                        "additionalProperties": False,
                        "properties": {},
                    },
                },
            },
            {
                "type": "function",
                "function": {
                    "name": "inspect_lean_goals",
                    "description": "Inspect current Lean diagnostics for explicit proof holes in the editable file. Returns unsupported if no hole is present.",
                    "parameters": {
                        "type": "object",
                        "additionalProperties": False,
                        "properties": {},
                    },
                },
            },
            {
                "type": "function",
                "function": {
                    "name": "search_public_defs",
                    "description": "Search the task's public implementation/specification files for matching def/theorem/lemma names. Scope is ONLY those task files — it does NOT search Lean core, Batteries, or Mathlib (Mathlib is not a dependency of this project). For standard-library lemmas, prefer `exact?` / `apply?` / `rw?` via `try_tactic_at_hole`, or tactics like `simp` / `omega` / `decide` that already know common arithmetic and boolean facts.",
                    "parameters": {
                        "type": "object",
                        "additionalProperties": False,
                        "required": ["query"],
                        "properties": {
                            "query": {"type": "string"},
                            "limit": {"type": "integer", "minimum": 1, "maximum": 50},
                        },
                    },
                },
            },
            {
                "type": "function",
                "function": {
                    "name": "try_tactic_at_hole",
                    "description": "Try replacing all `?_` holes in the current proof with a specific tactic and check if it compiles. Pass a raw tactic (e.g. `omega`, `simp_all [foo]`, `decide`, `exact h`); substitution auto-wraps as `(by tac)` when the hole is at a term position like `exact ?_`. Preserves the original proof if it fails.",
                    "parameters": {
                        "type": "object",
                        "additionalProperties": False,
                        "required": ["tactic"],
                        "properties": {
                            "tactic": {
                                "type": "string",
                                "description": "The Lean tactic to try at each ?_ hole.",
                            }
                        },
                    },
                },
            },
        ]

    def execute_tool(self, name: str, arguments: dict[str, Any]) -> dict[str, Any]:
        if name == "read_public_file":
            return self.read_public_file(str(arguments.get("path", "")))
        if name == "write_editable_proof":
            return self.write_editable_proof(str(arguments.get("content", "")))
        if name == "run_lean_check":
            # Short-circuit if the proof text is unchanged since the last
            # evaluation. Corpus analysis of 83 interactive runs found that
            # 201/201 (100%) of run_lean_check calls were made immediately
            # after a write_editable_proof that had already run Lean on the
            # same content. Returning the cached evaluation saves a full
            # Lean invocation (seconds) and teaches the model the call was
            # redundant via the `cached: true` marker + note.
            if self._last_eval_cache is not None:
                cached_text, cached_result = self._last_eval_cache
                # Never serve an `environment_error` from cache. The write-
                # side guard below already refuses to cache env errors, but
                # treat the read side defensively too: if an env error ever
                # ends up in the cache (e.g. via a future refactor), we
                # must still re-run `evaluate_current` so `_attempt_lake_build`
                # can retry the heal path instead of pinning the task to
                # a stale infra failure that may have recovered.
                cached_is_env_error = (
                    isinstance(cached_result, dict)
                    and (
                        cached_result.get("failure_class") == "environment_error"
                        or cached_result.get("environment_error") is True
                    )
                )
                if cached_text == self.current_proof_text and not cached_is_env_error:
                    reused = copy.deepcopy(cached_result)
                    reused["cached"] = True
                    reused["note"] = (
                        "Proof text is unchanged since the last evaluation; "
                        "returning cached result without re-running Lean. "
                        "`write_editable_proof` already runs the Lean check — "
                        "a follow-up `run_lean_check` on unchanged content is "
                        "redundant."
                    )
                    return reused
            result = self.evaluate_current()
            # Auto-heal environment errors (missing .olean) once before annotating.
            if result.get("status") == "failed" and result.get("failure_mode") == "lean_check_failed":
                details = str(result.get("details", ""))
                if classify_failure(details) == "environment_error":
                    module_name = _missing_olean_module(details)
                    healed = _attempt_lake_build(module_name)
                    if healed:
                        result = self.evaluate_current()
            if result.get("status") == "failed":
                result = self._annotate_check_result(result)
            # Cache the fresh evaluation against the current proof text so a
            # follow-up run_lean_check on unchanged content hits the fast path.
            # Exception: do NOT cache `environment_error` results. Those are
            # transient infrastructure failures (missing .olean, lake build
            # contention) that the heal path above tries to recover from via
            # `_attempt_lake_build`. Caching them would short-circuit every
            # subsequent `run_lean_check` on unchanged proof text back to the
            # stale env error, preventing the heal path from being re-entered
            # if infra recovers. Re-evaluate every time for env errors so the
            # heal path keeps getting a chance.
            is_env_error = (
                result.get("failure_class") == "environment_error"
                or result.get("environment_error") is True
            )
            if not is_env_error:
                self._last_eval_cache = (self.current_proof_text, copy.deepcopy(result))
            return result
        if name == "inspect_lean_goals":
            return self.inspect_goals()
        if name == "search_public_defs":
            limit = int(arguments.get("limit", 20))
            return self.search_public_defs(str(arguments.get("query", "")), limit=limit)
        if name == "try_tactic_at_hole":
            return self.try_tactic_at_hole(str(arguments.get("tactic", "")))
        return {"status": "rejected", "reason": "unknown_tool", "tool": name}

    def _annotate_check_result(self, result: dict[str, Any]) -> dict[str, Any]:
        """Annotate a failed check result with failure classification and repair hints."""
        failure_mode = result.get("failure_mode", "")
        # Only track actual Lean checker failures for stagnation detection,
        # not preflight failures (empty_response, placeholder_detected, etc.)
        is_lean_failure = failure_mode == "lean_check_failed"
        details = str(result.get("details", ""))
        # Preflight failures carry English-language details that classify_failure
        # can't pattern-match, so they all collapse to "other" and the model gets
        # no targeted hint. Map the failure_mode directly to a class name so the
        # model sees e.g. "placeholder_detected" instead of "other" and
        # _build_check_hints can dispatch a specific hint.
        if not is_lean_failure and failure_mode in _PREFLIGHT_FAILURE_MODES:
            failure_class = failure_mode
        else:
            failure_class = classify_failure(details)
        hints = _build_check_hints(failure_class, details)
        annotated = dict(result)
        annotated["failure_class"] = failure_class

        # environment_error is infrastructure, not a proof problem. Don't track
        # stagnation for it (retrying won't help) and tag the result clearly.
        if failure_class == "environment_error":
            annotated["environment_error"] = True
            if hints:
                annotated["repair_hints"] = hints
            return annotated

        if not is_lean_failure:
            if hints:
                annotated["repair_hints"] = hints
            return annotated

        # Track failure history for stagnation detection (Lean check failures only)
        self._check_history.append(failure_class)
        total_failures = len(self._check_history)

        # Count consecutive same-class failures
        same_class_count = 0
        for fc in reversed(self._check_history):
            if fc == failure_class:
                same_class_count += 1
            else:
                break

        # Detect true no-progress loops: the normalized error text matches the
        # previous failure byte-for-byte. This is a much stronger signal than
        # same-class stagnation — it proves the last edit had zero effect on
        # what Lean actually saw.
        details_fp = _normalize_details_fp(details)
        if details_fp and details_fp == self._last_details_fp:
            self._same_details_streak += 1
        else:
            self._same_details_streak = 1
        self._last_details_fp = details_fp

        # Escalate on either: 2+ consecutive same-class failures, or 4+ total failures
        if same_class_count >= 2 or total_failures >= 4:
            if same_class_count >= 2:
                annotated["stagnation_warning"] = (
                    f"Same failure class '{failure_class}' repeated {same_class_count} times. "
                    "Your current approach is not working. Try a fundamentally different proof structure."
                )
            else:
                annotated["stagnation_warning"] = (
                    f"You have failed {total_failures} times across different error classes. "
                    "Step back and reconsider your proof strategy from scratch."
                )
            escalation = self._build_escalation_hint(failure_class, details)
            if escalation:
                hints.append(escalation)

        # When the error text is byte-identical to the previous attempt, the
        # model's latest edit had zero effect — hints must call this out
        # explicitly, not just repeat class-level advice. Keep this BEFORE
        # the dedup so the fingerprint-unique streak count is surfaced fresh
        # each time.
        if self._same_details_streak >= 2:
            hints.insert(0, (
                f"NO-PROGRESS LOOP DETECTED: your last {self._same_details_streak} "
                "submissions produced byte-identical Lean errors. The changes you are "
                "making do not reach the failing goal. Stop editing around the symptom. "
                "Instead: (1) `write_editable_proof` with the failing tactic replaced by "
                "`?_`, (2) `inspect_lean_goals` to read the real goal at that hole, "
                "(3) `try_tactic_at_hole` with tactics you have NOT tried yet "
                "(e.g. `simp_all`, `aesop`, `decide`, `exact?`, `constructor; all_goals ...`)."
            ))

        # Dedupe hints we've already shown this session. Repeated-verbatim hints
        # are noise: corpus analysis of failing tasks showed the same 4-5 hints
        # echoed across 5+ stagnation events, training the model to skip the
        # repair_hints list entirely. Only surface *new* advice each time.
        hints = self._filter_seen_hints(hints)

        # Highest-leverage directive: corpus analysis of 83 runs shows 12/29
        # failed tasks (41%) ended with `?_` still in the submitted proof, and
        # in every one of those runs the agent re-submitted a `?_`-containing
        # proof 2–9 times after the first rejection. The hint BELOW already
        # existed but was inserted BEFORE `_filter_seen_hints`, so dedup
        # suppressed it on the 2nd–Nth resubmission and the agent got no
        # feedback tying its specific, detectable mistake (still-unfilled hole)
        # to the specific failure class. Insert AFTER the dedup filter so this
        # safety-critical, state-conditional warning fires on EVERY submission
        # that still contains `?_`. The hint is keyed to the literal proof
        # text state, not to the abstract hint corpus, so it is not a "noise"
        # dedup candidate — it tells the agent something about its concrete
        # current submission.
        if HOLE_PATTERN.search(self.current_proof_text):
            hole_count = len(HOLE_PATTERN.findall(self.current_proof_text))
            hints.insert(0, (
                f"UNFILLED HOLE IN SUBMITTED PROOF: your proof still contains "
                f"{hole_count} `?_` hole(s). `?_` is a PROBE for `inspect_lean_goals` "
                "and `try_tactic_at_hole`, never a final proof — Lean will reject "
                "every submission containing `?_`. Do not submit `?_` again. Next "
                "move: call `try_tactic_at_hole` with one concrete tactic at a "
                "time (`omega`, `simp_all`, `decide`, `rfl`, `assumption`, "
                "`trivial`, `exact h`, `linarith`, `aesop`, `exact?`). If any "
                "succeeds, the proof updates in place and the task closes. If "
                "none do, use `inspect_lean_goals` to read each hole's goal, then "
                "`write_editable_proof` with concrete tactics substituted for "
                "every `?_`."
            ))

        # Second safety-critical, state-conditional warning that must survive
        # `_filter_seen_hints`: tactic-in-term-position.
        # Corpus analysis of 29 failed runs: 19 tasks (66%) emit at least one
        # `unknown identifier '<tactic>'` diagnostic — 173 occurrences for
        # 'simp', 100 for 'simpa', 52 for 'omega', 43 for 'native_decide',
        # 24 for 'simp_all'. One task alone (safe/swap_owner_is_owner_correctness)
        # emits 52 repeats of `unknown identifier 'simp'` in a single run.
        # The existing tactic-in-term hint inside `_build_check_hints`
        # (line ~1466) is suppressed by the dedup filter after its first
        # emission, so the agent never gets feedback tying the specific
        # mistake to each subsequent rejection. This is identical to the
        # hole-warning failure mode: a state-conditional critical warning
        # that must repeat as long as the state persists. Re-detect the
        # tactic-in-term case against the current `details` and insert a
        # persistent warning post-dedup. The hint is keyed to the concrete
        # error-text state (which tactic is being misused), not the generic
        # hint corpus, so it is not a "noise" dedup candidate.
        _unknown_names = _UNKNOWN_IDENT_RE.findall(details)
        _tactic_in_term = [n for n in _unknown_names if n in _LEAN_TACTIC_NAMES]
        if _tactic_in_term:
            _tactic_name = _tactic_in_term[0]
            hints.insert(0, (
                f"TACTIC IN TERM POSITION: Lean reports `unknown identifier "
                f"'{_tactic_name}'` because `{_tactic_name}` is a TACTIC, not "
                f"a term. It appears in your proof after `exact` / `refine` / "
                f"`apply` / `:=` or inside `⟨ ⟩` — all term positions. Fix: "
                f"wrap the tactic in `by`, e.g. `exact by {_tactic_name} ...`, "
                f"`refine ⟨by {_tactic_name}, ...⟩`, or drop the `exact` / "
                f"`refine` prefix so `{_tactic_name}` runs as a tactic "
                f"directly (`by {_tactic_name} ...` at the top of the proof "
                f"body). Do NOT call search_public_defs for `{_tactic_name}` "
                f"— it is not a definition, it is a tactic, and the only fix "
                f"is the `by` wrapper."
            ))

        # Third safety-critical, state-conditional warning: local-variable
        # out-of-scope names. Corpus analysis of 29 failed runs: 6 tasks
        # (21%) emit `unknown identifier '<camelCase name>'` for names that
        # are clearly binder-shaped (no dots, lowercase first char, no
        # underscores) — up to 110 occurrences in a single run
        # (safe/swap_owner_is_owner_correctness: 91×prevOwner, 19×oldOwner).
        # The existing local-variable hint in `_build_check_hints`
        # (~line 1475) is actionable ("call inspect_lean_goals / re-check
        # the signature") but is suppressed by dedup after first emission.
        # Same failure mode as tactic-in-term and unfilled-hole: state
        # persists across re-submissions, warning must repeat. The hint
        # is keyed to the specific out-of-scope name from the error text,
        # not the generic corpus, so it is not a "noise" dedup candidate.
        # Only fire when no tactic-hit is present so we never spam both
        # warnings for the same line range — Lean reports tactic names
        # the same way as local vars, and if a tactic mistake is present
        # that's almost always the upstream cause.
        if not _tactic_in_term:
            _var_hits = [
                n for n in _unknown_names
                if n not in _LEAN_TACTIC_NAMES
                and "." not in n
                and n
                and n[0].islower()
                and "_" not in n
            ]
            if _var_hits:
                _var_name = _var_hits[0]
                hints.insert(0, (
                    f"LOCAL VARIABLE OUT OF SCOPE: Lean reports `unknown "
                    f"identifier '{_var_name}'` for a name that looks like "
                    f"a local binder, not a definition. `{_var_name}` is "
                    f"not in scope at the point it is used — common causes: "
                    f"(a) it was introduced inside a different `by_cases` / "
                    f"`rcases` / `·` branch and is not visible in the "
                    f"current branch; (b) the theorem signature uses a "
                    f"different parameter name (check the editable file "
                    f"header via `read_public_file`); (c) it was shadowed "
                    f"by a later `intro` / `rintro` / `obtain`. Fix: call "
                    f"`inspect_lean_goals` on a `?_` hole at this exact "
                    f"location to see the binders ACTUALLY in scope, then "
                    f"reference those names. Do NOT call search_public_defs "
                    f"for `{_var_name}` — it is a binder, not a definition, "
                    f"and search_public_defs cannot find binders."
                ))
        if not hints and same_class_count >= 3:
            # All the standing advice has already been seen and isn't working.
            # Issue a one-shot pivot directive rather than sending an empty list,
            # which the model interprets as "nothing new, carry on".
            hints = [
                f"All prior repair hints for '{failure_class}' have now been repeated "
                f"{same_class_count} times without progress. Stop retrying variations of "
                f"the same proof. Next move: write a minimal skeleton with a `?_` hole at "
                f"the first failing step, call `inspect_lean_goals` to read the actual "
                f"goal state, then use `try_tactic_at_hole` to probe tactics one at a time."
            ]

        if hints:
            annotated["repair_hints"] = hints

        # Add structured error summary with progress tracking
        error_lines: list[int] = []
        for match in re.finditer(r":(\d+):\d+: error:", details):
            error_lines.append(int(match.group(1)))
        if error_lines:
            error_count = len(error_lines)
            first_error = min(error_lines)
            annotated["error_count"] = error_count
            annotated["first_error_line"] = first_error

            # Track progress relative to best seen
            progress_parts: list[str] = []
            if self._best_error_count is not None:
                if error_count < self._best_error_count:
                    progress_parts.append(f"errors reduced ({self._best_error_count} -> {error_count})")
                elif error_count > self._best_error_count:
                    progress_parts.append(f"errors increased ({self._best_error_count} -> {error_count}), reverting direction")
            if self._best_first_error_line is not None:
                if first_error > self._best_first_error_line:
                    progress_parts.append(f"first error moved deeper (line {self._best_first_error_line} -> {first_error})")
                elif first_error < self._best_first_error_line:
                    progress_parts.append(f"first error moved earlier (line {self._best_first_error_line} -> {first_error})")

            if progress_parts:
                annotated["progress"] = "; ".join(progress_parts)

            # Update best-seen metrics
            if self._best_error_count is None or error_count < self._best_error_count:
                self._best_error_count = error_count
            if self._best_first_error_line is None or first_error > self._best_first_error_line:
                self._best_first_error_line = first_error

        return annotated

    def _filter_seen_hints(self, hints: list[str]) -> list[str]:
        """Drop hints whose fingerprint has already been surfaced this session.

        Fingerprint = lowercased first 80 non-whitespace chars. Short enough
        that wording tweaks still dedupe, long enough to distinguish genuinely
        different hints.
        """
        fresh: list[str] = []
        for hint in hints:
            key = "".join(hint.lower().split())[:80]
            if key in self._emitted_hint_keys:
                continue
            self._emitted_hint_keys.add(key)
            fresh.append(hint)
        return fresh

    def _build_escalation_hint(self, failure_class: str, details: str = "") -> str | None:
        """Build an escalation hint when the model is stagnating on a failure class."""
        terms = extract_contract_simp_terms(self._task)
        if terms:
            full_set = ", ".join(terms)
            full_set += ", getStorage, setStorage, Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd"
        else:
            full_set = ""

        if failure_class in ("simp_no_progress", "unsolved_goals", "rfl_failed", "unfold_failed"):
            # If the stuck goal carries a `case <label>` marker, the agent has
            # ALREADY case-split and is stalling on an open branch. Telling it
            # to "Start with unfold … then by_cases" would undo the split and
            # regress. Escalate with branch-closing advice instead.
            case_labels = re.findall(r"\ncase ([a-zA-Z_][a-zA-Z0-9_.]*)\n", details or "")
            if case_labels:
                seen_lbls: list[str] = []
                for lbl in case_labels:
                    if lbl not in seen_lbls:
                        seen_lbls.append(lbl)
                lbl_list = ", ".join(f"`{l}`" for l in seen_lbls[:4])
                simp_fragment = f"simp_all [{full_set}]" if full_set else "simp_all"
                return (
                    f"ESCALATION: You are stuck inside an open case branch ({lbl_list}). "
                    f"Do NOT restart the proof or re-split — your previous case-split is "
                    f"correct. Instead, close ONLY the open branch:\n"
                    f"1. Call inspect_lean_goals with a `?_` at the branch's current "
                    f"position to read the exact hypotheses (they include the branch "
                    f"condition as `h✝` or a named hypothesis).\n"
                    f"2. Try `{simp_fragment}` — it rewrites hypotheses into each other "
                    f"and closes branches where the branch hypothesis contradicts another.\n"
                    f"3. If two hypotheses literally contradict (e.g. `h1 : x = 0` and "
                    f"`h2 : x ≠ 0`), close with `exact absurd h1 h2`.\n"
                    f"4. If the goal is a linear (in)equality over `.val`, use `omega` "
                    f"after `simp only [...]` has exposed the `.val` form."
                )
            if full_set:
                return (
                    f"ESCALATION: You are stuck. Do NOT use `unfold` on contract functions. "
                    f"Instead, pass them to `simp`. Here is the proof template:\n"
                    f"1. Start with `unfold <spec_name>` to unfold the spec definition only\n"
                    f"2. Use `by_cases` on each conditional branch BEFORE calling simp\n"
                    f"3. In EVERY branch, use: simp [{full_set}, <all hypotheses including by_cases vars>]\n"
                    f"4. For nested conditionals, nest `by_cases` inside the outer branch\n"
                    f"5. Never use bare `simp [h]` or `unfold ContractName.functionName`"
                )
        if failure_class == "unknown_identifier":
            unknown_names = _UNKNOWN_IDENT_RE.findall(details or "")
            tactic_hits = [n for n in unknown_names if n in _LEAN_TACTIC_NAMES]
            if tactic_hits:
                name = tactic_hits[0]
                return (
                    f"ESCALATION: `{name}` is a TACTIC, not an identifier to search for. "
                    f"You are writing `{name}` in term position (after `exact`/`refine`/`apply`/`:=` or "
                    f"inside `⟨ ⟩`). Either wrap with `by` (e.g. `exact by {name} ...`) or drop the "
                    f"`exact`/`refine` prefix so `{name}` runs in tactic mode."
                )
            var_hits = [
                n for n in unknown_names
                if n not in _LEAN_TACTIC_NAMES and "." not in n
                and n and n[0].islower() and "_" not in n
            ]
            if var_hits:
                name = var_hits[0]
                return (
                    f"ESCALATION: `{name}` is a LOCAL VARIABLE shape, not a definition. "
                    f"search_public_defs cannot find binders — it only searches public "
                    f"definitions. Call `inspect_lean_goals` on a `?_` hole to see which "
                    f"binders are in scope, then match the actual parameter names from the "
                    f"theorem signature."
                )
            mathlib_hits = [
                n for n in unknown_names
                if n not in _LEAN_TACTIC_NAMES and _is_mathlib_shaped(n)
            ]
            if mathlib_hits:
                name = mathlib_hits[0]
                return (
                    f"ESCALATION: `{name}` is a Mathlib lemma name, but this workspace has "
                    f"NO Mathlib dependency. Stop searching for `add_*` / `sub_*` / `Nat.*` "
                    f"lemmas — they do not exist here. Close arithmetic goals with `omega` "
                    f"(linear Nat/Int), `ring` (commutative rings), or `simp arith`. For "
                    f"project helpers call search_public_defs with a KEYWORD, not a guessed "
                    f"lemma name."
                )
            return (
                "ESCALATION: Stop guessing identifier names. Use the search_public_defs tool "
                "to find the exact names from the implementation and specification files."
            )
        if failure_class == "type_mismatch":
            if full_set:
                return (
                    f"ESCALATION: Type mismatch usually means you're not simplifying enough. "
                    f"Use simp [{full_set}, <all hypotheses>] to fully reduce the expression."
                )
        return None

    def _materialize_workspace(self, workspace: Path) -> None:
        workspace.mkdir(parents=True, exist_ok=True)
        for rel_path in (
            "lakefile.lean",
            "lake-manifest.json",
            "lean-toolchain",
            ".lake",
        ):
            source = ROOT / rel_path
            target = workspace / rel_path
            if not source.exists():
                continue
            target.parent.mkdir(parents=True, exist_ok=True)
            os.symlink(source, target, target_is_directory=source.is_dir())
        for rel_path in self.paths.public_files:
            source = ROOT / rel_path
            target = workspace / rel_path
            target.parent.mkdir(parents=True, exist_ok=True)
            if rel_path == self.paths.editable_rel_path:
                target.write_text(self.current_proof_text, encoding="utf-8")
                continue
            if not source.is_file():
                continue
            os.symlink(source, target)

    def _extract_theorem_signature(self, text: str) -> str | None:
        short_name = self.paths.theorem_name.rsplit(".", 1)[-1]
        # Match any proof style: tactic-mode (`:= by ...`) or term-mode
        # (`:= rfl`, `:= fun n => ...`, `:= Eq.mpr ...`). Previously the
        # regex required `:= by`, so a valid term-mode proof returned None
        # while the expected signature (extracted from an initial `:= by`
        # file) was a string — the inequality fired a false
        # `theorem_statement_mismatch` even though the `theorem name : TYPE`
        # prefix was unchanged. Anchoring on `:=` alone (with the `by`
        # branch preferred when present, to stay bug-compatible for
        # tactic-mode) lets both styles produce the same signature string.
        pattern = re.compile(
            rf"theorem\s+{re.escape(short_name)}\b(?P<signature>.*?):=\s*(?:by\b)?",
            re.DOTALL,
        )
        match = pattern.search(text)
        if not match:
            return None
        signature = re.sub(r"/-.*?-/", " ", match.group("signature"), flags=re.DOTALL)
        signature = re.sub(r"--.*$", " ", signature, flags=re.MULTILINE)
        return " ".join(signature.split())

    def _find_blocked_case_imports(self, text: str) -> list[str]:
        blocked: list[str] = []
        for module_name in IMPORT_PATTERN.findall(text):
            if not module_name.startswith("Benchmark.Cases."):
                continue
            if module_name in self.allowed_task_modules:
                continue
            blocked.append(module_name)
        return sorted(set(blocked))

    @staticmethod
    def _module_name(rel_path: str) -> str:
        path = Path(rel_path)
        suffix = "".join(path.suffixes)
        module_path = str(path)
        if suffix:
            module_path = module_path[: -len(suffix)]
        return module_path.replace("/", ".")


_LAKE_BUILD_CACHE: dict[str, bool] = {}


def _attempt_lake_build(module_name: str | None) -> bool:
    """Best-effort `lake build` for a module. Returns True on success.

    Always invokes `lake build` — this is the self-heal path, called when the
    runtime observed a missing .olean at check time, so the previously cached
    "success" entry is stale and cannot be trusted. The cache is refreshed
    with the latest result so subsequent prebuild calls can short-circuit
    correctly.
    """
    if not module_name:
        return False
    if not module_name.startswith("Benchmark."):
        return False
    code, _output = lean_run_command(["lake", "build", module_name], cwd=ROOT)
    success = code == 0
    _LAKE_BUILD_CACHE[module_name] = success
    return success


def prebuild_task_modules(task: dict[str, Any]) -> list[dict[str, Any]]:
    """Pre-build implementation/specification .olean files for a task.

    Returns a list of build reports. Meant to be called once before starting
    the agent loop so on-the-fly compilation inside `lake env lean` does not
    race with fast agent retries.
    """
    reports: list[dict[str, Any]] = []
    targets: list[str] = []
    for rel_path in list(task.get("implementation_files", [])) + list(task.get("specification_files", [])):
        path = Path(rel_path)
        if path.suffix != ".lean":
            continue
        module_name = ".".join(path.with_suffix("").parts)
        # Only modules inside the `Benchmark` lean_lib are buildable via `lake build`.
        # Source-of-truth files under `cases/` are mirrored into `Benchmark/Cases/` and
        # that mirror is what lake actually compiles.
        if not module_name.startswith("Benchmark."):
            continue
        if module_name in targets:
            continue
        targets.append(module_name)
    for module_name in targets:
        if _LAKE_BUILD_CACHE.get(module_name):
            reports.append({"module": module_name, "status": "cached"})
            continue
        code, output = lean_run_command(["lake", "build", module_name], cwd=ROOT)
        success = code == 0
        if success:
            _LAKE_BUILD_CACHE[module_name] = True
        reports.append(
            {
                "module": module_name,
                "status": "ok" if success else "failed",
                "output": output[-600:] if not success else "",
            }
        )
    return reports


def extract_contract_simp_terms(task: dict[str, Any]) -> list[str]:
    """Extract concrete simp terms from implementation and specification files.

    Parses verity_contract storage field declarations, function names,
    and non-spec helper definitions to generate the simp lemma set.
    """
    terms: list[str] = []
    contract_name = ""
    for rel_path in task.get("implementation_files", []):
        path = ROOT / rel_path
        if not path.is_file():
            continue
        content = path.read_text(encoding="utf-8")
        contract_match = re.search(r"verity_contract\s+(\w+)\s+where", content)
        if contract_match:
            contract_name = contract_match.group(1)
        for field_match in re.finditer(
            r"^\s+(\w+)\s*:.*:=\s*slot\s+\d+", content, re.MULTILINE
        ):
            field_name = field_match.group(1)
            if contract_name:
                terms.append(f"{contract_name}.{field_name}")
        for fn_match in re.finditer(
            r"^\s+function\s+(\w+)\s*\(", content, re.MULTILINE
        ):
            fn_name = fn_match.group(1)
            if contract_name:
                terms.append(f"{contract_name}.{fn_name}")
    for rel_path in task.get("specification_files", []):
        path = ROOT / rel_path
        if not path.is_file():
            continue
        content = path.read_text(encoding="utf-8")
        for def_match in re.finditer(r"^def\s+(\w+)\b", content, re.MULTILINE):
            def_name = def_match.group(1)
            if not def_name.endswith("_spec") and def_name not in terms:
                terms.append(def_name)
    return terms


# Term-expecting tokens/punctuation that immediately precede a `?_` hole
# when the hole is in term (expression) position rather than tactic position.
# Matches at end-of-string after the hole's predecessor text is sliced off.
_TERM_POSITION_RE = re.compile(
    r"(?:"
    r"\b(?:exact|refine|apply|show|have|let|suffices|exact\?|refine!|exact!|"
    r"use|calc|from|fun)\s*"  # term-expecting keywords
    r"|[⟨(,\[{]\s*"             # inside anonymous constructors / tuples / lists
    r"|:=\s*"                    # RHS of let / have := ?_
    r")$"
)
# Lean's diagnostic header format is `<source-file>:LINE:COL: <kind>: <msg>`.
# Two code paths reach this regex family:
#   1. `evaluate_candidate` (run_lean_check / write_editable_proof) writes a
#      `CandidateCheck.lean` stub and reports errors against that name.
#   2. `inspect_lean_goals` runs Lean against the actual editable file path
#      (e.g. `Benchmark/Generated/Foo/Bar.lean`) because it needs `check_goals`
#      to introspect the real `?_` hole — no stub wrapper.
# Corpus analysis of 83 runs found 32/88 (36%) of inspect_lean_goals outputs
# still contained `linter.unusedSimpArgs` blocks because the old, hardcoded
# `CandidateCheck\.lean:` regex silently skipped them. Accepting any
# `<nonws>.lean:LINE:COL:` header lets the same strip + fingerprint logic
# apply to both code paths uniformly.
_FP_LINE_COL_RE = re.compile(r"\S+\.lean:\d+:\d+:")
_FP_WS_RE = re.compile(r"\s+")
_LEAN_BLOCK_HEADER_RE = re.compile(
    r"^\S+\.lean:\d+:\d+:\s*(error|warning|note|info):"
)


_LEAN_OUTPUT_CAP_CHARS = 16000


def _cap_lean_output(output: str, max_chars: int = _LEAN_OUTPUT_CAP_CHARS) -> str:
    """Bound Lean-check output to a character budget the model can read.

    Corpus analysis of 201 interactive `run_lean_check` results found the
    stripped-output distribution was heavy-tailed: median 1.4 KB, p95 32 KB,
    max 136 KB (pre-strip max 300 KB — a single call consuming >70 k tokens).
    The tail is driven by goals whose state contains deeply nested
    `match`/`if` chains over contract state; 16 separate errors each
    displaying a 10 KB goal easily adds up to 100 KB. That blows the
    context budget and buries the first (usually most actionable) error.

    Truncate to `max_chars` with a clear marker so the first errors stay
    intact and the model knows output was elided. 16 KB keeps ~89 % of
    real corpus outputs untouched while capping the worst case at about
    4 k tokens.
    """
    if len(output) <= max_chars:
        return output
    # Cut on a line boundary inside the budget so we never slice mid-token.
    head = output[:max_chars]
    last_newline = head.rfind("\n")
    if last_newline > max_chars // 2:
        head = head[:last_newline]
    dropped = len(output) - len(head)
    return (
        f"{head}\n"
        f"[... Lean output truncated: {dropped} more characters elided to "
        f"keep the tool result within the model's context budget. The first "
        f"errors are preserved above — address them before expecting the "
        f"later diagnostics to matter, since Lean errors cascade.]"
    )


def _strip_noise_warnings(output: str) -> str:
    """Drop `linter.unusedSimpArgs` warning blocks from Lean stdout.

    Lean 4.22 emits a multi-line warning for every simp argument it deems
    unused. Each block spans the header line, the unused-arg name, a
    "Hint: Omit it..." directive, a 3–8 line reconstructed simp invocation
    with strikethrough glyphs, and a "Note: This linter can be disabled
    with `set_option linter.unusedSimpArgs false`" footer. Across the 37
    failed-check blocks in the current corpus these blocks account for
    844/846 total warnings and roughly 20 KB of the average 34 KB
    details blob — pure noise from the model's point of view because
    the actual repair work is always driven by errors, not by this lint.

    A block begins at a `<source>.lean:L:C: warning: This simp argument
    is unused:` header and ends at the next Lean diagnostic header
    (error/warning/note/info) or end-of-output. The `<source>` prefix
    is matched generically so outputs from `inspect_lean_goals` (which
    runs Lean against the editable file directly, not the
    `CandidateCheck.lean` stub) are stripped the same as outputs from
    `run_lean_check`. Every other diagnostic kind (including unrelated
    warnings) is preserved verbatim.
    """
    if not output or "This simp argument is unused" not in output:
        return output
    lines = output.splitlines(keepends=True)
    kept: list[str] = []
    skip = False
    for line in lines:
        header = _LEAN_BLOCK_HEADER_RE.match(line)
        if header:
            skip = (
                header.group(1) == "warning"
                and "This simp argument is unused" in line
            )
        if not skip:
            kept.append(line)
    return "".join(kept)


def _is_term_position_hole(proof: str, hole_start: int) -> bool:
    """True iff the `?_` at `hole_start` sits where Lean expects a term.

    Looks back up to 40 chars of the preceding text (stripping trailing
    whitespace) and matches against known term-expecting prefixes. Used by
    `_substitute_holes` to decide whether a raw tactic substitution must be
    wrapped in `(by ...)` so the resulting expression type-checks.
    """
    window = proof[max(0, hole_start - 40):hole_start]
    # Strip trailing whitespace/newlines — `exact\n  ?_` is still term position.
    window_r = window.rstrip()
    # Re-append a single space so the regex's trailing `\s*$` consistently
    # matches with or without original whitespace.
    return bool(_TERM_POSITION_RE.search(window_r + " "))


def _is_fully_paren_wrapped(raw: str) -> bool:
    """Return True iff `raw` is a single parenthesised expression.

    Correct check: after the opening `(`, parenthesis nesting depth must stay
    >= 1 for every position up to (but not including) the final char, and
    return to 0 exactly at the final `)`. Rejects `(a) + (b)`, `(a)(b)`,
    `(foo) bar (baz)`; accepts `(a)`, `((a + b))`, `(first | a | b)`.
    Respects Lean string literals so a `(` inside `"..."` doesn't count.
    """
    n = len(raw)
    if n < 2 or raw[0] != "(" or raw[-1] != ")":
        return False
    depth = 0
    in_string = False
    i = 0
    while i < n:
        ch = raw[i]
        if in_string:
            if ch == "\\" and i + 1 < n:
                i += 2
                continue
            if ch == '"':
                in_string = False
            i += 1
            continue
        if ch == '"':
            in_string = True
        elif ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0 and i != n - 1:
                # Outer group closed before the end -> not a single wrap.
                return False
        i += 1
    return depth == 0


def _substitute_holes(proof: str, tactic: str) -> str:
    """Replace every `?_` in `proof` with a context-adapted form of `tactic`.

    At term-position holes (`exact ?_`, `⟨?_, ?_⟩`, `:= ?_`, ...) the
    substitute must be a term, so wrap a raw tactic as `(by <tactic>)` unless
    the caller already provided a term form. At tactic-position holes the
    substitute must be a tactic, so strip a leading `by ` to avoid nested
    `by ... by ...` blocks.
    """
    raw = tactic.strip()
    # Already a term form? (leading `by `/`by\n`, or fully wrapped in parens)
    starts_by = raw.startswith("by ") or raw.startswith("by\n")
    # `fully_paren_wrapped` means the outer `(` at position 0 is the partner
    # of the outer `)` at the end — i.e. the whole string is one parenthesised
    # expression. A plain depth count (startswith/endswith + balanced totals)
    # mis-classifies strings like `(a) + (b)` or `(foo) bar (baz)`, which
    # would get their "term form" left as-is and become invalid when
    # substituted into a term-position hole. Track nesting depth and confirm
    # it only returns to zero on the final character.
    fully_paren_wrapped = _is_fully_paren_wrapped(raw)
    # Precompute the tactic-position form: strip a leading `by ` or `by\n`
    # so substitution at a tactic hole doesn't nest `by`. Leave paren-
    # wrapped forms alone — those often indicate grouping the caller wants
    # preserved as a single tactic (`(first | a | b)`).
    if starts_by:
        tactic_form = raw[3:].lstrip()
    else:
        tactic_form = raw
    # Term-position form: must be a valid term. `(by <tac>)` wraps a raw
    # tactic. A bare `by <tac>` is also a tactic-block term, but at a
    # term-position hole like `exact ?_` it produces `exact by <tac>` which
    # Lean parses as applying `exact` to `by` rather than as an `exact` on a
    # tactic block — invalid syntax. Wrap `by <tac>` in parentheses in that
    # case. A fully paren-wrapped value is already a safe term and is left
    # alone (it may be grouping tactics the caller wants preserved, e.g.
    # `(first | a | b)`; at a term hole that still reads as a term).
    if fully_paren_wrapped:
        term_form = raw
    elif starts_by:
        term_form = f"({raw})"
    else:
        term_form = f"(by {raw})"

    out: list[str] = []
    cursor = 0
    for match in HOLE_PATTERN.finditer(proof):
        out.append(proof[cursor:match.start()])
        if _is_term_position_hole(proof, match.start()):
            out.append(term_form)
        else:
            out.append(tactic_form)
        cursor = match.end()
    out.append(proof[cursor:])
    return "".join(out)


def _normalize_details_fp(details: str) -> str:
    """Return a whitespace/line-number-agnostic fingerprint of a Lean error.

    Strips the leading `<source>.lean:LINE:COL:` markers and collapses
    all whitespace runs so two Lean runs that differ only in formatting
    noise produce the same fingerprint. Truncated to 512 chars — long
    enough to distinguish genuinely different errors, short enough that
    minor trailing-hint variation doesn't break the match.
    """
    if not details:
        return ""
    d = _FP_LINE_COL_RE.sub("", details)
    d = _FP_WS_RE.sub(" ", d).strip()
    return d[:512]


# Missing-olean errors can be infrastructure (a Benchmark dependency wasn't
# pre-built) or the model's fault (imported a module that doesn't exist). We
# only classify the former as environment_error so stagnation/temperature
# logic still applies to model-caused import mistakes.
# Lean prints both forms of this diagnostic, depending on context:
#   object file '<path>.olean' does not exist
#   object file '<path>.olean' of module <Name> does not exist
# so accept arbitrary text (incl. "of module <Name>") between the path and
# the "does not exist" tail.
_MISSING_OLEAN_RE = re.compile(
    r"object file ['\"]([^'\"]+\.olean)['\"]?[^\n]*?does not exist"
)
INFRA_ONLY_ERROR_PATTERNS = (
    re.compile(r"lean executable .* not found", re.IGNORECASE),
)


def _missing_olean_module(details: str) -> str | None:
    """Extract the module name whose .olean is missing, if the error is environmental."""
    match = _MISSING_OLEAN_RE.search(details)
    if not match:
        return None
    olean_path = match.group(1)
    # Strip any leading directories up to "Benchmark" (since paths may be absolute)
    marker = "/Benchmark/"
    idx = olean_path.rfind(marker)
    if idx >= 0:
        rel = olean_path[idx + 1 :]
    else:
        rel = olean_path
    if rel.endswith(".olean"):
        rel = rel[: -len(".olean")]
    return rel.replace("/", ".")


# Preflight failure_mode values that preflight_candidate returns. Used by
# _annotate_check_result to surface these as failure_class directly rather than
# collapsing them into "other" via English-language classify_failure lookup.
_PREFLIGHT_FAILURE_MODES = frozenset({
    "empty_response",
    "placeholder_detected",
    "hidden_proof_import_detected",
    "hidden_case_import_detected",
    "theorem_statement_mismatch",
})


def classify_failure(details: str) -> str:
    """Classify a Lean checker failure into a coarse category."""
    if not details:
        return "unknown"
    lower = details.lower()
    # Infrastructure errors that the model cannot reasonably be blamed for.
    for pattern in INFRA_ONLY_ERROR_PATTERNS:
        if pattern.search(details):
            return "environment_error"
    # Missing .olean is infra only when it is a Benchmark.* dependency *whose
    # source file actually exists* in the tree -- meaning lake should have
    # built it but didn't. If the source file is missing too, the model
    # imported / referenced something that doesn't exist, which is its own
    # mistake and should go through the normal stagnation/temperature loop.
    missing_module = _missing_olean_module(details)
    if missing_module and missing_module.startswith("Benchmark."):
        source_rel = Path(*missing_module.split(".")).with_suffix(".lean")
        if (ROOT / source_rel).is_file():
            return "environment_error"
    if "unknown identifier" in lower or "unknown constant" in lower:
        return "unknown_identifier"
    if "unsolved goals" in lower:
        return "unsolved_goals"
    if "application type mismatch" in lower or "function expected" in lower:
        return "type_error"
    if "type mismatch" in lower:
        return "type_mismatch"
    if "tactic 'split' failed" in details:
        return "split_failed"
    if "no goals to be solved" in details:
        return "no_goals"
    if "expected type must not contain free variables" in details:
        return "free_variables"
    if "declaration uses 'sorry'" in lower or "declaration uses 'admit'" in lower:
        return "placeholder"
    if "unknown tactic" in lower:
        return "unknown_tactic"
    if "simp made no progress" in lower:
        return "simp_no_progress"
    if "failed to unfold" in lower or ("unfold" in lower and "failed" in lower):
        return "unfold_failed"
    if "dsimp made no progress" in lower:
        return "simp_no_progress"
    if "tactic 'rfl' failed" in details:
        return "rfl_failed"
    if "invalid" in lower and "conv tactic" in lower:
        return "tactic_misuse"
    if "omega could not prove the goal" in lower:
        return "omega_failed"
    if "tactic 'constructor' failed" in details and "not an inductive datatype" in lower:
        return "constructor_failed"
    # `cases` / `induction` on a non-inductive target (e.g. an implication
    # `A → B`, a function, or a Prop that isn't a recognised eliminator) is a
    # distinct failure mode from `constructor` — Lean phrases it as "major
    # premise type is not an inductive type". Corpus analysis: 22 incidents in
    # 1 failed task (setup_owners_acyclicity) all repeating the same `cases h`
    # on an implication, because the generic "other" bucket gave no actionable
    # hint. Split into its own class so the hint can cover `intro` /
    # `by_cases` / `absurd` — the actual remedies for this shape.
    if (
        ("tactic 'cases' failed" in details or "tactic 'induction' failed" in details)
        and "not an inductive type" in lower
    ):
        return "cases_failed"
    if "unknown module prefix" in lower:
        return "module_not_found"
    if "don't know how to synthesize placeholder" in lower:
        return "synthesis_failed"
    # Parse errors (`unexpected token '…'`, `unexpected identifier`, or the
    # "expected '{' or indented tactic sequence" shape) indicate malformed
    # Lean syntax rather than a semantic proof failure. Corpus analysis of
    # 83 runs: 21 failed-run events across 14 tasks contain a parse error
    # as one of the error lines, and 2 tasks surface it with no other
    # classifiable signal (collapsing to "other"). Giving those cases an
    # explicit class unlocks a targeted syntax hint.
    if (
        "error: unexpected token" in lower
        or "error: unexpected identifier" in lower
        or "expected '{' or indented tactic sequence" in lower
    ):
        return "parse_error"
    return "other"


def _build_check_hints(failure_class: str, details: str) -> list[str]:
    """Build targeted repair hints based on failure classification."""
    hints: list[str] = []
    if failure_class == "environment_error":
        hints.append(
            "ENVIRONMENT ERROR (not your fault): a dependency .olean is missing. "
            "The harness is attempting to rebuild it. If this persists, your proof is likely correct; "
            "retry run_lean_check once more."
        )
        return hints
    if failure_class == "placeholder_detected":
        hints.append(
            "PREFLIGHT REJECTED: proof contains `sorry` or `admit`. The harness "
            "will never accept these. Replace every `sorry`/`admit` with a real "
            "tactic, or use `?_` (unnamed hole) to probe a sub-goal with "
            "inspect_lean_goals / try_tactic_at_hole."
        )
        return hints
    if failure_class == "theorem_statement_mismatch":
        hints.append(
            "PREFLIGHT REJECTED: you changed the editable theorem signature. Only "
            "the proof body after `:=` is editable. Restore the exact theorem "
            "declaration from the original editable file (re-read it with "
            "read_public_file if unsure) and edit only the body."
        )
        return hints
    if failure_class == "hidden_proof_import_detected":
        hints.append(
            "PREFLIGHT REJECTED: proof imports a hidden `Benchmark.Cases.*.Proofs` "
            "module. Reference-solution modules are not part of the public API. "
            "Remove that import and write the proof yourself."
        )
        return hints
    if failure_class == "hidden_case_import_detected":
        hints.append(
            "PREFLIGHT REJECTED: proof imports a non-public `Benchmark.Cases.*` "
            "module. Only `Benchmark.Cases.*.Specs` (and your own editable file) "
            "are visible. Remove the blocked import."
        )
        return hints
    if failure_class == "empty_response":
        hints.append(
            "PREFLIGHT REJECTED: the proof content was empty. Submit the full "
            "Lean file including `import`, `namespace`, and the theorem with "
            "its proof body."
        )
        return hints
    if failure_class == "unknown_identifier":
        unknown_names = _UNKNOWN_IDENT_RE.findall(details)
        tactic_hits = [n for n in unknown_names if n in _LEAN_TACTIC_NAMES]
        var_hits = [
            n for n in unknown_names
            if n not in _LEAN_TACTIC_NAMES and "." not in n
            and n and n[0].islower() and "_" not in n
        ]
        mathlib_hits = [
            n for n in unknown_names
            if n not in _LEAN_TACTIC_NAMES and _is_mathlib_shaped(n)
        ]
        if tactic_hits:
            name = tactic_hits[0]
            hints.append(
                f"`{name}` is a TACTIC, not an identifier. Lean reports `unknown identifier "
                f"'{name}'` when a tactic is written in TERM position (after `exact`, `refine`, "
                f"`apply`, `:=`, inside `⟨ ⟩`, etc.). Fix: wrap the tactic in `by` — e.g. "
                f"`exact by {name} ...` or `:= by {name} ...`. If the goal is already in tactic "
                f"mode, remove the `exact`/`refine` prefix and call `{name}` directly."
            )
        elif var_hits:
            name = var_hits[0]
            hints.append(
                f"`{name}` looks like a LOCAL VARIABLE name, not a definition. "
                f"`unknown identifier '{name}'` means `{name}` is not in scope at that point — "
                f"it may have been introduced in a different branch, shadowed, or never bound. "
                f"Use `inspect_lean_goals` to see the exact binders in scope at each `?_`, and "
                f"re-check the theorem signature for the actual parameter names. Do NOT call "
                f"search_public_defs for a local-variable-shaped name — it searches definitions, "
                f"not binders."
            )
        elif "decide_True" in details or "decide_False" in details:
            hints.append("CRITICAL: `decide_True` and `decide_False` do not exist. Remove them. Instead, pass precondition hypotheses directly to `simp` - it handles `decide` reduction automatically.")
        else:
            if mathlib_hits:
                name = mathlib_hits[0]
                hints.append(
                    f"`{name}` is a Mathlib-style lemma name, but this workspace has NO "
                    f"Mathlib dependency — only core Lean 4, Batteries, and the task's own "
                    f"`Benchmark.*` modules are importable. Do not keep guessing names like "
                    f"`add_sub_*`, `sub_eq_*`, `lt_of_*`, or `Nat.div_*` — they will not be "
                    f"found. For arithmetic goals use `omega` (linear Nat/Int), `ring` "
                    f"(commutative rings), or `simp arith` directly; for project helpers "
                    f"use search_public_defs on a keyword, not a guessed lemma name."
                )
            else:
                hints.append("Use search_public_defs to find correct names from spec/impl files.")
        if not tactic_hits and not var_hits and not mathlib_hits:
            hints.append("Check imports. Standard names: Nat.lt_of_not_ge, Nat.not_le_of_lt.")
    elif failure_class == "unsolved_goals":
        hints.append("Use inspect_lean_goals with a ?_ hole to see exact goal state.")
        # Detect `case <label>` markers in the unsolved-goals output. When
        # present, the agent has already case-split successfully and exactly
        # one branch remains open — re-splitting is wrong, the fix is to
        # close the specific branch using its branch-specific hypothesis.
        # Corpus analysis: 59 of 127 unsolved_goals incidents across 22
        # tasks (46%) carry a `case <label>` marker; the current hint set
        # tells the agent to "restructure with by_cases" which can make it
        # undo its own working split.
        case_labels = re.findall(r"\ncase ([a-zA-Z_][a-zA-Z0-9_.]*)\n", details)
        if case_labels:
            seen_lbls: list[str] = []
            for lbl in case_labels:
                if lbl not in seen_lbls:
                    seen_lbls.append(lbl)
            lbl_list = ", ".join(f"`{l}`" for l in seen_lbls[:4])
            hints.append(
                f"The unsolved goals list shows open case(s): {lbl_list}. You have "
                f"ALREADY split successfully — do NOT restructure or re-split. Focus on "
                f"closing just the named branch(es) using the branch-specific "
                f"hypotheses now in scope (e.g. `h✝ : ¬P` inside a negative case). "
                f"Common fixes per branch: add the branch hypothesis to "
                f"`simp_all [..., hbranch]`, use `omega` when the branch hypothesis "
                f"is an arithmetic (in)equality, or finish with `exact absurd hx hy` "
                f"when two branch hypotheses contradict each other."
            )
        if "if " in details or "match" in details:
            hints.append("If simp leaves `if`/`match` with free variables, use `by_cases` on each unresolved condition BEFORE calling simp. Pass all case hypotheses to simp. Do NOT use `split` after simp or `native_decide`/`decide` on goals with free variables.")
        # Corpus analysis of 29 failed interactive runs found 11 (38%) ending
        # with an unsolved_goals error whose goal still carried the UNFOLDED
        # MONADIC TRACE — markers like `ContractResult.success`/`.revert`,
        # `Contract.run`, or a wrapper like `Core.Address.ofNat ((match ...))`
        # around a nested `match` over `getMappingAddr`/storage. Cross-family:
        # safe/owner_manager_reach (6), zama/erc7984 (2), paladin_votes (1),
        # kleros/sortition_trees (1), with 0 of 54 passed runs showing the
        # pattern (clean failure signal). In every case the agent kept adding
        # more helpers (`ContractResult.success`, `.snd`, `Contract.run`, …)
        # to its `simp` list without closing the goal, because the remaining
        # `if <cond>` arms in the trace test PROPOSITIONAL equality while the
        # available hypotheses are in BEq form (`(x != zeroAddress) = true`).
        # The existing if/match hint above is too generic — it never tells
        # the agent to bridge BEq→Prop or to `split_ifs` on the unreduced arms.
        has_monadic_trace = (
            "ContractResult.success" in details
            or "ContractResult.revert" in details
            or "Contract.run" in details
        )
        # Also catch the case where the literal markers above are absent
        # but the goal carries a raw `(X).run s).snd` pattern — i.e. the
        # agent tried to close the theorem without ever unfolding
        # `Contract.run`. Corpus analysis: this adds `swap_owner_ownerListInvariant`
        # (1 failed task whose final error has "unsolved goals" alongside a
        # synthesis placeholder), with 0 of 54 passed runs' final details
        # matching the pattern in a goal line.
        if not has_monadic_trace:
            for _ln in details.split("\n"):
                _stripped = _ln.lstrip()
                if _stripped.startswith("⊢") and re.search(
                    r"\.run\s+\w+\)\.snd", _ln
                ):
                    has_monadic_trace = True
                    break
        if has_monadic_trace:
            hints.append(
                "Your `simp` unfolded the contract function but the goal "
                "still carries the UNFOLDED MONADIC TRACE — look for "
                "`ContractResult.success`/`.revert`, nested `match` arms, "
                "or wrappers like `Core.Address.ofNat ((match ...))`. Do "
                "NOT keep adding more definitions (`ContractResult.success`, "
                "`.revert`, `.snd`, `Contract.run`, …) to your `simp` list; "
                "those are not the closing rewrites. Two concrete moves: "
                "(1) `split_ifs` (or `split`) to force case analysis on every "
                "leftover `if <cond> then ... else ...` inside the trace — "
                "each branch gives you a propositional hypothesis `h : x = 0` "
                "or `h : ¬ x = 0` that discharges the arm. "
                "(2) PRECONVERT any BEq hypothesis to propositional form "
                "BEFORE re-running simp: e.g. "
                "`have hNZ : owner ≠ zeroAddress := by simpa using hNotZero`. "
                "The `if owner = 0 then revert …` branch in the trace tests "
                "propositional equality, so a bare `(owner != zeroAddress) = "
                "true` will not discharge it until you bridge the forms. "
                "After preconverting, `simp_all` (not `simp`) can usually "
                "close the whole trace in one step because it rewrites the "
                "Prop-form hypotheses into the goal."
            )
        if "unused" in details.lower() and ("hBound" in details or "hypothesis" in details.lower()):
            hints.append("If a hypothesis is reported as unused by simp, try `simp_all` instead of `simp`. `simp_all` rewrites hypotheses into the goal, resolving mismatches between spec helper names and unfolded definitions.")
        # Only suggest a fresh by_cases restructure when we're NOT already
        # inside a successful case-split — otherwise the agent may undo its
        # own progress.
        if not case_labels:
            hints.append("Try restructuring: `by_cases h : condition · simp [..., h] · simp [..., h]`.")
    elif failure_class == "type_mismatch":
        if "decide" in details:
            hints.append("The goal contains `decide` expressions. Pass all precondition hypotheses to `simp` and it will reduce `decide` automatically. Do NOT try to manually match `decide` types.")
        # Corpus analysis of 29 failed interactive runs: 8 tasks (28%) hit a
        # type_mismatch where "is expected to have type" is followed by
        # un-reduced monadic-trace machinery — `ContractResult.revert`,
        # `ContractResult.success`, or nested `match match if ...` blocks.
        # This is a distinct shape from the cross-class `.val` coercion
        # asymmetry detector: here the hypothesis has been simplified to a
        # concrete shape (e.g. `¬Core.Address.ofNat (s.storageMap 0 owner).val = 0`)
        # but the expected type still carries the raw Contract.run trace
        # (e.g. `... ((match match if owner = 0 then ContractResult.revert ...`).
        # The generic "Unfold definitions" hint below does not name the
        # actual reducers to feed simp, so the agent loops on `exact h`
        # or `rw [...]` without ever reducing the goal. Tasks affected:
        # safe/{add_owner,remove_owner,swap_owner,setup_owners}_* covering
        # is_owner_correctness, owner_list_invariant, in_list_reachable.
        _expected_unreduced = bool(
            re.search(
                r"is expected to have type.{0,800}?"
                r"(?:ContractResult\.(?:revert|success)|match\s+match)",
                details,
                re.DOTALL,
            )
        )
        if _expected_unreduced:
            hints.append(
                "TYPE MISMATCH with un-reduced monadic trace on the "
                "EXPECTED side: your hypothesis has been simplified "
                "(e.g. `.storageMap 0 owner`) but the goal's expected "
                "type still contains raw `ContractResult.revert` / "
                "`ContractResult.success` / nested `match match if ...` "
                "blocks from an unreduced `Contract.run`. `exact h` will "
                "NEVER unify these — Lean does not automatically reduce "
                "the expected type. Fix: reduce the goal FIRST with "
                "`simp only [X, Contract.run, ContractResult.snd, "
                "ContractResult.revert, ContractResult.success, "
                "Verity.bind, Bind.bind, Verity.pure, Pure.pure]` where "
                "`X` is the contract function literally visible in the "
                "match (e.g. `OwnerManager.addOwner`, "
                "`OwnerManager.removeOwner`, `OwnerManager.swapOwner`, "
                "`OwnerManager.setupOwners`). You may also need "
                "`split_ifs` on the `if owner = 0` / sentinel guards. "
                "ONLY after the expected type is in simplified form will "
                "`exact h` / `simpa using h` unify."
            )
        hints.append("Unfold definitions to align types. Check spec matches impl.")
    elif failure_class == "split_failed":
        hints.append("Do not split the post-state. Use by_cases with branch-specific helpers.")
    elif failure_class == "no_goals":
        hints.append("Previous simp closed the goal. Remove trailing tactics.")
    elif failure_class == "free_variables":
        # Corpus analysis of 29 failed interactive runs found 3 distinct tasks
        # (damn_vulnerable_defi side_entrance, kleros sortition_trees, safe
        # owner_manager_reach add_owner) hitting `expected type must not
        # contain free variables` with 19 total occurrences across attempts.
        # Lean's own error text tells the user "Use the '+revert' option to
        # automatically cleanup and revert free variables" — yet the prior
        # hint ("Reduce to concrete equalities before decide/native_decide")
        # didn't mention `revert` at all and pointed agents away from the
        # exact remedy. The trigger is always `decide` / `native_decide` /
        # `cases <var>` / `induction <var>` run on a goal that still
        # mentions local hypotheses (e.g. `hLow`, `hHigh`, `nodeIndex`) or
        # pattern-bound names (`val✝`, `isLt✝`). Surface `revert` as the
        # primary fix and list the alternative tactics (`omega`, `simp_all`,
        # `rcases`) that work on open goals with free hypotheses in scope.
        hints.append(
            "Lean rejected the goal because its type still contains FREE "
            "VARIABLES — local hypotheses or pattern-bound names "
            "(`val✝`, `isLt✝`, …) the tactic cannot close over. `decide`, "
            "`native_decide`, `cases <x>`, and `induction <x>` all require "
            "a closed goal. Two generic remedies: "
            "(a) `revert <h1> <h2> ... <x>` EVERY local hypothesis and "
            "variable that appears in the displayed goal, then re-run the "
            "tactic — this turns the goal into a closed implication. The "
            "Lean 4 shortcut is `decide +revert` / `native_decide +revert`, "
            "which Lean's own error hint recommends. "
            "(b) Replace `decide` / `native_decide` with `omega` (for "
            "Nat/Int inequalities), `simp_all` (for boolean/equational "
            "goals), or an explicit `exact` term — these tactics consult "
            "the local hypothesis context directly and do not require a "
            "closed goal. For `cases <x>` / `induction <x>` on a "
            "structure, prefer `rcases x with ⟨...⟩` or destructure inside "
            "a `have`/`obtain` so you do not leak `val✝`/`isLt✝` into the "
            "surrounding goal."
        )
    elif failure_class == "unknown_tactic":
        hints.append("Use standard Lean 4 / Mathlib tactics only.")
    elif failure_class == "simp_no_progress":
        hints.append("simp/dsimp made no progress. CRITICAL: In each `by_cases` branch, you MUST repeat the FULL simp set (all contract definitions, storage fields, getStorage, setStorage, Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd) PLUS the case hypothesis and all preconditions. Bare `simp [h]` will never work.")
        hints.append("Check that you are using the correct function name from the implementation file.")
    elif failure_class == "unfold_failed":
        hints.append("unfold failed. The definition name may be wrong or not unfoldable.")
        hints.append("Use search_public_defs to find the exact definition name.")
    elif failure_class == "rfl_failed":
        hints.append("rfl failed because the LHS is not definitionally equal to the RHS.")
        if "match" in details or "if " in details:
            hints.append("The goal has unresolved `if`/`match` expressions with free variables. Use `by_cases` on each condition BEFORE calling simp, not `split` after. Pass all case hypotheses to simp. For nested conditionals, nest `by_cases`. Example: `by_cases h : cond; · simp [..., h]; · simp [..., h]`.")
        else:
            hints.append("Try replacing `rfl` with `simp` or adding more definitions to the simp set.")
    elif failure_class == "tactic_misuse":
        hints.append("The tactic was used incorrectly for this goal shape.")
        hints.append("Check the goal state with inspect_lean_goals using a ?_ hole.")
    elif failure_class == "omega_failed":
        hints.append(
            "omega only handles LINEAR integer/natural arithmetic. It cannot close goals "
            "containing variable * variable, division, or modulus. Look at the "
            "counterexample section — any term on the RHS of `where` that mixes two "
            "variables multiplicatively, or uses `/` or `%`, is outside omega's reach."
        )
        nonlinear_hints: list[str] = []
        # Verity-specific: when the counterexample's `where:` section binds a
        # variable to `↑(mul …)`, `↑(add …)`, or `↑(sub …)`, omega is seeing
        # the Uint256 operation as an OPAQUE Nat — not as `a.val * b.val`,
        # `a.val + b.val`, or `a.val - b.val`. That masks what is often
        # actually a LINEAR goal once the `.val` coercion is rewritten under
        # the no-overflow hypothesis already in scope. Corpus analysis of 29
        # failed interactive runs found 38 omega_failed incidents carrying
        # 96 opaque-op occurrences (mul: 45, add: 34, sub: 17), yet ZERO
        # proofs (failed OR passed) used the canonical conversion lemmas —
        # the agent searched for related terms like "val_mul", "Uint256
        # mul add sub ge theorem lemma val", "div_mul_le" but never found
        # the right names. Give it the specific lemma + hypothesis shape.
        opaque_ops = set(re.findall(r"↑\((mul|add|sub)\s", details))
        if opaque_ops:
            op_lemmas = []
            if "mul" in opaque_ops:
                op_lemmas.append(
                    "`Uint256.mul_eq_of_lt (h : a.val * b.val < modulus) : "
                    "(a * b).val = a.val * b.val`"
                )
            if "add" in opaque_ops:
                op_lemmas.append(
                    "`Uint256.add_eq_of_lt (h : a.val + b.val < modulus) : "
                    "(a + b).val = a.val + b.val`"
                )
            if "sub" in opaque_ops:
                op_lemmas.append(
                    "`Uint256.sub_eq_of_le (h : b.val ≤ a.val) : "
                    "(a - b).val = a.val - b.val`"
                )
            ops_shown = "/".join(sorted(opaque_ops))
            nonlinear_hints.append(
                f"The counterexample shows `↑({ops_shown} …)` opaque terms — "
                f"omega cannot see inside a Uint256 `mul` / `add` / `sub` "
                f"application. Rewrite the `.val` coercion FIRST using: "
                + "; ".join(op_lemmas)
                + ". The required bound (typically the spec's `hNoOverflow` "
                "premise) is already in scope — pass it as the argument. "
                "After `rw [Uint256.mul_eq_of_lt hNoOverflow]` (or similar) "
                "the goal becomes a plain `Nat` (in)equality and omega will "
                "close it."
            )
        if "/" in details or "% " in details or " mod " in details:
            nonlinear_hints.append(
                "For division/modulus: first rewrite `a / b` and `a % b` via "
                "`Nat.div_add_mod` / `Nat.mul_div_cancel'` so omega sees a linear form, "
                "or case-split on whether the divisor is zero and handle each branch."
            )
        if "val *" in details or "* ↑" in details:
            nonlinear_hints.append(
                "For variable multiplications: introduce helper lemmas that bound the "
                "product (e.g. `Nat.mul_le_mul`), or try `nlinarith` / `positivity` which "
                "handle some nonlinear cases. Pure omega will never close a goal whose "
                "counterexample mentions a product of two symbolic `.val` terms."
            )
        hints.extend(nonlinear_hints)
    elif failure_class == "constructor_failed":
        hints.append(
            "`constructor` only works on inductive-type goals (And, Or, Exists, Sigma, "
            "structures). The goal you're targeting is an equality, implication, or an "
            "unreduced expression — not a constructor-shaped type. Either (a) `simp` / "
            "`unfold` first to expose an inductive head symbol, (b) `intro` pending "
            "hypotheses if the goal is `A → B`, or (c) use `refine ⟨_, _⟩` / "
            "`exact ⟨_, _⟩` if you already know the witnesses for an And/Exists."
        )
    elif failure_class == "cases_failed":
        hints.append(
            "`cases` / `induction` requires an inductive-type term. The major "
            "premise here is NOT inductive — most commonly it's an implication "
            "`A → B` (the agent tried `cases h` where `h : A → B`), a function "
            "type, or a raw equality between non-inductive values. Remedies: "
            "(a) if the hypothesis is `A → B`, first produce `A` and apply it "
            "(`have hb := h ha`) or `intro` if the implication is the goal; "
            "(b) for a decidable Prop use `by_cases h : P` instead of `cases`; "
            "(c) to derive `False` from a contradictory hypothesis use "
            "`exact absurd … h` or `exact (h …).elim`; (d) for `Bool`-valued "
            "equalities like `x == y = true`, rewrite with `Bool.ne_iff` / "
            "`beq_iff_eq` before case-splitting. Do NOT keep retrying `cases` "
            "on the same target."
        )
    elif failure_class == "module_not_found":
        hints.append(
            "The import path you requested is not available in this workspace. In "
            "particular, `Mathlib` is NOT a dependency of verity-benchmark — only the "
            "core Lean 4 prelude, `Batteries`, and the task's own `Benchmark.*` public "
            "modules are importable. Remove the offending `import` line and reach for "
            "core Lean / Batteries lemmas, or search_public_defs for existing helpers."
        )
    elif failure_class == "synthesis_failed":
        hints.append(
            "Lean could not infer a `_` / `?_` placeholder from context. Either (a) "
            "replace `_` with an explicit term, (b) add a `show <goal type>` line above "
            "the tactic so Lean knows the expected type, or (c) use `?_` (named hole) "
            "with `inspect_lean_goals` to see what Lean expected there before filling it."
        )
        # Corpus analysis: 3 of 7 failed runs ending in `synthesis_failed` left
        # a raw `(X).run s).snd` monadic trace in the goal at the hole — the
        # agent had written `exact ?_` without ever unfolding the contract
        # function, so `inspect_lean_goals` would just show the un-reduced
        # trace again. Of 54 passed runs, only 1 intermediate check hit this
        # shape (and the run recovered afterward), so the pattern is a clean
        # failure-side signal. Tasks: safe/swap_owner_ownerListInvariant,
        # safe/setupOwners_ownerListInvariant, safe/removeOwner_isOwnerCorrectness,
        # zama/transfer_sufficient. The existing generic hint above never tells
        # the agent that the hole is unreachable until `Contract.run` unfolds.
        _run_snd_in_goal = False
        for _ln in details.split("\n"):
            _stripped = _ln.lstrip()
            if _stripped.startswith("⊢") and re.search(
                r"\.run\s+\w+\)\.snd", _ln
            ):
                _run_snd_in_goal = True
                break
        if _run_snd_in_goal:
            hints.append(
                "The goal at the `?_` / `_` hole still contains a raw "
                "`(X).run s).snd` monadic trace — `Contract.run` has NOT "
                "been reduced, so no placeholder term can unify with it. "
                "Filling the hole with more `?_` or `inspect_lean_goals` "
                "alone will not make progress; you must first UNFOLD the "
                "contract function before (or at) the hole. Concrete move: "
                "replace `exact ?_` with "
                "`simp [X, Contract.run, Verity.bind, Bind.bind, Verity.pure, "
                "Pure.pure, ContractResult.snd]` where `X` is the contract "
                "function literally visible in the goal (e.g. "
                "`OwnerManager.swapOwner`, `ERC7984.transfer`). Once the "
                "trace is reduced, re-run inspect_lean_goals to see the "
                "propositional residue and close it with `split_ifs` / "
                "`simp_all` / branch-hypotheses as usual. Do NOT submit a "
                "final proof body that still contains `?_`; the harness "
                "reports `don't know how to synthesize placeholder` and the "
                "run fails even though the rest of the skeleton is fine."
            )
        else:
            # Corpus analysis of 29 failed runs: 7 terminate with
            # `don't know how to synthesize placeholder`. Of those 7, only
            # ~3 have a `(X).run s).snd` monadic trace in the goal (handled
            # above). The other ~4 land with goals that are arithmetic on
            # `s.storage` (ethereum/full_deposit_preserves_partial_gap,
            # lido/shares_conversion_monotone), list-predicate witnesses
            # (safe/setup_owners_acyclicity,
            # safe/setup_owners_owner_list_invariant), or conditional
            # `if … then … else …` expressions — shapes where the existing
            # generic `show <goal type>` hint is not actionable, so the
            # agent just re-probes with `inspect_lean_goals` and loops
            # until the tool budget runs out. Emit a shape-aware hint so
            # the agent knows to replace the underscore with an explicit
            # witness rather than continue probing.
            hints.append(
                "`don't know how to synthesize placeholder` means an "
                "underscore `_` (or named hole `?_`) inside a `refine` / "
                "`exact ⟨…⟩` / constructor call has no canonical filling. "
                "Lean will NOT invent a Nat, Uint256, list, or proof term "
                "— you must supply it. Concrete fixes by goal shape: "
                "(a) arithmetic (e.g. `⊢ add x 1 - add y 1 = x - y`, "
                "`⊢ n + k = m`) → replace `_` with `(by omega)` or "
                "`(by simp; omega)`; "
                "(b) conditional (`⊢ if P then … else …`) → case-split "
                "with `split_ifs` BEFORE reaching the hole so each branch "
                "has a concrete target; "
                "(c) list-invariant witness → write the explicit list "
                "literal (e.g. `[owner1, owner2, owner3]`) rather than "
                "`_`; "
                "(d) propositional `And` / `Exists` → replace `⟨_, _⟩` "
                "with `⟨<explicit witness>, by <tactic>⟩`. Repeating "
                "`inspect_lean_goals` at the same hole will show the same "
                "unsolvable placeholder — do not retry the same shape, "
                "rewrite the hole with one of the concrete forms above."
            )
    elif failure_class == "parse_error":
        # Lean 4 core does NOT recognise `lemma` — it is a Mathlib-only alias
        # for `theorem`. When the agent writes `(private) lemma foo ...` in a
        # no-Mathlib workspace, Lean reports `unexpected identifier; expected
        # 'abbrev', 'axiom', ..., or 'theorem'` at the `lemma` token. Corpus
        # analysis of 83 interactive runs: 3 of 29 failed tasks
        # (lido/locked_funds_solvency, openzeppelin/preview_deposit_rounds_down,
        # safe/in_list_reachable — 10% of failures) wrote `lemma` helpers at
        # some point; 1 of 54 passed runs also tried it but moved on after
        # one rewrite. The generic parse-error hint below lists four shapes
        # (tactic-in-term-position, missing `by`, stray tokens, branch
        # indentation) but NONE of them mention keyword choice, so the agent
        # keeps re-editing the proof body while the real fix is a one-token
        # rename at the declaration header. Fire the lemma-specific hint FIRST
        # when the error's "expected … or 'theorem'" list appears (a fingerprint
        # unique to the top-level-command parse shape).
        _expects_theorem = (
            "expected 'abbrev'" in details
            and "'theorem'" in details
        )
        if _expects_theorem:
            hints.append(
                "Lean 4 core does NOT recognise `lemma` — it is a Mathlib-only "
                "alias for `theorem`, and this workspace has no Mathlib. The "
                "\"expected 'abbrev', …, or 'theorem'\" list in the error is "
                "Lean telling you which top-level commands ARE valid at that "
                "position. Fix: rename every `lemma` (and `private lemma`) "
                "helper in the candidate to `theorem` (and `private theorem`). "
                "The declaration body does not need any other change."
            )
        hints.append(
            "Lean rejected the proof before type-checking — the candidate contains "
            "invalid Lean 4 syntax. Common causes: (a) a tactic written in term "
            "position (e.g. `exact simp [...]` instead of `exact by simp [...]`), "
            "(b) a `by` block without an indented tactic on the next line, (c) stray "
            "`;`, `|`, or `using` tokens outside a `have`/`simpa` context, (d) a "
            "`· simp [...]` branch indented less than the bullet. Re-read the "
            "editable file via read_public_file to see the exact character positions "
            "in the error, and rewrite the proof body as a clean `:= by <tactics>` "
            "block — do not try to patch token-by-token."
        )

    # Pattern-based hints that cut across failure classes. These used to live in
    # a separate `_build_repair_guidance` pass that was appended after this
    # function ran; corpus analysis showed 68% of its output was semantically
    # redundant (sometimes contradictory) with the class-based hints above, so
    # that pass was removed. The few patterns it uniquely covered — binder-type
    # inference, Lean syntax errors, and the ContractState.storage function
    # hint — are preserved here.
    if "failed to infer binder type" in details:
        hints.append(
            "Lean cannot infer a binder type. Add explicit type annotations to "
            "your helper lemma parameters."
        )
    if "unexpected token" in details or "expected 'by'" in details:
        hints.append(
            "Syntax error. Ensure the theorem body uses `:= by` followed by "
            "tactics. Do not use `:=` with a term-mode proof unless you are "
            "certain of the syntax."
        )
    if "Function expected at" in details:
        hints.append(
            "Use `s.storage 0` (function application) not `s.storage[0]` or "
            "`s.storage.0`. `ContractState.storage` is a function `Nat → Uint256`."
        )
    # Detect the recurring Uint256/Address `.val` coercion asymmetry: one side
    # of a `type mismatch … has type … but is expected to have type …` pair
    # has a `.val` projection and the other does not. Corpus analysis of 83
    # interactive runs: the pattern `"after simplification has type … .val"`
    # appears in 14 of 29 failed tasks (48%), yet only 2 of those tasks have
    # `failure_class == "type_mismatch"` at the point of failure — the rest
    # cascade into `unsolved_goals` / `unknown_identifier` when secondary
    # errors come from the same simp call, so the old in-branch hint was
    # skipped for 12/14 of the actual `.val` mismatches. Lifting the check
    # to run cross-class fires the hint whenever the mismatch text appears,
    # regardless of which error Lean listed first.
    _tm = re.search(
        r"has type\s+(.{5,300}?)\s+but is expected to have type\s+(.{5,300})",
        details, re.DOTALL,
    )
    if _tm and (".val" in _tm.group(1)) != (".val" in _tm.group(2)):
        _val_hint = (
            "Your hypothesis differs from the expected type by a `.val` projection "
            "(Uint256/Address/Nat). Do NOT keep retrying `exact h` — Lean will not "
            "insert the coercion for you. Use `by simpa using h` or `by simp_all` "
            "to let simp bridge the `.val`; if the goal is a Prop inequality, "
            "`by omega` after exposing `.val` on both sides also works. If the "
            "mismatch is inside a negation like `¬x = 0` vs `¬x.val = 0`, rewrite "
            "with the underlying injectivity lemma (e.g. `Core.Uint256.val_eq_zero`, "
            "`Core.Address.ofNat_eq_zero`) found via search_public_defs."
        )
        if _val_hint not in hints:
            hints.append(_val_hint)
    # Detect Lean's `unused simp argument` linter warning and surface
    # generic meta-advice. Corpus analysis of 29 failed interactive runs:
    # 16 tasks (55%) emit at least one `This simp argument is unused:
    # <name>` warning (450 total matches across those tasks), spanning 5
    # failure classes — unsolved_goals (8), synthesis_failed (3),
    # unknown_identifier (3), free_variables (1), omega_failed (1). The
    # only pre-existing gate lives inside the `unsolved_goals` branch and
    # fires on `"hBound" in details or "hypothesis" in details.lower()` —
    # `hBound` is a hypothesis name from one single task, and the word
    # `"hypothesis"` never appears in Lean's linter text (the linter says
    # "simp argument"), so in practice the old gate only matched 1 of 16
    # tasks. A cross-class check on the exact warning text fires on all
    # 16 with no FP risk: 45 passing tasks also hit this warning during
    # iteration and still closed their proofs, so the warning is
    # non-terminal. The name-bearing hint text is naturally state-keyed
    # (different flagged args → different first-80-char fingerprint), so
    # it won't be dedup-suppressed when the agent resubmits with new
    # unused args.
    _unused_simp_args = re.findall(
        r"This simp argument is unused:\s*\n\s*(\S+)", details
    )
    if _unused_simp_args:
        # Dedupe while preserving order, cap to keep hint readable.
        _seen: set[str] = set()
        _ordered: list[str] = []
        for _n in _unused_simp_args:
            if _n not in _seen:
                _seen.add(_n)
                _ordered.append(_n)
            if len(_ordered) >= 4:
                break
        _names_str = ", ".join(f"`{n}`" for n in _ordered)
        _unused_hint = (
            f"Lean's linter reports UNUSED simp arguments ({_names_str}): "
            f"these hypotheses/definitions cannot be used as rewrites by "
            f"`simp [...]` against the current goal. Piling on more arguments "
            f"will not close it. Concrete moves: (1) REMOVE each flagged "
            f"argument as the linter suggests — leaving dead args in obscures "
            f"the real obstruction. (2) If the flagged item is a HYPOTHESIS "
            f"in BEq form (e.g. `(x != y) = true`), convert to Prop form "
            f"FIRST: `have h' : x ≠ y := by simpa using h`, then pass `h'` "
            f"to simp, OR switch the whole call to `simp_all` — `simp_all` "
            f"rewrites hypotheses INTO the goal and often bridges BEq/Prop "
            f"mismatches that `simp [h]` cannot. (3) If the flagged item is "
            f"a DEFINITION (module-qualified, e.g. `ContractX.foo`), simp "
            f"either already unfolded it or it has no simp-lemma form — "
            f"drop it, and if you need the unfolding use `unfold` / "
            f"`simp only [ContractX.foo]` explicitly. Do NOT resubmit with "
            f"the same unused arguments."
        )
        if _unused_hint not in hints:
            hints.append(_unused_hint)
    return hints


def tool_result_json(result: dict[str, Any]) -> str:
    return json.dumps(result, indent=2, sort_keys=True)

# Proof Patterns

Use public operational proof patterns, not hidden case solutions.

The editable file already imports `Benchmark.Grindset`, which provides the
`grind_norm` simp set: monad collapse (`bind`/`Contract.run`/`.snd`),
read-after-write storage and mapping lemmas (including Uint256-keyed and
double mappings), `require` discharge, branch distribution (`ite_apply_arg`),
and Uint256 order/val normalization. Build your proof around it.

## Primary: the normalize–unfold–simp–split template

This template closes most slot-write and spec-unfolding obligations. The
name lists are mechanical: every `*_spec` name in the editable file, the
contract function under test, every storage field of the contract
(`fieldName : Uint256 := slot N` declarations), and every helper `def` from
the public spec files (read them with `read_file` if unsure).

```lean
theorem slot_write_theorem ... := by
  -- 1. normalize hypotheses into .val form
  try simp only [grind_norm] at *
  -- 2. unfold spec + contract function + helpers (try each; unused ones no-op)
  try unfold spec_name
  try unfold ContractName.fn
  -- 3. one simp with everything: grind_norm + storage fields + helpers + hyps
  simp [grind_norm, ContractName.fn, ContractName.fieldA, ContractName.fieldB,
        specHelper, *]
  -- 4. discharge remaining branches
  all_goals try (split_ifs <;> simp_all [grind_norm])
  all_goals try (repeat' (split <;> simp_all [grind_norm]))
  all_goals try omega
```

Why each step matters:

- Storage field names in the simp list reduce symbolic `.slot` projections
  (`ContractName.fieldA.slot`) to numeric literals, letting `simp` discharge
  `require` guards directly from your hypotheses.
- `simp [..., *]` uses your hypotheses as rewrites; if a hypothesis mentions
  a spec helper (e.g. `computedClaimAmount`) while the goal has it inlined,
  use `simp_all [grind_norm, spec_name, ContractName.fn, <fields>, <helpers>]`
  instead — it unfolds inside hypotheses too.
- `split_ifs <;> simp_all [grind_norm]` handles undecided contract branches
  (deposit-size thresholds and similar) without manual `by_cases`.

## Secondary: grind-first pattern

Start with `unfold` on the spec name followed by `grind [...]` passing the
contract function you are reasoning about and every storage field it touches.
Storage fields are declared as `fieldName : Uint256 := slot N` inside
`verity_contract`; hint each one by its fully-qualified name
(e.g. `ContractName.depositCount`, `ContractName.chainStarted`) so `grind` can
reduce `.slot` to the concrete slot number.

```lean
theorem slot_write_theorem
    (x : Uint256) (s : ContractState)
    (hGuard : ...) :
    let s' := ((ContractName.fn x).run s).snd
    spec_name x s s' := by
  unfold spec_name
  grind [ContractName.fn,
         ContractName.fieldA, ContractName.fieldB, ContractName.fieldC]
```

Rules of thumb for the grind hint list:

- Always include `ContractName.fn` for the contract function under test.
- Always include every storage field of `ContractName` that the function
  reads or writes (when in doubt, include them all — extra hints are cheap).
- If the spec references another helper function (e.g. `computedClaimAmount`),
  add that helper name too so `grind` can unfold it.
- Do not add imports: `Benchmark.Grindset` is already imported by the task
  skeleton, and modules outside your workspace will not compile.

If `grind` leaves the goal visibly closer but not closed, use `grind?` once
to print the actual lemma set it chose; copy any useful additions back into
your `grind [...]` hint list, then retry.

## Branching with grind

When the contract has a case split (an `ite`, a `require` with a non-trivial
condition, or nested `if`s in the spec), prove the branch facts first and
pass them to `grind` along with the usual hints:

```lean
theorem branch_theorem ... := by
  by_cases hBranch : condition
  · unfold spec_name
    grind [ContractName.fn, ContractName.field, hBranch]
  · have hNotBranch : ¬ condition := hBranch
    unfold spec_name
    grind [ContractName.fn, ContractName.field, hNotBranch]
```

For nested conditionals (e.g. a threshold check inside a deposit-size check),
nest `by_cases` the same way and put every branch hypothesis into the
`grind [...]` list:

```lean
by_cases hBig : depositAmount >= 32000000000
· by_cases hThresh : add (s.storage 1) 1 = 65536
  · grind [ContractName.fn, ContractName.field, hCount, hMin, hBig, hThresh]
  · grind [ContractName.fn, ContractName.field, hCount, hMin, hBig, hThresh]
· grind [ContractName.fn, ContractName.field, hCount, hMin, hBig]
```

For arithmetic threshold branches, restate the negated fact in the comparator
form used by the generated code before handing it to `grind`:

```lean
have hNotFull : ¬ 32000000000 ≤ depositAmount := Nat.not_le_of_lt hSmall
grind [ContractName.fn, ContractName.field, hCount, hMin, hNotFull]
```

If one theorem has to work for both sides of a branch, prove two private
helpers first (one per branch, each closed by `grind`), then `by_cases` in
the public theorem and finish each branch with `exact helper_branch ...`.

## Fallback: simp + by_cases

If `grind` still leaves goals after you have unfolded the spec and hinted the
contract function plus every storage field, fall back to the pre-grindset
simp-heavy recipe. This is strictly a fallback; prefer to extend the `grind`
hint list first.

```lean
-- Fallback when grind alone does not close:
by_cases hBranch : condition
· simp [ContractName.fn, hBranch, ContractName.slotField,
    getStorage, setStorage, Verity.require, Verity.bind, Bind.bind,
    Verity.pure, Pure.pure, Contract.run, ContractResult.snd]
· have hNotBranch : ¬ condition := hBranch
  simp [ContractName.fn, hNotBranch, ContractName.slotField,
    getStorage, setStorage, Verity.require, Verity.bind, Bind.bind,
    Verity.pure, Pure.pure, Contract.run, ContractResult.snd]
```

The simp set MUST include every storage field definition from the contract.
Without them, `simp` leaves unresolved `if` expressions comparing
`s.storage ContractName.field.slot` against constants.

Do not use `split` on the final post-state goal unless the goal itself is
explicitly a conjunction or a sum-type elimination. Generated Verity
execution terms often simplify better if you first prove the exact branch
facts used by the contract and then call `simp`.

If `simp` leaves nested `match`/`if` expressions with free variables, use
`by_cases` on each unresolved condition BEFORE calling `simp`, not `split`
after. Pass all case hypotheses to `simp`.

If `simp` leaves unsolved goals because a hypothesis uses a spec helper name
(e.g., `computedClaimAmount`) while the goal has the definition already
unfolded, use `simp_all` instead of `simp`. `simp_all` rewrites hypotheses
into the goal context, resolving name mismatches automatically.

```lean
unfold specName
simp_all [ContractName.fn, getStorage, setStorage, getMapping, setMapping,
          msgSender, Verity.require, Verity.bind, Bind.bind,
          Verity.pure, Pure.pure, Contract.run, ContractResult.snd,
          specHelper]
```

If `simp` reduces the goal to concrete slot equalities or a finite `if` over
concrete slot numbers, `native_decide` or `decide` often closes the remaining
goal:

```lean
have hSlot : s'.storage slot = expected := by
  simp [ContractName.fn, hGuard, ...]
  native_decide
```

If `simp` already solves the goal, do not leave a trailing `decide`, `exact`,
or extra tactic line after it; Lean will report `no goals to be solved`.

If the public theorem is just a named spec, it is often cleaner to:

1. prove a private helper theorem about the concrete post-state slots,
2. unfold the spec,
3. finish with `simpa using ...`.

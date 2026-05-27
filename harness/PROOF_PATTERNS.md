# Proof Patterns

Use public operational proof patterns, not hidden case solutions.

Lean 4.22's `grind` tactic is the primary closer for Verity execution proofs.
Every generated task skeleton imports `Benchmark.Grindset`, which bundles the
`@[grind]`-tagged operational lemmas (`getStorage`, `setStorage`,
`setMapping`, `setMappingUint`, `Verity.require`, `Verity.bind`, `Bind.bind`,
`Verity.pure`, `Pure.pure`, `Contract.run`, `ContractResult.snd`, and friends)
needed to reduce Verity execution terms. You should lean on `grind` first and
only fall back to `simp`/`by_cases` if grind leaves goals open.

## Primary: grind-first pattern

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
- You do NOT need to hint the operational lemmas (`getStorage`, `setStorage`,
  `Verity.bind`, `Contract.run`, `ContractResult.snd`, ...). They are already
  tagged `@[grind]` via `Benchmark.Grindset`.

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

# Harness Prompt

Each task gives the agent:
- fixed implementation files
- fixed specification files
- one editable proof file
- one theorem target

The agent must return the full proof file. It must not change specs, change
implementations, or rely on hidden solved proofs.

The harness rejects placeholders, runs Lean in a temp workspace, and checks
the target theorem.

## Proof strategy

Every generated task skeleton already imports `Benchmark.Grindset` and starts
with a grind-first body of the form:

```lean
theorem foo ... := by
  unfold foo_spec
  grind [ContractName.fn, ContractName.fieldA, ContractName.fieldB]
```

That is the pattern to keep. Your first attempt should always be:

1. Keep `unfold <spec_name>` on the first line of the proof.
2. Call `grind [ContractName.fn, <every storage field the function touches>]`.
   Include every storage field declared inside `verity_contract ContractName`
   — extra hints are cheap, missing hints are expensive. Do NOT hint the
   generic operational lemmas (`getStorage`, `setStorage`, `Verity.bind`,
   `Contract.run`, `ContractResult.snd`, …); they are already tagged
   `@[grind]` by `Benchmark.Grindset`.
3. If the goal has a case split, introduce the branch hypotheses with
   `by_cases` BEFORE the `grind` call and pass each hypothesis into the
   `grind [...]` list alongside the contract hints.
4. If `grind` leaves goals open, call `grind?` once on the stuck state. It
   prints the concrete lemma set grind chose; copy any additions you see back
   into your `grind [...]` hint list, then retry.
5. Only if `grind` still fails after the above, fall back to the simp-heavy
   recipe in `harness/PROOF_PATTERNS.md` (`simp` / `simp_all` with the
   operational lemmas enumerated explicitly, optionally finished with
   `native_decide`).

Do not remove `import Benchmark.Grindset`, do not remove `unfold <spec>`, and
do not revert to a pure `simp`-only pattern unless you have first tried
`grind` with a complete hint list and observed it fail.

See `harness/PROOF_PATTERNS.md` for worked examples of both the grind-first
primary pattern and the simp/`by_cases` fallback.

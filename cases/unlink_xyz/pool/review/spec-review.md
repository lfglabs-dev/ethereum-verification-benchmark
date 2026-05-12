# Spec review

The Verity model of `UnlinkPool` exposes three classes of declarations:

## 1. Pure Lean specs (`Specs.lean`)

Assumed protocol boundaries — Poseidon, Permit2, Lazy-IMT, Groth16. Each is
declared with an explicit `axiom` and an associated proof-status tag in the
`unlink-verity` namespace. These declarations are not part of Verity core
and should appear in the case's trust manifest at proof time.

## 2. Verity contract surface (`Contract.lean`)

Mirrors the Solidity source structure: storage layout, custom errors,
constructor, initializer, owner / relayer admin functions, the two
`Note[]`-only entrypoints (`deposit`, `adapterDeposit`), and the
public views.

## 3. Blocked surface (`Contract.lean`, `BLOCKED(#1760-nested-dynamic):` markers)

`transfer`, `withdraw`, `adapterWithdraw` are documented but not translated,
because their parameter shapes carry nested dynamic members through struct
arrays. The Verity macro reports
"struct parameter projection from an ABI-dynamic root is not supported" at
`Verity/Macro/Translate.lean:1715`. Once that lands (tracked in verity#1760
P0), these can be filled in 1:1 from `UnlinkPool.sol`.

## Build status

Case stage: `scoped`. The translation compiles incrementally — the four
Lean files exist in the case skeleton and are valid against the lakefile-
pinned Verity revision. Promotion to `build_green` happens when:

1. PR #1827 merges in lfglabs-dev/verity (BN254 precompile ECMs + keccak256_lit literal sugar).
2. The lakefile in this repo is bumped to the resulting verity commit.
3. The four entry points that depend on those features (constructor /
   initialize / hashNote / deposit) are wired through and pass `lake build`.
4. The three blocked entry points carry explicit `BLOCKED(...)` markers so
   the case has no unconstrained stubs.

## Next milestones

- `build_green` once the constructor + initialize + deposit + adapterDeposit
  + admin / view functions all elaborate.
- `proof_partial` after a target invariant is selected (likely:
  per-token conservation across `deposit + adapterDeposit` once nullifier
  spend is gated, modeled with the four assumed boundaries).

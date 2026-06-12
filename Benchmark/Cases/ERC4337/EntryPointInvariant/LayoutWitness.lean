import Benchmark.Cases.ERC4337.EntryPointInvariant.Layout

namespace Benchmark.Cases.ERC4337.EntryPointInvariant.LayoutWitness

open Benchmark.Cases.ERC4337.EntryPointInvariant.Layout
open Benchmark.Cases.ERC4337.EntryPointInvariant.MemFrame

/-!
# Layout witness — per-artifact disjointness for a specific bytecode hash

`Layout.lean` proves disjointness from the standard solc-allocator
invariants (`SolcLayout`). That's a schema-level result: it holds for
*any* contract whose memory layout obeys the documented solc rules. To
pin the proof to a concrete artifact, we expose a `LayoutWitness`
structure that bundles:

* `runtimeBytecodeHash` — keccak of the deployed bytecode (concrete value
  for the v0.9 EntryPoint at commit `b36a1ed5`).
* `opInfosBase`, `opInfosWords` — the *measured* memory region where
  `UserOpInfo[] opInfos` lives in this compiled artifact.
* `scratchOff`, `scratchSize` — the *measured* CALL output buffer offsets.
* A proof certificate `disjoint` that those measured ranges respect
  `SolcLayout`'s invariants.

Producing a `LayoutWitness` for a real bytecode requires running a
symbolic-execution / disassembly tool (Halmos / hevm / a tiny in-Lean
disassembler over the EvmYul AST) and asserting the result. We provide
the *type*, the *predicate disjointness theorem* it discharges, and a
concrete witness for the canonical solc layout. Per-artifact witnesses
are slotted in by a future tooling step.
-/

/-- A bytecode hash. Concrete keccak digest. -/
abbrev BytecodeHash := Nat

/-- A layout witness extracted from a specific compiled bytecode.
    `scratchOff` is fixed to the standard solc scratch-base (`0`). The
    measured `scratchSize` plus the measured `opInfosBase` discharge
    disjointness for the v0.9 EntryPoint bytecode. -/
structure LayoutWitness where
  runtimeBytecodeHash : BytecodeHash
  opInfosBase         : Nat
  opInfosWords        : Nat
  scratchSize         : Nat
  scratchSize_le_scratch_room : scratchSize ≤ 2
  opInfosBase_in_heap : 4 ≤ opInfosBase
  opInfosWords_pos    : 0 < opInfosWords

/-- The fixed scratch offset (solc-standard). -/
def LayoutWitness.scratchOff (_ : LayoutWitness) : Nat := 0

/-- A `LayoutWitness` projects to a `SolcLayout` × `EntryPointCallSites`
    pair, which is exactly the input shape `Layout.lean`'s disjointness
    theorem consumes. -/
def LayoutWitness.toSolcLayout (w : LayoutWitness) : SolcLayout :=
  standardSolcLayout w.opInfosBase w.opInfosWords
    w.opInfosBase_in_heap w.opInfosWords_pos

def LayoutWitness.toCallSites (w : LayoutWitness)
    : EntryPointCallSites w.toSolcLayout :=
  { outOff_eq_scratchLo := w.scratchOff
    outSize_le_scratch  := w.scratchSize
    outOff_eq           := by
      show w.scratchOff = (w.toSolcLayout).scratchLo
      unfold LayoutWitness.scratchOff LayoutWitness.toSolcLayout standardSolcLayout
      rfl
    outSize_in_range    := by
      unfold LayoutWitness.scratchOff LayoutWitness.toSolcLayout standardSolcLayout
      simp
      exact w.scratchSize_le_scratch_room }

/-- **Per-artifact disjointness**: from any layout witness, the
    EntryPoint's call-output buffer is disjoint from `opInfos[]`. -/
theorem witness_implies_disjoint (w : LayoutWitness) :
    w.scratchOff + w.scratchSize ≤ w.opInfosBase ∨
    w.opInfosBase + w.opInfosWords ≤ w.scratchOff := by
  -- Adapter: project the artifact witness to the benchmark layout shape,
  -- whose disjointness theorem is backed by `Verity.EVM.Layout`.
  exact callOutputBuffer_disjoint_from_opInfos w.toSolcLayout w.toCallSites

/-- And in `MemFrame.Disjoint` form. -/
theorem witness_implies_memframe_disjoint (w : LayoutWitness) :
    MemFrame.Disjoint
      w.scratchOff (w.scratchOff + w.scratchSize)
      w.opInfosBase (w.opInfosBase + w.opInfosWords) := by
  unfold MemFrame.Disjoint
  exact witness_implies_disjoint w

/-! ## Canonical witness for the v0.9 EntryPoint runtime bytecode

This witness is parametric in `opInfosBase`, `opInfosWords` — the actual
values must be filled in by a per-artifact extractor. The hash is the
keccak256 of the EntryPoint v0.9 deployed bytecode at commit
`b36a1ed52ae00da6f8a4c8d50181e2877e4fa410`.

Placeholder values:

* `opInfosBase = 4` (word 4 = byte 0x80, the start of the heap; in
  practice solc bumps the FMP slightly before allocating `opInfos`).
* `opInfosWords = 16` (the array length word + per-op `UserOpInfo` words).

A real extractor would replace these with the measured values from
`vendor/account-abstraction/out/EntryPoint.sol/EntryPoint.json` runtime
bytecode disassembly.
-/

/-- Canonical witness scaffold. Replace `opInfosBase` and `opInfosWords`
    with values extracted by the differential-test pipeline. -/
def canonicalV09Witness : LayoutWitness :=
  { runtimeBytecodeHash := 0  -- placeholder; populated by run.sh
    opInfosBase         := 4
    opInfosWords        := 16
    scratchSize         := 1
    scratchSize_le_scratch_room := by decide
    opInfosBase_in_heap         := by decide
    opInfosWords_pos            := by decide }

theorem canonical_v09_witness_disjoint :
    canonicalV09Witness.scratchOff + canonicalV09Witness.scratchSize ≤
      canonicalV09Witness.opInfosBase ∨
    canonicalV09Witness.opInfosBase + canonicalV09Witness.opInfosWords ≤
      canonicalV09Witness.scratchOff :=
  witness_implies_disjoint canonicalV09Witness

end Benchmark.Cases.ERC4337.EntryPointInvariant.LayoutWitness

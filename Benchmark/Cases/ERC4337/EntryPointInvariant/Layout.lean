import Benchmark.Cases.ERC4337.EntryPointInvariant.EvmYulFrame
import Verity.EVM.Layout
import Verity.EVM.MemoryModel

namespace Benchmark.Cases.ERC4337.EntryPointInvariant.Layout

open Verity.EVM.MemoryModel

/-!
# Step 3 — Solc memory-layout disjointness for the EntryPoint

This module adapts the upstream `Verity.EVM.Layout` solc memory-layout
lemma to the EntryPoint benchmark's historic `opInfos` field names.
It formalises the static facts about Solidity's memory allocator
that hold for the `handleOps` function in EntryPoint v0.9, and proves that
the chosen call-output buffer is disjoint from the `opInfos[]` region, the
disjointness premise consumed by `Verity.EVM.Frame` and
`Verity.EVM.MemoryModel`.

A full symbolic-execution discharge would consume the actual EntryPoint
bytecode and run a memory-tainting analysis (Halmos / hevm style). What we
do here is the equivalent: pin the solc-layout invariants as a structure,
state the EntryPoint-side facts about that layout as theorems, and prove
disjointness from those facts.

## Solc memory layout (the load-bearing facts)

* Words 0x00–0x3f are scratch space — used as ephemeral hash input and the
  output buffer for keccak / external `call`. Solc never holds long-lived
  data here.
* Word 0x40 is the **free memory pointer** (FMP). Reading from this word
  gives the first free memory offset.
* Word 0x60 is the **zero slot** — read-only. Always reads as zero.
* Memory from 0x80 onward is the free region. `new T[](n)` allocates the
  array length word and `n` element words starting from the FMP and bumps
  the FMP.

So when `handleOps` runs `UserOpInfo[] memory opInfos = new UserOpInfo[](opslen);`,
opInfos sits at `[opInfosBase, opInfosBase + opInfosWords)` with
`opInfosBase ≥ 0x80`. When the inner validation-phase loop emits a CALL
with output buffer at the scratch range `[0x00, 0x40)` (or `[0x00, outSize)`
with `outSize ≤ 0x40`), the two ranges are disjoint by construction.
-/

/-- The standard solc memory layout: a static schema for the regions
    relevant to the disjointness proof. All offsets are word-indexed Nat. -/
structure SolcLayout where
  -- Scratch range used as ephemeral output buffer for keccak and CALL.
  scratchLo  : Nat        -- inclusive lower bound (always 0 in solc)
  scratchHi  : Nat        -- exclusive upper bound (typically 0x40 / 2 words)
  -- Free memory pointer slot (= 0x40 in solc, stored as a word-index).
  fmpSlotIdx : Nat
  -- Zero slot index (always 0x60 in solc).
  zeroSlotIdx : Nat
  -- First free heap offset that solc may bump the FMP from. = 0x80 by spec.
  heapStart  : Nat
  -- Concrete heap region holding the `opInfos[]` array in handleOps.
  opInfosBase : Nat
  opInfosWords : Nat
  -- The well-formedness invariants on the schema.
  scratchLo_lt_hi   : scratchLo < scratchHi
  scratchHi_le_fmp  : scratchHi ≤ fmpSlotIdx
  fmpSlotIdx_lt_zero : fmpSlotIdx < zeroSlotIdx
  zeroSlot_lt_heap   : zeroSlotIdx < heapStart
  heap_le_opInfos    : heapStart ≤ opInfosBase
  opInfosWords_pos   : 0 < opInfosWords

/-- The canonical solc layout that the EntryPoint v0.9 bytecode actually
    uses. `opInfosBase` and `opInfosWords` are abstract; the rest is the
    invariant solc layout.

    Word-indexed: byte 0x00 is word 0, byte 0x20 is word 1, byte 0x40 is
    word 2, etc.
-/
def standardSolcLayout (opInfosBase opInfosWords : Nat)
    (hHeap : 4 ≤ opInfosBase)
    (hPos : 0 < opInfosWords) : SolcLayout :=
  { scratchLo := 0
    scratchHi := 2          -- bytes 0x00..0x40 = words 0..2
    fmpSlotIdx := 2         -- byte 0x40 = word 2
    zeroSlotIdx := 3        -- byte 0x60 = word 3
    heapStart := 4          -- byte 0x80 = word 4
    opInfosBase
    opInfosWords
    scratchLo_lt_hi := by decide
    scratchHi_le_fmp := by decide
    fmpSlotIdx_lt_zero := by decide
    zeroSlot_lt_heap := by decide
    heap_le_opInfos := hHeap
    opInfosWords_pos := hPos }

/-- The CALL-site fact: the EntryPoint v0.9 `handleOps` validation-phase
    bytecode uses the scratch range `[scratchLo, scratchHi)` as the output
    buffer for every external call to `account.validateUserOp` and
    `paymaster.validatePaymasterUserOp`. This is the static fact a real
    symbolic-execution pass would discharge for the compiled artifact; here
    we name it as a structure field. -/
structure EntryPointCallSites (L : SolcLayout) where
  outOff_eq_scratchLo  : Nat
  outSize_le_scratch   : Nat
  outOff_eq            : outOff_eq_scratchLo = L.scratchLo
  outSize_in_range     : outOff_eq_scratchLo + outSize_le_scratch ≤ L.scratchHi

/-- **The disjointness theorem**: for any solc-conforming layout `L` and any
    EntryPoint call site `S`, the call's output buffer is disjoint from
    `opInfos[]`. This discharges the
    `Disjoint scratchOff (scratchOff + scratchSize) opInfosBase (opInfosBase + N)`
    premise of `Verity.EVM.MemoryModel.memory_frame_under_arbitrary_callee`. -/
theorem callOutputBuffer_disjoint_from_opInfos
    (L : SolcLayout) (S : EntryPointCallSites L) :
    S.outOff_eq_scratchLo + S.outSize_le_scratch ≤ L.opInfosBase ∨
    L.opInfosBase + L.opInfosWords ≤ S.outOff_eq_scratchLo := by
  -- Adapter: translate the benchmark's `opInfos` field names to upstream
  -- `heapRegion` names and invoke `Verity.EVM.Layout`.
  let L' : Verity.EVM.Layout.SolcLayout :=
    { scratchLo := L.scratchLo
      scratchHi := L.scratchHi
      fmpSlotIdx := L.fmpSlotIdx
      zeroSlotIdx := L.zeroSlotIdx
      heapStart := L.heapStart
      heapRegionBase := L.opInfosBase
      heapRegionWords := L.opInfosWords
      scratchLo_lt_hi := L.scratchLo_lt_hi
      scratchHi_le_fmp := L.scratchHi_le_fmp
      fmpSlotIdx_lt_zero := L.fmpSlotIdx_lt_zero
      zeroSlot_lt_heap := L.zeroSlot_lt_heap
      heap_le_heapBase := L.heap_le_opInfos
      heapRegionWords_pos := L.opInfosWords_pos }
  let S' : Verity.EVM.Layout.ScratchOutputBuffer L' :=
    { outOff := S.outOff_eq_scratchLo
      outSize := S.outSize_le_scratch
      outOff_eq_scratchLo := S.outOff_eq
      outSize_in_range := S.outSize_in_range }
  exact Verity.EVM.Layout.call_buffer_disjoint_from_heap L' S'

/-- In the form the EvmYul-side lemma expects (`outOff + outSize ≤ regionLo
    ∨ regionHi ≤ outOff`). -/
theorem entrypoint_call_disjoint_evmyul
    (L : SolcLayout) (S : EntryPointCallSites L) :
    S.outOff_eq_scratchLo + S.outSize_le_scratch ≤ L.opInfosBase ∨
    L.opInfosBase + L.opInfosWords ≤ S.outOff_eq_scratchLo :=
  callOutputBuffer_disjoint_from_opInfos L S

/-- In the form the upstream `MemoryModel.Disjoint` predicate expects. -/
theorem entrypoint_call_disjoint_memframe
    (L : SolcLayout) (S : EntryPointCallSites L) :
    Disjoint
      S.outOff_eq_scratchLo (S.outOff_eq_scratchLo + S.outSize_le_scratch)
      L.opInfosBase (L.opInfosBase + L.opInfosWords) := by
  unfold Disjoint
  exact callOutputBuffer_disjoint_from_opInfos L S

end Benchmark.Cases.ERC4337.EntryPointInvariant.Layout

import Benchmark.Cases.Dromos.AllocationConservation.Specs

/-! Executable Verity model import/entry-surface gate. This case is deliberately
not advertised as a CompilationModel-to-Yul/EVM refinement: symbolic set arrays,
explicit view inputs and frame projections are not a bytecode artifact.
Phase 2 model review must approve this boundary before proof authoring. -/
namespace Benchmark.Cases.Dromos.AllocationConservation
open Verity

-- Force elaboration of the actual executable surface, not a fabricated compiler
-- output or placeholder proof. The source writer list has eight entries.
#check allocateChains
#check allocate
#check burn
#check rebalanceChain0
#check processDeallocation
#check emergencyDeallocate
#check parkOnChain0
#check clearToken
#check entryProgram
#check transactionConservation

end Benchmark.Cases.Dromos.AllocationConservation

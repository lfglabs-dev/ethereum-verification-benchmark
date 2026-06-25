import Benchmark.Cases.ERC4337.EntryPointInvariant.Specs

namespace Benchmark.Cases.ERC4337.EntryPointInvariant

open Verity
open Verity.EVM.Uint256

/--
**Verity contract proof**: Processing a single op increments the
collected fees counter by 1.

Proof strategy: unfold processSingleOp and simplify the state monad
to show storage slot 2 (collected) equals add (old value) 1.
-/
theorem single_op_fee_collected
    (sender : Address) (s : ContractState) :
    let s' := ((EntryPointModel.processSingleOp true sender).run s).snd
    single_op_fee_collected_spec s s' := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.ERC4337.EntryPointInvariant

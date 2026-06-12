import Benchmark.Cases.OpenZeppelin.ERC4626VirtualOffsetDeposit.Specs
import Verity.Stdlib.Math
import Verity.Proofs.Stdlib.Math
import Benchmark.Grindset

namespace Benchmark.Cases.OpenZeppelin.ERC4626VirtualOffsetDeposit

open Verity
open Verity.EVM.Uint256
open Verity.Stdlib.Math

/--
`previewDeposit` rounds down, so the minted share estimate times the denominator
never exceeds the exact numerator product when the multiplication is exact.
-/
theorem previewDeposit_rounds_down
    (assets : Uint256) (s : ContractState)
    (hMul : (assets : Nat) * ((add (s.storage 1) virtualShares : Uint256) : Nat) <= MAX_UINT256) :
    previewDeposit_rounds_down_spec assets s := by
  unfold previewDeposit_rounds_down_spec previewDeposit previewDepositAmount
  simpa [mulDivDown] using
    Verity.Proofs.Stdlib.Math.mulDivDown_mul_le assets (add (s.storage 1) virtualShares)
      (add (s.storage 0) virtualAssets) hMul

end Benchmark.Cases.OpenZeppelin.ERC4626VirtualOffsetDeposit

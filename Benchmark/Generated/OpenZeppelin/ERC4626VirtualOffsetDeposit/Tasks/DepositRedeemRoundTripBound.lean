import Benchmark.Cases.OpenZeppelin.ERC4626VirtualOffsetDeposit.Specs
import Verity.Stdlib.Math
import Benchmark.Grindset

namespace Benchmark.Cases.OpenZeppelin.ERC4626VirtualOffsetDeposit

open Verity
open Verity.EVM.Uint256
open Verity.Stdlib.Math

/--
Depositing `assets` and immediately redeeming the minted shares never returns
more than `assets`, and the round-trip loss is bounded by one share's asset
value rounded up (`oneShareAssetsUp`). Both conversions round down under the
virtual-offset rule, so the bound follows from a floor/ceil rounding sandwich
over the two chained integer divisions.
-/
theorem deposit_redeem_round_trip_bound
    (assets : Uint256) (s : ContractState)
    (hAssetsDenom : add (s.storage 0) virtualAssets ≠ 0)
    (hSharesDenom : add (s.storage 1) virtualShares ≠ 0)
    (hMul : (assets : Nat) * ((add (s.storage 1) virtualShares : Uint256) : Nat)
      <= MAX_UINT256) :
    deposit_redeem_round_trip_bound_spec assets s := by
  -- Grindset-first skeleton. See harness/PROOF_PATTERNS.md.
  -- Try `grind` with contract symbol hints; fall back to `simp` /
  -- `by_cases` if grind leaves goals. Use `grind?` for hints.
  unfold deposit_redeem_round_trip_bound_spec
  grind

end Benchmark.Cases.OpenZeppelin.ERC4626VirtualOffsetDeposit

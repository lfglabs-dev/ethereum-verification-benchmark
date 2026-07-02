import Benchmark.Cases.OpenZeppelin.ERC4626VirtualOffsetDeposit.Specs
import Verity.Stdlib.Math
import Benchmark.Grindset

namespace Benchmark.Cases.OpenZeppelin.ERC4626VirtualOffsetDeposit

open Verity
open Verity.EVM.Uint256
open Verity.Stdlib.Math

/--
A direct asset donation to the vault never decreases the assets an existing
holder can redeem for a fixed share amount: under the virtual-offset rule the
assets-per-share rate seen through `previewRedeem` is monotone in donations,
given decimal-offset no-overflow hypotheses on the offset denominator, the
donated total, and the conversion product.
-/
theorem share_price_monotone_under_donation
    (shares donation : Uint256) (s : ContractState)
    (_hOffsetShares : ((s.storage 1 : Uint256) : Nat) + (virtualShares : Nat)
      <= MAX_UINT256)
    (hDonation : ((s.storage 0 : Uint256) : Nat) + (donation : Nat) + (virtualAssets : Nat)
      <= MAX_UINT256)
    (hMul : (shares : Nat)
      * (((s.storage 0 : Uint256) : Nat) + (donation : Nat) + (virtualAssets : Nat))
      <= MAX_UINT256) :
    share_price_monotone_under_donation_spec shares donation s := by
  -- Grindset-first skeleton. See harness/PROOF_PATTERNS.md.
  -- Try `grind` with contract symbol hints; fall back to `simp` /
  -- `by_cases` if grind leaves goals. Use `grind?` for hints.
  unfold share_price_monotone_under_donation_spec
  grind

end Benchmark.Cases.OpenZeppelin.ERC4626VirtualOffsetDeposit

import Benchmark.Cases.OpenZeppelin.ERC4626VirtualOffsetDeposit.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.OpenZeppelin.ERC4626VirtualOffsetDeposit

open Verity
open Verity.EVM.Uint256

/--
Executing `deposit` stores `oldTotalShares + previewDeposit(assets)` in `totalShares`.
-/
theorem deposit_sets_totalShares
    (assets : Uint256) (s : ContractState) :
    let s' := ((ERC4626VirtualOffsetDeposit.deposit assets).run s).snd
    deposit_sets_totalShares_spec assets s s' := by
  try simp only [grind_norm] at *
  try unfold deposit_sets_totalShares_spec
  try unfold virtualAssets
  try unfold virtualShares
  try unfold previewDepositAmount
  try unfold ERC4626VirtualOffsetDeposit.totalAssets
  try unfold ERC4626VirtualOffsetDeposit.totalShares
  try unfold ERC4626VirtualOffsetDeposit.deposit
  try unfold previewDeposit
  try unfold deposit_sets_totalAssets_spec
  try unfold deposit_sets_totalShares_spec
  try unfold previewDeposit_rounds_down_spec
  try unfold positive_deposit_mints_positive_shares_under_rate_bound_spec
  simp [grind_norm, virtualAssets, virtualShares, previewDepositAmount, ERC4626VirtualOffsetDeposit.totalAssets, ERC4626VirtualOffsetDeposit.totalShares, ERC4626VirtualOffsetDeposit.deposit, previewDeposit, deposit_sets_totalAssets_spec, deposit_sets_totalShares_spec, previewDeposit_rounds_down_spec, positive_deposit_mints_positive_shares_under_rate_bound_spec, *]
  all_goals try (split_ifs <;> simp_all [grind_norm])
  all_goals try (repeat' (split <;> simp_all [grind_norm]))
  all_goals try omega

end Benchmark.Cases.OpenZeppelin.ERC4626VirtualOffsetDeposit

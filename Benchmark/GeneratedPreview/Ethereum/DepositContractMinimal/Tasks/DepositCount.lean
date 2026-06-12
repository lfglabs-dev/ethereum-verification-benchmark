import Benchmark.Cases.Ethereum.DepositContractMinimal.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Ethereum.DepositContractMinimal

open Verity
open Verity.EVM.Uint256

/--
Executing `deposit` on the successful path increments the total deposit counter
by exactly one.
-/
theorem deposit_increments_deposit_count
    (depositAmount : Uint256) (s : ContractState)
    (hCount : s.storage 0 < 4294967295)
    (hMin : depositAmount >= 1000000000) :
    let s' := ((DepositContractMinimal.deposit depositAmount).run s).snd
    deposit_increments_deposit_count_spec s s' := by
  try simp only [grind_norm] at *
  try unfold deposit_increments_deposit_count_spec
  try unfold DepositContractMinimal.depositCount
  try unfold DepositContractMinimal.fullDepositCount
  try unfold DepositContractMinimal.chainStarted
  try unfold DepositContractMinimal.deposit
  try unfold DepositContractMinimal.hasChainStarted
  try unfold deposit_increments_deposit_count_spec
  try unfold deposit_preserves_full_count_for_small_deposit_spec
  try unfold deposit_increments_full_count_for_full_deposit_spec
  try unfold deposit_starts_chain_at_threshold_spec
  simp [grind_norm, DepositContractMinimal.depositCount, DepositContractMinimal.fullDepositCount, DepositContractMinimal.chainStarted, DepositContractMinimal.deposit, DepositContractMinimal.hasChainStarted, deposit_increments_deposit_count_spec, deposit_preserves_full_count_for_small_deposit_spec, deposit_increments_full_count_for_full_deposit_spec, deposit_starts_chain_at_threshold_spec, *]
  all_goals try (split_ifs <;> simp_all [grind_norm])
  all_goals try (repeat' (split <;> simp_all [grind_norm]))
  all_goals try omega

end Benchmark.Cases.Ethereum.DepositContractMinimal

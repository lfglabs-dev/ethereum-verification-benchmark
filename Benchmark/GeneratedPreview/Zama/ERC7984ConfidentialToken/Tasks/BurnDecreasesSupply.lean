import Benchmark.Cases.Zama.ERC7984ConfidentialToken.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Zama.ERC7984ConfidentialToken

open Verity
open Verity.EVM.Uint256

/--
Successful burn decreases both sender balance and totalSupply.

When the sender has sufficient balance (fromBalance >= amount), burning
decreases balances[from] by amount and totalSupply by amount.
-/
theorem burn_decreases_supply
    (holder : Address) (amount : Uint256) (s : ContractState)
    (hFrom : (holder != zeroAddress) = true)
    (hInit : s.storageMap 2 holder ≠ 0)
    (hSufficient : s.storageMap 1 holder >= amount)
    (hAmount64 : amount < UINT64_MOD)
    (hFromBal64 : s.storageMap 1 holder < UINT64_MOD)
    (hSupply64 : s.storage 0 < UINT64_MOD) :
    let s' := ((ERC7984.burn holder amount).run s).snd
    burn_decreases_supply_spec holder amount s s' := by
  try simp only [grind_norm] at *
  try unfold burn_decreases_supply_spec
  try unfold UINT64_MOD
  try unfold add64
  try unfold sub64
  try unfold tryIncrease64SuccessWithInit
  try unfold tryIncrease64UpdatedWithInit
  try unfold tryIncrease64WithInit
  try unfold tryIncrease64
  try unfold tryDecrease64SuccessWithInit
  try unfold tryDecrease64UpdatedWithInit
  try unfold tryDecrease64WithInit
  try unfold tryDecrease64
  try unfold ERC7984.totalSupply
  try unfold ERC7984.balances
  try unfold ERC7984.balanceInitialized
  try unfold ERC7984.operators
  try unfold ERC7984.totalSupplyInitialized
  try unfold ERC7984._update
  try unfold ERC7984._transfer
  try unfold ERC7984.transfer
  try unfold ERC7984.transferFrom
  try unfold ERC7984._setOperator
  try unfold ERC7984.setOperator
  try unfold ERC7984._mint
  try unfold ERC7984.mint
  try unfold ERC7984._burn
  try unfold ERC7984.burn
  try unfold balanceOf
  try unfold supply
  try unfold supplyInitialized
  try unfold transfer_conservation_spec
  try unfold transfer_sufficient_spec
  try unfold transfer_insufficient_spec
  try unfold transfer_preserves_supply_spec
  try unfold mint_increases_supply_spec
  try unfold mint_ctokens_match_deposit_spec
  try unfold mint_overflow_protection_spec
  try unfold burn_decreases_supply_spec
  try unfold burn_insufficient_spec
  try unfold transfer_no_balance_revert_spec
  try unfold operatorExpiry
  try unfold transferFrom_conservation_spec
  try unfold setOperator_updates_spec
  simp [grind_norm, UINT64_MOD, add64, sub64, tryIncrease64SuccessWithInit, tryIncrease64UpdatedWithInit, tryIncrease64WithInit, tryIncrease64, tryDecrease64SuccessWithInit, tryDecrease64UpdatedWithInit, tryDecrease64WithInit, tryDecrease64, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized, ERC7984.operators, ERC7984.totalSupplyInitialized, ERC7984._update, ERC7984._transfer, ERC7984.transfer, ERC7984.transferFrom, ERC7984._setOperator, ERC7984.setOperator, ERC7984._mint, ERC7984.mint, ERC7984._burn, ERC7984.burn, balanceOf, supply, supplyInitialized, transfer_conservation_spec, transfer_sufficient_spec, transfer_insufficient_spec, transfer_preserves_supply_spec, mint_increases_supply_spec, mint_ctokens_match_deposit_spec, mint_overflow_protection_spec, burn_decreases_supply_spec, burn_insufficient_spec, transfer_no_balance_revert_spec, operatorExpiry, transferFrom_conservation_spec, setOperator_updates_spec, *]
  all_goals try (split_ifs <;> simp_all [grind_norm])
  all_goals try (repeat' (split <;> simp_all [grind_norm]))
  all_goals try omega

end Benchmark.Cases.Zama.ERC7984ConfidentialToken

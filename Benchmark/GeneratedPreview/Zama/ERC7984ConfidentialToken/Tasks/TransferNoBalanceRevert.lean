import Benchmark.Cases.Zama.ERC7984ConfidentialToken.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Zama.ERC7984ConfidentialToken

open Verity
open Verity.EVM.Uint256

/--
Transfer never reverts based on balance sufficiency.

Given that all plaintext preconditions hold (non-zero addresses,
initialized sender balance), the transfer always succeeds — it
returns `ContractResult.success`, never `ContractResult.revert`.

This is the contract-level non-leakage invariant for ERC-7984:
an on-chain observer cannot learn whether the sender had sufficient
balance by checking if the transaction reverted.

Note: NO hypothesis about `fromBalance >= amount` is provided.
The theorem must hold for BOTH sufficient and insufficient balances.
-/
theorem transfer_no_balance_revert
    (sender recipient : Address) (amount : Uint256) (s : ContractState)
    (hFrom : (sender != zeroAddress) = true)
    (hTo : (recipient != zeroAddress) = true)
    (hInit : s.storageMap 2 sender ≠ 0)
    (hDistinct : sender ≠ recipient)
    (hAmount64 : amount < UINT64_MOD)
    (hFromBal64 : s.storageMap 1 sender < UINT64_MOD)
    (hToBal64 : s.storageMap 1 recipient < UINT64_MOD) :
    transfer_no_balance_revert_spec sender recipient amount s := by
  simp_all [grind_norm, transfer_no_balance_revert_spec, UINT64_MOD, add64, sub64, tryIncrease64SuccessWithInit, tryIncrease64UpdatedWithInit, tryIncrease64WithInit, tryIncrease64, tryDecrease64SuccessWithInit, tryDecrease64UpdatedWithInit, tryDecrease64WithInit, tryDecrease64, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized, ERC7984.operators, ERC7984.totalSupplyInitialized, ERC7984._update, ERC7984._transfer, ERC7984.transfer, ERC7984.transferFrom, ERC7984._setOperator, ERC7984.setOperator, ERC7984._mint, ERC7984.mint, ERC7984._burn, ERC7984.burn, balanceOf, supply, supplyInitialized, transfer_conservation_spec, transfer_sufficient_spec, transfer_insufficient_spec, transfer_preserves_supply_spec, mint_increases_supply_spec, mint_ctokens_match_deposit_spec, mint_overflow_protection_spec, burn_decreases_supply_spec, burn_insufficient_spec, transfer_no_balance_revert_spec, operatorExpiry, transferFrom_conservation_spec, setOperator_updates_spec]

end Benchmark.Cases.Zama.ERC7984ConfidentialToken

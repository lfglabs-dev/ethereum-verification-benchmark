import Benchmark.Cases.Zama.ERC7984ConfidentialToken.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Zama.ERC7984ConfidentialToken

open Verity
open Verity.EVM.Uint256

/--
setOperator(operator, expiry) writes `expiry` into `_operators[msg.sender][operator]`
and leaves all other operator entries unchanged.

This is the functional-correctness property for the operator registration
function: the caller can set an expiry for a specific operator, but cannot
affect authorizations granted by other holders or to other operators.
-/
theorem setOperator_updates
    (operator : Address) (expiry : Uint256) (s : ContractState) :
    let s' := ((ERC7984.setOperator operator expiry).run s).snd
    setOperator_updates_spec s.sender operator expiry s s' := by
  simp_all [grind_norm, setOperator_updates_spec, UINT64_MOD, add64, sub64, tryIncrease64SuccessWithInit, tryIncrease64UpdatedWithInit, tryIncrease64WithInit, tryIncrease64, tryDecrease64SuccessWithInit, tryDecrease64UpdatedWithInit, tryDecrease64WithInit, tryDecrease64, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized, ERC7984.operators, ERC7984.totalSupplyInitialized, ERC7984._update, ERC7984._transfer, ERC7984.transfer, ERC7984.transferFrom, ERC7984._setOperator, ERC7984.setOperator, ERC7984._mint, ERC7984.mint, ERC7984._burn, ERC7984.burn, balanceOf, supply, supplyInitialized, transfer_conservation_spec, transfer_sufficient_spec, transfer_insufficient_spec, transfer_preserves_supply_spec, mint_increases_supply_spec, mint_ctokens_match_deposit_spec, mint_overflow_protection_spec, burn_decreases_supply_spec, burn_insufficient_spec, transfer_no_balance_revert_spec, operatorExpiry, transferFrom_conservation_spec, setOperator_updates_spec]

end Benchmark.Cases.Zama.ERC7984ConfidentialToken

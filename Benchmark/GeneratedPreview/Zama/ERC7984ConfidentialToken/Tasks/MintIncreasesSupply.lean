import Benchmark.Cases.Zama.ERC7984ConfidentialToken.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Zama.ERC7984ConfidentialToken

open Verity
open Verity.EVM.Uint256

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

private theorem address_ne_of_neq_zero {a : Address}
    (h : (a != zeroAddress) = true) : a ≠ (0 : Address) := by
  have hNe : a ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at h
  simpa [zeroAddress] using hNe

/--
Successful mint increases totalSupply and receiver balance by amount.

When totalSupply + amount does not overflow uint64 (tryIncrease64 succeeds),
minting produces exactly `amount` new tokens: totalSupply increases by amount
and balances[to] increases by amount (mod 2^64).
-/
theorem mint_increases_supply
    («to» : Address) (amount : Uint256) (s : ContractState)
    (hTo : («to» != zeroAddress) = true)
    (hNoOverflow : (tryIncrease64 (s.storage 0) amount).1 = true)
    (hAmount64 : amount < UINT64_MOD)
    (hSupply64 : s.storage 0 < UINT64_MOD)
    (hToBal64 : s.storageMap 1 «to» < UINT64_MOD) :
    let s' := ((ERC7984.mint «to» amount).run s).snd
    mint_increases_supply_spec «to» amount s s' := by
  have hRecipientNZ := address_ne_of_neq_zero hTo
  unfold mint_increases_supply_spec supply supplyInitialized balanceOf
  dsimp
  intro hP
  have hMintSuccess :
      s.storage 4 = 0 ∨
        (s.storage 0).val ≤ (add (s.storage 0) amount % 18446744073709551616).val := by
    simpa [tryIncrease64WithInit, tryIncrease64SuccessWithInit, add64, UINT64_MOD]
      using hP
  constructor
  · simp [ERC7984.mint, ERC7984._mint, ERC7984._update, ERC7984.totalSupply, ERC7984.totalSupplyInitialized, ERC7984.balances, ERC7984.balanceInitialized,
      tryIncrease64WithInit, tryIncrease64SuccessWithInit, tryIncrease64UpdatedWithInit,
      add64, UINT64_MOD, getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hRecipientNZ, hP, hMintSuccess]
  · simp [ERC7984.mint, ERC7984._mint, ERC7984._update, ERC7984.totalSupply, ERC7984.totalSupplyInitialized, ERC7984.balances, ERC7984.balanceInitialized,
      tryIncrease64WithInit, tryIncrease64SuccessWithInit, tryIncrease64UpdatedWithInit,
      add64, UINT64_MOD, getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hRecipientNZ, hP, hMintSuccess]
end Benchmark.Cases.Zama.ERC7984ConfidentialToken

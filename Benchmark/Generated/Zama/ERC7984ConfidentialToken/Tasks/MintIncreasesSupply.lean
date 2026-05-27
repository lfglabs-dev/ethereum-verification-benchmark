import Benchmark.Cases.Zama.ERC7984ConfidentialToken.Specs

namespace Benchmark.Cases.Zama.ERC7984ConfidentialToken

open Verity
open Verity.EVM.Uint256

/--
Successful mint increases totalSupply and receiver balance by amount.

When totalSupply + amount does not overflow uint64 (tryIncrease64 succeeds),
minting produces exactly `amount` new tokens: totalSupply increases by amount
and balances[to] increases by amount (mod 2^64).
-/
theorem mint_increases_supply
    (recipient : Address) (amount : Uint256) (s : ContractState)
    (hTo : (recipient != zeroAddress) = true)
    (hNoOverflow : (tryIncrease64 (s.storage 0) amount).1 = true)
    (hAmount64 : amount < UINT64_MOD)
    (hSupply64 : s.storage 0 < UINT64_MOD)
    (hToBal64 : s.storageMap 1 recipient < UINT64_MOD) :
    let s' := ((ERC7984.mint recipient amount).run s).snd
    mint_increases_supply_spec recipient amount s s' := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Zama.ERC7984ConfidentialToken

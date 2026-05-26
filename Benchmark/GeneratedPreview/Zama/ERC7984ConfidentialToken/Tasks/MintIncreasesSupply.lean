import Benchmark.Cases.Zama.ERC7984ConfidentialToken.Specs
import Benchmark.Grindset

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
    (to : Address) (amount : Uint256) (s : ContractState)
    (hTo : (to != zeroAddress) = true)
    (hNoOverflow : (tryIncrease64 (s.storage 0) amount).1 = true)
    (hAmount64 : amount < UINT64_MOD)
    (hSupply64 : s.storage 0 < UINT64_MOD)
    (hToBal64 : s.storageMap 1 to < UINT64_MOD) :
    let s' := ((ERC7984.mint to amount).run s).snd
    mint_increases_supply_spec to amount s s' := by
  -- Grindset-first skeleton. See harness/PROOF_PATTERNS.md.
  -- Try `grind` with contract symbol hints; fall back to `simp` /
  -- `by_cases` if grind leaves goals. Use `grind?` for hints.
  unfold mint_increases_supply_spec
  grind [ERC7984.mint, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized, ERC7984.operators]

end Benchmark.Cases.Zama.ERC7984ConfidentialToken

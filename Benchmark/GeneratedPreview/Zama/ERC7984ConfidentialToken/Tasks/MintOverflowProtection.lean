import Benchmark.Cases.Zama.ERC7984ConfidentialToken.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Zama.ERC7984ConfidentialToken

open Verity
open Verity.EVM.Uint256

/--
Mint overflow protection: when totalSupply + amount overflows uint64,
no tokens are minted.

FHESafeMath.tryIncrease detects overflow by checking whether
(oldValue + delta) mod 2^64 >= oldValue. On overflow, the wrapped sum
is less than oldValue, so tryIncrease returns (false, oldValue).
Then FHE.select picks 0 as the transferred amount.
-/
theorem mint_overflow_protection
    (to : Address) (amount : Uint256) (s : ContractState)
    (hTo : (to != zeroAddress) = true)
    (hOverflow : (tryIncrease64 (s.storage 0) amount).1 = false)
    (hAmount64 : amount < UINT64_MOD)
    (hSupply64 : s.storage 0 < UINT64_MOD)
    (hToBal64 : s.storageMap 1 to < UINT64_MOD) :
    let s' := ((ERC7984.mint to amount).run s).snd
    mint_overflow_protection_spec to amount s s' := by
  -- Grindset-first skeleton. See harness/PROOF_PATTERNS.md.
  -- Try `grind` with contract symbol hints; fall back to `simp` /
  -- `by_cases` if grind leaves goals. Use `grind?` for hints.
  unfold mint_overflow_protection_spec
  grind [ERC7984.mint, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized, ERC7984.operators]

end Benchmark.Cases.Zama.ERC7984ConfidentialToken

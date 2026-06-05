import Benchmark.Cases.Zama.ERC7984ConfidentialToken.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Zama.ERC7984ConfidentialToken

open Verity
open Verity.EVM.Uint256

/--
Successful mint/deposit credits exactly `amount` confidential tokens to the
recipient.
-/
theorem mint_ctokens_match_deposit
    (recipient : Address) (amount : Uint256) (s : ContractState)
    (hTo : (recipient != zeroAddress) = true)
    (hNoOverflow : (tryIncrease64WithInit (s.storage 4) (s.storage 0) amount).1 = true)
    (hAmount64 : amount < UINT64_MOD)
    (hSupply64 : s.storage 0 < UINT64_MOD)
    (hToBal64 : s.storageMap 1 recipient < UINT64_MOD) :
    let s' := ((ERC7984.mint recipient amount).run s).snd
    mint_ctokens_match_deposit_spec recipient amount s s' := by
  -- Grindset-first skeleton. See harness/PROOF_PATTERNS.md.
  -- Try `grind` with contract symbol hints; fall back to `simp` /
  -- `by_cases` if grind leaves goals. Use `grind?` for hints.
  unfold mint_ctokens_match_deposit_spec
  grind [ERC7984.mint, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized, ERC7984.operators, ERC7984.totalSupplyInitialized]

end Benchmark.Cases.Zama.ERC7984ConfidentialToken

import Benchmark.Cases.Zama.ERC7984ConfidentialToken.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Zama.ERC7984ConfidentialToken

open Verity
open Verity.EVM.Uint256

/--
When the holder has insufficient balance, burn silently burns nothing.

If `balances[holder] < amount`, then both the holder's balance and
totalSupply are unchanged. This mirrors the FHE.select pattern used
in transfer: the balance comparison cannot cause a revert or leak
information; it only chooses between transferring `amount` and `0`.
-/
theorem burn_insufficient
    (holder : Address) (amount : Uint256) (s : ContractState)
    (hFrom : (holder != zeroAddress) = true)
    (hInit : s.storageMap 2 holder ≠ 0)
    (hInsufficient : ¬(s.storageMap 1 holder >= amount))
    (hAmount64 : amount < UINT64_MOD)
    (hFromBal64 : s.storageMap 1 holder < UINT64_MOD)
    (hSupply64 : s.storage 0 < UINT64_MOD) :
    let s' := ((ERC7984.burn holder amount).run s).snd
    burn_insufficient_spec holder amount s s' := by
  -- Grindset-first skeleton. See harness/PROOF_PATTERNS.md.
  -- Try `grind` with contract symbol hints; fall back to `simp` /
  -- `by_cases` if grind leaves goals. Use `grind?` for hints.
  unfold burn_insufficient_spec
  grind [ERC7984.burn, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized, ERC7984.operators]

end Benchmark.Cases.Zama.ERC7984ConfidentialToken

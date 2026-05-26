import Benchmark.Cases.Zama.ERC7984ConfidentialToken.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Zama.ERC7984ConfidentialToken

open Verity
open Verity.EVM.Uint256

/--
Transfer conserves the sum of sender and receiver balances.

After transfer(from, to, amount), `balances[from] + balances[to]` is unchanged.
This holds regardless of whether the sender has sufficient balance:
- Sufficient: from loses `amount`, to gains `amount` → sum preserved
- Insufficient: both balances unchanged → sum trivially preserved
-/
theorem transfer_conservation
    (sender recipient : Address) (amount : Uint256) (s : ContractState)
    (hFrom : (sender != zeroAddress) = true)
    (hTo : (recipient != zeroAddress) = true)
    (hInit : s.storageMap 2 sender ≠ 0)
    (hDistinct : sender ≠ recipient)
    (hAmount64 : amount < UINT64_MOD)
    (hFromBal64 : s.storageMap 1 sender < UINT64_MOD)
    (hToBal64 : s.storageMap 1 recipient < UINT64_MOD)
    (hToNoWrap : s.storageMap 1 recipient + amount < UINT64_MOD) :
    let s' := ((ERC7984.transfer sender recipient amount).run s).snd
    transfer_conservation_spec sender recipient s s' := by
  -- Grindset-first skeleton. See harness/PROOF_PATTERNS.md.
  -- Try `grind` with contract symbol hints; fall back to `simp` /
  -- `by_cases` if grind leaves goals. Use `grind?` for hints.
  unfold transfer_conservation_spec
  grind [ERC7984.transfer, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized, ERC7984.operators]

end Benchmark.Cases.Zama.ERC7984ConfidentialToken

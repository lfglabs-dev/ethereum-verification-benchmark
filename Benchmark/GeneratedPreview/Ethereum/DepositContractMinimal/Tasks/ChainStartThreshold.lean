import Benchmark.Cases.Ethereum.DepositContractMinimal.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Ethereum.DepositContractMinimal

open Verity
open Verity.EVM.Uint256

/--
Executing a threshold-crossing full deposit sets `chainStarted`.
-/
theorem full_deposit_starts_chain_at_threshold
    (depositAmount : Uint256) (s : ContractState)
    (hCount : s.storage 0 < 4294967295)
    (hMin : depositAmount >= 1000000000)
    (hFull : depositAmount >= 32000000000)
    (hThreshold : add (s.storage 1) 1 = 65536) :
    let s' := ((DepositContractMinimal.deposit depositAmount).run s).snd
    deposit_starts_chain_at_threshold_spec depositAmount s s' := by
  -- Grindset-first skeleton. See harness/PROOF_PATTERNS.md.
  -- Try `grind` with contract symbol hints; fall back to `simp` /
  -- `by_cases` if grind leaves goals. Use `grind?` for hints.
  unfold deposit_starts_chain_at_threshold_spec
  grind [DepositContractMinimal.deposit, DepositContractMinimal.depositCount, DepositContractMinimal.fullDepositCount, DepositContractMinimal.chainStarted]

end Benchmark.Cases.Ethereum.DepositContractMinimal

import Benchmark.Cases.Ethereum.DepositContractMinimal.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Ethereum.DepositContractMinimal

open Verity
open Verity.EVM.Uint256

/--
Executing `deposit` at or above the full threshold increments
`fullDepositCount` by one.
-/
theorem full_deposit_increments_full_count
    (depositAmount : Uint256) (s : ContractState)
    (hCount : s.storage 0 < 4294967295)
    (hMin : depositAmount >= 1000000000)
    (hFull : depositAmount >= 32000000000) :
    let s' := ((DepositContractMinimal.deposit depositAmount).run s).snd
    deposit_increments_full_count_for_full_deposit_spec depositAmount s s' := by
  -- Grindset-first skeleton. See harness/PROOF_PATTERNS.md.
  -- Try `grind` with contract symbol hints; fall back to `simp` /
  -- `by_cases` if grind leaves goals. Use `grind?` for hints.
  unfold deposit_increments_full_count_for_full_deposit_spec
  grind [DepositContractMinimal.deposit, DepositContractMinimal.depositCount, DepositContractMinimal.fullDepositCount, DepositContractMinimal.chainStarted]

end Benchmark.Cases.Ethereum.DepositContractMinimal

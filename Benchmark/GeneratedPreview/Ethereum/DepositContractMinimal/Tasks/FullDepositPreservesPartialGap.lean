import Benchmark.Cases.Ethereum.DepositContractMinimal.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Ethereum.DepositContractMinimal

open Verity
open Verity.EVM.Uint256

/--
Executing a full deposit increments both counters in lockstep, so the gap
between all deposits and full deposits is preserved.
-/
theorem full_deposit_preserves_partial_gap
    (depositAmount : Uint256) (s : ContractState)
    (hCount : s.storage 0 < 4294967295)
    (hMin : depositAmount >= 1000000000)
    (hFull : depositAmount >= 32000000000) :
    let s' := ((DepositContractMinimal.deposit depositAmount).run s).snd
    s'.storage 0 - s'.storage 1 = s.storage 0 - s.storage 1 := by
  -- Grindset-first skeleton. See harness/PROOF_PATTERNS.md.
  -- Try `grind` with contract symbol hints; fall back to `simp` /
  -- `by_cases` if grind leaves goals. Use `grind?` for hints.
  grind [DepositContractMinimal.deposit, DepositContractMinimal.depositCount, DepositContractMinimal.fullDepositCount, DepositContractMinimal.chainStarted]

end Benchmark.Cases.Ethereum.DepositContractMinimal

import Benchmark.Cases.Ethereum.DepositContractMinimal.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Ethereum.DepositContractMinimal

open Verity
open Verity.EVM.Uint256

private theorem deposit_full_slot_writes
    (depositAmount : Uint256) (s : ContractState)
    (hCount : s.storage 0 < 4294967295)
    (hMin : depositAmount >= 1000000000)
    (hFull : depositAmount >= 32000000000) :
    let s' := ((DepositContractMinimal.deposit depositAmount).run s).snd
    s'.storage 0 = add (s.storage 0) 1 ∧
    s'.storage 1 = add (s.storage 1) 1 := by
  by_cases hThreshold : add (s.storage 1) 1 = 65536
  · constructor
    · simp [DepositContractMinimal.deposit, hCount, hMin, hFull, hThreshold,
        DepositContractMinimal.depositCount, DepositContractMinimal.fullDepositCount,
        DepositContractMinimal.chainStarted, getStorage, setStorage, Verity.require, Verity.bind,
        Bind.bind, Contract.run, ContractResult.snd]
    · simp [DepositContractMinimal.deposit, hCount, hMin, hFull, hThreshold,
        DepositContractMinimal.depositCount, DepositContractMinimal.fullDepositCount,
        DepositContractMinimal.chainStarted, getStorage, setStorage, Verity.require, Verity.bind,
        Bind.bind, Contract.run, ContractResult.snd]
  · constructor
    · simp [DepositContractMinimal.deposit, hCount, hMin, hFull, hThreshold,
        DepositContractMinimal.depositCount, DepositContractMinimal.fullDepositCount,
        getStorage, setStorage, Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
        Contract.run, ContractResult.snd]
    · simp [DepositContractMinimal.deposit, hCount, hMin, hFull, hThreshold,
        DepositContractMinimal.depositCount, DepositContractMinimal.fullDepositCount,
        getStorage, setStorage, Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
        Contract.run, ContractResult.snd]

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
  dsimp
  rcases deposit_full_slot_writes depositAmount s hCount hMin hFull with ⟨hDeposits, hFullDeposits⟩
  rw [hDeposits, hFullDeposits]
  apply Verity.Core.Uint256.add_right_cancel
  calc
    ((s.storage 0 + 1) - (s.storage 1 + 1)) + (s.storage 1 + 1)
        = s.storage 0 + 1 := by
            exact Verity.Core.Uint256.sub_add_cancel_left (s.storage 0 + 1) (s.storage 1 + 1)
    _ = (s.storage 0 - s.storage 1) + (s.storage 1 + 1) := by
          rw [← Verity.Core.Uint256.add_assoc]
          rw [Verity.Core.Uint256.sub_add_cancel_left (s.storage 0) (s.storage 1)]

end Benchmark.Cases.Ethereum.DepositContractMinimal

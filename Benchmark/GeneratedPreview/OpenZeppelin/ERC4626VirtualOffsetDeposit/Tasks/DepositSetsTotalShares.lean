import Benchmark.Cases.OpenZeppelin.ERC4626VirtualOffsetDeposit.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.OpenZeppelin.ERC4626VirtualOffsetDeposit

open Verity
open Verity.EVM.Uint256

/--
Executing `deposit` stores `oldTotalShares + previewDeposit(assets)` in `totalShares`.
-/
theorem deposit_sets_totalShares
    (assets : Uint256) (s : ContractState) :
    let s' := ((ERC4626VirtualOffsetDeposit.deposit assets).run s).snd
    deposit_sets_totalShares_spec assets s s' := by
  -- Grindset-first skeleton. See harness/PROOF_PATTERNS.md.
  -- Try `grind` with contract symbol hints; fall back to `simp` /
  -- `by_cases` if grind leaves goals. Use `grind?` for hints.
  unfold deposit_sets_totalShares_spec
  grind [ERC4626VirtualOffsetDeposit.deposit, ERC4626VirtualOffsetDeposit.totalAssets, ERC4626VirtualOffsetDeposit.totalShares]

end Benchmark.Cases.OpenZeppelin.ERC4626VirtualOffsetDeposit

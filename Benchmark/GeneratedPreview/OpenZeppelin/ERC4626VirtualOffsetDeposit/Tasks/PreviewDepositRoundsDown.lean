import Benchmark.Cases.OpenZeppelin.ERC4626VirtualOffsetDeposit.Specs
import Verity.Stdlib.Math
import Benchmark.Grindset

namespace Benchmark.Cases.OpenZeppelin.ERC4626VirtualOffsetDeposit

open Verity
open Verity.EVM.Uint256
open Verity.Stdlib.Math

/--
`previewDeposit` rounds down, so the minted share estimate times the denominator
never exceeds the exact numerator product when the multiplication is exact.
-/
theorem previewDeposit_rounds_down
    (assets : Uint256) (s : ContractState)
    (hMul : (assets : Nat) * ((add (s.storage 1) virtualShares : Uint256) : Nat) <= MAX_UINT256) :
    previewDeposit_rounds_down_spec assets s := by
  -- Grindset-first skeleton. See harness/PROOF_PATTERNS.md.
  -- Try `grind` with contract symbol hints; fall back to `simp` /
  -- `by_cases` if grind leaves goals. Use `grind?` for hints.
  unfold previewDeposit_rounds_down_spec
  grind

end Benchmark.Cases.OpenZeppelin.ERC4626VirtualOffsetDeposit

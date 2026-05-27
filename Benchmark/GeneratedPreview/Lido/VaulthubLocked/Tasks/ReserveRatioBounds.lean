import Benchmark.Cases.Lido.VaulthubLocked.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Lido.VaulthubLocked

open Verity
open Verity.EVM.Uint256

/--
Certora P-VH-03: Reserve ratio is strictly between 0 and TOTAL_BASIS_POINTS.
This is enforced by the vault connection validation logic.
-/
theorem reserve_ratio_bounds
    (reserveRatioBP : Uint256)
    (hPos : reserveRatioBP > 0)
    (hLt : reserveRatioBP < TOTAL_BASIS_POINTS) :
    reserve_ratio_bounds_spec reserveRatioBP := by
  -- Grindset-first skeleton. See harness/PROOF_PATTERNS.md.
  -- Try `grind` with contract symbol hints; fall back to `simp` /
  -- `by_cases` if grind leaves goals. Use `grind?` for hints.
  unfold reserve_ratio_bounds_spec
  grind

end Benchmark.Cases.Lido.VaulthubLocked

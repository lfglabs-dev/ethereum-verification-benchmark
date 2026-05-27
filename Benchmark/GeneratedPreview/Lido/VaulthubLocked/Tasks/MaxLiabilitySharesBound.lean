import Benchmark.Cases.Lido.VaulthubLocked.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Lido.VaulthubLocked

open Verity
open Verity.EVM.Uint256

/--
Certora P-VH-04: maxLiabilityShares >= liabilityShares.
This invariant is maintained by the VaultHub's minting and reporting logic.
-/
theorem max_liability_shares_bound
    (maxLiabilityShares liabilityShares : Uint256)
    (hBound : maxLiabilityShares ≥ liabilityShares) :
    max_liability_shares_bound_spec maxLiabilityShares liabilityShares := by
  -- Grindset-first skeleton. See harness/PROOF_PATTERNS.md.
  -- Try `grind` with contract symbol hints; fall back to `simp` /
  -- `by_cases` if grind leaves goals. Use `grind?` for hints.
  unfold max_liability_shares_bound_spec
  grind

end Benchmark.Cases.Lido.VaulthubLocked

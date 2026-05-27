import Benchmark.Cases.Lido.VaulthubLocked.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Lido.VaulthubLocked

open Verity
open Verity.EVM.Uint256

/--
Certora F-01: Locked funds solvency.
After executing `syncLocked`, the stored locked amount (slot 6) multiplied by
the reserve ratio complement is at least the liability (from liabilityShares
in slot 1) multiplied by total basis points:

  s'.storage 6 * (BP - RR) >= getPooledEthBySharesRoundUp(LS, TPE, TS) * BP

The proof requires a case split on whether the computed reserve or the minimal
reserve dominates, then algebraic manipulation using the ceilDiv sandwich bound
and share conversion monotonicity.
-/
theorem locked_funds_solvency
    (s : ContractState)
    -- Axioms
    (hMaxLS : s.storage 0 ≥ s.storage 1)
    (hRR_pos : s.storage 3 > 0)
    (hRR_lt : s.storage 3 < TOTAL_BASIS_POINTS)
    (hTS : s.storage 5 > 0)
    (hTPE : s.storage 4 > 0)
    -- No overflow: maxLiabilityShares * totalPooledEther fits in Uint256
    (hNoOverflow1 : (s.storage 0).val * (s.storage 4).val < modulus)
    -- No overflow: liability * reserveRatioBP fits in Uint256
    (hNoOverflow2 : (getPooledEthBySharesRoundUp (s.storage 0) (s.storage 4) (s.storage 5)).val
                    * (s.storage 3).val < modulus)
    -- No overflow: the add inside locked (liability + effectiveReserve) fits in Uint256
    (hNoOverflow3 : let liab := getPooledEthBySharesRoundUp (s.storage 0) (s.storage 4) (s.storage 5)
                    let reserve := ceilDiv (mul liab (s.storage 3)) (sub TOTAL_BASIS_POINTS (s.storage 3))
                    let eff := if reserve ≥ s.storage 2 then reserve else s.storage 2
                    liab.val + eff.val < modulus)
    -- No overflow: locked * (BP - RR) fits in Uint256
    (hNoOverflow4 : let liab := getPooledEthBySharesRoundUp (s.storage 0) (s.storage 4) (s.storage 5)
                    let reserve := ceilDiv (mul liab (s.storage 3)) (sub TOTAL_BASIS_POINTS (s.storage 3))
                    let eff := if reserve ≥ s.storage 2 then reserve else s.storage 2
                    (add liab eff).val * (sub TOTAL_BASIS_POINTS (s.storage 3)).val < modulus)
    -- No overflow: liability * BP fits in Uint256
    (hNoOverflow5 : (getPooledEthBySharesRoundUp (s.storage 1) (s.storage 4) (s.storage 5)).val
                    * TOTAL_BASIS_POINTS.val < modulus) :
    let s' := ((VaultHubLocked.syncLocked).run s).snd
    locked_funds_solvency_spec s s' := by
  -- Grindset-first skeleton. See harness/PROOF_PATTERNS.md.
  -- Try `grind` with contract symbol hints; fall back to `simp` /
  -- `by_cases` if grind leaves goals. Use `grind?` for hints.
  unfold locked_funds_solvency_spec
  grind [VaultHubLocked.syncLocked, VaultHubLocked.maxLiabilityShares, VaultHubLocked.liabilityShares, VaultHubLocked.minimalReserve, VaultHubLocked.reserveRatioBP, VaultHubLocked.totalPooledEther, VaultHubLocked.totalShares, VaultHubLocked.lockedAmount]

end Benchmark.Cases.Lido.VaulthubLocked

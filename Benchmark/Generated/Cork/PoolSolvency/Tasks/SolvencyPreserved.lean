import Benchmark.Cases.Cork.PoolSolvency.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Cork.PoolSolvency

open Verity
open Verity.EVM.Uint256

/--
Certora P-02: Solvency preserved by unwindExerciseOther.
After executing unwindExerciseOther, locked collateral normalized to 18 decimals
still covers the outstanding swap share supply:

  collateralAssetLocked' * colScaleUp >= swapTotalSupply - swapBalanceOfPool'

The proof requires showing that the ceiling-rounded collateral added
(assetsInWithoutFee * colScaleUp) is at least the floor-rounded shares released
(cstSharesOut), which follows from the ceilDiv sandwich bound and the
monotonicity of ceiling division under multiplication.

Hypotheses encode:
- Pre-condition: solvency holds before the call
- Scale factors are positive (decimals <= 18)
- Swap rate is positive
- No overflow in intermediate computations
-/
theorem solvency_preserved
    (s : ContractState)
    (referenceAssetsOut : Uint256)
    -- Pre-condition: solvency holds before the call
    (hSolvencyBefore : mul (s.storage 0) (s.storage 5) ≥ sub (s.storage 1) (s.storage 2))
    -- colScaleUp > 0 (collateralDecimals <= 18)
    (hColScale : s.storage 5 > 0)
    -- refScaleUp > 0 (referenceDecimals <= 18)
    (hRefScale : s.storage 4 > 0)
    -- swapRate > 0
    (hSwapRate : s.storage 3 > 0)
    -- referenceAssetsOut > 0
    (hRefOut : referenceAssetsOut > 0)
    -- No overflow: referenceAssetsOut * refScaleUp
    (hNoOvf1 : referenceAssetsOut.val * (s.storage 4).val < modulus)
    -- No overflow: refFixed * swapRate
    (hNoOvf2 : (referenceAssetsOut.val * (s.storage 4).val) * (s.storage 3).val < modulus)
    -- No overflow: normalizedReferenceAsset * swapRate
    (hNoOvf3 : let refFixed := referenceAssetsOut.val * (s.storage 4).val
               let normalizedReferenceAsset := if refFixed = 0 then 0
                 else (refFixed - 1) / (s.storage 5).val + 1
               normalizedReferenceAsset * (s.storage 3).val < modulus)
    -- No overflow: collateralAssetLocked + assetsInWithoutFee
    (hNoOvf4 : let refFixed := referenceAssetsOut.val * (s.storage 4).val
               let normalizedReferenceAsset := if refFixed = 0 then 0
                 else (refFixed - 1) / (s.storage 5).val + 1
               let assetProduct := normalizedReferenceAsset * (s.storage 3).val
               let assetsInWithoutFee := if assetProduct = 0 then 0
                 else (assetProduct - 1) / 1000000000000000000 + 1
               (s.storage 0).val + assetsInWithoutFee < modulus)
    -- No overflow: (collateralAssetLocked + assetsInWithoutFee) * colScaleUp
    (hNoOvf5 : let refFixed := referenceAssetsOut.val * (s.storage 4).val
               let normalizedReferenceAsset := if refFixed = 0 then 0
                 else (refFixed - 1) / (s.storage 5).val + 1
               let assetProduct := normalizedReferenceAsset * (s.storage 3).val
               let assetsInWithoutFee := if assetProduct = 0 then 0
                 else (assetProduct - 1) / 1000000000000000000 + 1
               ((s.storage 0).val + assetsInWithoutFee) * (s.storage 5).val < modulus)
    -- swapTotalSupply >= swapBalanceOfPool (outstanding shares non-negative)
    (hSupplyGeBal : s.storage 1 ≥ s.storage 2) :
    let s' := ((CorkUnwindExerciseOther.unwindExerciseOther referenceAssetsOut).run s).snd
    solvency_preserved_spec s s' := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Cork.PoolSolvency

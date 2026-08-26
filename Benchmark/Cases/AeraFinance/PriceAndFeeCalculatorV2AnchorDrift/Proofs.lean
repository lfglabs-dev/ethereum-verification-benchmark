import Benchmark.Cases.AeraFinance.PriceAndFeeCalculatorV2AnchorDrift.Specs

namespace Benchmark.Cases.AeraFinance.PriceAndFeeCalculatorV2AnchorDrift

open Verity
open Verity.EVM.Uint256
set_option linter.unusedSimpArgs false

/-- Successful drift writes remain inside the source anchor band. -/
theorem drift_update_preserves_anchor_band
    (price timestamp : Uint256) (s : ContractState)
    (hActive : pausedOf s = 0)
    (hInitialized : anchorPriceOf s ≠ 0)
    (hBand : priceWithinAnchorBand s (anchorPriceOf s) price)
    (hProducts : anchorBandProductsExact s (anchorPriceOf s) price) :
    drift_update_preserves_anchor_band_spec price timestamp s := by
  have hActiveRaw : s.storage 0 = 0 := by simpa [pausedOf] using hActive
  have hInitializedRaw : s.storage 2 ≠ 0 := by simpa [anchorPriceOf] using hInitialized
  rcases hProducts with ⟨hCandidateExact, hMaxExact, hMinExact⟩
  have hMaxExactRaw :
      (mul (s.storage 2) (s.storage 7)).val =
        (s.storage 2).val * (s.storage 7).val := by
    simpa [anchorPriceOf, maxPriceToleranceRatioOf] using hMaxExact
  have hMinExactRaw :
      (mul (s.storage 2) (s.storage 6)).val =
        (s.storage 2).val * (s.storage 6).val := by
    simpa [anchorPriceOf, minPriceToleranceRatioOf] using hMinExact
  by_cases hHigh : price > s.storage 2
  · have hBandNat : price.val * 10000 <= (s.storage 2).val * (s.storage 7).val := by
      simpa [priceWithinAnchorBand, anchorPriceOf, maxPriceToleranceRatioOf, hHigh] using hBand
    have hBandRaw : (mul price 10000).val <= (mul (s.storage 2) (s.storage 7)).val := by
      rw [hCandidateExact, hMaxExactRaw]
      exact hBandNat
    simp [drift_update_preserves_anchor_band_spec, priceWithinAnchorBand,
      AeraPriceAndFeeCalculatorV2.setDriftPrice,
      AeraPriceAndFeeCalculatorV2._isPriceWithinAnchorBand,
      AeraPriceAndFeeCalculatorV2.paused, AeraPriceAndFeeCalculatorV2.anchorPrice,
      AeraPriceAndFeeCalculatorV2.anchorTimestamp, AeraPriceAndFeeCalculatorV2.driftPrice,
      AeraPriceAndFeeCalculatorV2.driftTimestamp,
      AeraPriceAndFeeCalculatorV2.minPriceToleranceRatio,
      AeraPriceAndFeeCalculatorV2.maxPriceToleranceRatio,
      pausedOf, anchorPriceOf, anchorTimestampOf, driftPriceOf, driftTimestampOf,
      minPriceToleranceRatioOf, maxPriceToleranceRatioOf, getStorage, setStorage,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hActiveRaw, hInitializedRaw, hHigh, hBandRaw, hBandNat]
  · have hBandNat : (s.storage 2).val * (s.storage 6).val <= price.val * 10000 := by
      simpa [priceWithinAnchorBand, anchorPriceOf, minPriceToleranceRatioOf, hHigh, GE.ge] using hBand
    have hBandRaw : (mul (s.storage 2) (s.storage 6)).val <= (mul price 10000).val := by
      rw [hMinExactRaw, hCandidateExact]
      exact hBandNat
    simp [drift_update_preserves_anchor_band_spec, priceWithinAnchorBand,
      AeraPriceAndFeeCalculatorV2.setDriftPrice,
      AeraPriceAndFeeCalculatorV2._isPriceWithinAnchorBand,
      AeraPriceAndFeeCalculatorV2.paused, AeraPriceAndFeeCalculatorV2.anchorPrice,
      AeraPriceAndFeeCalculatorV2.anchorTimestamp, AeraPriceAndFeeCalculatorV2.driftPrice,
      AeraPriceAndFeeCalculatorV2.driftTimestamp,
      AeraPriceAndFeeCalculatorV2.minPriceToleranceRatio,
      AeraPriceAndFeeCalculatorV2.maxPriceToleranceRatio,
      pausedOf, anchorPriceOf, anchorTimestampOf, driftPriceOf, driftTimestampOf,
      minPriceToleranceRatioOf, maxPriceToleranceRatioOf, getStorage, setStorage,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hActiveRaw, hInitializedRaw, hHigh, hBandRaw, hBandNat]

/-- A bad anchor update in fail-safe mode records the tuple and pauses. -/
theorem bad_anchor_pause_mode
    (price timestamp : Uint256) (s : ContractState)
    (hActive : pausedOf s = 0)
    (hPauseMode : pauseOnBadAnchorUpdateOf s ≠ 0) :
    bad_anchor_pause_mode_spec price timestamp s := by
  have hActiveRaw : s.storage 0 = 0 := by simpa [pausedOf] using hActive
  have hPauseModeRaw : s.storage 1 ≠ 0 := by
    simpa [pauseOnBadAnchorUpdateOf] using hPauseMode
  simp [bad_anchor_pause_mode_spec, AeraPriceAndFeeCalculatorV2.setAnchorPrice,
    AeraPriceAndFeeCalculatorV2.paused, AeraPriceAndFeeCalculatorV2.pauseOnBadAnchorUpdate,
    AeraPriceAndFeeCalculatorV2.anchorPrice, AeraPriceAndFeeCalculatorV2.anchorTimestamp,
    AeraPriceAndFeeCalculatorV2.accrualLag,
    pausedOf, anchorPriceOf, anchorTimestampOf, accrualLagOf, getStorage, setStorage,
    Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    Contract.run, ContractResult.snd, hActiveRaw, hPauseModeRaw]

/-- Disabled fail-safe mode makes a bad anchor update revert atomically. -/
theorem bad_anchor_revert_mode
    (price timestamp : Uint256) (s : ContractState)
    (hActive : pausedOf s = 0)
    (hRevertMode : pauseOnBadAnchorUpdateOf s = 0) :
    bad_anchor_revert_mode_spec price timestamp s := by
  have hActiveRaw : s.storage 0 = 0 := by simpa [pausedOf] using hActive
  have hRevertModeRaw : s.storage 1 = 0 := by
    simpa [pauseOnBadAnchorUpdateOf] using hRevertMode
  simp [bad_anchor_revert_mode_spec, AeraPriceAndFeeCalculatorV2.setAnchorPrice,
    AeraPriceAndFeeCalculatorV2.paused, AeraPriceAndFeeCalculatorV2.pauseOnBadAnchorUpdate,
    AeraPriceAndFeeCalculatorV2.anchorPrice, AeraPriceAndFeeCalculatorV2.anchorTimestamp,
    AeraPriceAndFeeCalculatorV2.accrualLag,
    getStorage, setStorage, Verity.require, Verity.bind, Bind.bind,
    Verity.pure, Pure.pure, Contract.run, hActiveRaw, hRevertModeRaw]

end Benchmark.Cases.AeraFinance.PriceAndFeeCalculatorV2AnchorDrift

import Benchmark.Cases.AeraFinance.PriceAndFeeCalculatorV2AnchorDrift.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.AeraFinance.PriceAndFeeCalculatorV2AnchorDrift

open Verity
open Verity.EVM.Uint256

theorem drift_update_preserves_anchor_band
    (price timestamp : Uint256) (s : ContractState)
    (hActive : pausedOf s = 0)
    (hInitialized : anchorPriceOf s ≠ 0)
    (hBand : priceWithinAnchorBand s (anchorPriceOf s) price)
    (hProducts : anchorBandProductsExact s (anchorPriceOf s) price) :
    drift_update_preserves_anchor_band_spec price timestamp s := by
  exact ?_

end Benchmark.Cases.AeraFinance.PriceAndFeeCalculatorV2AnchorDrift

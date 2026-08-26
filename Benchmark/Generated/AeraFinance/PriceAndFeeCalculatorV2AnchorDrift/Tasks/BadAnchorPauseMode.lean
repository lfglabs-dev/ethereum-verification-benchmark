import Benchmark.Cases.AeraFinance.PriceAndFeeCalculatorV2AnchorDrift.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.AeraFinance.PriceAndFeeCalculatorV2AnchorDrift

open Verity
open Verity.EVM.Uint256

theorem bad_anchor_pause_mode
    (price timestamp : Uint256) (s : ContractState)
    (hActive : pausedOf s = 0)
    (hPauseMode : pauseOnBadAnchorUpdateOf s ≠ 0) :
    bad_anchor_pause_mode_spec price timestamp s := by
  exact ?_

end Benchmark.Cases.AeraFinance.PriceAndFeeCalculatorV2AnchorDrift

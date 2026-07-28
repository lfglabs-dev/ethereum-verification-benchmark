import Benchmark.Cases.Enzyme.OnyxFeeHandler.Specs
import Verity.Proofs.Stdlib.Automation
import Verity.Proofs.Stdlib.Math

namespace Benchmark.Cases.Enzyme.OnyxFeeHandler

open Verity
open Verity.EVM.Uint256
open Verity.Stdlib.Math

set_option linter.unusedSimpArgs false

theorem settleDynamicFeesGivenPositionsValue_exact_accounting
    (env : Verity.Env)
    (totalPositionsValue : Uint256)
    (shares : Address)
    (s : ContractState)
    (hReentry : DynamicFeeReentryStable env.reenter)
    (hValuationCall : valuationHandlerCallSucceeds env shares)
    (hCaller : s.sender = wordToAddress (valuationHandlerWord env shares))
    (hPositionsCoverPriorFees : totalFeesOwedOf s <= totalPositionsValue)
    (hManagementEnabled : managementFeeTrackerOf s ≠ zeroAddress)
    (hPerformanceEnabled : performanceFeeTrackerOf s ≠ zeroAddress)
    (hManagementCall : managementFeeCallSucceeds env s totalPositionsValue)
    (hPerformanceCall : performanceFeeCallSucceeds env s totalPositionsValue)
    (hManagementFitsNet :
      managementFeeAmount env s totalPositionsValue <= managementFeeBase s totalPositionsValue)
    (hManagementRecipientNoOverflow :
      (feesOwedTo s (managementFeeRecipientOf s) : Nat) +
        (managementFeeAmount env s totalPositionsValue : Nat) <= MAX_UINT256)
    (hManagementTotalNoOverflow :
      (totalFeesOwedOf s : Nat) +
        (managementFeeAmount env s totalPositionsValue : Nat) <= MAX_UINT256)
    (hPerformanceRecipientNoOverflow :
      (feesOwedAfterManagement env s totalPositionsValue (performanceFeeRecipientOf s) : Nat) +
        (performanceFeeAmount env s totalPositionsValue : Nat) <= MAX_UINT256)
    (hPerformanceTotalNoOverflow :
      (totalFeesOwedAfterManagement env s totalPositionsValue : Nat) +
        (performanceFeeAmount env s totalPositionsValue : Nat) <= MAX_UINT256) :
    ∃ s',
      FeeHandler.settleDynamicFeesGivenPositionsValue env totalPositionsValue shares s =
        ContractResult.success () s' ∧
      exact_dynamic_fee_settlement env totalPositionsValue s s' := by
  exact ?_

end Benchmark.Cases.Enzyme.OnyxFeeHandler

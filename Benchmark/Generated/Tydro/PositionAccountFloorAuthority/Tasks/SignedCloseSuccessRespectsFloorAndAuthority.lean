import Benchmark.Cases.Tydro.PositionAccountFloorAuthority.Specs
import Verity.Proofs.Stdlib.Automation
import Benchmark.Grindset

namespace Benchmark.Cases.Tydro.PositionAccountFloorAuthority

open Verity
open Verity.EVM.Uint256

/-- Successful signed close composes lifecycle authority with every modeled floor and ceiling. -/
theorem signed_close_success_respects_floor_and_authority
    (account owner pool supplyAsset borrowAsset authorizedCaller : Address)
    (intentNonce intentDeadline : Uint256)
    (route : Address) (routeConfigHash : Uint256) (assetIn : Address)
    (amountIn maxAmountIn : Uint256) (assetOut : Address) (minAmountOut : Uint256)
    (recipient : Address) (conversionDeadline routeDataHash : Uint256)
    (debtToken : Address)
    (maxRepayAmount maxFlashLoanRepayment minWithdrawAmount maxRemainingDebt
      maxRemainingCollateral minHealthFactor : Uint256)
    (residualReceiver : Address)
    (digest signature : Uint256) (recoveredSigner : Address)
    (withdrawnAmount measuredAmountOut remainingDebt remainingCollateral healthFactor : Uint256)
    (finalPoolSettlementSucceeds : Bool) (s : ContractState) :
    signed_close_floor_authority_spec account owner pool supplyAsset borrowAsset authorizedCaller
      intentNonce intentDeadline route routeConfigHash assetIn amountIn maxAmountIn assetOut
      minAmountOut recipient conversionDeadline routeDataHash debtToken maxRepayAmount
      maxFlashLoanRepayment minWithdrawAmount maxRemainingDebt maxRemainingCollateral
      minHealthFactor residualReceiver digest signature recoveredSigner withdrawnAmount
      measuredAmountOut remainingDebt remainingCollateral healthFactor
      finalPoolSettlementSucceeds s := by
  exact ?_

end Benchmark.Cases.Tydro.PositionAccountFloorAuthority

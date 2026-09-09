import Benchmark.Cases.Tydro.PositionAccountFloorAuthority.Specs
import Verity.Proofs.Stdlib.Automation
import Benchmark.Grindset

namespace Benchmark.Cases.Tydro.PositionAccountFloorAuthority

open Verity
open Verity.EVM.Uint256

/-- Successful signed open composes lifecycle authority with every modeled floor and ceiling. -/
theorem signed_open_success_respects_floor_and_authority
    (account owner pool supplyAsset borrowAsset authorizedCaller : Address)
    (intentNonce intentDeadline : Uint256)
    (route : Address) (routeConfigHash : Uint256) (assetIn : Address)
    (amountIn maxAmountIn : Uint256) (assetOut : Address) (minAmountOut : Uint256)
    (recipient : Address) (conversionDeadline routeDataHash : Uint256)
    (debtToken : Address)
    (initialCollateralAmount eModeCategory flashLoanAmount minSuppliedTokenAmount
      maxBorrowedTokenAmount minHealthFactor : Uint256)
    (digest signature : Uint256) (recoveredSigner : Address)
    (measuredAmountOut suppliedTokenAmount borrowedTokenAmount healthFactor : Uint256)
    (finalPoolSettlementSucceeds : Bool) (s : ContractState) :
    signed_open_floor_authority_spec account owner pool supplyAsset borrowAsset authorizedCaller
      intentNonce intentDeadline route routeConfigHash assetIn amountIn maxAmountIn assetOut
      minAmountOut recipient conversionDeadline routeDataHash debtToken initialCollateralAmount
      eModeCategory flashLoanAmount minSuppliedTokenAmount maxBorrowedTokenAmount minHealthFactor
      digest signature recoveredSigner measuredAmountOut suppliedTokenAmount borrowedTokenAmount
      healthFactor finalPoolSettlementSucceeds s := by
  exact ?_

end Benchmark.Cases.Tydro.PositionAccountFloorAuthority

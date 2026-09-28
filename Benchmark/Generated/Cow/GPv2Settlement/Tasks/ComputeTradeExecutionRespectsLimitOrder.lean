import Benchmark.Cases.Cow.GPv2Settlement.Specs

namespace Benchmark.Cases.Cow.GPv2Settlement

open Verity
open Verity.EVM.Uint256

/-- One successful `computeTradeExecution` respects the signed limit price after rounding, grows `filledAmount` by exactly the filled part without exceeding the limit amount, and returns a computed fee of at most `feeAmount` pro rata. Token movements are not modeled. -/
theorem computeTradeExecution_respects_limit_order
    (orderUid : Uint256) (o : SignedOrder)
    (sellPrice buyPrice executedAmount inAmount outAmount fee : Uint256)
    (s s' : ContractState)
    (hRun : (tradeCall orderUid o sellPrice buyPrice executedAmount).run s =
      ContractResult.success (inAmount, outAmount, fee) s') :
    trade_execution_spec orderUid o s s' inAmount outAmount fee := by
  exact ?_

end Benchmark.Cases.Cow.GPv2Settlement

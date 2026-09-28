import Benchmark.Cases.Cow.GPv2Settlement.Specs

namespace Benchmark.Cases.Cow.GPv2Settlement

open Verity
open Verity.EVM.Uint256

/-- If the two transfers of a successful trade move exactly the amounts that `settle` hands to them (`MovesExactly`, the token hypothesis), the owner's and receiver's balance changes respect the signed limit price and fee. -/
theorem settle_trade_respects_limit_order_in_balances
    (orderUid : Uint256) (o : SignedOrder)
    (sellPrice buyPrice executedAmount inAmount outAmount fee : Uint256)
    (s s' : ContractState)
    (owner receiver settlement : Address)
    (sellBefore sellAfter buyBefore buyAfter : Balances)
    (hRun : (tradeCall orderUid o sellPrice buyPrice executedAmount).run s =
      ContractResult.success (inAmount, outAmount, fee) s')
    (hPull : MovesExactly sellBefore sellAfter owner settlement inAmount.val)
    (hPay : MovesExactly buyBefore buyAfter settlement receiver outAmount.val) :
    trade_balance_spec o owner receiver sellBefore sellAfter buyBefore buyAfter fee.val := by
  exact ?_

end Benchmark.Cases.Cow.GPv2Settlement

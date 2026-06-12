import Benchmark.Cases.Balancer.ReClammSwapRounding.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Balancer.ReClammSwapRounding

open Verity
open Verity.EVM.Uint256

/--
ReClamm swap rounding invariant.

For any successful exact-in or exact-out `onSwap` quote, with the current
virtual balances held fixed during the quote, applying the returned real-balance
deltas does not decrease:

  `(balanceA + virtualBalanceA) * (balanceB + virtualBalanceB)`.
-/
theorem onSwap_fixed_virtual_balances_product_non_decreasing
    (exactIn : Bool)
    (balanceA balanceB virtualBalanceA virtualBalanceB : Uint256)
    (indexIn indexOut amountGivenScaled18 amountCalculatedScaled18 : Uint256)
    (s : ContractState)
    -- Valid route condition for the two-token ReClamm pool: A -> B or B -> A.
    -- The scalar model keeps this explicit because token indexes are raw inputs.
    (hTokenPair : (indexIn = 0 ∧ indexOut = 1) ∨ (indexIn = 1 ∧ indexOut = 0))
    (hNoOverflow :
      onSwap_no_overflow_assumptions exactIn balanceA balanceB
        virtualBalanceA virtualBalanceB indexIn indexOut amountGivenScaled18)
    (hRun :
      (ReClammPool.onSwap exactIn balanceA balanceB virtualBalanceA virtualBalanceB
        indexIn indexOut amountGivenScaled18).run s =
        ContractResult.success amountCalculatedScaled18 s) :
    onSwap_fixed_virtual_balances_product_non_decreasing_spec
      exactIn balanceA balanceB virtualBalanceA virtualBalanceB
      indexIn indexOut amountGivenScaled18 amountCalculatedScaled18 := by
  exact ?_

end Benchmark.Cases.Balancer.ReClammSwapRounding

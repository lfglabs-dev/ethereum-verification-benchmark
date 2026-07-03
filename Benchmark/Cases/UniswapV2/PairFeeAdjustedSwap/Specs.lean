import Verity.Specs.Common
import Benchmark.Cases.UniswapV2.PairFeeAdjustedSwap.Contract

namespace Benchmark.Cases.UniswapV2.PairFeeAdjustedSwap

open Verity
open Verity.EVM.Uint256

def applySwap_sets_reserve0_spec
    (balance0 : Uint256) (_s s' : ContractState) : Prop :=
  s'.storage 0 = balance0

def applySwap_sets_reserve1_spec
    (balance1 : Uint256) (_s s' : ContractState) : Prop :=
  s'.storage 1 = balance1

def applySwap_sets_reserve_product_spec
    (balance0 balance1 : Uint256) (_s s' : ContractState) : Prop :=
  mul (s'.storage 0) (s'.storage 1) = mul balance0 balance1

def applySwap_enforces_fee_adjusted_invariant_spec
    (_balance0 _balance1 amount0In amount1In : Uint256) (s s' : ContractState) : Prop :=
  let balance0Adjusted := sub (mul (s'.storage 0) 1000) (mul amount0In 3)
  let balance1Adjusted := sub (mul (s'.storage 1) 1000) (mul amount1In 3)
  mul balance0Adjusted balance1Adjusted >= mul (mul (s.storage 0) (s.storage 1)) 1000000

/--
Constant-product monotonicity across two sequential fee-adjusted swaps:
the reserve product after the second swap is at least the reserve product
before the first swap (`k' >= k`).
-/
def applySwap_two_swap_k_monotone_spec (s s' : ContractState) : Prop :=
  mul (s'.storage 0) (s'.storage 1) >= mul (s.storage 0) (s.storage 1)

/--
Sandwich output bound. `s` is the state before the adversarial front-run,
`frontBalance0` is reserve0 observed after the front-run, and `s'` is the
state after the victim swap. The token0 output realized by the victim,
`frontBalance0 - s'.storage 0`, is bounded by the fee-adjusted no-front-run
output bound computed from the original reserves:
`out * (1000 * reserve1 + 997 * amountIn) <= 997 * amountIn * reserve0`.
-/
def applySwap_swap_sandwich_output_bound_spec
    (frontBalance0 amountIn : Uint256) (s s' : ContractState) : Prop :=
  (frontBalance0.val - (s'.storage 0).val)
      * (1000 * (s.storage 1).val + 997 * amountIn.val)
    ≤ 997 * (amountIn.val * (s.storage 0).val)

end Benchmark.Cases.UniswapV2.PairFeeAdjustedSwap

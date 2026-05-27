import Benchmark.Cases.UniswapV2.PairFeeAdjustedSwap.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.UniswapV2.PairFeeAdjustedSwap

open Verity
open Verity.EVM.Uint256

/--
Executing `applySwap` stores the observed `balance1` as `reserve1`.
-/
theorem applySwap_sets_reserve1
    (balance0 balance1 amount0In amount1In : Uint256) (s : ContractState)
    (hInput : amount0In != 0 || amount1In != 0)
    (hFee0 : mul balance0 1000 >= mul amount0In 3)
    (hFee1 : mul balance1 1000 >= mul amount1In 3)
    (hK : mul (sub (mul balance0 1000) (mul amount0In 3))
        (sub (mul balance1 1000) (mul amount1In 3))
        >= mul (mul (s.storage 0) (s.storage 1)) 1000000) :
    let s' := ((PairFeeAdjustedSwap.applySwap balance0 balance1 amount0In amount1In).run s).snd
    applySwap_sets_reserve1_spec balance1 s s' := by
  -- Grindset-first skeleton. See harness/PROOF_PATTERNS.md.
  -- Try `grind` with contract symbol hints; fall back to `simp` /
  -- `by_cases` if grind leaves goals. Use `grind?` for hints.
  unfold applySwap_sets_reserve1_spec
  grind [PairFeeAdjustedSwap.applySwap, PairFeeAdjustedSwap.reserve0, PairFeeAdjustedSwap.reserve1]

end Benchmark.Cases.UniswapV2.PairFeeAdjustedSwap

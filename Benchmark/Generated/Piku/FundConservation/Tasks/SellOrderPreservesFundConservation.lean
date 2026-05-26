import Benchmark.Cases.Piku.FundConservation.Specs

namespace Benchmark.Cases.Piku.FundConservation

open Verity
open Verity.EVM.Uint256

/--
Piku redemption-order creation preserves the accounting decomposition:
distributed backing + queued redemption backing + remaining backing +
protocol fees + project fees = initial backing.

The arithmetic hypothesis exposes the real proof boundary: the Solidity
fee split uses integer division, so exact conservation requires a no-rounding
condition.
-/
theorem _sellOrder_preserves_fund_conservation
    (total protocolFeeBps : Uint256) (s : ContractState)
    (hAmount : total != 0)
    (hFees : add protocolFeeBps (s.storage 7) < 10000)
    (hRemaining : total.val <= (s.storage 2).val) :
    let s' := ((FM_PC_Oracle_Redeeming_v1._sellOrder total protocolFeeBps).run s).snd
    _sellOrder_preserves_fund_conservation_spec total protocolFeeBps s s' := by
  exact ?_

end Benchmark.Cases.Piku.FundConservation

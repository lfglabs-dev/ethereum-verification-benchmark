import Benchmark.Cases.Piku.FundConservation.Specs

namespace Benchmark.Cases.Piku.FundConservation

open Verity
open Verity.EVM.Uint256

theorem _sellOrder_records_redemption_buckets
    (total protocolFeeBps : Uint256) (s : ContractState)
    (hAmount : total != 0)
    (hFees : add protocolFeeBps (s.storage 7) < 10000)
    (hRemaining : total.val <= (s.storage 2).val) :
    let s' := ((FM_PC_Oracle_Redeeming_v1._sellOrder total protocolFeeBps).run s).snd
    _sellOrder_records_redemption_buckets_spec total protocolFeeBps s s' := by
  exact ?_

end Benchmark.Cases.Piku.FundConservation

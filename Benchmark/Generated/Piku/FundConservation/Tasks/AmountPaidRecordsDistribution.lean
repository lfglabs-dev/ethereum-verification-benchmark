import Benchmark.Cases.Piku.FundConservation.Specs

namespace Benchmark.Cases.Piku.FundConservation

open Verity
open Verity.EVM.Uint256

theorem amountPaid_records_distribution
    (amount protocolFeeAmount_ : Uint256) (s : ContractState)
    (hOpen : amount.val <= (s.storage 5).val)
    (hFee : protocolFeeAmount_.val <= amount.val) :
    let s' := ((FM_PC_Oracle_Redeeming_v1.amountPaid amount protocolFeeAmount_).run s).snd
    amountPaid_records_distribution_spec amount protocolFeeAmount_ s s' := by
  exact ?_

end Benchmark.Cases.Piku.FundConservation

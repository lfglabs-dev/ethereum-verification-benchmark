import Benchmark.Cases.Piku.FundConservation.Specs

namespace Benchmark.Cases.Piku.FundConservation

open Verity
open Verity.EVM.Uint256

/--
Manual queue payment execution preserves the same backing decomposition
when the queued amount splits exactly into user distribution plus protocol
treasury fee.
-/
theorem amountPaid_preserves_fund_conservation
    (amount protocolFeeAmount_ : Uint256) (s : ContractState)
    (hOpen : amount.val <= (s.storage 5).val)
    (hFee : protocolFeeAmount_.val <= amount.val) :
    let s' := ((FM_PC_Oracle_Redeeming_v1.amountPaid amount protocolFeeAmount_).run s).snd
    amountPaid_preserves_fund_conservation_spec amount protocolFeeAmount_ s s' := by
  exact ?_

end Benchmark.Cases.Piku.FundConservation

/-
Model/specification elaboration target.
Complete reference proofs are in Proofs.lean. This target does not emit Yul
or establish Solidity/compiler/bytecode refinement.
-/
import Benchmark.Cases.Kuru.WithdrawalLimit.Contract
import Benchmark.Cases.Kuru.WithdrawalLimit.Specs

namespace Benchmark.Cases.Kuru.WithdrawalLimit

#check referenceAt
#check write
#check recordWithdrawal
#check recordDeposit
#check transferAsset
#check withdrawBeforeTransfer
#check refundAsset
#check receivedAmount
#check debitedAmount
#check MeasuredDepositCredit
#check MeasuredOrdinarySettlement
#check MeasuredApprovedSettlement
#check fulfillApprovedWithdrawal
#check executeTransaction
#check Reachable
#check PolicyBundle

end Benchmark.Cases.Kuru.WithdrawalLimit

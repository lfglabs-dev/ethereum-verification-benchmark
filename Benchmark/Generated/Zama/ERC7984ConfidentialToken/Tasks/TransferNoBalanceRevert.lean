import Benchmark.Cases.Zama.ERC7984ConfidentialToken.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Zama.ERC7984ConfidentialToken

open Verity
open Verity.EVM.Uint256

/--
Transfer never reverts based on balance sufficiency.

Given that all plaintext preconditions hold (non-zero addresses,
initialized sender balance), the transfer always succeeds — it
returns `ContractResult.success`, never `ContractResult.revert`.

This is the contract-level non-leakage invariant for ERC-7984:
an on-chain observer cannot learn whether the sender had sufficient
balance by checking if the transaction reverted.

Note: NO hypothesis about `fromBalance >= amount` is provided.
The theorem must hold for BOTH sufficient and insufficient balances.
-/
theorem transfer_no_balance_revert
    (sender recipient : Address) (amount : Uint256) (s : ContractState)
    (hFrom : (sender != zeroAddress) = true)
    (hTo : (recipient != zeroAddress) = true)
    (hInit : s.storageMap 2 sender ≠ 0)
    (hDistinct : sender ≠ recipient)
    (hAmount64 : amount < UINT64_MOD)
    (hFromBal64 : s.storageMap 1 sender < UINT64_MOD)
    (hToBal64 : s.storageMap 1 recipient < UINT64_MOD) :
    transfer_no_balance_revert_spec sender recipient amount s := by
  -- Grindset-first skeleton. See harness/PROOF_PATTERNS.md.
  -- Try `grind` with contract symbol hints; fall back to `simp` /
  -- `by_cases` if grind leaves goals. Use `grind?` for hints.
  unfold transfer_no_balance_revert_spec
  grind

end Benchmark.Cases.Zama.ERC7984ConfidentialToken

import Benchmark.Cases.Zama.ERC7984ConfidentialToken.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Zama.ERC7984ConfidentialToken

open Verity
open Verity.EVM.Uint256

/--
Operator-gated transferFrom preserves balance conservation.

When the caller is authorized (either `holder == msg.sender` or
`block.timestamp <= operators[holder][msg.sender]`), transferFrom
preserves the sum `balances[holder] + balances[recipient]`.

This ensures that delegating transfer authority via the operator
pattern does not allow creation or destruction of tokens.
-/
theorem transferFrom_conservation
    (holder recipient : Address) (amount blockTimestamp : Uint256)
    (s : ContractState)
    (hFrom : (holder != zeroAddress) = true)
    (hTo : (recipient != zeroAddress) = true)
    (hInit : s.storageMap 2 holder ≠ 0)
    (hDistinct : holder ≠ recipient)
    (hAuthorized :
      holder == s.sender ∨ blockTimestamp <= s.storageMap2 3 holder s.sender)
    (hAmount64 : amount < UINT64_MOD)
    (hHolderBal64 : s.storageMap 1 holder < UINT64_MOD)
    (hRecipientBal64 : s.storageMap 1 recipient < UINT64_MOD)
    (hToNoWrap : s.storageMap 1 recipient + amount < UINT64_MOD) :
    let s' := ((ERC7984.transferFrom holder recipient amount blockTimestamp).run s).snd
    transferFrom_conservation_spec holder recipient s s' := by
  -- Grindset-first skeleton. See harness/PROOF_PATTERNS.md.
  -- Try `grind` with contract symbol hints; fall back to `simp` /
  -- `by_cases` if grind leaves goals. Use `grind?` for hints.
  unfold transferFrom_conservation_spec
  grind [ERC7984.transferFrom, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized, ERC7984.operators]

end Benchmark.Cases.Zama.ERC7984ConfidentialToken

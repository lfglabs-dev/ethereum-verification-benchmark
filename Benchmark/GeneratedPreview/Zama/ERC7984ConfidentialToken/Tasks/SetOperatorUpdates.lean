import Benchmark.Cases.Zama.ERC7984ConfidentialToken.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Zama.ERC7984ConfidentialToken

open Verity
open Verity.EVM.Uint256

/--
setOperator(operator, expiry) writes `expiry` into `_operators[msg.sender][operator]`
and leaves all other operator entries unchanged.

This is the functional-correctness property for the operator registration
function: the caller can set an expiry for a specific operator, but cannot
affect authorizations granted by other holders or to other operators.
-/
theorem setOperator_updates
    (operator : Address) (expiry : Uint256) (s : ContractState) :
    let s' := ((ERC7984.setOperator operator expiry).run s).snd
    setOperator_updates_spec s.sender operator expiry s s' := by
  -- Grindset-first skeleton. See harness/PROOF_PATTERNS.md.
  -- Try `grind` with contract symbol hints; fall back to `simp` /
  -- `by_cases` if grind leaves goals. Use `grind?` for hints.
  unfold setOperator_updates_spec
  grind [ERC7984.setOperator, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized, ERC7984.operators]

end Benchmark.Cases.Zama.ERC7984ConfidentialToken

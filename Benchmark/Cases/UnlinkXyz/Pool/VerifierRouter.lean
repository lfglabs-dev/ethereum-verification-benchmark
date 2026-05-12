/-
  Verity model of `VerifierRouter` — placeholder.

  Upstream: unlink-xyz/monorepo@4bc46c1fffbc0e146dccfff5b9fe00167121b27b
  Source:   protocol/contracts/src/VerifierRouter.sol

  The Solidity `mapping(bytes32 => Circuit)` storage shape would benefit
  from Verity's `MappingStruct(Uint256, [verifier @word 0 packed(0,160),
  inputCount @word 0 packed(160,16), outputCount @word 0 packed(176,16),
  active @word 0 packed(192,8)])` (verity#623 / #1470 / #1738), collapsing
  the previous "four parallel scalar mappings" workaround in the local
  scratchpad. An initial attempt to land that `verity_contract
  VerifierRouter` declaration here is on hold pending two framework
  limitations observed while wiring `MappingStruct(Uint256, ...)`:

    1. `setStructMember "field" key "member" (1 : Uint256)` (or bare `1`)
       fails the macro's typeclass synthesis for the value position;
       the smoke pattern in `Contracts/Smoke.lean` only exercises member
       values that arrive as function parameters, not literals.
    2. `structMember "field" key "member"` for a `Uint256`-keyed mapping
       struct fails the same synthesis on read (no Uint256-keyed example
       in the upstream smoke; the working example is `Address`-keyed).

  Both are tracked under verity#623 follow-up work (MappingStruct macro
  ergonomics — literal value writes + Uint256-key read/write paths). The
  pool calls into this router today via the typed `linked_externals
  getCircuit(Uint256) -> (Uint256, Uint256, Uint256, Uint256)` declared
  in `Contract.lean`, which is the canonical cross-contract dispatch
  surface — so the missing sibling contract is a translation
  completeness gap, not a wire-up gap.
-/
import Contracts.Common

namespace Benchmark.Cases.UnlinkXyz.Pool

/-- Placeholder marker so `Compile.lean` can import this module. The
    actual `verity_contract VerifierRouter` declaration will replace
    this once the MappingStruct literal-value-write path is exercised
    for `Uint256`-keyed mappings in the upstream Verity macro tests. -/
def verifierRouterPlaceholder : Bool := true

end Benchmark.Cases.UnlinkXyz.Pool

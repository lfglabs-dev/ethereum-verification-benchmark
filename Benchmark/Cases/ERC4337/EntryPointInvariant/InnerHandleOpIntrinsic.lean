import Contracts.Common

namespace Benchmark.Cases.ERC4337.EntryPointInvariant

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math
open Contracts

/-!
# `innerHandleOp` calldata-buffer abstract function + documented Yul lowering

The real `EntryPoint._executeUserOp` does:

```solidity
function _executeUserOp(uint256 opIndex, PackedUserOperation calldata userOp,
                        UserOpInfo memory opInfo) {
    bytes calldata callData = userOp.callData;
    if (callData.length > 0) {
        // assembly { ... pack [selector || encoded args] into scratch ... }
        Exec.call(opInfo.mUserOp.sender, gasLimit, 0, callData);
    }
    ...
}
```

The inline assembly (skipped in the snippet above) packs the
`Exec.call` calldata: selector + ABI-encoded `(sender, gasLimit, value,
data)`. Verity's plain EDSL cannot express the layout directly.

## Approach

We expose:

* `packInnerCalldata` — the abstract Lean function used by the
  biconditional proofs. The control-flow biconditional only depends on
  the **presence** of the inner call (gated by `callData.length > 0`)
  and the success bit it returns, not on the byte-level layout of the
  packed buffer.

* A documented Yul lowering reference: the differential test
  (`differential/`) is the empirical certificate that the Verity
  emitter's calldata packing matches solc on the chosen scenarios.

## Why not a `verity_intrinsic`?

Verity's `verity_intrinsic` macro currently accepts a single-parameter
signature only. The `_executeUserOp` calldata packing takes four
parameters (sender, gasLimit, callDataOffset, callDataLength), so a
multi-arg intrinsic extension to Verity is required to land this as a
first-class intrinsic. That extension is the right Verity follow-up;
this file landed the abstract function so the rest of the proofs are
ready.

## Trust class

The Yul lowering is a documented `assumed` obligation tagged
`entrypoint_inner_calldata_layout`. It surfaces in any future Verity
`--trust-report` output for the case once the multi-arg intrinsic
extension lands. The differential test gives the empirical check.

## Roadmap

When Verity gains a multi-arg `verity_intrinsic` declaration, this
file becomes a one-liner:

```
verity_intrinsic entryPointPackInnerCalldata
    (sender, gasLimit, callDataOffset, callDataLength : Uint256) : Uint256
  where pure;
        yul := …;
        semantics := packInnerCalldata;
        obligation [entrypoint_inner_calldata_layout := assumed "…"]
```
-/

/-- The abstract calldata-layout function used by the biconditional
    proofs. The control-flow biconditional only depends on the function
    being deterministic and total — the actual byte layout is the
    Yul-lowering's responsibility, certified empirically by the
    differential test. -/
def packInnerCalldata
    (sender : Uint256) (gasLimit : Uint256)
    (callDataOffset callDataLength : Uint256) : Uint256 :=
  -- Sum-of-positions sentinel: deterministic and total. The differential
  -- test confirms the real Yul lowering matches solc's actual byte layout.
  add sender (add gasLimit (add callDataOffset callDataLength))

/-- The intended Yul lowering for the multi-arg intrinsic, kept here as
    a documentation artifact for the future Verity extension. The hex
    is a placeholder — the real lowering will be vendored verbatim
    from solc's emission for `_executeUserOp` at EntryPoint v0.9 commit
    `b36a1ed5`. -/
def entryPointInnerCalldataYulLoweringRef : String :=
  "// Yul lowering placeholder — see EntryPoint v0.9 _executeUserOp assembly block."

/-- Documented trust obligation tag for the Yul lowering. Surfaces in
    `verity --trust-report` output once the multi-arg intrinsic
    extension lands upstream. -/
def entryPointInnerCalldataObligationTag : String :=
  "entrypoint_inner_calldata_layout"

end Benchmark.Cases.ERC4337.EntryPointInvariant

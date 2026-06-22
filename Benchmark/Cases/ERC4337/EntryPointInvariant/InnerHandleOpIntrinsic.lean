import Contracts.Common

namespace Benchmark.Cases.ERC4337.EntryPointInvariant

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math
open Contracts

/-!
# `innerHandleOp` calldata-buffer intrinsic

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

The inline assembly (skipped in the snippet above) packs the `Exec.call`
calldata: selector + ABI-encoded `(sender, gasLimit, value, data)`.

## Approach

We expose:

* `packInnerCalldata` — the abstract Lean function used by the
  biconditional proofs. The control-flow biconditional only depends on
  the **presence** of the inner call (gated by `callData.length > 0`)
  and the success bit it returns, not on the byte-level layout of the packed
  buffer.

* `entryPointPackInnerCalldata` — a four-argument `verity_intrinsic`
  declaration. Verity #1977 landed multi-argument intrinsic declarations, so
  the ERC-4337 benchmark registers this boundary directly. Verity #2050 adds
  the multi-statement Yul template lowering used here to copy the calldata
  slice into memory before the sender call.

## Trust class

The intrinsic carries an explicit `assumed` obligation tagged
`entrypoint_inner_calldata_layout`: the byte-level Yul template must match the
EntryPoint v0.9 calldata forwarding layout for the chosen source commit. The
differential shim still decodes the real upstream `handleOps` calldata and
exercises the same sender-call slice empirically.
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

/-- Documented trust obligation tag for the Yul lowering. -/
def entryPointInnerCalldataObligationTag : String :=
  "entrypoint_inner_calldata_layout"

def entryPointPackInnerCalldataLowering : Verity.Core.Intrinsics.YulLowering :=
  Verity.Core.Intrinsics.YulLowering.template
    ["sender", "gasLimit", "callDataOffset", "callDataLength"]
    "packed"
    [
      Compiler.Yul.YulStmt.assign "packed"
        (Compiler.Yul.YulExpr.call "mload" [Compiler.Yul.YulExpr.lit 64]),
      Compiler.Yul.YulStmt.exprStmt
        (Compiler.Yul.YulExpr.call "calldatacopy"
          [ Compiler.Yul.YulExpr.ident "packed"
          , Compiler.Yul.YulExpr.ident "callDataOffset"
          , Compiler.Yul.YulExpr.ident "callDataLength"
          ]),
      Compiler.Yul.YulStmt.exprStmt
        (Compiler.Yul.YulExpr.call "mstore"
          [ Compiler.Yul.YulExpr.lit 64
          , Compiler.Yul.YulExpr.call "add"
              [ Compiler.Yul.YulExpr.ident "packed"
              , Compiler.Yul.YulExpr.call "and"
                  [ Compiler.Yul.YulExpr.call "add"
                      [Compiler.Yul.YulExpr.ident "callDataLength", Compiler.Yul.YulExpr.lit 31]
                  , Compiler.Yul.YulExpr.call "not" [Compiler.Yul.YulExpr.lit 31]
                  ]
              ]
          ])
    ]

verity_intrinsic entryPointPackInnerCalldata
    (sender : Uint256, gasLimit : Uint256,
     callDataOffset : Uint256, callDataLength : Uint256) : Uint256
  where pure;
        -- Copy the calldata slice into fresh memory and return its pointer.
        -- This mirrors the EntryPoint v0.9 execution path that forwards
        -- `userOp.callData` to the sender account.
        yul := [template (sender, gasLimit, callDataOffset, callDataLength) -> packed := [
          packed := mload(64),
          yulcall calldatacopy(packed, callDataOffset, callDataLength),
          yulcall mstore(64, add(packed, and(add(callDataLength, 31), not(31))))
        ]];
        min_fork := prague;
        semantics := packInnerCalldata;
        obligation [
          entrypoint_inner_calldata_layout := assumed
            "EntryPoint v0.9 innerHandleOp calldata packing; differential harness covers selected bytecode scenarios"
        ]

example :
    entryPointPackInnerCalldata 1 2 3 4 = packInnerCalldata 1 2 3 4 := rfl

example :
    entryPointPackInnerCalldata_intrinsic_obligations.startsWith
      "entrypoint_inner_calldata_layout: assumed" := by
  native_decide

end Benchmark.Cases.ERC4337.EntryPointInvariant

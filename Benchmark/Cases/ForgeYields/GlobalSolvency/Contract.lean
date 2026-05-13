import Contracts.Common

namespace Benchmark.Cases.ForgeYields.GlobalSolvency

open Verity hiding pure bind
open Verity.EVM.Uint256

/-
  Focused Verity model of ForgeYields `TokenGateway` accounting for the guarded
  global-solvency invariant.

  What was simplified | Why
  - ERC20 `balanceOf(address(this))` is represented by ghost slot `assetBalance` |
    external token storage is outside this contract, but solvency depends on it.
  - `_redeemInfo.assetsLocked` is represented by slot `assetsLocked` |
    the proof target only needs this aggregate field.
  - Queue NFTs, Hyperlane payloads, bridge dispatch, and report bytes parsing are
    represented by decoded scalar inputs | these external and dynamic structures do
    not affect the accounting inequality once the successful branch is selected.
  - Share/asset conversion and fee math are represented by direct `assets` inputs |
    Phase 3 target is the accounting preservation shape, not rate correctness.

  The key spec change from the initial candidate invariant is that solvency is
  required only while the gateway is not depreciated:

    `depreciated == 0 -> assetBalance >= buffer + assetsLocked`

  This matches ForgeYields' clarification that `_redeemInfo.assetsLocked` is not
  used by active code after depreciation mode is entered.
-/

verity_contract TokenGateway where
  storage
    assetBalance : Uint256 := slot 0
    buffer : Uint256 := slot 1
    assetsLocked : Uint256 := slot 2
    depreciated : Uint256 := slot 3

  -- src: TokenGateway.sol deposit path — active mode deposits increase both ERC20 balance and buffer.
  function deposit (assets : Uint256) : Unit := do
    let depreciated_ ← getStorage depreciated
    require (depreciated_ == 0) "depreciated"
    let assetBalance_ ← getStorage assetBalance
    let buffer_ ← getStorage buffer
    setStorage assetBalance (add assetBalance_ assets)
    setStorage buffer (add buffer_ assets)

  -- src: TokenGateway.sol requestRedeem — moves redeemable buffer assets into locked redeem accounting.
  function requestRedeem (assets : Uint256) : Unit := do
    let depreciated_ ← getStorage depreciated
    require (depreciated_ == 0) "depreciated"
    let buffer_ ← getStorage buffer
    require (assets <= buffer_) "insufficient-buffer"
    let assetsLocked_ ← getStorage assetsLocked
    setStorage buffer (sub buffer_ assets)
    setStorage assetsLocked (add assetsLocked_ assets)

  -- src: TokenGateway.sol claimRedeem — pays locked assets and decrements locked accounting.
  function claimRedeem (assets : Uint256) : Unit := do
    let assetsLocked_ ← getStorage assetsLocked
    require (assets <= assetsLocked_) "insufficient-locked"
    let assetBalance_ ← getStorage assetBalance
    require (assets <= assetBalance_) "insufficient-assets"
    setStorage assetBalance (sub assetBalance_ assets)
    setStorage assetsLocked (sub assetsLocked_ assets)

  -- src: TokenGateway.sol redeemTokenGatewayDepreciated — pays assets in depreciation mode.
  -- `_redeemInfo.assetsLocked` is intentionally not decremented; the guarded invariant is vacuous.
  function redeemTokenGatewayDepreciated (assets : Uint256) : Unit := do
    let depreciated_ ← getStorage depreciated
    require (depreciated_ != 0) "not-depreciated"
    let assetBalance_ ← getStorage assetBalance
    require (assets <= assetBalance_) "insufficient-assets"
    setStorage assetBalance (sub assetBalance_ assets)

  -- src: TokenGateway.sol transferRemote / bridge — active bridge outflow consumes buffer and ERC20 balance.
  function transferRemote (assets : Uint256) : Unit := do
    let depreciated_ ← getStorage depreciated
    require (depreciated_ == 0) "depreciated"
    let buffer_ ← getStorage buffer
    require (assets <= buffer_) "insufficient-buffer"
    let assetBalance_ ← getStorage assetBalance
    require (assets <= assetBalance_) "insufficient-assets"
    setStorage buffer (sub buffer_ assets)
    setStorage assetBalance (sub assetBalance_ assets)

  -- src: TokenGateway.sol handle — decoded controller/gateway message abstraction.
  function handle (assetsIn : Uint256, lockAssets : Uint256) : Unit := do
    let depreciated_ ← getStorage depreciated
    require (depreciated_ == 0) "depreciated"
    let assetBalance_ ← getStorage assetBalance
    let buffer_ ← getStorage buffer
    let assetsLocked_ ← getStorage assetsLocked
    setStorage assetBalance (add assetBalance_ assetsIn)
    setStorage buffer (add buffer_ assetsIn)
    setStorage buffer (sub (add buffer_ assetsIn) lockAssets)
    setStorage assetsLocked (add assetsLocked_ lockAssets)

  -- src: TokenGateway.sol report — does not mutate local solvency accounting.
  function report () : Unit := do
    return ()

end Benchmark.Cases.ForgeYields.GlobalSolvency

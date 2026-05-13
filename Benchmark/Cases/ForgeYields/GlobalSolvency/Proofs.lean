import Benchmark.Cases.ForgeYields.GlobalSolvency.Specs
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Cases.ForgeYields.GlobalSolvency

open Verity
open Verity.EVM.Uint256

private theorem deposit_bound
    (asset buffer locked assets : Uint256)
    (hInv : buffer.val + locked.val <= asset.val)
    (hAsset : asset.val + assets.val < Verity.Core.Uint256.modulus)
    (hBuffer : buffer.val + assets.val < Verity.Core.Uint256.modulus) :
    (add buffer assets).val + locked.val <= (add asset assets).val := by
  rw [Verity.EVM.Uint256.add_eq_of_lt hBuffer]
  rw [Verity.EVM.Uint256.add_eq_of_lt hAsset]
  omega

private theorem request_bound
    (asset buffer locked assets : Uint256)
    (hInv : buffer.val + locked.val <= asset.val)
    (hAssetsLeBuffer : assets.val <= buffer.val)
    (hLocked : locked.val + assets.val < Verity.Core.Uint256.modulus) :
    (sub buffer assets).val + (add locked assets).val <= asset.val := by
  rw [Verity.EVM.Uint256.sub_eq_of_le hAssetsLeBuffer]
  rw [Verity.EVM.Uint256.add_eq_of_lt hLocked]
  omega

private theorem claim_bound
    (asset buffer locked assets : Uint256)
    (hInv : buffer.val + locked.val <= asset.val)
    (hAssetsLeLocked : assets.val <= locked.val)
    (hAssetsLeAsset : assets.val <= asset.val) :
    buffer.val + (sub locked assets).val <= (sub asset assets).val := by
  rw [Verity.EVM.Uint256.sub_eq_of_le hAssetsLeLocked]
  rw [Verity.EVM.Uint256.sub_eq_of_le hAssetsLeAsset]
  omega

private theorem transfer_bound
    (asset buffer locked assets : Uint256)
    (hInv : buffer.val + locked.val <= asset.val)
    (hAssetsLeBuffer : assets.val <= buffer.val)
    (hAssetsLeAsset : assets.val <= asset.val) :
    (sub buffer assets).val + locked.val <= (sub asset assets).val := by
  rw [Verity.EVM.Uint256.sub_eq_of_le hAssetsLeBuffer]
  rw [Verity.EVM.Uint256.sub_eq_of_le hAssetsLeAsset]
  omega

private theorem handle_bound
    (asset buffer locked assetsIn lockAssets : Uint256)
    (hInv : buffer.val + locked.val <= asset.val)
    (hAssetIn : asset.val + assetsIn.val < Verity.Core.Uint256.modulus)
    (hBufferIn : buffer.val + assetsIn.val < Verity.Core.Uint256.modulus)
    (hLockedAdd : locked.val + lockAssets.val < Verity.Core.Uint256.modulus)
    (hLockLeBufferIn : lockAssets.val <= buffer.val + assetsIn.val) :
    (sub (add buffer assetsIn) lockAssets).val + (add locked lockAssets).val
      <= (add asset assetsIn).val := by
  have hAddBufferVal :
      ((add buffer assetsIn : Uint256) : Nat) = buffer.val + assetsIn.val := by
    rw [Verity.EVM.Uint256.add_eq_of_lt hBufferIn]
  change ((sub (add buffer assetsIn) lockAssets : Uint256) : Nat) +
      ((add locked lockAssets : Uint256) : Nat) <= ((add asset assetsIn : Uint256) : Nat)
  rw [Verity.EVM.Uint256.add_eq_of_lt hAssetIn]
  rw [Verity.EVM.Uint256.add_eq_of_lt hLockedAdd]
  rw [Verity.EVM.Uint256.sub_eq_of_le]
  · rw [hAddBufferVal]
    omega
  · rw [hAddBufferVal]
    exact hLockLeBufferIn

private theorem active_right {s : ContractState} (hActive : s.storage 3 = 0)
    (h : global_solvency_spec s) :
    (s.storage 1).val + (s.storage 2).val <= (s.storage 0).val := by
  rcases h with hDep | hBound
  · exfalso
    have : ¬ s.storage 3 != 0 := by simp [hActive]
    exact this hDep
  · exact hBound

/-- Active deposits preserve guarded global solvency on the successful no-overflow path. -/
theorem deposit_preserves_global_solvency
    (assets : Uint256) (s : ContractState)
    (hActive : s.storage 3 = 0)
    (hAssetNoOverflow : (s.storage 0).val + assets.val < Verity.Core.Uint256.modulus)
    (hBufferNoOverflow : (s.storage 1).val + assets.val < Verity.Core.Uint256.modulus) :
    let s' := ((TokenGateway.deposit assets).run s).snd
    deposit_preserves_global_solvency_spec s s' := by
  dsimp [deposit_preserves_global_solvency_spec]
  intro hPre
  unfold global_solvency_spec
  right
  have hPreRight := active_right hActive hPre
  simpa [TokenGateway.deposit, TokenGateway.assetBalance, TokenGateway.buffer,
    TokenGateway.depreciated, assetBalanceOf, bufferOf, assetsLockedOf, depreciatedOf,
    hActive, getStorage, setStorage, Verity.require, Verity.bind, Bind.bind,
    Verity.pure, Pure.pure, Contract.run, ContractResult.snd] using
    deposit_bound (s.storage 0) (s.storage 1) (s.storage 2) assets
      hPreRight hAssetNoOverflow hBufferNoOverflow

/-- Active redeem requests preserve guarded global solvency on the successful path. -/
theorem requestRedeem_preserves_global_solvency
    (assets : Uint256) (s : ContractState)
    (hActive : s.storage 3 = 0)
    (hAssetsLeBuffer : assets.val <= (s.storage 1).val)
    (hLockedNoOverflow : (s.storage 2).val + assets.val < Verity.Core.Uint256.modulus) :
    let s' := ((TokenGateway.requestRedeem assets).run s).snd
    requestRedeem_preserves_global_solvency_spec s s' := by
  dsimp [requestRedeem_preserves_global_solvency_spec]
  intro hPre
  unfold global_solvency_spec
  right
  have hPreRight := active_right hActive hPre
  have hReq : assets <= s.storage 1 := by
    simpa [Verity.Core.Uint256.le_def] using hAssetsLeBuffer
  simpa [TokenGateway.requestRedeem, TokenGateway.assetBalance, TokenGateway.buffer,
    TokenGateway.assetsLocked, TokenGateway.depreciated, assetBalanceOf, bufferOf,
    assetsLockedOf, depreciatedOf, hActive, hReq, getStorage, setStorage,
    Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run,
    ContractResult.snd] using
    request_bound (s.storage 0) (s.storage 1) (s.storage 2) assets
      hPreRight hAssetsLeBuffer hLockedNoOverflow

/-- Normal redeem claims preserve guarded global solvency on the successful path. -/
theorem claimRedeem_preserves_global_solvency
    (assets : Uint256) (s : ContractState)
    (hAssetsLeLocked : assets.val <= (s.storage 2).val)
    (hAssetsLeAsset : assets.val <= (s.storage 0).val) :
    let s' := ((TokenGateway.claimRedeem assets).run s).snd
    claimRedeem_preserves_global_solvency_spec s s' := by
  dsimp [claimRedeem_preserves_global_solvency_spec]
  intro hPre
  unfold global_solvency_spec
  have hReqLocked : assets <= s.storage 2 := by
    simpa [Verity.Core.Uint256.le_def] using hAssetsLeLocked
  have hReqAsset : assets <= s.storage 0 := by
    simpa [Verity.Core.Uint256.le_def] using hAssetsLeAsset
  rcases hPre with hDep | hBound
  · left
    simpa [TokenGateway.claimRedeem, TokenGateway.assetBalance, TokenGateway.assetsLocked,
      TokenGateway.depreciated, assetBalanceOf, bufferOf, assetsLockedOf, depreciatedOf,
      hReqLocked, hReqAsset, getStorage, setStorage, Verity.require, Verity.bind,
      Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd] using hDep
  · right
    simpa [TokenGateway.claimRedeem, TokenGateway.assetBalance, TokenGateway.assetsLocked,
      TokenGateway.depreciated, assetBalanceOf, bufferOf, assetsLockedOf, depreciatedOf,
      hReqLocked, hReqAsset, getStorage, setStorage, Verity.require, Verity.bind,
      Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd] using
      claim_bound (s.storage 0) (s.storage 1) (s.storage 2) assets
        hBound hAssetsLeLocked hAssetsLeAsset

/-- Depreciated redemptions preserve the guarded invariant because the post-state stays depreciated. -/
theorem redeemTokenGatewayDepreciated_preserves_global_solvency
    (assets : Uint256) (s : ContractState)
    (hDep : s.storage 3 != 0)
    (hAssetsLeAsset : assets.val <= (s.storage 0).val) :
    let s' := ((TokenGateway.redeemTokenGatewayDepreciated assets).run s).snd
    redeemTokenGatewayDepreciated_preserves_global_solvency_spec s s' := by
  dsimp [redeemTokenGatewayDepreciated_preserves_global_solvency_spec]
  intro _hPre
  unfold global_solvency_spec
  left
  simp [TokenGateway.redeemTokenGatewayDepreciated, TokenGateway.assetBalance,
    TokenGateway.depreciated,
    depreciatedOf, hAssetsLeAsset, getStorage, setStorage, Verity.require,
    Verity.bind, Bind.bind, Contract.run, ContractResult.snd, hDep]

/-- Active remote transfers preserve guarded global solvency on the successful path. -/
theorem transferRemote_preserves_global_solvency
    (assets : Uint256) (s : ContractState)
    (hActive : s.storage 3 = 0)
    (hAssetsLeBuffer : assets.val <= (s.storage 1).val)
    (hAssetsLeAsset : assets.val <= (s.storage 0).val) :
    let s' := ((TokenGateway.transferRemote assets).run s).snd
    transferRemote_preserves_global_solvency_spec s s' := by
  dsimp [transferRemote_preserves_global_solvency_spec]
  intro hPre
  unfold global_solvency_spec
  right
  have hPreRight := active_right hActive hPre
  have hReqBuffer : assets <= s.storage 1 := by
    simpa [Verity.Core.Uint256.le_def] using hAssetsLeBuffer
  have hReqAsset : assets <= s.storage 0 := by
    simpa [Verity.Core.Uint256.le_def] using hAssetsLeAsset
  simpa [TokenGateway.transferRemote, TokenGateway.assetBalance, TokenGateway.buffer,
    TokenGateway.depreciated, assetBalanceOf, bufferOf, assetsLockedOf, depreciatedOf,
    hActive, hReqBuffer, hReqAsset, getStorage, setStorage, Verity.require,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd] using
    transfer_bound (s.storage 0) (s.storage 1) (s.storage 2) assets
      hPreRight hAssetsLeBuffer hAssetsLeAsset

/-- Decoded active `handle` accounting preserves guarded global solvency on the successful path. -/
theorem handle_preserves_global_solvency
    (assetsIn lockAssets : Uint256) (s : ContractState)
    (hActive : s.storage 3 = 0)
    (hAssetNoOverflow : (s.storage 0).val + assetsIn.val < Verity.Core.Uint256.modulus)
    (hBufferNoOverflow : (s.storage 1).val + assetsIn.val < Verity.Core.Uint256.modulus)
    (hLockedNoOverflow : (s.storage 2).val + lockAssets.val < Verity.Core.Uint256.modulus)
    (hLockLeBufferIn : lockAssets.val <= (s.storage 1).val + assetsIn.val) :
    let s' := ((TokenGateway.handle assetsIn lockAssets).run s).snd
    handle_preserves_global_solvency_spec s s' := by
  dsimp [handle_preserves_global_solvency_spec]
  intro hPre
  unfold global_solvency_spec
  right
  have hPreRight := active_right hActive hPre
  simpa [TokenGateway.handle, TokenGateway.assetBalance, TokenGateway.buffer,
    TokenGateway.assetsLocked, TokenGateway.depreciated, assetBalanceOf, bufferOf,
    assetsLockedOf, depreciatedOf, hActive, getStorage, setStorage, Verity.require,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd] using
    handle_bound (s.storage 0) (s.storage 1) (s.storage 2) assetsIn lockAssets
      hPreRight hAssetNoOverflow hBufferNoOverflow hLockedNoOverflow hLockLeBufferIn

/-- Reports do not mutate the local solvency accounting slice. -/
theorem report_preserves_global_solvency
    (s : ContractState) :
    let s' := ((TokenGateway.report).run s).snd
    report_preserves_global_solvency_spec s s' := by
  dsimp [report_preserves_global_solvency_spec]
  intro hPre
  simpa [TokenGateway.report, report_preserves_global_solvency_spec,
    global_solvency_spec, assetBalanceOf, bufferOf, assetsLockedOf, depreciatedOf,
    Verity.pure, Pure.pure, Contract.run, ContractResult.snd] using hPre

end Benchmark.Cases.ForgeYields.GlobalSolvency

import Benchmark.Cases.Pendle.PySupplyPairing.Specs
import Verity.Proofs.Stdlib.Math

namespace Benchmark.Cases.Pendle.PySupplyPairing

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000

open Verity
open Verity.EVM.Uint256
open Verity.Proofs.Stdlib.Math (safeAdd_some safeMul_some safeDiv_some)

/-- Convert Verity's boolean nonzero-address guard into a Lean inequality. -/
private theorem address_ne_of_neq_zero {a : Address}
    (h : (a != zeroAddress) = true) : a ≠ (0 : Address) := by
  have hNe : a ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at h
  simpa [zeroAddress] using hNe

/-- Convert Verity's boolean nonzero-uint guard into a Lean inequality. -/
private theorem uint_ne_of_neq_zero {a : Uint256}
    (h : (a != 0) = true) : a ≠ 0 := by
  intro hEq
  subst hEq
  simp at h

/--
`mintPY` increments both supplies and both recipient balances by the exact PY
amount computed from floating SY and the current index.
-/
theorem mint_py_mints_equal_amount
    (receiverPT receiverYT : Address) (s : ContractState)
    (hNotExpired : s.storage 8 = 0)
    (hSyNoUnderflow : s.storage 5 >= s.storage 4)
    (hFloatingNonzero : (sub (s.storage 5) (s.storage 4) != 0) = true)
    (hMintMulNoOverflow :
      (floatingSyOf s : Nat) * (currentIndexOf s : Nat) <= Verity.Stdlib.Math.MAX_UINT256)
    (hMintUint248 : mintPYAmountOf s <= uint248Max)
    (hYtSupplyAddNoOverflow :
      (ytSupply s : Nat) + (mintPYAmountOf s : Nat) <= Verity.Stdlib.Math.MAX_UINT256)
    (hYtBalanceAddNoOverflow :
      (ytBalanceOf s receiverYT : Nat) + (mintPYAmountOf s : Nat) <= Verity.Stdlib.Math.MAX_UINT256)
    (hPtSupplyAddNoOverflow :
      (ptSupply s : Nat) + (mintPYAmountOf s : Nat) <= Verity.Stdlib.Math.MAX_UINT256)
    (hPtBalanceAddNoOverflow :
      (ptBalanceOf s receiverPT : Nat) + (mintPYAmountOf s : Nat) <= Verity.Stdlib.Math.MAX_UINT256)
    (hReceiverPT : (receiverPT != zeroAddress) = true)
    (hReceiverYT : (receiverYT != zeroAddress) = true) :
    let s' := ((PendlePY.mintPY receiverPT receiverYT).run s).snd
    mint_py_mints_equal_amount_spec receiverPT receiverYT s s' := by
  have hReceiverPTNZ := address_ne_of_neq_zero hReceiverPT
  have hReceiverYTNZ := address_ne_of_neq_zero hReceiverYT
  simp [mintPYAmountOf, currentIndexOf, floatingSyOf, syBalanceOf, syReserveOf,
    exchangeRateOf, pyIndexStoredOf, ytSupply, ptSupply, ytBalanceOf, ptBalanceOf,
    syToAsset, uint248Max, ONE] at hMintMulNoOverflow
  simp [mintPYAmountOf, currentIndexOf, floatingSyOf, syBalanceOf, syReserveOf,
    exchangeRateOf, pyIndexStoredOf, ytSupply, ptSupply, ytBalanceOf, ptBalanceOf,
    syToAsset, uint248Max, ONE] at hMintUint248
  simp [mintPYAmountOf, currentIndexOf, floatingSyOf, syBalanceOf, syReserveOf,
    exchangeRateOf, pyIndexStoredOf, ytSupply, ptSupply, ytBalanceOf, ptBalanceOf,
    syToAsset, uint248Max, ONE] at hYtSupplyAddNoOverflow
  simp [mintPYAmountOf, currentIndexOf, floatingSyOf, syBalanceOf, syReserveOf,
    exchangeRateOf, pyIndexStoredOf, ytSupply, ptSupply, ytBalanceOf, ptBalanceOf,
    syToAsset, uint248Max, ONE] at hYtBalanceAddNoOverflow
  simp [mintPYAmountOf, currentIndexOf, floatingSyOf, syBalanceOf, syReserveOf,
    exchangeRateOf, pyIndexStoredOf, ytSupply, ptSupply, ytBalanceOf, ptBalanceOf,
    syToAsset, uint248Max, ONE] at hPtSupplyAddNoOverflow
  simp [mintPYAmountOf, currentIndexOf, floatingSyOf, syBalanceOf, syReserveOf,
    exchangeRateOf, pyIndexStoredOf, ytSupply, ptSupply, ytBalanceOf, ptBalanceOf,
    syToAsset, uint248Max, ONE] at hPtBalanceAddNoOverflow
  have hSafeMintMul :=
    safeMul_some (sub (s.storage 5) (s.storage 4)) (maxUint (s.storage 7) (s.storage 6))
      hMintMulNoOverflow
  have hSafeMintMulBody :
      safeMul (sub (s.storage 5) (s.storage 4)) (maxUint (s.storage 7) (s.storage 6)) =
        some (sub (s.storage 5) (s.storage 4) * maxUint (s.storage 7) (s.storage 6)) := by
    simpa using hSafeMintMul
  have hSafeYtSupply :=
    safeAdd_some (s.storage 0)
      (div (mul (sub (s.storage 5) (s.storage 4)) (maxUint (s.storage 7) (s.storage 6)))
        1000000000000000000)
      hYtSupplyAddNoOverflow
  have hSafeYtSupplyBody :
      safeAdd (s.storage 0)
          (div (sub (s.storage 5) (s.storage 4) * maxUint (s.storage 7) (s.storage 6))
            1000000000000000000) =
        some
          (s.storage 0 +
            div (sub (s.storage 5) (s.storage 4) * maxUint (s.storage 7) (s.storage 6))
              1000000000000000000) := by
    simpa [HMul.hMul] using hSafeYtSupply
  have hSafeYtBalance :=
    safeAdd_some (s.storageMap 2 receiverYT)
      (div (mul (sub (s.storage 5) (s.storage 4)) (maxUint (s.storage 7) (s.storage 6)))
        1000000000000000000)
      hYtBalanceAddNoOverflow
  have hSafeYtBalanceBody :
      safeAdd (s.storageMap 2 receiverYT)
          (div (sub (s.storage 5) (s.storage 4) * maxUint (s.storage 7) (s.storage 6))
            1000000000000000000) =
        some
          (s.storageMap 2 receiverYT +
            div (sub (s.storage 5) (s.storage 4) * maxUint (s.storage 7) (s.storage 6))
              1000000000000000000) := by
    simpa [HMul.hMul] using hSafeYtBalance
  have hSafePtSupply :=
    safeAdd_some (s.storage 1)
      (div (mul (sub (s.storage 5) (s.storage 4)) (maxUint (s.storage 7) (s.storage 6)))
        1000000000000000000)
      hPtSupplyAddNoOverflow
  have hSafePtSupplyBody :
      safeAdd (s.storage 1)
          (div (sub (s.storage 5) (s.storage 4) * maxUint (s.storage 7) (s.storage 6))
            1000000000000000000) =
        some
          (s.storage 1 +
            div (sub (s.storage 5) (s.storage 4) * maxUint (s.storage 7) (s.storage 6))
              1000000000000000000) := by
    simpa [HMul.hMul] using hSafePtSupply
  have hSafePtBalance :=
    safeAdd_some (s.storageMap 3 receiverPT)
      (div (mul (sub (s.storage 5) (s.storage 4)) (maxUint (s.storage 7) (s.storage 6)))
        1000000000000000000)
      hPtBalanceAddNoOverflow
  have hSafePtBalanceBody :
      safeAdd (s.storageMap 3 receiverPT)
          (div (sub (s.storage 5) (s.storage 4) * maxUint (s.storage 7) (s.storage 6))
            1000000000000000000) =
        some
          (s.storageMap 3 receiverPT +
            div (sub (s.storage 5) (s.storage 4) * maxUint (s.storage 7) (s.storage 6))
              1000000000000000000) := by
    simpa [HMul.hMul] using hSafePtBalance
  have hMintUint248Body :
      (div (sub (s.storage 5) (s.storage 4) * maxUint (s.storage 7) (s.storage 6))
            1000000000000000000).val ≤
        Verity.Core.Uint256.val
          452312848583266388373324160190187140051835877600158453279131187530910662655 := by
    simpa [HMul.hMul] using hMintUint248
  unfold mint_py_mints_equal_amount_spec ytSupply ptSupply ytBalanceOf ptBalanceOf
    mintPYAmountOf currentIndexOf floatingSyOf syBalanceOf syReserveOf exchangeRateOf
    pyIndexStoredOf
  dsimp
  simp [PendlePY.mintPY, PendlePY._currentIndex, PendlePY._mintYT, PendlePY._mintPT,
    syToAsset, PendlePY.expired, PendlePY.syBalance, PendlePY.syReserve,
    PendlePY.exchangeRate, PendlePY.pyIndexStored, PendlePY.ytTotalSupply,
    PendlePY.ptTotalSupply, PendlePY.ytBalances, PendlePY.ptBalances,
    getStorage, setStorage, getMapping, setMapping, Verity.require, Verity.bind,
    Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd,
    hNotExpired, hSyNoUnderflow, hFloatingNonzero, hReceiverPT, hReceiverYT,
    hReceiverPTNZ, hReceiverYTNZ, hSafeMintMulBody, hSafeYtSupplyBody,
    hSafeYtBalanceBody, hSafePtSupplyBody, hSafePtBalanceBody, hMintUint248Body,
    hMintUint248, uint248Max, requireSomeUint, Verity.Stdlib.Math.requireSomeUint,
    HAdd.hAdd, ONE]
  simp [Verity.EVM.Uint256.add, Verity.EVM.Uint256.mul, HMul.hMul]

/--
`mintPY` preserves equality between YT total supply and PT total supply on the
successful non-expired path.
-/
theorem mint_py_preserves_supply_pairing
    (receiverPT receiverYT : Address) (s : ContractState)
    (hNotExpired : s.storage 8 = 0)
    (hSyNoUnderflow : s.storage 5 >= s.storage 4)
    (hFloatingNonzero : (sub (s.storage 5) (s.storage 4) != 0) = true)
    (hMintMulNoOverflow :
      (floatingSyOf s : Nat) * (currentIndexOf s : Nat) <= Verity.Stdlib.Math.MAX_UINT256)
    (hMintUint248 : mintPYAmountOf s <= uint248Max)
    (hYtSupplyAddNoOverflow :
      (ytSupply s : Nat) + (mintPYAmountOf s : Nat) <= Verity.Stdlib.Math.MAX_UINT256)
    (hYtBalanceAddNoOverflow :
      (ytBalanceOf s receiverYT : Nat) + (mintPYAmountOf s : Nat) <= Verity.Stdlib.Math.MAX_UINT256)
    (hPtSupplyAddNoOverflow :
      (ptSupply s : Nat) + (mintPYAmountOf s : Nat) <= Verity.Stdlib.Math.MAX_UINT256)
    (hPtBalanceAddNoOverflow :
      (ptBalanceOf s receiverPT : Nat) + (mintPYAmountOf s : Nat) <= Verity.Stdlib.Math.MAX_UINT256)
    (hReceiverPT : (receiverPT != zeroAddress) = true)
    (hReceiverYT : (receiverYT != zeroAddress) = true) :
    let s' := ((PendlePY.mintPY receiverPT receiverYT).run s).snd
    mint_py_preserves_supply_pairing_spec s s' := by
  dsimp
  have hExact :=
    mint_py_mints_equal_amount receiverPT receiverYT s hNotExpired hSyNoUnderflow
      hFloatingNonzero hMintMulNoOverflow hMintUint248 hYtSupplyAddNoOverflow
      hYtBalanceAddNoOverflow hPtSupplyAddNoOverflow hPtBalanceAddNoOverflow
      hReceiverPT hReceiverYT
  unfold mint_py_preserves_supply_pairing_spec supplyPairing ytSupply ptSupply
  intro hPair
  unfold mint_py_mints_equal_amount_spec ytSupply ptSupply ytBalanceOf ptBalanceOf at hExact
  rw [hExact.1, hExact.2.1, hPair]

/--
Before expiry, `redeemPY` burns the exact computed redeem amount from both
supplies and from the contract's own PT/YT balances.
-/
theorem redeem_py_pre_expiry_burns_equal_amount
    (receiver : Address) (s : ContractState)
    (hNotExpired : s.storage 8 = 0)
    (hSelf : (s.thisAddress != zeroAddress) = true)
    (hPtBalanceEnough : s.storageMap 3 s.thisAddress >= redeemPYAmountOf s)
    (hYtBalanceEnough : s.storageMap 2 s.thisAddress >= redeemPYAmountOf s)
    (hPtSupplyEnough : s.storage 1 >= redeemPYAmountOf s)
    (hYtSupplyEnough : s.storage 0 >= redeemPYAmountOf s)
    (hRedeemUint248 : redeemPYAmountOf s <= uint248Max)
    (hIndexNonzero : (currentIndexOf s != 0) = true)
    (hRedeemMulNoOverflow :
      (redeemPYAmountOf s : Nat) * (ONE : Nat) <= Verity.Stdlib.Math.MAX_UINT256) :
    let s' := ((PendlePY.redeemPY receiver).run s).snd
    redeem_py_pre_expiry_burns_equal_amount_spec s s' := by
  have hSelfNZ := address_ne_of_neq_zero hSelf
  simp [currentIndexOf, exchangeRateOf, pyIndexStoredOf] at hIndexNonzero
  have hIndexNZ : maxUint (s.storage 7) (s.storage 6) ≠ 0 := hIndexNonzero
  simp [redeemPYAmountOf, expiredFlagOf, ptBalanceOf, ytBalanceOf, pyToRedeem,
    minUint, hNotExpired, ONE] at hPtBalanceEnough
  simp [redeemPYAmountOf, expiredFlagOf, ptBalanceOf, ytBalanceOf, pyToRedeem,
    minUint, hNotExpired, ONE] at hYtBalanceEnough
  simp [redeemPYAmountOf, expiredFlagOf, ptBalanceOf, ytBalanceOf, pyToRedeem,
    minUint, hNotExpired, ONE] at hPtSupplyEnough
  simp [redeemPYAmountOf, expiredFlagOf, ptBalanceOf, ytBalanceOf, pyToRedeem,
    minUint, hNotExpired, ONE] at hYtSupplyEnough
  simp [redeemPYAmountOf, expiredFlagOf, ptBalanceOf, ytBalanceOf, pyToRedeem,
    minUint, hNotExpired, uint248Max, ONE] at hRedeemUint248
  have hIndexNZBody :
      (if (s.storage 6).val <= (s.storage 7).val then s.storage 7 else s.storage 6) ≠ 0 := by
    simpa [maxUint] using hIndexNZ
  unfold redeem_py_pre_expiry_burns_equal_amount_spec ytSupply ptSupply ytBalanceOf
    ptBalanceOf
  dsimp
  intro _hExpired
  simp [PendlePY.redeemPY, PendlePY._burnPT, PendlePY._burnYT, PendlePY._currentIndex,
    redeemPYAmountOf, redeemPYSyOutOf, currentIndexOf, expiredFlagOf, ptBalanceOf,
    ytBalanceOf, assetToSy, pyToRedeem, minUint, maxUint, exchangeRateOf, pyIndexStoredOf,
    PendlePY.expired, PendlePY.ptBalances, PendlePY.ytBalances, PendlePY.ptTotalSupply,
    PendlePY.ytTotalSupply, PendlePY.exchangeRate, PendlePY.pyIndexStored,
    PendlePY.syBalance, PendlePY.syReserve, getStorage, setStorage, getMapping, setMapping,
    contractAddress, Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    Contract.run, ContractResult.snd, hNotExpired, hSelf, hPtBalanceEnough,
    hYtBalanceEnough, hPtSupplyEnough, hYtSupplyEnough, hRedeemUint248,
    hIndexNonzero, hSelfNZ, hIndexNZ, hIndexNZBody, requireSomeUint,
    Verity.Stdlib.Math.requireSomeUint, uint248Max, ONE]

/--
Before expiry, `redeemPY` burns the same amount from PT and YT, so it preserves
the supply-pairing invariant on the successful path.
-/
theorem redeem_py_pre_expiry_preserves_supply_pairing
    (receiver : Address) (s : ContractState)
    (hNotExpired : s.storage 8 = 0)
    (hSelf : (s.thisAddress != zeroAddress) = true)
    (hPtBalanceEnough : s.storageMap 3 s.thisAddress >= redeemPYAmountOf s)
    (hYtBalanceEnough : s.storageMap 2 s.thisAddress >= redeemPYAmountOf s)
    (hPtSupplyEnough : s.storage 1 >= redeemPYAmountOf s)
    (hYtSupplyEnough : s.storage 0 >= redeemPYAmountOf s)
    (hRedeemUint248 : redeemPYAmountOf s <= uint248Max)
    (hIndexNonzero : (currentIndexOf s != 0) = true)
    (hRedeemMulNoOverflow :
      (redeemPYAmountOf s : Nat) * (ONE : Nat) <= Verity.Stdlib.Math.MAX_UINT256) :
    let s' := ((PendlePY.redeemPY receiver).run s).snd
    redeem_py_pre_expiry_preserves_supply_pairing_spec s s' := by
  dsimp
  have hExact :=
    redeem_py_pre_expiry_burns_equal_amount receiver s hNotExpired hSelf hPtBalanceEnough
      hYtBalanceEnough hPtSupplyEnough hYtSupplyEnough hRedeemUint248 hIndexNonzero
      hRedeemMulNoOverflow
  unfold redeem_py_pre_expiry_preserves_supply_pairing_spec supplyPairing
  intro _hExpired hPair
  have hBurn := hExact hNotExpired
  rw [hBurn.1, hBurn.2.1, hPair]

end Benchmark.Cases.Pendle.PySupplyPairing

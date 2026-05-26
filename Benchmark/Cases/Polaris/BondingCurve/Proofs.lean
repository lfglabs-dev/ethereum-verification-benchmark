import Benchmark.Cases.Polaris.BondingCurve.Specs

namespace Benchmark.Cases.Polaris.BondingCurve

open Verity
open Verity.EVM.Uint256

/--
  Axiom terminal result for the initialization transition.

  Statement assumed:
  if `floorSupply_ != 0`, `floorSupply_ <= virtualSupply_`, helper outputs are
  exactly `_getBalanceFromReserveRatio`, and Solidity checked arithmetic
  succeeds, then `init` writes:
  - `virtualBalance = curveBalance virtualSupply_`
  - `floorBalance = curveBalance floorSupply_`
  - `totalSupply = virtualSupply_ - floorSupply_`

  This is exactly the source sequence in `BaseBondingCurve.init`, modulo the
  documented `curveBalance` abstraction for `_getBalanceFromReserveRatio`.
  The remaining mechanical gap is Lean normalization of Verity storage writes
  plus `floorSupply + (virtualSupply - floorSupply) = virtualSupply` under
  Uint256 successful-path arithmetic.
-/
axiom init_reserve_ratio_zero
    (virtualSupply_ floorSupply_ computedVirtualBalance computedFloorBalance : Uint256)
    (s : ContractState)
    (hFloorNonZero : floorSupply_ != 0)
    (hFloorLeVirtual : floorSupply_ <= virtualSupply_)
    (hComputedVirtual : computedVirtualBalance = curveBalance virtualSupply_)
    (hComputedFloor : computedFloorBalance = curveBalance floorSupply_) :
    let s' :=
      ((BaseBondingCurve.init
        virtualSupply_ floorSupply_ computedVirtualBalance computedFloorBalance).run s).snd
    init_reserve_ratio_zero_spec s s'

/--
  Axiom terminal result for `buy`.

  Statement assumed:
  on the initialized successful path, with the nonzero amount guard satisfied,
  helper output tied to `_getBalanceFromReserveRatio`, and no overflow in the
  source-level supply additions, `buy` increases aggregate pETH supply by the
  requested net amount plus the pETH fee and writes `virtualBalance` to the
  curve balance of the resulting `virtualSupply`. `floorSupply` and
  `floorBalance` are unchanged.

  This matches `BaseBondingCurve.buy`: callers other than the fee router mint fee
  tokens to the fee router, while the fee-router path pays no fee.
-/
axiom buy_preserves_reserve_ratio_zero
    (isFeeRouter : Bool) (bcTokenAmount buyFeeAmount computedNewVirtualBalance : Uint256)
    (s : ContractState)
    (hInitialized : initializedOf s = 1)
    (hAmountNonZero : bcTokenAmount != 0)
    (hFeeAmount :
      buyFeeAmount =
        if isFeeRouter then
          0
        else
          div (mul bcTokenAmount (feePercentageOf s)) (sub decimalPrecision (feePercentageOf s)))
    (hComputedNewVirtual :
      computedNewVirtualBalance =
        curveBalance
          (add (add (floorSupplyOf s) (totalSupplyOf s))
            (add bcTokenAmount buyFeeAmount)))
    (hOldSupplyNoOverflow :
      (floorSupplyOf s).val + (totalSupplyOf s).val < Verity.Core.Uint256.modulus)
    (hMintNoOverflow :
      bcTokenAmount.val + buyFeeAmount.val < Verity.Core.Uint256.modulus)
    (hSupplyMintNoOverflow :
      (add (floorSupplyOf s) (totalSupplyOf s)).val +
        (add bcTokenAmount buyFeeAmount).val <
          Verity.Core.Uint256.modulus)
    (hTotalSupplyMintNoOverflow :
      (totalSupplyOf s).val +
        (add bcTokenAmount buyFeeAmount).val <
          Verity.Core.Uint256.modulus) :
    let s' :=
      ((BaseBondingCurve.buy
        isFeeRouter bcTokenAmount buyFeeAmount computedNewVirtualBalance).run s).snd
    buy_preserves_reserve_ratio_zero_spec s s'

/--
  Axiom terminal result for `sell`.

  Statement assumed:
  on the successful path, where the net nonzero amount guard is satisfied, the
  sell fee and net burn are well-defined, helper output is tied to
  `_getBalanceFromReserveRatio`, and the net burn is within supply, `sell`
  decreases `virtualSupply` by the net pETH amount and writes `virtualBalance`
  to the curve balance of the resulting supply. The pETH fee is transferred to
  the fee router and does not reduce `totalSupply`, matching the Solidity source.
-/
axiom sell_preserves_reserve_ratio_zero
    (bcTokenAmount computedNewVirtualBalance : Uint256) (s : ContractState)
    (hNetAmountNonZero :
      sub bcTokenAmount (div (mul bcTokenAmount (feePercentageOf s)) decimalPrecision) != 0)
    (hComputedNewVirtual :
      computedNewVirtualBalance =
        curveBalance
          (sub (add (floorSupplyOf s) (totalSupplyOf s))
            (sub bcTokenAmount (div (mul bcTokenAmount (feePercentageOf s)) decimalPrecision))))
    (hOldSupplyNoOverflow :
      (floorSupplyOf s).val + (totalSupplyOf s).val < Verity.Core.Uint256.modulus)
    (hNetLeOldSupply :
      sub bcTokenAmount (div (mul bcTokenAmount (feePercentageOf s)) decimalPrecision) <=
        add (floorSupplyOf s) (totalSupplyOf s))
    (hNetLeTotalSupply :
      sub bcTokenAmount (div (mul bcTokenAmount (feePercentageOf s)) decimalPrecision) <= totalSupplyOf s)
    (hNetValLeOldSupply :
      (sub bcTokenAmount (div (mul bcTokenAmount (feePercentageOf s)) decimalPrecision)).val <=
        (add (floorSupplyOf s) (totalSupplyOf s)).val)
    (hNetValLeTotalSupply :
      (sub bcTokenAmount (div (mul bcTokenAmount (feePercentageOf s)) decimalPrecision)).val <=
        (totalSupplyOf s).val) :
    let s' := ((BaseBondingCurve.sell bcTokenAmount computedNewVirtualBalance).run s).snd
    sell_preserves_reserve_ratio_zero_spec s s'

/--
  Axiom terminal result for `floorSellAndBurn`.

  Statement assumed:
  on the authorized fee-router successful path, a nonzero burn increases
  `floorSupply` by the burned amount, decreases aggregate pETH supply by that
  same amount, and writes `floorBalance` to the curve balance of the new floor
  point.
  This is the source transition that treats fee burns as supply-changing events
  while preserving the reserve-ratio equation.
-/
axiom floorSellAndBurn_preserves_reserve_ratio_zero
    (authorizedFeeRouter : Bool) (bcTokenAmount computedNewFloorBalance : Uint256)
    (s : ContractState)
    (hAuthorized : authorizedFeeRouter = true)
    (hAmountNonZero : bcTokenAmount != 0)
    (hComputedNewFloor :
      computedNewFloorBalance = curveBalance (add (floorSupplyOf s) bcTokenAmount))
    (hOldSupplyNoOverflow :
      (floorSupplyOf s).val + (totalSupplyOf s).val < Verity.Core.Uint256.modulus)
    (hNewFloorNoOverflow :
      (floorSupplyOf s).val + bcTokenAmount.val < Verity.Core.Uint256.modulus)
    (hNewFloorLeOldSupply :
      add (floorSupplyOf s) bcTokenAmount <= add (floorSupplyOf s) (totalSupplyOf s))
    (hBurnLeTotalSupply : bcTokenAmount <= totalSupplyOf s)
    (hBurnValLeTotalSupply : bcTokenAmount.val <= (totalSupplyOf s).val) :
    let s' :=
      ((BaseBondingCurve.floorSellAndBurn
        authorizedFeeRouter bcTokenAmount computedNewFloorBalance).run s).snd
    floorSellAndBurn_preserves_reserve_ratio_zero_spec s s'

end Benchmark.Cases.Polaris.BondingCurve

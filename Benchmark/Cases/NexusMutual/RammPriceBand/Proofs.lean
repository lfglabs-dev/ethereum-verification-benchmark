import Benchmark.Cases.NexusMutual.RammPriceBand.Specs
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Cases.NexusMutual.RammPriceBand

set_option maxRecDepth 1000000

open Verity
open Verity.EVM.Uint256

private theorem syncPriceBand_slot_write
    (capital_ supply_ : Uint256) (s : ContractState)
    (hSupply : supply_ != 0) :
    let s' := ((RammPriceBand.syncPriceBand capital_ supply_).run s).snd
    s'.storage 0 = capital_ ∧
    s'.storage 2 = div (mul 1000000000000000000 capital_) supply_ ∧
    s'.storage 3 = div (mul (div (mul 1000000000000000000 capital_) supply_) 10100) 10000 ∧
    s'.storage 4 = div (mul (div (mul 1000000000000000000 capital_) supply_) 9900) 10000 := by
  repeat' constructor
  all_goals
    simp [RammPriceBand.syncPriceBand, hSupply, RammPriceBand.capital, RammPriceBand.supply,
      RammPriceBand.bookValue, RammPriceBand.buySpotPrice, RammPriceBand.sellSpotPrice,
      Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd, setStorage]

/--
Executing `syncPriceBand` stores the provided capital value.
-/
theorem syncPriceBand_sets_capital_main
    (capital_ supply_ : Uint256) (s : ContractState)
    (hSupply : supply_ != 0) :
    let s' := ((RammPriceBand.syncPriceBand capital_ supply_).run s).snd
    syncPriceBand_sets_capital_spec capital_ s s' := by
  simpa [syncPriceBand_sets_capital_spec] using (syncPriceBand_slot_write capital_ supply_ s hSupply).1

/--
Executing `syncPriceBand` stores the synchronized book value.
-/
theorem syncPriceBand_sets_book_value_main
    (capital_ supply_ : Uint256) (s : ContractState)
    (hSupply : supply_ != 0) :
    let s' := ((RammPriceBand.syncPriceBand capital_ supply_).run s).snd
    syncPriceBand_sets_book_value_spec capital_ supply_ s s' := by
  simpa [syncPriceBand_sets_book_value_spec] using (syncPriceBand_slot_write capital_ supply_ s hSupply).2.1

/--
Executing `syncPriceBand` stores the synchronized buy quote.
-/
theorem syncPriceBand_sets_buy_price_main
    (capital_ supply_ : Uint256) (s : ContractState)
    (hSupply : supply_ != 0) :
    let s' := ((RammPriceBand.syncPriceBand capital_ supply_).run s).snd
    syncPriceBand_sets_buy_price_spec capital_ supply_ s s' := by
  simpa [syncPriceBand_sets_buy_price_spec] using (syncPriceBand_slot_write capital_ supply_ s hSupply).2.2.1

/--
Executing `syncPriceBand` stores the synchronized sell quote.
-/
theorem syncPriceBand_sets_sell_price_main
    (capital_ supply_ : Uint256) (s : ContractState)
    (hSupply : supply_ != 0) :
    let s' := ((RammPriceBand.syncPriceBand capital_ supply_).run s).snd
    syncPriceBand_sets_sell_price_spec capital_ supply_ s s' := by
  simpa [syncPriceBand_sets_sell_price_spec] using (syncPriceBand_slot_write capital_ supply_ s hSupply).2.2.2

-- Reference-solution aliases (names expected by task manifests)
abbrev syncPriceBand_sets_capital := @syncPriceBand_sets_capital_main
abbrev syncPriceBand_sets_book_value := @syncPriceBand_sets_book_value_main
abbrev syncPriceBand_sets_buy_price := @syncPriceBand_sets_buy_price_main
abbrev syncPriceBand_sets_sell_price := @syncPriceBand_sets_sell_price_main

/--
The sell spot price never exceeds the buy spot price,
provided the book-value multiplication does not overflow.
-/
private theorem div_mul_le_div_mul (bv : Uint256)
    (hNoOverflow : bv.val * 10100 < modulus) :
    div (mul bv 9900) 10000 ≤ div (mul bv 10100) 10000 := by
  -- Work at Nat level
  show (div (mul bv 9900) 10000).val ≤ (div (mul bv 10100) 10000).val
  -- mul doesn't overflow
  have hMul9900Lt : bv.val * 9900 < modulus :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_left bv.val (by omega : (9900 : Nat) ≤ 10100)) hNoOverflow
  have hMul9900 : (mul bv (9900 : Uint256)).val = bv.val * 9900 := by
    simp [HMul.hMul, Verity.Core.Uint256.mul, Verity.Core.Uint256.ofNat]
    exact Nat.mod_eq_of_lt hMul9900Lt
  have hMul10100 : (mul bv (10100 : Uint256)).val = bv.val * 10100 := by
    simp [HMul.hMul, Verity.Core.Uint256.mul, Verity.Core.Uint256.ofNat]
    exact Nat.mod_eq_of_lt hNoOverflow
  -- Expand div at Uint256 level
  simp only [HDiv.hDiv, Verity.Core.Uint256.div, hMul9900, hMul10100,
    show (10000 : Uint256).val ≠ 0 from by decide, ↓reduceIte,
    Verity.Core.Uint256.val_ofNat, Verity.Core.Uint256.modulus]
  -- Goal: Div.div (a) 10k % 2^256 ≤ Div.div (b) 10k % 2^256
  have h10kval : Verity.Core.Uint256.val (10000 : Uint256) = 10000 := by decide
  simp only [h10kval, Verity.Core.UINT256_MODULUS]
  -- Both quotients are < 2^256, so % is identity
  have h9900Lt : bv.val * 9900 / 10000 < 2 ^ 256 := by
    have : bv.val * 9900 / 10000 ≤ bv.val * 9900 := Nat.div_le_self _ _
    simp [modulus, Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] at hMul9900Lt
    omega
  have h10100Lt : bv.val * 10100 / 10000 < 2 ^ 256 := by
    have : bv.val * 10100 / 10000 ≤ bv.val * 10100 := Nat.div_le_self _ _
    simp [modulus, Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] at hNoOverflow
    omega
  -- Use show to normalize Div.div to / notation for rw to work
  show bv.val * 9900 / 10000 % 2 ^ 256 ≤ bv.val * 10100 / 10000 % 2 ^ 256
  rw [Nat.mod_eq_of_lt h9900Lt, Nat.mod_eq_of_lt h10100Lt]
  exact Nat.div_le_div_right (by omega : bv.val * 9900 ≤ bv.val * 10100)

theorem syncPriceBand_sell_le_buy
    (capital_ supply_ : Uint256) (s : ContractState)
    (hSupply : supply_ != 0)
    (hNoOverflow : (div (mul 1000000000000000000 capital_) supply_).val * 10100 < modulus) :
    let s' := ((RammPriceBand.syncPriceBand capital_ supply_).run s).snd
    syncPriceBand_sell_le_buy_spec s s' := by
  have hw := syncPriceBand_slot_write capital_ supply_ s hSupply
  simp only [syncPriceBand_sell_le_buy_spec, hw.2.2.2, hw.2.2.1]
  exact div_mul_le_div_mul _ hNoOverflow

end Benchmark.Cases.NexusMutual.RammPriceBand

namespace Benchmark.Cases.NexusMutual.RammSpotPrice

open Verity
open Verity.EVM.Uint256

private def buyScaledNat (eth oldEth oldNxmBuyReserve : Uint256) : Nat :=
  oldNxmBuyReserve.val * eth.val / oldEth.val

private def sellScaledNat (eth oldEth oldNxmSellReserve : Uint256) : Nat :=
  oldNxmSellReserve.val * eth.val / oldEth.val

private def buyBufferedNat (capital : Uint256) : Nat :=
  capital.val * 10100 / 10000

private def sellBufferedNat (capital : Uint256) : Nat :=
  capital.val * 9900 / 10000

private def buyRatchetTermNat
    (eth oldEth oldNxmBuyReserve capital supply elapsed speed : Uint256) : Nat :=
  capital.val * buyScaledNat eth oldEth oldNxmBuyReserve * elapsed.val * speed.val /
    supply.val / RATCHET_PERIOD.val / RATCHET_DENOMINATOR.val

private def sellRatchetTermNat
    (eth oldEth oldNxmSellReserve capital supply elapsed speed : Uint256) : Nat :=
  capital.val * sellScaledNat eth oldEth oldNxmSellReserve * elapsed.val * speed.val /
    supply.val / RATCHET_PERIOD.val / RATCHET_DENOMINATOR.val

private def buyRatchetExtraNat
    (eth oldEth oldNxmBuyReserve capital elapsed speed : Uint256) : Nat :=
  buyBufferedNat capital * buyScaledNat eth oldEth oldNxmBuyReserve * elapsed.val * speed.val /
    RATCHET_PERIOD.val / RATCHET_DENOMINATOR.val

private def sellRatchetExtraNat
    (eth oldEth oldNxmSellReserve capital elapsed speed : Uint256) : Nat :=
  capital.val * sellScaledNat eth oldEth oldNxmSellReserve * elapsed.val * speed.val /
    RATCHET_PERIOD.val / RATCHET_DENOMINATOR.val

def buyArithmeticSafe
    (eth oldEth oldNxmBuyReserve capital supply elapsed speed : Uint256) : Prop :=
  ONE_ETHER.val * eth.val < modulus ∧
  ONE_ETHER.val * capital.val < modulus ∧
  oldNxmBuyReserve.val * eth.val < modulus ∧
  capital.val * 10100 < modulus ∧
  eth.val * supply.val < modulus ∧
  buyBufferedNat capital * buyScaledNat eth oldEth oldNxmBuyReserve < modulus ∧
  capital.val * buyScaledNat eth oldEth oldNxmBuyReserve < modulus ∧
  capital.val * buyScaledNat eth oldEth oldNxmBuyReserve * elapsed.val < modulus ∧
  capital.val * buyScaledNat eth oldEth oldNxmBuyReserve * elapsed.val * speed.val < modulus ∧
  buyBufferedNat capital * buyScaledNat eth oldEth oldNxmBuyReserve * elapsed.val < modulus ∧
  buyBufferedNat capital * buyScaledNat eth oldEth oldNxmBuyReserve * elapsed.val * speed.val < modulus ∧
  buyBufferedNat capital * buyScaledNat eth oldEth oldNxmBuyReserve +
      buyRatchetExtraNat eth oldEth oldNxmBuyReserve capital elapsed speed < modulus

def sellArithmeticSafe
    (eth oldEth oldNxmSellReserve capital supply elapsed speed : Uint256) : Prop :=
  ONE_ETHER.val * eth.val < modulus ∧
  ONE_ETHER.val * capital.val < modulus ∧
  oldNxmSellReserve.val * eth.val < modulus ∧
  capital.val * 9900 < modulus ∧
  eth.val * supply.val < modulus ∧
  eth.val * sellScaledNat eth oldEth oldNxmSellReserve < modulus ∧
  sellBufferedNat capital * sellScaledNat eth oldEth oldNxmSellReserve < modulus ∧
  capital.val * sellScaledNat eth oldEth oldNxmSellReserve < modulus ∧
  capital.val * sellScaledNat eth oldEth oldNxmSellReserve * elapsed.val < modulus ∧
  capital.val * sellScaledNat eth oldEth oldNxmSellReserve * elapsed.val * speed.val < modulus ∧
  eth.val * supply.val + sellRatchetExtraNat eth oldEth oldNxmSellReserve capital elapsed speed < modulus ∧
  eth.val + sellRatchetTermNat eth oldEth oldNxmSellReserve capital supply elapsed speed < modulus

def realisticSellScale (eth capital supply : Uint256) : Prop :=
  100 ≤ capital.val ∧ 99 ≤ eth.val * supply.val / capital.val

private theorem div_val_eq (a b : Uint256) (hb : b != 0) :
    (div a b).val = a.val / b.val := by
  have hb' : b ≠ 0 := by
    simpa using hb
  have hbval : b.val ≠ 0 := by
    intro h
    apply hb'
    apply Verity.Core.Uint256.ext
    simpa [Verity.Core.Uint256.val_zero] using h
  simp [HDiv.hDiv, Verity.Core.Uint256.div, hbval, Verity.Core.Uint256.ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt)

private theorem val_pos_of_ne_zero (a : Uint256) (ha : a != 0) :
    0 < a.val := by
  have ha' : a ≠ 0 := by
    simpa using ha
  have hne : a.val ≠ 0 := by
    intro h
    apply ha'
    apply Verity.Core.Uint256.ext
    simpa [Verity.Core.Uint256.val_zero] using h
  exact Nat.pos_of_ne_zero hne

private theorem ne_zero_of_val_ne_zero (a : Uint256) (ha : a.val ≠ 0) :
    a != 0 := by
  have ha' : a ≠ 0 := by
    intro hZero
    apply ha
    simpa [Verity.Core.Uint256.val_zero] using congrArg Verity.Core.Uint256.val hZero
  simpa using ha'

private theorem mul_val_eq (a b : Uint256) (h : a.val * b.val < modulus) :
    (mul a b).val = a.val * b.val := by
  simp [HMul.hMul, Verity.Core.Uint256.mul, Verity.Core.Uint256.ofNat]
  exact Nat.mod_eq_of_lt h

private theorem add_val_eq (a b : Uint256) (h : a.val + b.val < modulus) :
    (add a b).val = a.val + b.val := by
  simp [HAdd.hAdd, Verity.Core.Uint256.add, Verity.Core.Uint256.ofNat]
  exact Nat.mod_eq_of_lt h

private theorem mul_val_le (a b : Uint256) :
    (mul a b).val ≤ a.val * b.val := by
  simp [HMul.hMul, Verity.Core.Uint256.mul, Verity.Core.Uint256.ofNat]
  exact Nat.mod_le _ _

private theorem mul3_val_eq
    (a b c : Uint256)
    (hAB : a.val * b.val < modulus)
    (hABC : a.val * b.val * c.val < modulus) :
    (mul (mul a b) c).val = a.val * b.val * c.val := by
  have hMulAB : (mul a b).val = a.val * b.val := mul_val_eq a b hAB
  have hMulABC : (mul (mul a b) c).val = (mul a b).val * c.val := by
    apply mul_val_eq
    simpa [hMulAB, Nat.mul_assoc] using hABC
  simpa [hMulAB, Nat.mul_assoc] using hMulABC

private theorem mul4_val_eq
    (a b c d : Uint256)
    (hAB : a.val * b.val < modulus)
    (hABC : a.val * b.val * c.val < modulus)
    (hABCD : a.val * b.val * c.val * d.val < modulus) :
    (mul (mul (mul a b) c) d).val = a.val * b.val * c.val * d.val := by
  have hMulABC : (mul (mul a b) c).val = a.val * b.val * c.val :=
    mul3_val_eq a b c hAB hABC
  have hMulABCD : (mul (mul (mul a b) c) d).val = (mul (mul a b) c).val * d.val := by
    apply mul_val_eq
    simpa [hMulABC, Nat.mul_assoc] using hABCD
  simpa [hMulABC, Nat.mul_assoc] using hMulABCD

private theorem buy_buffered_ge_cap (capital : Nat) :
    capital ≤ capital * 10100 / 10000 := by
  have h : capital * 10000 ≤ capital * 10100 := by omega
  exact (Nat.le_div_iff_mul_le (by decide : 0 < 10000)).2 (by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h)

private theorem sell_buffered_gap (capital : Nat) :
    capital ≤ 100 * (capital - capital * 9900 / 10000) := by
  let buffered := capital * 9900 / 10000
  have hBuffered : buffered * 10000 ≤ capital * 9900 := by
    simpa [buffered] using Nat.div_mul_le_self (capital * 9900) 10000
  omega

private theorem sell_buffered_pos (capital : Nat) (hCapital : 100 ≤ capital) :
    0 < capital * 9900 / 10000 := by
  have hOne : 1 ≤ capital * 9900 / 10000 := by
    refine (Nat.le_div_iff_mul_le (by decide : 0 < 10000)).2 ?_
    omega
  omega

private theorem sell_bv_reserve_ge_book_reserve_succ
    (eth supply capital : Nat)
    (hCapital : 100 ≤ capital)
    (hScale : 99 ≤ eth * supply / capital) :
    eth * supply / (capital * 9900 / 10000) ≥ eth * supply / capital + 1 := by
  let a := eth * supply
  let q := a / capital
  let r := a % capital
  let buffered := capital * 9900 / 10000
  have hBufferedPos : 0 < buffered := by
    simpa [buffered] using sell_buffered_pos capital hCapital
  have ha : a = capital * q + r := by
    simpa [a, q, r, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (Nat.div_add_mod a capital).symm
  have hGap99 : buffered ≤ 99 * (capital - buffered) := by
    have hGap := sell_buffered_gap capital
    omega
  have hScale' : 99 ≤ q := by
    simpa [a, q] using hScale
  have hBufferedLeCapital : buffered ≤ capital := by
    dsimp [buffered]
    have : capital * 9900 / 10000 ≤ capital * 9900 := Nat.div_le_self _ _
    omega
  have hMulGap : 99 * (capital - buffered) ≤ q * (capital - buffered) := by
    exact Nat.mul_le_mul_right _ hScale'
  have hBufferedLe : buffered ≤ q * (capital - buffered) := Nat.le_trans hGap99 hMulGap
  have hMain : buffered * (q + 1) ≤ a := by
    calc
      buffered * (q + 1) = buffered * q + buffered := by rw [Nat.mul_add, Nat.mul_one]
      _ ≤ buffered * q + q * (capital - buffered) := by
          exact Nat.add_le_add_left hBufferedLe _
      _ = capital * q := by
          rw [Nat.mul_comm buffered q, ← Nat.mul_add]
          rw [Nat.add_comm buffered (capital - buffered), Nat.sub_add_cancel hBufferedLeCapital]
          rw [Nat.mul_comm]
      _ ≤ capital * q + r := Nat.le_add_right _ _
      _ = a := by simpa [ha] using ha.symm
  exact (Nat.le_div_iff_mul_le hBufferedPos).2 <| by
    simpa [a, q, buffered, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hMain

private theorem buy_price_ge_book_value_nat
    (eth supply capital reserve : Nat)
    (hSupply : 0 < supply)
    (hReserve : 0 < reserve)
    (hReserveBound : reserve * capital ≤ eth * supply) :
    ONE_ETHER.val * capital / supply ≤ ONE_ETHER.val * eth / reserve := by
  let bv := ONE_ETHER.val * capital / supply
  have hBvMul : bv * supply ≤ ONE_ETHER.val * capital := by
    simpa [bv, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      Nat.div_mul_le_self (ONE_ETHER.val * capital) supply
  have hReserveBound' : reserve * (ONE_ETHER.val * capital) ≤ (ONE_ETHER.val * eth) * supply := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      Nat.mul_le_mul_left ONE_ETHER.val hReserveBound
  have hCombined : bv * reserve * supply ≤ (ONE_ETHER.val * eth) * supply := by
    calc
      bv * reserve * supply = reserve * (bv * supply) := by
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ reserve * (ONE_ETHER.val * capital) := by
          exact Nat.mul_le_mul_left _ hBvMul
      _ ≤ (ONE_ETHER.val * eth) * supply := hReserveBound'
  have hCancel := Nat.le_of_mul_le_mul_right hCombined hSupply
  exact (Nat.le_div_iff_mul_le hReserve).2 <| by
    simpa [bv, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hCancel

private theorem sell_price_le_book_value_nat
    (eth supply capital reserve : Nat)
    (hSupply : 0 < supply)
    (hReserve : 0 < reserve)
    (hReserveBound : eth * supply < reserve * capital) :
    ONE_ETHER.val * eth / reserve ≤ ONE_ETHER.val * capital / supply := by
  let bv := ONE_ETHER.val * capital / supply
  have hOnePos : 0 < ONE_ETHER.val := by decide
  have hBvSucc : ONE_ETHER.val * capital < (bv + 1) * supply := by
    exact (Nat.div_lt_iff_lt_mul hSupply).1 (Nat.lt_succ_self _)
  have hReserveBound' : (ONE_ETHER.val * eth) * supply < reserve * (ONE_ETHER.val * capital) := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      Nat.mul_lt_mul_of_pos_left hReserveBound hOnePos
  have hCombined : (ONE_ETHER.val * eth) * supply < (bv + 1) * reserve * supply := by
    calc
      (ONE_ETHER.val * eth) * supply < reserve * (ONE_ETHER.val * capital) := hReserveBound'
      _ < reserve * ((bv + 1) * supply) := by
          exact Nat.mul_lt_mul_of_pos_left hBvSucc hReserve
      _ = (bv + 1) * reserve * supply := by
          simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hCancel : ONE_ETHER.val * eth < (bv + 1) * reserve := by
    exact Nat.lt_of_mul_lt_mul_right hCombined
  have hDivLt : ONE_ETHER.val * eth / reserve < bv + 1 := by
    exact (Nat.div_lt_iff_lt_mul hReserve).2 <| by
      simpa [bv, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hCancel
  exact Nat.le_of_lt_succ hDivLt

private theorem div_le_div_of_mul_le_mul
    (num denom target targetDenom : Nat)
    (hDenom : 0 < denom)
    (hTargetDenom : 0 < targetDenom)
    (hCross : num * targetDenom ≤ target * denom) :
    num / denom ≤ target / targetDenom := by
  refine (Nat.le_div_iff_mul_le hTargetDenom).2 ?_
  have hBound : ((num / denom) * targetDenom) * denom ≤ target * denom := by
    calc
      ((num / denom) * targetDenom) * denom = (num / denom * denom) * targetDenom := by
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ num * targetDenom := by
          exact Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)
      _ ≤ target * denom := hCross
  exact Nat.le_of_mul_le_mul_right hBound hDenom

private theorem div_le_div_of_mul_le_mul'
    (targetNum targetDenom num denom : Nat)
    (hDenom : 0 < denom)
    (hTargetDenom : 0 < targetDenom)
    (hCross : targetNum * denom ≤ num * targetDenom) :
    targetNum / targetDenom ≤ num / denom := by
  exact div_le_div_of_mul_le_mul targetNum targetDenom num denom hTargetDenom hDenom <| by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hCross

private theorem lt_mul_of_div_succ_le
    (a b c : Nat)
    (hC : 0 < c)
    (h : a / c + 1 ≤ b) :
    a < b * c := by
  let q := a / c
  let r := a % c
  have hEuclid : a = q * c + r := by
    simpa [q, r, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (Nat.div_add_mod a c).symm
  have hRem : r < c := Nat.mod_lt _ hC
  have hq : q + 1 ≤ b := by simpa [q] using h
  calc
    a = q * c + r := hEuclid
    _ < q * c + c := by exact Nat.add_lt_add_left hRem _
    _ = (q + 1) * c := by
        calc
          q * c + c = q * c + 1 * c := by simp
          _ = (q + 1) * c := by rw [Nat.add_mul]
    _ ≤ b * c := Nat.mul_le_mul_right _ hq

private theorem scaled_ratchet_term_mul_le_extra_nat
    (numerator supply : Nat)
    (hSupply : 0 < supply) :
    supply * (numerator / supply / RATCHET_PERIOD.val / RATCHET_DENOMINATOR.val) ≤
      numerator / RATCHET_PERIOD.val / RATCHET_DENOMINATOR.val := by
  have hReassoc :
      numerator / supply / RATCHET_PERIOD.val / RATCHET_DENOMINATOR.val =
        (numerator / RATCHET_PERIOD.val / RATCHET_DENOMINATOR.val) / supply := by
    calc
      numerator / supply / RATCHET_PERIOD.val / RATCHET_DENOMINATOR.val
          = numerator / (supply * (RATCHET_PERIOD.val * RATCHET_DENOMINATOR.val)) := by
              rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
      _ = numerator / ((RATCHET_PERIOD.val * RATCHET_DENOMINATOR.val) * supply) := by
            simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      _ = (numerator / RATCHET_PERIOD.val / RATCHET_DENOMINATOR.val) / supply := by
            rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
            congr 1
            rw [Nat.mul_assoc]
  rw [hReassoc]
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    Nat.div_mul_le_self (numerator / RATCHET_PERIOD.val / RATCHET_DENOMINATOR.val) supply

private theorem buy_ratchet_extra_ge_supply_term_nat
    (capital buffered scaled elapsed speed supply : Nat)
    (hSupply : 0 < supply)
    (hBuffered : capital ≤ buffered) :
    supply * (capital * scaled * elapsed * speed / supply / RATCHET_PERIOD.val / RATCHET_DENOMINATOR.val) ≤
      buffered * scaled * elapsed * speed / RATCHET_PERIOD.val / RATCHET_DENOMINATOR.val := by
  have hScaleMul :
      capital * scaled * elapsed * speed ≤ buffered * scaled * elapsed * speed := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      Nat.mul_le_mul_right (scaled * elapsed * speed) hBuffered
  calc
    supply * (capital * scaled * elapsed * speed / supply / RATCHET_PERIOD.val / RATCHET_DENOMINATOR.val)
      ≤ capital * scaled * elapsed * speed / RATCHET_PERIOD.val / RATCHET_DENOMINATOR.val := by
          exact scaled_ratchet_term_mul_le_extra_nat (capital * scaled * elapsed * speed) supply hSupply
    _ ≤ buffered * scaled * elapsed * speed / RATCHET_PERIOD.val / RATCHET_DENOMINATOR.val := by
        have hDiv1 :
            capital * scaled * elapsed * speed / RATCHET_PERIOD.val ≤
              buffered * scaled * elapsed * speed / RATCHET_PERIOD.val :=
          Nat.div_le_div_right hScaleMul
        exact Nat.div_le_div_right hDiv1

private theorem sell_ratchet_extra_ge_supply_term_nat
    (capital scaled elapsed speed supply : Nat)
    (hSupply : 0 < supply) :
    supply * (capital * scaled * elapsed * speed / supply / RATCHET_PERIOD.val / RATCHET_DENOMINATOR.val) ≤
      capital * scaled * elapsed * speed / RATCHET_PERIOD.val / RATCHET_DENOMINATOR.val := by
  exact scaled_ratchet_term_mul_le_extra_nat (capital * scaled * elapsed * speed) supply hSupply

private theorem buy_scaled_val
    (eth oldEth oldNxmBuyReserve capital supply elapsed speed : Uint256)
    (hOldEth : oldEth != 0)
    (hSafe : buyArithmeticSafe eth oldEth oldNxmBuyReserve capital supply elapsed speed) :
    (div (mul oldNxmBuyReserve eth) oldEth).val = buyScaledNat eth oldEth oldNxmBuyReserve := by
  rcases hSafe with ⟨_, _, hMul, _, _, _, _, _, _, _, _, _⟩
  rw [div_val_eq _ _ hOldEth, mul_val_eq _ _ hMul]
  rfl

private theorem sell_scaled_val
    (eth oldEth oldNxmSellReserve capital supply elapsed speed : Uint256)
    (hOldEth : oldEth != 0)
    (hSafe : sellArithmeticSafe eth oldEth oldNxmSellReserve capital supply elapsed speed) :
    (div (mul oldNxmSellReserve eth) oldEth).val = sellScaledNat eth oldEth oldNxmSellReserve := by
  rcases hSafe with ⟨_, _, hMul, _, _, _, _, _, _, _, _, _⟩
  rw [div_val_eq _ _ hOldEth, mul_val_eq _ _ hMul]
  rfl

private theorem buy_buffered_val
    (eth oldEth oldNxmBuyReserve capital supply elapsed speed : Uint256)
    (hSafe : buyArithmeticSafe eth oldEth oldNxmBuyReserve capital supply elapsed speed) :
    (div (mul capital (add PRICE_BUFFER_DENOMINATOR PRICE_BUFFER)) PRICE_BUFFER_DENOMINATOR).val =
      buyBufferedNat capital := by
  rcases hSafe with ⟨_, _, _, hMul, _, _, _, _, _, _, _, _⟩
  have hAddVal : (add PRICE_BUFFER_DENOMINATOR PRICE_BUFFER).val = 10100 := by decide
  have hMul' : capital.val * (add PRICE_BUFFER_DENOMINATOR PRICE_BUFFER).val < modulus := by
    simpa [hAddVal] using hMul
  rw [div_val_eq _ _ (by decide : PRICE_BUFFER_DENOMINATOR != 0), mul_val_eq _ _ hMul', hAddVal]
  change capital.val * 10100 / 10000 = buyBufferedNat capital
  rfl

private theorem sell_buffered_val
    (eth oldEth oldNxmSellReserve capital supply elapsed speed : Uint256)
    (hSafe : sellArithmeticSafe eth oldEth oldNxmSellReserve capital supply elapsed speed) :
    (div (mul capital (sub PRICE_BUFFER_DENOMINATOR PRICE_BUFFER)) PRICE_BUFFER_DENOMINATOR).val =
      sellBufferedNat capital := by
  rcases hSafe with ⟨_, _, _, hMul, _, _, _, _, _, _, _, _⟩
  have hSubVal : (sub PRICE_BUFFER_DENOMINATOR PRICE_BUFFER).val = 9900 := by decide
  have hMul' : capital.val * (sub PRICE_BUFFER_DENOMINATOR PRICE_BUFFER).val < modulus := by
    simpa [hSubVal] using hMul
  rw [div_val_eq _ _ (by decide : PRICE_BUFFER_DENOMINATOR != 0), mul_val_eq _ _ hMul', hSubVal]
  change capital.val * 9900 / 10000 = sellBufferedNat capital
  rfl

private theorem calculateBuyReserve_le_book_reserve
    (eth oldEth oldNxmBuyReserve capital supply elapsed speed : Uint256)
    (hOldEth : oldEth != 0)
    (hSupply : supply != 0)
    (hCapital : capital != 0)
    (hSafe : buyArithmeticSafe eth oldEth oldNxmBuyReserve capital supply elapsed speed) :
    (calculateBuyReserve eth oldEth oldNxmBuyReserve capital supply elapsed speed).val ≤
      eth.val * supply.val / capital.val := by
  have hSafe' := hSafe
  rcases hSafe with ⟨_, _, _, _, hEthSupply, hBase, hCapScaled, hCapScaledElapsed,
    hCapScaledElapsedSpeed, hBaseElapsed, hBaseElapsedSpeed, hBaseAdd⟩
  have hScaledVal := buy_scaled_val eth oldEth oldNxmBuyReserve capital supply elapsed speed hOldEth hSafe'
  have hBufferedVal := buy_buffered_val eth oldEth oldNxmBuyReserve capital supply elapsed speed hSafe'
  have hEthSupplyVal : (mul eth supply).val = eth.val * supply.val := mul_val_eq eth supply hEthSupply
  have hCapitalPos : 0 < capital.val := val_pos_of_ne_zero capital hCapital
  let scaledReserve := div (mul oldNxmBuyReserve eth) oldEth
  let bufferedCapital := div (mul capital (add PRICE_BUFFER_DENOMINATOR PRICE_BUFFER)) PRICE_BUFFER_DENOMINATOR
  let ratchetTerm := div (div (div (mul (mul (mul capital scaledReserve) elapsed) speed) supply) RATCHET_PERIOD) RATCHET_DENOMINATOR
  let base := mul bufferedCapital scaledReserve
  let ratchetExtra := div (div (mul (mul base elapsed) speed) RATCHET_PERIOD) RATCHET_DENOMINATOR
  have hScaledReserveVal : scaledReserve.val = buyScaledNat eth oldEth oldNxmBuyReserve := by
    simpa [scaledReserve] using hScaledVal
  have hBufferedCapitalVal : bufferedCapital.val = buyBufferedNat capital := by
    simpa [bufferedCapital] using hBufferedVal
  have hBaseOverflow : bufferedCapital.val * scaledReserve.val < modulus := by
    rw [hBufferedCapitalVal, hScaledReserveVal]
    exact hBase
  have hCapScaledOverflow : capital.val * scaledReserve.val < modulus := by
    rw [hScaledReserveVal]
    exact hCapScaled
  have hCapScaledElapsedOverflow : capital.val * scaledReserve.val * elapsed.val < modulus := by
    rw [hScaledReserveVal]
    exact hCapScaledElapsed
  have hCapScaledElapsedSpeedOverflow :
      capital.val * scaledReserve.val * elapsed.val * speed.val < modulus := by
    rw [hScaledReserveVal]
    exact hCapScaledElapsedSpeed
  have hBaseElapsedOverflow : bufferedCapital.val * scaledReserve.val * elapsed.val < modulus := by
    rw [hBufferedCapitalVal, hScaledReserveVal]
    exact hBaseElapsed
  have hBaseElapsedSpeedOverflow :
      bufferedCapital.val * scaledReserve.val * elapsed.val * speed.val < modulus := by
    rw [hBufferedCapitalVal, hScaledReserveVal]
    exact hBaseElapsedSpeed
  have hBaseVal : base.val = buyBufferedNat capital * buyScaledNat eth oldEth oldNxmBuyReserve := by
    dsimp [base]
    rw [mul_val_eq _ _ hBaseOverflow, hBufferedCapitalVal, hScaledReserveVal]
  have hRatchetTermVal : ratchetTerm.val = buyRatchetTermNat eth oldEth oldNxmBuyReserve capital supply elapsed speed := by
    dsimp [ratchetTerm, buyRatchetTermNat]
    rw [div_val_eq _ _ (by decide : RATCHET_DENOMINATOR != 0)]
    rw [div_val_eq _ _ (by decide : RATCHET_PERIOD != 0)]
    rw [div_val_eq _ _ hSupply]
    rw [mul4_val_eq capital scaledReserve elapsed speed
      hCapScaledOverflow hCapScaledElapsedOverflow hCapScaledElapsedSpeedOverflow]
    rw [hScaledReserveVal]
  have hBaseElapsed' : base.val * elapsed.val < modulus := by
    simpa [hBaseVal, Nat.mul_assoc] using hBaseElapsed
  have hBaseElapsedSpeed' : base.val * elapsed.val * speed.val < modulus := by
    simpa [hBaseVal, Nat.mul_assoc] using hBaseElapsedSpeed
  have hRatchetExtraVal : ratchetExtra.val = buyRatchetExtraNat eth oldEth oldNxmBuyReserve capital elapsed speed := by
    dsimp [ratchetExtra, buyRatchetExtraNat]
    rw [div_val_eq _ _ (by decide : RATCHET_DENOMINATOR != 0)]
    rw [div_val_eq _ _ (by decide : RATCHET_PERIOD != 0)]
    rw [mul3_val_eq base elapsed speed hBaseElapsed' hBaseElapsedSpeed']
    rw [hBaseVal]
  by_cases hBranch : add base ratchetExtra > mul eth supply
  · have hBufferedCapitalPos : 0 < bufferedCapital.val := by
      rw [hBufferedCapitalVal]
      exact Nat.lt_of_lt_of_le hCapitalPos (buy_buffered_ge_cap capital.val)
    have hBufferedPos : 0 < buyBufferedNat capital := by
      simpa [hBufferedCapitalVal] using hBufferedCapitalPos
    have hBufferedCapitalNe : bufferedCapital != 0 := by
      exact ne_zero_of_val_ne_zero bufferedCapital (Nat.ne_of_gt hBufferedCapitalPos)
    simp [calculateBuyReserve, scaledReserve, bufferedCapital, base, ratchetExtra, hBranch]
    rw [div_val_eq _ _ hBufferedCapitalNe, hEthSupplyVal, hBufferedCapitalVal]
    exact div_le_div_of_mul_le_mul
      (eth.val * supply.val) (buyBufferedNat capital) (eth.val * supply.val) capital.val
      hBufferedPos hCapitalPos <|
      Nat.mul_le_mul_left _ (buy_buffered_ge_cap capital.val)
  · have hBranchNat : ¬ (mul eth supply).val < (add base ratchetExtra).val := by
      simpa [GT.gt, Verity.Core.Uint256.lt_def] using hBranch
    have hBranchLeRaw : (add base ratchetExtra).val ≤ (mul eth supply).val := Nat.not_lt.mp hBranchNat
    have hBaseAddOverflow : base.val + ratchetExtra.val < modulus := by
      rw [hBaseVal, hRatchetExtraVal]
      exact hBaseAdd
    have hBranchLe :
        buyBufferedNat capital * buyScaledNat eth oldEth oldNxmBuyReserve +
            buyRatchetExtraNat eth oldEth oldNxmBuyReserve capital elapsed speed ≤
          eth.val * supply.val := by
      rw [add_val_eq _ _ hBaseAddOverflow, hBaseVal, hRatchetExtraVal, hEthSupplyVal] at hBranchLeRaw
      exact hBranchLeRaw
    have hSupplyPos : 0 < supply.val := val_pos_of_ne_zero supply hSupply
    have hBufferedScaled :
        capital.val * buyScaledNat eth oldEth oldNxmBuyReserve ≤
          buyBufferedNat capital * buyScaledNat eth oldEth oldNxmBuyReserve := by
      exact Nat.mul_le_mul_right _ (buy_buffered_ge_cap capital.val)
    have hRtLeExtra :
        supply.val * buyRatchetTermNat eth oldEth oldNxmBuyReserve capital supply elapsed speed ≤
          buyRatchetExtraNat eth oldEth oldNxmBuyReserve capital elapsed speed := by
      exact buy_ratchet_extra_ge_supply_term_nat capital.val (buyBufferedNat capital)
        (buyScaledNat eth oldEth oldNxmBuyReserve) elapsed.val speed.val supply.val hSupplyPos
        (buy_buffered_ge_cap capital.val)
    have hCrossSum :
        capital.val * buyScaledNat eth oldEth oldNxmBuyReserve +
            supply.val * buyRatchetTermNat eth oldEth oldNxmBuyReserve capital supply elapsed speed ≤
          eth.val * supply.val := by
      calc
        capital.val * buyScaledNat eth oldEth oldNxmBuyReserve +
            supply.val * buyRatchetTermNat eth oldEth oldNxmBuyReserve capital supply elapsed speed
          ≤ buyBufferedNat capital * buyScaledNat eth oldEth oldNxmBuyReserve +
              buyRatchetExtraNat eth oldEth oldNxmBuyReserve capital elapsed speed := by
                exact Nat.add_le_add hBufferedScaled hRtLeExtra
        _ ≤ eth.val * supply.val := hBranchLe
    have hRtMul :
        supply.val * buyRatchetTermNat eth oldEth oldNxmBuyReserve capital supply elapsed speed ≤
          eth.val * supply.val := by
      exact Nat.le_trans (Nat.le_add_left _ _) hCrossSum
    have hRtMul' :
        buyRatchetTermNat eth oldEth oldNxmBuyReserve capital supply elapsed speed * supply.val ≤
          eth.val * supply.val := by
      simpa [Nat.mul_comm] using hRtMul
    have hRtLeEth :
        buyRatchetTermNat eth oldEth oldNxmBuyReserve capital supply elapsed speed ≤ eth.val := by
      exact Nat.le_of_mul_le_mul_right hRtMul' hSupplyPos
    have hSubVal :
        (sub eth ratchetTerm).val =
          eth.val - buyRatchetTermNat eth oldEth oldNxmBuyReserve capital supply elapsed speed := by
      have hRatchetLe : ratchetTerm.val ≤ eth.val := by
        simpa [hRatchetTermVal] using hRtLeEth
      have hSub := Verity.EVM.Uint256.sub_eq_of_le hRatchetLe
      simpa [hRatchetTermVal] using hSub
    simp [calculateBuyReserve, scaledReserve, bufferedCapital, base, ratchetExtra, hBranch]
    by_cases hDenZero : (sub eth ratchetTerm).val = 0
    · have hZeroVal : (div (mul eth scaledReserve) (sub eth ratchetTerm)).val = 0 := by
        simp [HDiv.hDiv, Verity.Core.Uint256.div, hDenZero]
      rw [hZeroVal]
      exact Nat.zero_le _
    · have hDen : sub eth ratchetTerm != 0 := by
        exact ne_zero_of_val_ne_zero _ hDenZero
      rw [div_val_eq _ _ hDen]
      have hDenPos : 0 < eth.val - buyRatchetTermNat eth oldEth oldNxmBuyReserve capital supply elapsed speed := by
        have : 0 < (sub eth ratchetTerm).val := Nat.pos_of_ne_zero hDenZero
        simpa [hSubVal] using this
      have hTmp :
          capital.val * buyScaledNat eth oldEth oldNxmBuyReserve ≤
            eth.val * supply.val -
              supply.val * buyRatchetTermNat eth oldEth oldNxmBuyReserve capital supply elapsed speed := by
        omega
      have hMulSub :
          supply.val * (eth.val - buyRatchetTermNat eth oldEth oldNxmBuyReserve capital supply elapsed speed) =
            eth.val * supply.val -
              supply.val * buyRatchetTermNat eth oldEth oldNxmBuyReserve capital supply elapsed speed := by
        rw [Nat.mul_comm supply.val _, Nat.mul_sub_right_distrib, Nat.mul_comm _ supply.val,
          Nat.mul_comm (buyRatchetTermNat eth oldEth oldNxmBuyReserve capital supply elapsed speed) supply.val]
      have hCrossDiff :
          capital.val * buyScaledNat eth oldEth oldNxmBuyReserve ≤
            supply.val * (eth.val - buyRatchetTermNat eth oldEth oldNxmBuyReserve capital supply elapsed speed) := by
        rw [hMulSub]
        exact hTmp
      have hCrossMul :
          (eth.val * buyScaledNat eth oldEth oldNxmBuyReserve) * capital.val ≤
            (eth.val * supply.val) *
              (eth.val - buyRatchetTermNat eth oldEth oldNxmBuyReserve capital supply elapsed speed) := by
        have := Nat.mul_le_mul_left eth.val hCrossDiff
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using this
      have hNumLe : (mul eth scaledReserve).val ≤ eth.val * buyScaledNat eth oldEth oldNxmBuyReserve := by
        calc
          (mul eth scaledReserve).val ≤ eth.val * scaledReserve.val := mul_val_le _ _
          _ = eth.val * buyScaledNat eth oldEth oldNxmBuyReserve := by rw [hScaledReserveVal]
      calc
        (mul eth scaledReserve).val / (sub eth ratchetTerm).val
          ≤ (eth.val * buyScaledNat eth oldEth oldNxmBuyReserve) /
              (eth.val - buyRatchetTermNat eth oldEth oldNxmBuyReserve capital supply elapsed speed) := by
                rw [hSubVal]
                exact Nat.div_le_div_right hNumLe
        _ ≤ eth.val * supply.val / capital.val := by
            exact div_le_div_of_mul_le_mul
              (eth.val * buyScaledNat eth oldEth oldNxmBuyReserve)
              (eth.val - buyRatchetTermNat eth oldEth oldNxmBuyReserve capital supply elapsed speed)
              (eth.val * supply.val) capital.val hDenPos hCapitalPos hCrossMul

theorem spotPrice_buy_ge_book_value_main
    (eth oldEth oldNxmBuyReserve oldNxmSellReserve capital supply elapsed speed : Uint256)
    (hEth : eth != 0)
    (hOldEth : oldEth != 0)
    (hSupply : supply != 0)
    (hCapital : capital != 0)
    (hBuyReserve : calculateBuyReserve eth oldEth oldNxmBuyReserve capital supply elapsed speed != 0)
    (hSafe : buyArithmeticSafe eth oldEth oldNxmBuyReserve capital supply elapsed speed) :
    spotPrice_buy_ge_book_value_spec
      eth oldEth oldNxmBuyReserve oldNxmSellReserve capital supply elapsed speed := by
  dsimp [spotPrice_buy_ge_book_value_spec, spotPrices]
  show (div (mul ONE_ETHER capital) supply).val ≤
    (div (mul ONE_ETHER eth) (calculateBuyReserve eth oldEth oldNxmBuyReserve capital supply elapsed speed)).val
  have hReserveBound :=
    calculateBuyReserve_le_book_reserve eth oldEth oldNxmBuyReserve capital supply elapsed speed
      hOldEth hSupply hCapital hSafe
  have hCapitalPos : 0 < capital.val := val_pos_of_ne_zero capital hCapital
  have hSupplyPos : 0 < supply.val := val_pos_of_ne_zero supply hSupply
  have hReservePos :
      0 < (calculateBuyReserve eth oldEth oldNxmBuyReserve capital supply elapsed speed).val :=
    val_pos_of_ne_zero _ hBuyReserve
  have hReserveMul :
      (calculateBuyReserve eth oldEth oldNxmBuyReserve capital supply elapsed speed).val * capital.val ≤
        eth.val * supply.val := by
    exact (Nat.le_div_iff_mul_le hCapitalPos).mp hReserveBound
  rcases hSafe with ⟨hMulEth, hMulCapital, _, _, _, _, _, _, _, _, _, _⟩
  rw [div_val_eq _ _ hSupply, mul_val_eq _ _ hMulCapital]
  rw [div_val_eq _ _ hBuyReserve, mul_val_eq _ _ hMulEth]
  exact buy_price_ge_book_value_nat eth.val supply.val capital.val
    (calculateBuyReserve eth oldEth oldNxmBuyReserve capital supply elapsed speed).val
    hSupplyPos hReservePos hReserveMul

private theorem calculateSellReserve_ge_book_reserve_succ
    (eth oldEth oldNxmSellReserve capital supply elapsed speed : Uint256)
    (hEth : eth != 0)
    (hOldEth : oldEth != 0)
    (hSupply : supply != 0)
    (hCapital : capital != 0)
    (hSafe : sellArithmeticSafe eth oldEth oldNxmSellReserve capital supply elapsed speed)
    (hScale : realisticSellScale eth capital supply) :
    eth.val * supply.val / capital.val + 1 ≤
      (calculateSellReserve eth oldEth oldNxmSellReserve capital supply elapsed speed).val := by
  rcases hScale with ⟨hCapitalLarge, hScale99⟩
  have hSafe' := hSafe
  rcases hSafe with ⟨_, _, _, _, hEthSupply, hEthScaled, hBase, hCapScaled, hCapScaledElapsed,
    hCapScaledElapsedSpeed, hEthSupplyAddExtra, hEthAddTerm⟩
  have hScaledVal := sell_scaled_val eth oldEth oldNxmSellReserve capital supply elapsed speed hOldEth hSafe'
  have hBufferedVal := sell_buffered_val eth oldEth oldNxmSellReserve capital supply elapsed speed hSafe'
  have hEthSupplyVal : (mul eth supply).val = eth.val * supply.val := mul_val_eq eth supply hEthSupply
  have hEthPos : 0 < eth.val := val_pos_of_ne_zero eth hEth
  have hCapitalPos : 0 < capital.val := val_pos_of_ne_zero capital hCapital
  have hSupplyPos : 0 < supply.val := val_pos_of_ne_zero supply hSupply
  let scaledReserve := div (mul oldNxmSellReserve eth) oldEth
  let bufferedCapital := div (mul capital (sub PRICE_BUFFER_DENOMINATOR PRICE_BUFFER)) PRICE_BUFFER_DENOMINATOR
  let ratchetTerm := div (div (div (mul (mul (mul capital scaledReserve) elapsed) speed) supply) RATCHET_PERIOD) RATCHET_DENOMINATOR
  let base := mul bufferedCapital scaledReserve
  let ratchetExtra := div (div (mul (mul (mul capital scaledReserve) elapsed) speed) RATCHET_PERIOD) RATCHET_DENOMINATOR
  have hScaledReserveVal : scaledReserve.val = sellScaledNat eth oldEth oldNxmSellReserve := by
    simpa [scaledReserve] using hScaledVal
  have hBufferedCapitalVal : bufferedCapital.val = sellBufferedNat capital := by
    simpa [bufferedCapital] using hBufferedVal
  have hBaseOverflow : bufferedCapital.val * scaledReserve.val < modulus := by
    rw [hBufferedCapitalVal, hScaledReserveVal]
    exact hBase
  have hCapScaledOverflow : capital.val * scaledReserve.val < modulus := by
    rw [hScaledReserveVal]
    exact hCapScaled
  have hCapScaledElapsedOverflow : capital.val * scaledReserve.val * elapsed.val < modulus := by
    rw [hScaledReserveVal]
    exact hCapScaledElapsed
  have hCapScaledElapsedSpeedOverflow :
      capital.val * scaledReserve.val * elapsed.val * speed.val < modulus := by
    rw [hScaledReserveVal]
    exact hCapScaledElapsedSpeed
  have hBaseVal : base.val = sellBufferedNat capital * sellScaledNat eth oldEth oldNxmSellReserve := by
    dsimp [base]
    rw [mul_val_eq _ _ hBaseOverflow, hBufferedCapitalVal, hScaledReserveVal]
  have hRatchetTermVal : ratchetTerm.val = sellRatchetTermNat eth oldEth oldNxmSellReserve capital supply elapsed speed := by
    dsimp [ratchetTerm, sellRatchetTermNat]
    rw [div_val_eq _ _ (by decide : RATCHET_DENOMINATOR != 0)]
    rw [div_val_eq _ _ (by decide : RATCHET_PERIOD != 0)]
    rw [div_val_eq _ _ hSupply]
    rw [mul4_val_eq capital scaledReserve elapsed speed
      hCapScaledOverflow hCapScaledElapsedOverflow hCapScaledElapsedSpeedOverflow]
    rw [hScaledReserveVal]
  have hRatchetExtraVal : ratchetExtra.val = sellRatchetExtraNat eth oldEth oldNxmSellReserve capital elapsed speed := by
    dsimp [ratchetExtra, sellRatchetExtraNat]
    rw [div_val_eq _ _ (by decide : RATCHET_DENOMINATOR != 0)]
    rw [div_val_eq _ _ (by decide : RATCHET_PERIOD != 0)]
    rw [mul4_val_eq capital scaledReserve elapsed speed
      hCapScaledOverflow hCapScaledElapsedOverflow hCapScaledElapsedSpeedOverflow]
    rw [hScaledReserveVal]
  by_cases hBranch : base < add (mul eth supply) ratchetExtra
  · have hBufferedCapitalPos : 0 < bufferedCapital.val := by
      rw [hBufferedCapitalVal]
      exact sell_buffered_pos capital.val hCapitalLarge
    have hBufferedPos : 0 < sellBufferedNat capital := by
      simpa [hBufferedCapitalVal] using hBufferedCapitalPos
    have hBufferedCapitalNe : bufferedCapital != 0 := by
      exact ne_zero_of_val_ne_zero bufferedCapital (Nat.ne_of_gt hBufferedCapitalPos)
    simp [calculateSellReserve, scaledReserve, bufferedCapital, base, ratchetExtra, hBranch]
    rw [div_val_eq _ _ hBufferedCapitalNe, hEthSupplyVal, hBufferedCapitalVal]
    exact sell_bv_reserve_ge_book_reserve_succ eth.val supply.val capital.val hCapitalLarge hScale99
  · have hBranchNat : ¬ base.val < (add (mul eth supply) ratchetExtra).val := by
      simpa [Verity.Core.Uint256.lt_def] using hBranch
    have hBranchLeRaw : (add (mul eth supply) ratchetExtra).val ≤ base.val := Nat.not_lt.mp hBranchNat
    have hEthSupplyAddExtraOverflow : (mul eth supply).val + ratchetExtra.val < modulus := by
      rw [hEthSupplyVal, hRatchetExtraVal]
      exact hEthSupplyAddExtra
    have hBranchLe :
        eth.val * supply.val + sellRatchetExtraNat eth oldEth oldNxmSellReserve capital elapsed speed ≤
          sellBufferedNat capital * sellScaledNat eth oldEth oldNxmSellReserve := by
      rw [add_val_eq _ _ hEthSupplyAddExtraOverflow, hEthSupplyVal, hRatchetExtraVal, hBaseVal] at hBranchLeRaw
      exact hBranchLeRaw
    have hRtLeExtra :
        supply.val * sellRatchetTermNat eth oldEth oldNxmSellReserve capital supply elapsed speed ≤
          sellRatchetExtraNat eth oldEth oldNxmSellReserve capital elapsed speed := by
      exact sell_ratchet_extra_ge_supply_term_nat capital.val
        (sellScaledNat eth oldEth oldNxmSellReserve) elapsed.val speed.val supply.val hSupplyPos
    have hCrossBase :
        eth.val * supply.val + supply.val * sellRatchetTermNat eth oldEth oldNxmSellReserve capital supply elapsed speed ≤
          sellBufferedNat capital * sellScaledNat eth oldEth oldNxmSellReserve := by
      calc
        eth.val * supply.val + supply.val * sellRatchetTermNat eth oldEth oldNxmSellReserve capital supply elapsed speed
          ≤ eth.val * supply.val + sellRatchetExtraNat eth oldEth oldNxmSellReserve capital elapsed speed := by
              exact Nat.add_le_add_left hRtLeExtra _
        _ ≤ sellBufferedNat capital * sellScaledNat eth oldEth oldNxmSellReserve := hBranchLe
    have hNumOverflow : eth.val * scaledReserve.val < modulus := by
      rw [hScaledReserveVal]
      exact hEthScaled
    have hNumVal : (mul eth scaledReserve).val = eth.val * sellScaledNat eth oldEth oldNxmSellReserve := by
      rw [mul_val_eq _ _ hNumOverflow, hScaledReserveVal]
    have hDenOverflow : eth.val + ratchetTerm.val < modulus := by
      rw [hRatchetTermVal]
      exact hEthAddTerm
    have hDenVal :
        (add eth ratchetTerm).val =
          eth.val + sellRatchetTermNat eth oldEth oldNxmSellReserve capital supply elapsed speed := by
      rw [add_val_eq _ _ hDenOverflow, hRatchetTermVal]
    have hDenPos : 0 < eth.val + sellRatchetTermNat eth oldEth oldNxmSellReserve capital supply elapsed speed := by
      omega
    have hDenNe : add eth ratchetTerm != 0 := by
      have hAddPos : 0 < (add eth ratchetTerm).val := by
        simpa [hDenVal] using hDenPos
      exact ne_zero_of_val_ne_zero _ (Nat.ne_of_gt hAddPos)
    have hBufferedPos : 0 < sellBufferedNat capital := sell_buffered_pos capital.val hCapitalLarge
    have hSupplyDen :
        supply.val * (eth.val + sellRatchetTermNat eth oldEth oldNxmSellReserve capital supply elapsed speed) ≤
          sellBufferedNat capital * sellScaledNat eth oldEth oldNxmSellReserve := by
      simpa [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hCrossBase
    have hCrossMul :
        (eth.val * supply.val) * (eth.val + sellRatchetTermNat eth oldEth oldNxmSellReserve capital supply elapsed speed) ≤
          (eth.val * sellScaledNat eth oldEth oldNxmSellReserve) * sellBufferedNat capital := by
      have := Nat.mul_le_mul_left eth.val hSupplyDen
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using this
    have hRatchetGeBv :
        eth.val * supply.val / sellBufferedNat capital ≤
          (eth.val * sellScaledNat eth oldEth oldNxmSellReserve) /
            (eth.val + sellRatchetTermNat eth oldEth oldNxmSellReserve capital supply elapsed speed) := by
      exact div_le_div_of_mul_le_mul'
        (eth.val * supply.val) (sellBufferedNat capital)
        (eth.val * sellScaledNat eth oldEth oldNxmSellReserve)
        (eth.val + sellRatchetTermNat eth oldEth oldNxmSellReserve capital supply elapsed speed)
        hDenPos hBufferedPos hCrossMul
    simp [calculateSellReserve, scaledReserve, bufferedCapital, base, ratchetExtra, hBranch]
    rw [div_val_eq _ _ hDenNe, hNumVal, hDenVal]
    calc
      eth.val * supply.val / capital.val + 1 ≤ eth.val * supply.val / sellBufferedNat capital := by
        exact sell_bv_reserve_ge_book_reserve_succ eth.val supply.val capital.val hCapitalLarge hScale99
      _ ≤ (eth.val * sellScaledNat eth oldEth oldNxmSellReserve) /
            (eth.val + sellRatchetTermNat eth oldEth oldNxmSellReserve capital supply elapsed speed) := hRatchetGeBv

theorem spotPrice_sell_le_book_value_main
    (eth oldEth oldNxmBuyReserve oldNxmSellReserve capital supply elapsed speed : Uint256)
    (hEth : eth != 0)
    (hOldEth : oldEth != 0)
    (hSupply : supply != 0)
    (hCapital : capital != 0)
    (hSellReserve : calculateSellReserve eth oldEth oldNxmSellReserve capital supply elapsed speed != 0)
    (hSafe : sellArithmeticSafe eth oldEth oldNxmSellReserve capital supply elapsed speed)
    (hScale : realisticSellScale eth capital supply) :
    spotPrice_sell_le_book_value_spec
      eth oldEth oldNxmBuyReserve oldNxmSellReserve capital supply elapsed speed := by
  dsimp [spotPrice_sell_le_book_value_spec, spotPrices]
  show (div (mul ONE_ETHER eth)
      (calculateSellReserve eth oldEth oldNxmSellReserve capital supply elapsed speed)).val ≤
    (div (mul ONE_ETHER capital) supply).val
  have hReserveSucc :=
    calculateSellReserve_ge_book_reserve_succ eth oldEth oldNxmSellReserve capital supply elapsed speed
      hEth hOldEth hSupply hCapital hSafe hScale
  have hCapitalPos : 0 < capital.val := val_pos_of_ne_zero capital hCapital
  have hSupplyPos : 0 < supply.val := val_pos_of_ne_zero supply hSupply
  have hReservePos :
      0 < (calculateSellReserve eth oldEth oldNxmSellReserve capital supply elapsed speed).val :=
    val_pos_of_ne_zero _ hSellReserve
  have hCross :
      eth.val * supply.val <
        (calculateSellReserve eth oldEth oldNxmSellReserve capital supply elapsed speed).val * capital.val := by
    exact lt_mul_of_div_succ_le
      (eth.val * supply.val)
      (calculateSellReserve eth oldEth oldNxmSellReserve capital supply elapsed speed).val
      capital.val hCapitalPos hReserveSucc
  rcases hSafe with ⟨hMulEth, hMulCapital, _, _, _, _, _, _, _, _, _, _⟩
  rw [div_val_eq _ _ hSellReserve, mul_val_eq _ _ hMulEth]
  rw [div_val_eq _ _ hSupply, mul_val_eq _ _ hMulCapital]
  exact sell_price_le_book_value_nat eth.val supply.val capital.val
    (calculateSellReserve eth oldEth oldNxmSellReserve capital supply elapsed speed).val
    hSupplyPos hReservePos hCross

theorem spotPrice_sell_le_buy_main
    (eth oldEth oldNxmBuyReserve oldNxmSellReserve capital supply elapsed speed : Uint256)
    (hEth : eth != 0)
    (hOldEth : oldEth != 0)
    (hSupply : supply != 0)
    (hCapital : capital != 0)
    (hBuyReserve : calculateBuyReserve eth oldEth oldNxmBuyReserve capital supply elapsed speed != 0)
    (hSellReserve : calculateSellReserve eth oldEth oldNxmSellReserve capital supply elapsed speed != 0)
    (hBuySafe : buyArithmeticSafe eth oldEth oldNxmBuyReserve capital supply elapsed speed)
    (hSellSafe : sellArithmeticSafe eth oldEth oldNxmSellReserve capital supply elapsed speed)
    (hScale : realisticSellScale eth capital supply) :
    spotPrice_sell_le_buy_spec
      eth oldEth oldNxmBuyReserve oldNxmSellReserve capital supply elapsed speed := by
  have hBuy :
      div (mul ONE_ETHER capital) supply ≤
        div (mul ONE_ETHER eth) (calculateBuyReserve eth oldEth oldNxmBuyReserve capital supply elapsed speed) := by
    simpa [spotPrice_buy_ge_book_value_spec, spotPrices] using
      spotPrice_buy_ge_book_value_main
        eth oldEth oldNxmBuyReserve oldNxmSellReserve capital supply elapsed speed
        hEth hOldEth hSupply hCapital hBuyReserve hBuySafe
  have hSell :
      div (mul ONE_ETHER eth) (calculateSellReserve eth oldEth oldNxmSellReserve capital supply elapsed speed) ≤
        div (mul ONE_ETHER capital) supply := by
    simpa [spotPrice_sell_le_book_value_spec, spotPrices] using
      spotPrice_sell_le_book_value_main
        eth oldEth oldNxmBuyReserve oldNxmSellReserve capital supply elapsed speed
        hEth hOldEth hSupply hCapital hSellReserve hSellSafe hScale
  have hSellVal :
      (div (mul ONE_ETHER eth) (calculateSellReserve eth oldEth oldNxmSellReserve capital supply elapsed speed)).val ≤
        (div (mul ONE_ETHER capital) supply).val := by
    simpa [Verity.Core.Uint256.le_def] using hSell
  have hBuyVal :
      (div (mul ONE_ETHER capital) supply).val ≤
        (div (mul ONE_ETHER eth) (calculateBuyReserve eth oldEth oldNxmBuyReserve capital supply elapsed speed)).val := by
    simpa [Verity.Core.Uint256.le_def] using hBuy
  have hChainVal :
      (div (mul ONE_ETHER eth) (calculateSellReserve eth oldEth oldNxmSellReserve capital supply elapsed speed)).val ≤
        (div (mul ONE_ETHER eth) (calculateBuyReserve eth oldEth oldNxmBuyReserve capital supply elapsed speed)).val :=
    Nat.le_trans hSellVal hBuyVal
  simpa [spotPrice_sell_le_buy_spec, spotPrices, Verity.Core.Uint256.le_def] using hChainVal

end Benchmark.Cases.NexusMutual.RammSpotPrice

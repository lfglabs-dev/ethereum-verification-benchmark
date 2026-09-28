import Benchmark.Cases.Cow.GPv2Settlement.Specs
import Mathlib.Tactic.Ring
namespace Benchmark.Cases.Cow.GPv2Settlement
open Verity
open Verity.EVM.Uint256
open Verity.Stdlib.Math

set_option linter.unusedSimpArgs false

/-!
# Proofs: CoW GPv2Settlement settle path never violates a limit order

Scope: trades executed by `computeTradeExecution`, the per-trade check of
`settle`. `swap` (the Balancer direct path) is included only through its
`filledAmount` bookkeeping; no claim is made about its price.

Main results:

* `computeTradeExecution_respects_limit_order`: one successful trade satisfies
  `trade_execution_spec`.
* `settle_trade_respects_limit_order_in_balances`: under the token hypotheses
  `DebitedExactly` (pull) and `CreditedExactly` (payout), the owner's and
  receiver's balance changes satisfy `trade_balance_spec`.
* `order_lifecycle_safety`: in every tracked `OrderLifecycle`, the totals of
  the settle-path trades since tracking began satisfy
  `cumulative_order_safety_spec`. Swap fills are not counted.
* `order_lifecycle_fee_cap`: the total computed fee of those settle-path trades
  is at most `feeAmount` when the limit amount is nonzero.
* `order_lifecycle_zero_fee`: with `feeAmount = 0`, those settle-path trades
  compute a zero fee. Token movements and swap fee transfers are not modeled.
* `zero_amount_order_replay`: reproduces CoW's documented zero-amount replay,
  showing that the fee-cap exclusion is necessary.

Strategy: `trade_success_facts` walks the monadic body of each of the four
branches (sell/buy × partial/fill-or-kill) and converts every successful
SafeMath step into an exact natural-number equation. The limit inequality then
follows from the L368 check combined with the rounding direction:
`sell_limit_nat` (ceiling) and `buy_limit_nat` (floor). The lifecycle
invariant `LifecycleInv` is proved by induction on `OrderLifecycle`.
No proof placeholders and no custom axioms: `#print axioms` reports only
`propext` and `Quot.sound`.
-/

/-! ## SafeMath value lemmas -/

theorem MAX_lt_mod : MAX_UINT256 + 1 = 2 ^ 256 := by
  simp [MAX_UINT256, Verity.Core.MAX_UINT256]

theorem safeMul_val {a b r : Uint256} (h : safeMul a b = some r) : r.val = a.val * b.val := by
  by_cases hle : a.val * b.val ≤ MAX_UINT256
  · have hm : safeMul a b = some (a * b) := by simp [safeMul, Nat.not_lt.mpr hle]
    rw [hm] at h; cases h
    apply Verity.Core.Uint256.mul_eq_of_lt
    have := MAX_lt_mod
    simp [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]; omega
  · have hm : safeMul a b = none := by simp [safeMul]; omega
    rw [hm] at h; cases h

theorem safeAdd_val {a b r : Uint256} (h : safeAdd a b = some r) : r.val = a.val + b.val := by
  by_cases hle : a.val + b.val ≤ MAX_UINT256
  · have hm : safeAdd a b = some (a + b) := by simp [safeAdd, Nat.not_lt.mpr hle]
    rw [hm] at h; cases h
    apply Verity.Core.Uint256.add_eq_of_lt
    have := MAX_lt_mod
    simp [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]; omega
  · have hm : safeAdd a b = none := by simp [safeAdd]; omega
    rw [hm] at h; cases h

theorem div_val_of_pos {a b : Uint256} (hb : 0 < b.val) : (div a b).val = a.val / b.val := by
  have hb0 : b.val ≠ 0 := by omega
  simp only [Verity.EVM.Uint256.div, Verity.Core.Uint256.div, hb0, if_false, Verity.Core.Uint256.val_ofNat]
  apply Nat.mod_eq_of_lt
  exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt

theorem mod_val_of_pos {a b : Uint256} (hb : 0 < b.val) : (mod a b).val = a.val % b.val := by
  have hb0 : b.val ≠ 0 := by omega
  simp only [Verity.EVM.Uint256.mod, Verity.Core.Uint256.mod, hb0, if_false, Verity.Core.Uint256.val_ofNat]
  apply Nat.mod_eq_of_lt
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) a.isLt

/-- Source `ceilDiv`: `a / b + (a % b == 0 ? 0 : 1)` has value `⌈a / b⌉` and never wraps. -/
theorem ceilDiv_src_val {a b : Uint256} (hb : 0 < b.val) :
    (add (div a b) (if mod a b = 0 then 0 else 1)).val =
      a.val / b.val + (if a.val % b.val = 0 then 0 else 1) := by
  have hmod : (mod a b = 0) ↔ a.val % b.val = 0 := by
    constructor
    · intro h; have := congrArg Verity.Core.Uint256.val h
      rw [mod_val_of_pos hb] at this; simpa using this
    · intro h; apply Verity.Core.Uint256.ext
      rw [mod_val_of_pos hb]; simpa using h
  have hdiv := div_val_of_pos (a := a) hb
  have ha := a.isLt
  simp only [Verity.Core.UINT256_MODULUS] at ha
  by_cases hr : a.val % b.val = 0
  · have : mod a b = 0 := hmod.mpr hr
    simp only [this, if_true, hr]
    simp only [Verity.EVM.Uint256.add, Verity.Core.Uint256.add, Verity.Core.Uint256.val_ofNat, Verity.Core.Uint256.val_zero, Nat.add_zero, hdiv]
    apply Nat.mod_eq_of_lt
    simp [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha
  · have : ¬ mod a b = 0 := fun h => hr (hmod.mp h)
    simp only [this, if_false, hr]
    simp only [Verity.EVM.Uint256.add, Verity.Core.Uint256.add, Verity.Core.Uint256.val_ofNat, Verity.Core.Uint256.val_one, hdiv]
    apply Nat.mod_eq_of_lt
    simp [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]
    -- b ≥ 2 since a % b ≠ 0 forces b ≠ 1
    have hb2 : 2 ≤ b.val := by
      rcases Nat.lt_or_ge b.val 2 with h | h
      · have : b.val = 1 := by omega
        exact absurd (by rw [this]; exact Nat.mod_one _) hr
      · exact h
    have : a.val / b.val ≤ a.val / 2 := Nat.div_le_div_left hb2 (by decide)
    omega


/-! ## Rounding arithmetic -/

/-- Sell branch arithmetic: `⌈xs·ps/pb⌉` and the L368 check give the limit price. -/
theorem sell_limit_nat (S B ps pb xs xb : Nat) (hpb : 0 < pb)
    (hL368 : B * pb ≤ S * ps) (hceil : xs * ps ≤ xb * pb) :
    xs * B ≤ xb * S := by
  have h1 : xs * B * pb ≤ xb * S * pb := by
    calc xs * B * pb = xs * (B * pb) := by ring
      _ ≤ xs * (S * ps) := Nat.mul_le_mul_left _ hL368
      _ = S * (xs * ps) := by ring
      _ ≤ S * (xb * pb) := Nat.mul_le_mul_left _ hceil
      _ = xb * S * pb := by ring
  exact Nat.le_of_mul_le_mul_right h1 hpb

/-- Buy branch arithmetic: `⌊xb·pb/ps⌋` and the L368 check give the limit price. -/
theorem buy_limit_nat (S B ps pb xs xb : Nat) (hps : 0 < ps)
    (hL368 : B * pb ≤ S * ps) (hfloor : xs * ps ≤ xb * pb) :
    xs * B ≤ xb * S := by
  have h1 : xs * B * ps ≤ xb * S * ps := by
    calc xs * B * ps = B * (xs * ps) := by ring
      _ ≤ B * (xb * pb) := Nat.mul_le_mul_left _ hfloor
      _ = xb * (B * pb) := by ring
      _ ≤ xb * (S * ps) := Nat.mul_le_mul_left _ hL368
      _ = xb * S * ps := by ring
  exact Nat.le_of_mul_le_mul_right h1 hps

theorem ceil_mul_ge (a b : Nat) (hb : 0 < b) :
    a ≤ (a / b + (if a % b = 0 then 0 else 1)) * b := by
  have h := Nat.div_add_mod a b
  have hlt := Nat.mod_lt a hb
  split
  · rename_i hr; rw [hr] at h; simp; rw [Nat.mul_comm]; omega
  · rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]; omega


/-! ## Branch analysis of `computeTradeExecution` -/

/-- Nat-level facts about one successful execution, shared by all branches. -/
structure TradeFacts (o : SignedOrder) (f0 f1 : Nat) (inA outA fee : Uint256) : Prop where
  fee_le_in : fee.val ≤ inA.val
  limit : (inA.val - fee.val) * o.buyAmount.val ≤ outA.val * o.sellAmount.val
  filled_eq : f1 = f0 + filledPart o (inA.val - fee.val) outA.val
  filled_le : f1 ≤ limitAmount o
  fee_le : fee.val * limitAmount o ≤ o.feeAmount.val * filledPart o (inA.val - fee.val) outA.val
  fee_eq_zero_of : o.feeAmount = 0 → fee.val = 0

set_option maxHeartbeats 2000000 in
/-- Branch analysis of a successful `computeTradeExecution`. -/
theorem trade_success_facts (orderUid : Uint256) (o : SignedOrder)
    (ps pb ea inA outA fee : Uint256) (s s' : ContractState)
    (h : (tradeCall orderUid o ps pb ea).run s = ContractResult.success (inA, outA, fee) s') :
    s.blockTimestamp.val ≤ o.validTo.val ∧
    ∃ newFilled : Uint256,
      s' = s.writeMapUint GPv2Settlement.filledAmount.slot orderUid newFilled ∧
      TradeFacts o (filledOf s orderUid) newFilled.val inA outA fee := by
  unfold tradeCall GPv2Settlement.computeTradeExecution at h
  simp [Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, Verity.require,
    blockTimestamp, getMappingUint, setMappingUint, requireSomeUint] at h
  by_cases hT : s.blockTimestamp.val ≤ o.validTo.val <;> simp [hT, getMappingUint, setMappingUint, Verity.bind, Verity.pure, Verity.require, Bind.bind, Pure.pure] at h
  refine ⟨hT, ?_⟩
  rcases h1 : safeMul o.sellAmount ps with _ | lhs <;> simp [h1, Verity.bind, Verity.require, Verity.pure] at h
  rcases h2 : safeMul o.buyAmount pb with _ | rhs <;> simp [h2, Verity.bind, Verity.require, Verity.pure] at h
  by_cases hL : rhs.val ≤ lhs.val <;> simp [hL, getMappingUint, setMappingUint, Verity.bind, Verity.pure, Verity.require, Bind.bind, Pure.pure] at h
  have hL368 : o.buyAmount.val * pb.val ≤ o.sellAmount.val * ps.val := by
    rw [← safeMul_val h1, ← safeMul_val h2]; exact hL
  by_cases hK : o.kind = GPv2Settlement.KIND_SELL
  · -- sell order
    have hSell : isSellOrder o := hK
    simp [hK, getMappingUint, setMappingUint] at h
    by_cases hP : o.partiallyFillable = true
    · simp [hP, getMappingUint, setMappingUint] at h
      rcases h3 : safeMul o.feeAmount ea with _ | fp <;> simp [h3, Verity.bind, Verity.require, Verity.pure] at h
      by_cases hS : 0 < o.sellAmount.val <;> simp [hS, getMappingUint, setMappingUint, Verity.bind, Verity.pure, Verity.require, Bind.bind, Pure.pure] at h
      rcases h4 : safeMul ea ps with _ | sv <;> simp [h4, Verity.bind, Verity.require, Verity.pure] at h
      by_cases hB : 0 < pb.val <;> simp [hB, getMappingUint, setMappingUint, Verity.bind, Verity.pure, Verity.require, Bind.bind, Pure.pure] at h
      rcases h5 : safeAdd (s.storageMapUint GPv2Settlement.filledAmount.slot orderUid) ea with _ | fa <;> simp [h5, Verity.bind, Verity.require, Verity.pure] at h
      by_cases hF : fa.val ≤ o.sellAmount.val <;> simp [hF, getMappingUint, setMappingUint, Verity.bind, Verity.pure, Verity.require, Bind.bind, Pure.pure] at h
      rcases h6 : safeAdd ea (div fp o.sellAmount) with _ | tot <;> simp [h6, Verity.bind, Verity.require, Verity.pure] at h
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
      refine ⟨fa, by simp [ContractState.writeMapUint], ?_⟩
      have eFp := safeMul_val h3
      have eSv := safeMul_val h4
      have eFa := safeAdd_val h5
      have eTot := safeAdd_val h6
      have eFee := div_val_of_pos (a := fp) hS
      have eOut := ceilDiv_src_val (a := sv) hB
      have hceil := ceil_mul_ge sv.val pb.val hB
      have hLim : limitAmount o = o.sellAmount.val := by simp [limitAmount, hSell]
      have hSold : tot.val - (div fp o.sellAmount).val = ea.val := by omega
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · omega
      · rw [hSold, eOut]
        apply sell_limit_nat _ _ ps.val pb.val _ _ hB hL368
        rw [← eSv]; exact hceil
      · simp only [filledPart, hSell, if_true, hSold, filledOf]; omega
      · rw [hLim]; exact hF
      · simp only [filledPart, hSell, if_true, hLim]
        rw [hSold, eFee, ← eFp]; exact Nat.div_mul_le_self _ _
      · intro h0; rw [eFee, eFp, h0]; simp
    · simp [hP, getMappingUint, setMappingUint] at h
      by_cases hB : 0 < pb.val <;> simp [hB, getMappingUint, setMappingUint, Verity.bind, Verity.pure, Verity.require, Bind.bind, Pure.pure] at h
      rcases h5 : safeAdd (s.storageMapUint GPv2Settlement.filledAmount.slot orderUid) o.sellAmount with _ | fa <;> simp [h5, Verity.bind, Verity.require, Verity.pure] at h
      by_cases hF : fa.val ≤ o.sellAmount.val <;> simp [hF, getMappingUint, setMappingUint, Verity.bind, Verity.pure, Verity.require, Bind.bind, Pure.pure] at h
      rcases h6 : safeAdd o.sellAmount o.feeAmount with _ | tot <;> simp [h6, Verity.bind, Verity.require, Verity.pure] at h
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
      refine ⟨fa, by simp [ContractState.writeMapUint], ?_⟩
      have eSv := safeMul_val h1
      have eFa := safeAdd_val h5
      have eTot := safeAdd_val h6
      have eOut := ceilDiv_src_val (a := lhs) hB
      have hceil := ceil_mul_ge lhs.val pb.val hB
      have hLim : limitAmount o = o.sellAmount.val := by simp [limitAmount, hSell]
      have hSold : tot.val - o.feeAmount.val = o.sellAmount.val := by omega
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · omega
      · rw [hSold, eOut]
        apply sell_limit_nat _ _ ps.val pb.val _ _ hB hL368
        rw [← eSv]; exact hceil
      · simp only [filledPart, hSell, if_true, hSold, filledOf]; omega
      · rw [hLim]; exact hF
      · simp only [filledPart, hSell, if_true, hLim]
        rw [hSold, Nat.mul_comm]
      · intro h0; rw [h0]; simp
  · -- buy order (any kind word other than KIND_SELL)
    have hBuy : ¬ isSellOrder o := hK
    simp [hK, getMappingUint, setMappingUint] at h
    by_cases hP : o.partiallyFillable = true
    · simp [hP, getMappingUint, setMappingUint] at h
      rcases h3 : safeMul o.feeAmount ea with _ | fp <;> simp [h3, Verity.bind, Verity.require, Verity.pure] at h
      by_cases hBa : 0 < o.buyAmount.val <;> simp [hBa, getMappingUint, setMappingUint, Verity.bind, Verity.pure, Verity.require, Bind.bind, Pure.pure] at h
      rcases h4 : safeMul ea pb with _ | bv <;> simp [h4, Verity.bind, Verity.require, Verity.pure] at h
      by_cases hSp : 0 < ps.val <;> simp [hSp, getMappingUint, setMappingUint, Verity.bind, Verity.pure, Verity.require, Bind.bind, Pure.pure] at h
      rcases h5 : safeAdd (s.storageMapUint GPv2Settlement.filledAmount.slot orderUid) ea with _ | fa <;> simp [h5, Verity.bind, Verity.require, Verity.pure] at h
      by_cases hF : fa.val ≤ o.buyAmount.val <;> simp [hF, getMappingUint, setMappingUint, Verity.bind, Verity.pure, Verity.require, Bind.bind, Pure.pure] at h
      rcases h6 : safeAdd (div bv ps) (div fp o.buyAmount) with _ | tot <;> simp [h6, Verity.bind, Verity.require, Verity.pure] at h
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
      refine ⟨fa, by simp [ContractState.writeMapUint], ?_⟩
      have eFp := safeMul_val h3
      have eBv := safeMul_val h4
      have eFa := safeAdd_val h5
      have eTot := safeAdd_val h6
      have eFee := div_val_of_pos (a := fp) hBa
      have eSold := div_val_of_pos (a := bv) hSp
      have hLim : limitAmount o = o.buyAmount.val := by simp [limitAmount, hBuy]
      have hSold : tot.val - (div fp o.buyAmount).val = bv.val / ps.val := by omega
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · omega
      · rw [hSold]
        apply buy_limit_nat _ _ ps.val pb.val _ _ hSp hL368
        rw [← eBv]; exact Nat.div_mul_le_self _ _
      · simp only [filledPart, hBuy, if_false, filledOf]; omega
      · rw [hLim]; exact hF
      · simp only [filledPart, hBuy, if_false, hLim]
        rw [eFee, ← eFp]; exact Nat.div_mul_le_self _ _
      · intro h0; rw [eFee, eFp, h0]; simp
    · simp [hP, getMappingUint, setMappingUint] at h
      by_cases hSp : 0 < ps.val <;> simp [hSp, getMappingUint, setMappingUint, Verity.bind, Verity.pure, Verity.require, Bind.bind, Pure.pure] at h
      rcases h5 : safeAdd (s.storageMapUint GPv2Settlement.filledAmount.slot orderUid) o.buyAmount with _ | fa <;> simp [h5, Verity.bind, Verity.require, Verity.pure] at h
      by_cases hF : fa.val ≤ o.buyAmount.val <;> simp [hF, getMappingUint, setMappingUint, Verity.bind, Verity.pure, Verity.require, Bind.bind, Pure.pure] at h
      rcases h6 : safeAdd (div rhs ps) o.feeAmount with _ | tot <;> simp [h6, Verity.bind, Verity.require, Verity.pure] at h
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
      refine ⟨fa, by simp [ContractState.writeMapUint], ?_⟩
      have eBv := safeMul_val h2
      have eFa := safeAdd_val h5
      have eTot := safeAdd_val h6
      have eSold := div_val_of_pos (a := rhs) hSp
      have hLim : limitAmount o = o.buyAmount.val := by simp [limitAmount, hBuy]
      have hSold : tot.val - o.feeAmount.val = rhs.val / ps.val := by omega
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · omega
      · rw [hSold]
        apply buy_limit_nat _ _ ps.val pb.val _ _ hSp hL368
        rw [← eBv]; exact Nat.div_mul_le_self _ _
      · simp only [filledPart, hBuy, if_false, filledOf]; omega
      · rw [hLim]; exact hF
      · simp only [filledPart, hBuy, if_false, hLim]
        rw [Nat.mul_comm]
      · intro h0; rw [h0]; simp

/-! ## Per-trade theorem -/

theorem computeTradeExecution_respects_limit_order
    (orderUid : Uint256) (o : SignedOrder)
    (sellPrice buyPrice executedAmount inAmount outAmount fee : Uint256)
    (s s' : ContractState)
    (hRun : (tradeCall orderUid o sellPrice buyPrice executedAmount).run s =
      ContractResult.success (inAmount, outAmount, fee) s') :
    trade_execution_spec orderUid o s s' inAmount outAmount fee := by
  obtain ⟨_, nf, hs', hf⟩ := trade_success_facts orderUid o sellPrice buyPrice executedAmount
    inAmount outAmount fee s s' hRun
  have hread : filledOf s' orderUid = nf.val := by
    subst hs'; simp [filledOf, ContractState.writeMapUint]
  refine ⟨hf.fee_le_in, hf.limit, ?_, ?_, hf.fee_le, ?_⟩
  · rw [hread]; exact hf.filled_eq
  · rw [hread]; exact hf.filled_le
  · subst hs'; simp [ContractState.writeMapUint]

/-! ## Balance-level theorem -/

/-- If the pull takes exactly the computed sell amount from the owner and the
payout gives exactly the computed buy amount to the receiver (the token
hypotheses), the owner's and receiver's balance changes respect the signed
limit price and fee. -/
theorem settle_trade_respects_limit_order_in_balances
    (orderUid : Uint256) (o : SignedOrder)
    (sellPrice buyPrice executedAmount inAmount outAmount fee : Uint256)
    (s s' : ContractState)
    (owner receiver : Address)
    (sellBefore sellAfter buyBefore buyAfter : Balances)
    (hRun : (tradeCall orderUid o sellPrice buyPrice executedAmount).run s =
      ContractResult.success (inAmount, outAmount, fee) s')
    (hPull : DebitedExactly sellBefore sellAfter owner inAmount.val)
    (hPay : CreditedExactly buyBefore buyAfter receiver outAmount.val) :
    trade_balance_spec o owner receiver sellBefore sellAfter buyBefore buyAfter fee.val := by
  have h := computeTradeExecution_respects_limit_order orderUid o sellPrice buyPrice
    executedAmount inAmount outAmount fee s s' hRun
  dsimp only [trade_execution_spec] at h
  obtain ⟨hFee, hLimit, _, _, hFeeRate, _⟩ := h
  unfold DebitedExactly at hPull
  unfold CreditedExactly at hPay
  have hPaid : sellBefore owner - sellAfter owner = inAmount.val := by omega
  have hReceived : buyAfter receiver - buyBefore receiver = outAmount.val := by omega
  unfold trade_balance_spec
  rw [hPaid, hReceived]
  exact ⟨hFee, hLimit, hFeeRate⟩

/-! ## Lifecycle invariant -/

/-- Invariant carried along every reachable state of one order. -/
def LifecycleInv (orderUid : Uint256) (o : SignedOrder) (s : ContractState) (t : OrderTotals) : Prop :=
  respectsLimitPrice o t.sold t.bought ∧
  feeWithinSignedFee o t.fee (filledPart o t.sold t.bought) ∧
  filledPart o t.sold t.bought ≤ limitAmount o ∧
  (filledPart o t.sold t.bought ≤ filledOf s orderUid ∨ o.validTo.val < s.blockTimestamp.val)

theorem limitAmount_lt (o : SignedOrder) : limitAmount o < 2 ^ 256 := by
  unfold limitAmount
  split
  · exact o.sellAmount.isLt
  · exact o.buyAmount.isLt

theorem filledPart_add (o : SignedOrder) (a b c d : Nat) :
    filledPart o (a + c) (b + d) = filledPart o a b + filledPart o c d := by
  unfold filledPart; split <;> rfl

theorem lifecycle_inv (orderUid : Uint256) (o : SignedOrder) (s : ContractState) (t : OrderTotals)
    (h : OrderLifecycle orderUid o s t) : LifecycleInv orderUid o s t := by
  induction h with
  | start s =>
      refine ⟨by simp [respectsLimitPrice], by simp [feeWithinSignedFee, filledPart], by simp [filledPart], ?_⟩
      left; simp [filledPart]
  | @trade s s' t sellPrice buyPrice executedAmount inAmount outAmount fee _ hRun ih =>
      obtain ⟨ihLim, ihFee, ihCap, ihDisj⟩ := ih
      obtain ⟨hT, nf, hs', hf⟩ := trade_success_facts orderUid o sellPrice buyPrice executedAmount
        inAmount outAmount fee s s' hRun
      have hFilled : filledPart o t.sold t.bought ≤ filledOf s orderUid := by
        rcases ihDisj with h | h
        · exact h
        · omega
      have hread : filledOf s' orderUid = nf.val := by
        subst hs'; simp [filledOf, ContractState.writeMapUint]
      have hsum := filledPart_add o t.sold t.bought (inAmount.val - fee.val) outAmount.val
      have fl := hf.filled_eq
      have fc := hf.filled_le
      refine ⟨?_, ?_, ?_, ?_⟩
      · unfold respectsLimitPrice at ihLim ⊢
        have := hf.limit
        simp only
        rw [Nat.add_mul, Nat.add_mul]; omega
      · unfold feeWithinSignedFee at ihFee ⊢
        have := hf.fee_le
        simp only
        rw [hsum, Nat.add_mul, Nat.mul_add]; omega
      · simp only; rw [hsum]; omega
      · left; simp only; rw [hsum, hread]; omega
  | @invalidate s s' t uidOwner _ hRun ih =>
      obtain ⟨ihLim, ihFee, ihCap, _⟩ := ih
      refine ⟨ihLim, ihFee, ihCap, ?_⟩
      left
      unfold GPv2Settlement.invalidateOrder at hRun
      simp [Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, Verity.require,
        msgSender, setMappingUint] at hRun
      by_cases hO : uidOwner = s.sender <;> simp [hO] at hRun
      subst hRun
      have := limitAmount_lt o
      have hmax : (115792089237316195423570985008687907853269984665640564039457584007913129639935 : Uint256).val =
          115792089237316195423570985008687907853269984665640564039457584007913129639935 := by
        decide
      simp [filledOf]
      omega
  | @free s s' t _ hRun ih =>
      obtain ⟨ihLim, ihFee, ihCap, _⟩ := ih
      refine ⟨ihLim, ihFee, ihCap, ?_⟩
      right
      unfold GPv2Settlement.freeFilledAmountStorage at hRun
      simp [Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, Verity.require,
        msgSender, setMappingUint, blockTimestamp, Verity.contractAddress] at hRun
      by_cases hI : s.thisAddress = s.sender <;> simp [hI] at hRun
      by_cases hV : o.validTo.val < s.blockTimestamp.val <;> simp [hV] at hRun
      subst hRun
      simpa using hV
  | @environment s s' t _ hSame hTime ih =>
      obtain ⟨ihLim, ihFee, ihCap, ihDisj⟩ := ih
      refine ⟨ihLim, ihFee, ihCap, ?_⟩
      rcases ihDisj with h | h
      · left; unfold filledOf at h ⊢; rw [hSame]; exact h
      · right; omega
  | @swapFill s s' t executedSellAmount executedBuyAmount _ hRun ih =>
      obtain ⟨ihLim, ihFee, ihCap, _⟩ := ih
      refine ⟨ihLim, ihFee, ihCap, ?_⟩
      left
      unfold GPv2Settlement.swapFilledAmountUpdate at hRun
      simp [Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, Verity.require,
        getMappingUint, setMappingUint] at hRun
      by_cases hZ : s.storageMapUint GPv2Settlement.filledAmount.slot orderUid = 0 <;> simp [hZ] at hRun
      by_cases hK : o.kind = GPv2Settlement.KIND_SELL
      · have hSell : isSellOrder o := hK
        simp [hK] at hRun
        by_cases hE : executedSellAmount = o.sellAmount <;>
          simp [hE, Verity.bind, Verity.require, setMappingUint] at hRun
        subst hRun
        have : limitAmount o = o.sellAmount.val := by simp [limitAmount, hSell]
        simp [filledOf]; omega
      · have hBuy : ¬ isSellOrder o := hK
        simp [hK] at hRun
        by_cases hE : executedBuyAmount = o.buyAmount <;>
          simp [hE, Verity.bind, Verity.require, setMappingUint] at hRun
        subst hRun
        have : limitAmount o = o.buyAmount.val := by simp [limitAmount, hBuy]
        simp [filledOf]; omega

/-- Cumulative theorem: in any tracked lifecycle of one order, the settle-path
trades since tracking began together respect the limit price, never overfill
the order, and keep fees at most `F` pro rata. Swap fills are not counted and
carry no price or fee claim. -/
theorem order_lifecycle_safety (orderUid : Uint256) (o : SignedOrder) (s : ContractState) (t : OrderTotals)
    (h : OrderLifecycle orderUid o s t) : cumulative_order_safety_spec o t := by
  obtain ⟨a, b, c, _⟩ := lifecycle_inv orderUid o s t h
  exact ⟨a, c, b⟩

theorem order_lifecycle_fee_cap (orderUid : Uint256) (o : SignedOrder) (s : ContractState) (t : OrderTotals)
    (h : OrderLifecycle orderUid o s t) : total_fee_cap_spec o t := by
  intro hPos
  obtain ⟨_, hFee, hCap, _⟩ := lifecycle_inv orderUid o s t h
  unfold feeWithinSignedFee at hFee
  have : t.fee * limitAmount o ≤ o.feeAmount.val * limitAmount o :=
    le_trans hFee (Nat.mul_le_mul_left _ hCap)
  exact Nat.le_of_mul_le_mul_right this hPos

theorem order_lifecycle_zero_fee (orderUid : Uint256) (o : SignedOrder) (s : ContractState) (t : OrderTotals)
    (h : OrderLifecycle orderUid o s t) : zero_fee_spec o t := by
  intro h0
  induction h with
  | start => rfl
  | @trade s s' t sellPrice buyPrice executedAmount inAmount outAmount fee _ hRun ih =>
      obtain ⟨_, nf, _, hf⟩ := trade_success_facts orderUid o sellPrice buyPrice executedAmount
        inAmount outAmount fee s s' hRun
      simp only [ih, hf.fee_eq_zero_of h0]
  | invalidate _ _ _ ih => exact ih
  | free _ _ ih => exact ih
  | environment _ _ _ ih => exact ih
  | swapFill _ _ _ _ ih => exact ih

/-! ## CoW's documented known issue: zero-amount orders can be replayed -/

/-- Witness for CoW's documented known issue (README "Known issues", c6b61ce).
A fill-or-kill sell order with `sellAmount = 0`, `buyAmount = 0` and
`feeAmount = 1` trades successfully, returns the full fee as its computed fee, and leaves
`filledAmount` at 0. The same trade then succeeds again from the new state,
so the computed fee is counted twice. This is why `total_fee_cap_spec` requires a
nonzero limit amount. -/
theorem zero_amount_order_replay (s : ContractState)
    (hTime : s.blockTimestamp.val ≤ 100)
    (hFilled : s.storageMapUint GPv2Settlement.filledAmount.slot 7 = 0) :
    (tradeCall 7 zeroAmountSellOrder 1 1 0).run s = ContractResult.success (1, 0, 1) s ∧
    OrderLifecycle 7 zeroAmountSellOrder s ⟨0, 0, 2⟩ ∧
    ¬ (⟨0, 0, 2⟩ : OrderTotals).fee ≤ zeroAmountSellOrder.feeAmount.val := by
  have h100 : (100 : Uint256).val = 100 := by decide
  have hMax : ¬ MAX_UINT256 = 0 := by simp [MAX_UINT256, Verity.Core.MAX_UINT256]
  have hOut : add (div (0 : Uint256) 1) (if mod (0 : Uint256) 1 = 0 then 0 else 1) = 0 := by decide
  have hMap : (fun sl k => if sl = GPv2Settlement.filledAmount.slot ∧ k = (7 : Uint256) then (0 : Uint256)
      else s.storageMapUint sl k) = s.storageMapUint := by
    funext sl k
    by_cases hk : sl = GPv2Settlement.filledAmount.slot ∧ k = 7
    · obtain ⟨rfl, rfl⟩ := hk; simp [hFilled]
    · simp [hk]
  have hRun : (tradeCall 7 zeroAmountSellOrder 1 1 0).run s = ContractResult.success (1, 0, 1) s := by
    unfold tradeCall GPv2Settlement.computeTradeExecution zeroAmountSellOrder
    simp [Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, Verity.require,
      blockTimestamp, getMappingUint, setMappingUint, requireSomeUint, safeMul, safeAdd, hTime, hFilled,
      h100, hMax, hOut, hMap]
  refine ⟨hRun, ?_, by decide⟩
  have step1 := OrderLifecycle.trade (orderUid := 7) (o := zeroAmountSellOrder) 1 1 0 1 0 1
    (OrderLifecycle.start s) hRun
  have step2 := OrderLifecycle.trade 1 1 0 1 0 1 step1 hRun
  simpa using step2

end Benchmark.Cases.Cow.GPv2Settlement

import Benchmark.Cases.KPK.SharesSettlementAccounting.FeeTrace
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace Benchmark.Cases.KPK.SharesSettlementAccounting
open Verity
set_option maxHeartbeats 2000000
theorem scaled_double_floor (n p d k u : Nat) (hk : k > 0) (hu : u > 0) :
    (n*k / p * u) / (d*k*u) = n / (p*d) := by
  rw [Nat.mul_div_mul_right _ _ hu, Nat.div_div_eq_div_mul]
  rw [show p * (d*k) = (p*d)*k by ring]
  exact Nat.mul_div_mul_right n (p*d) hk

theorem Mint_eq_single_floor (amount price decimals : Nat) (hp : price > 0) :
    Mint amount price decimals = amount * wad * usd / (price * 10^decimals) := by
  by_cases ha : amount = 0
  · simp [Mint, ha]
  · unfold Mint
    rw [if_neg (by omega : ¬ (price = 0 ∨ amount = 0))]
    have h1 : amount * (wad * wad) = (amount * wad * usd) * 10^10 := by
      norm_num [wad, usd]; ring
    have h2 : 10^decimals * wad = 10^decimals * 10^10 * usd := by
      norm_num [wad, usd]; ring
    rw [h1, h2]
    exact scaled_double_floor _ _ _ _ _ (by norm_num) (by norm_num [usd])

theorem Out_eq_single_floor (net price decimals : Nat) :
    Out net price decimals = net * price * 10^decimals / (wad * usd) := by
  by_cases hp : price = 0
  · simp [Out, hp]
  by_cases hn : net = 0
  · simp [Out, hn]
  unfold Out
  rw [if_neg (by omega : ¬ (price = 0 ∨ net = 0))]
  have h1 : net * (price * wad) = (net * price * 10^10) * usd := by
    norm_num [wad, usd]; ring
  have h2 : wad * wad = (wad * usd) * 10^10 := by norm_num [wad, usd]
  rw [h1, Nat.mul_div_cancel _ (by norm_num [usd]), h2]
  rw [show net * price * 10^10 * 10^decimals = (net*price*10^decimals)*10^10 by ring]
  exact Nat.mul_div_mul_right _ _ (by norm_num)

theorem Mint_floor_bounds (amount price decimals : Nat) (hp : price > 0) :
    Mint amount price decimals * price * 10^decimals ≤ amount * wad * usd ∧
    amount * wad * usd < (Mint amount price decimals + 1) * price * 10^decimals := by
  rw [Mint_eq_single_floor _ _ _ hp]
  have hd : price * 10^decimals > 0 := Nat.mul_pos hp (by positivity)
  constructor
  · simpa only [Nat.mul_assoc] using Nat.div_mul_le_self (amount*wad*usd) (price*10^decimals)
  · have h := Nat.lt_mul_div_succ (amount*wad*usd) hd
    simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

theorem Out_floor_bounds (net price decimals : Nat) :
    Out net price decimals * wad * usd ≤ net * price * 10^decimals ∧
    net * price * 10^decimals < (Out net price decimals + 1) * wad * usd := by
  rw [Out_eq_single_floor]
  constructor
  · simpa only [Nat.mul_assoc] using Nat.div_mul_le_self (net*price*10^decimals) (wad*usd)
  · have h := Nat.lt_mul_div_succ (net*price*10^decimals) (by norm_num [wad,usd] : wad*usd > 0)
    simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

theorem assetsToShares_floor_bounds (amount price q : Nat) (asset : Address) (s t : State)
    (ha : amount < wordLimit) (hp : price < wordLimit)
    (hd : (s.config.assets asset).decimals ≤ 36) (hpos : price > 0)
    (h : assetsToShares amount price asset s = .ok (q,t)) :
    q * price * 10^(s.config.assets asset).decimals ≤ amount * wad * usd ∧
    amount * wad * usd < (q+1) * price * 10^(s.config.assets asset).decimals := by
  rw [(assetsToShares_success _ _ _ _ _ _ ha hp hd h).1]
  exact Mint_floor_bounds _ _ _ hpos

theorem sharesToAssets_floor_bounds (shares price q : Nat) (asset : Address) (s t : State)
    (ha : shares < wordLimit) (hp : price < wordLimit)
    (hd : (s.config.assets asset).decimals ≤ 36)
    (h : sharesToAssets shares price asset s = .ok (q,t)) :
    q * wad * usd ≤ shares * price * 10^(s.config.assets asset).decimals ∧
    shares * price * 10^(s.config.assets asset).decimals < (q+1) * wad * usd := by
  rw [(sharesToAssets_success _ _ _ _ _ _ ha hp hd h).1]
  exact Out_floor_bounds _ _ _

#print axioms assetsToShares_floor_bounds
#print axioms sharesToAssets_floor_bounds

end Benchmark.Cases.KPK.SharesSettlementAccounting

import Benchmark.Cases.KPK.SharesSettlementAccounting.Specs

namespace Benchmark.Generated.KPK.SharesSettlementAccounting
open Benchmark.Cases.KPK.SharesSettlementAccounting

theorem Mint_floor_bounds (amount price decimals : Nat) (hp : price > 0) :
    Mint amount price decimals * price * 10^decimals ≤ amount * wad * usd ∧
    amount * wad * usd < (Mint amount price decimals + 1) * price * 10^decimals := by
  exact ?_
end Benchmark.Generated.KPK.SharesSettlementAccounting

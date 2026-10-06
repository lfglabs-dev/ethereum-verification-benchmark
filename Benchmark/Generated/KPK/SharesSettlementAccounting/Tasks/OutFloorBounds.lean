import Benchmark.Cases.KPK.SharesSettlementAccounting.Specs

namespace Benchmark.Generated.KPK.SharesSettlementAccounting
open Benchmark.Cases.KPK.SharesSettlementAccounting

theorem Out_floor_bounds (net price decimals : Nat) :
    Out net price decimals * wad * usd ≤ net * price * 10^decimals ∧
    net * price * 10^decimals < (Out net price decimals + 1) * wad * usd := by
  exact ?_
end Benchmark.Generated.KPK.SharesSettlementAccounting

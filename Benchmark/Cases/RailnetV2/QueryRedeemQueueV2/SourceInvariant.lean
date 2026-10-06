import Benchmark.Cases.RailnetV2.QueryRedeemQueueV2.SourceFunding
import Benchmark.Cases.RailnetV2.QueryRedeemQueueV2.CallbackProofs

namespace Benchmark.Cases.RailnetV2.QueryRedeemQueueV2


set_option maxHeartbeats 2000000

/-- Source-derived induction predicate; no budget or history premise. -/
def SourceSafe (s : QueueState) : Prop :=
  SourceGeometrySafe s ∧ SourceFundingSafe s

@[simp] private theorem throw_except {α : Type} (e : String) :
    (throw e : Except String α) = .error e := rfl

private theorem initial_arrays (s : QueueState) (h : Initialized s) :
    s.demands = #[] ∧ s.fulfillments = #[] ∧ s.allocations = #[] := by
  simp only [Initialized] at h
  rcases h with ⟨parent, manager, assetIn, assetOut, codeIn, codeOut,
    decIn, decOut, h⟩
  simp only [«initialize», throw_except, bind, Except.bind, pure,
    Except.pure, Except.map] at h
  split_ifs at h <;> simp_all
  subst s
  exact ⟨rfl, rfl, rfl⟩

/-- A successful one-time source initialization has empty ledgers. -/
theorem initialized_source_safe (s : QueueState) (h : Initialized s) : SourceSafe s := by
  obtain ⟨hd, hf, ha⟩ := initial_arrays s h
  exact ⟨initialized_empty_geometry s hd ha, empty_funding s hf ha⟩

/-- Successful demand writes only a fresh demand at its checked predecessor endpoint. -/
private theorem demand_success_shape (s post : QueueState) (calls : Array ExternalCall)
    (caller amount cap : Nat) (h : demand s caller amount cap = .ok (post, calls)) :
    ∃ position hint : Nat,
      post = {s with demands := s.demands.push ⟨position, amount, cap, hint⟩} ∧
      position = (if s.demands.isEmpty then 0 else
        s.demands.back!.position + s.demands.back!.amountIn) := by
  simp only [demand, bind, Except.bind, pure, Except.pure] at h
  repeat' (split at h <;> try simp_all)
  all_goals
    rcases h with ⟨hpost, _⟩
    subst post
    have hpos (z : Nat) (hz : checkedAdd s.demands.back!.position
        s.demands.back!.amountIn = .ok z) :
        z = s.demands.back!.position + s.demands.back!.amountIn :=
      (checked_add_ok hz).1
    simp_all only
    exact ⟨_, rfl⟩

private theorem demand_preserves (s post : QueueState) (calls : Array ExternalCall)
    (caller amount cap : Nat) (h : SourceSafe s)
    (he : demand s caller amount cap = .ok (post, calls)) : SourceSafe post := by
  obtain ⟨position, hint, rfl, hp⟩ := demand_success_shape s post calls caller amount cap he
  rcases h with ⟨⟨ho, hb, hd⟩, hf⟩
  exact ⟨⟨ordered_ends_push s ho position amount cap hint hp,
    history_bounds_push s hb position amount cap hint,
    hd⟩, by simpa only [SourceFundingSafe] using hf⟩

private theorem check_value_positive {x : Nat} {v : Unit}
    (h : checkValue x = .ok v) : 0 < x := by
  simp only [checkValue] at h
  split at h <;> simp_all

private theorem fulfill_success_shape (s post : QueueState) (calls : Array ExternalCall)
    (caller amount supplied : Nat)
    (h : fulfill s caller amount supplied = .ok (post, calls)) :
    ∃ position : Nat, post = {s with fulfillments :=
      (s.fulfillments.push (Fulfillment.mk position amount supplied))} ∧ 0 < amount := by
  simp only [fulfill, bind, Except.bind, pure, Except.pure] at h
  repeat' (split at h <;> try simp_all)
  all_goals
    rcases h with ⟨hpost, _⟩
    subst post
    refine ⟨⟨_, rfl⟩, ?_⟩
    exact check_value_positive (by assumption)

private theorem fulfill_preserves (s post : QueueState) (calls : Array ExternalCall)
    (caller amount supplied : Nat) (h : SourceSafe s)
    (he : fulfill s caller amount supplied = .ok (post, calls)) : SourceSafe post := by
  obtain ⟨position, rfl, hp⟩ := fulfill_success_shape s post calls caller amount supplied he
  rcases h with ⟨hg, hf⟩
  exact ⟨by simpa only [SourceGeometrySafe, OrderedDemandEnds,
    AllocationHistoryBounds, disjointAllocations] using hg,
    funding_push_fulfillment s hf ⟨position, amount, supplied⟩ hp⟩

/-- The two literal source writes are safe when the checked overlap and
mulDiv result have been extracted from a successful iteration. -/
private theorem safe_consumption (s : QueueState) (h : SourceSafe s)
    (j fid width payout cap hint : Nat) (hj : j < s.demands.size)
    (hw : width ≤ (s.demands[j]!).amountIn)
    (hnew : 0 < fid ∧ fid ≤ s.fulfillments.size ∧
      (s.fulfillments[fid - 1]!).position ≤ (s.demands[j]!).position ∧
      (s.demands[j]!).position + width ≤
        (s.fulfillments[fid - 1]!).position +
        (s.fulfillments[fid - 1]!).filledAmountIn ∧
      payout ≤ width * (s.fulfillments[fid - 1]!).amountOut /
        (s.fulfillments[fid - 1]!).filledAmountIn) :
    SourceSafe (geometryStep s j width fid payout cap hint) := by
  refine ⟨source_geometry_consumption s h.1 j hj width fid payout cap hint hw, ?_⟩
  let d' : Demand := ⟨(s.demands[j]!).position + width,
    (s.demands[j]!).amountIn - width, cap, hint⟩
  let pre : QueueState := {s with demands := s.demands.set! j d'}
  let a : Allocation := ⟨j + 1, fid, (s.demands[j]!).position, width, payout⟩
  have hf : SourceFundingSafe pre := by simpa only [SourceFundingSafe] using h.2
  have hp : SourceFundingSafe {pre with allocations := pre.allocations.push a} := by
    apply funding_push_allocation pre hf a
    simpa only [pre, a] using hnew
  simpa only [geometryStep, pre, a, d'] using hp


/-- Bounds extracted solely from the successful matching test, checked
endpoints, checked subtraction and Math.mulDiv floor. -/
private theorem checked_overlap_bounds (d : Demand) (f : Fulfillment)
    (dEnd fEnd width fAssets dAssets : Nat)
    (hm : _isMatchingFulfillment d.position f = .ok true)
    (hd : checkedAdd d.position d.amountIn = .ok dEnd)
    (hf : checkedAdd f.position f.filledAmountIn = .ok fEnd)
    (hw : checkedSub (min dEnd fEnd) (max d.position f.position) = .ok width)
    (hfloor : mulDivFloor width f.amountOut f.filledAmountIn = .ok fAssets) :
    width ≤ d.amountIn ∧ f.position ≤ d.position ∧
      d.position + width ≤ f.position + f.filledAmountIn ∧
      min dAssets fAssets ≤ width * f.amountOut / f.filledAmountIn := by
  have hm' := matching_ok hm
  have hd' := (checked_add_ok hd).1
  have hf' := (checked_add_ok hf).1
  have hw' := (checked_sub_ok hw).2
  have hfloor' := (mul_div_floor_ok hfloor).2
  have hstart : max d.position f.position = d.position := max_eq_left hm'.1
  rw [hstart] at hw'
  rcases le_total dEnd fEnd with hle | hle
  · have he : min dEnd fEnd = dEnd := min_eq_left hle
    rw [he] at hw'
    constructor
    · omega
    constructor
    · exact hm'.1
    constructor
    · have hwd : width = d.amountIn := by
        rw [hd'] at hw'
        simpa using hw'
      rw [hwd, ← hd', ← hf']
      exact hle
    · rw [hfloor']
      exact min_le_right _ _
  · have he : min dEnd fEnd = fEnd := min_eq_right hle
    rw [he] at hw'
    constructor
    · omega
    constructor
    · exact hm'.1
    constructor
    · have hpre : d.position ≤ fEnd := by
        rw [hf']
        exact Nat.le_of_lt hm'.2
      have hwidthEnd : d.position + width = fEnd := by
        rw [hw']
        exact Nat.add_sub_of_le hpre
      exact le_of_eq (hwidthEnd.trans hf')
    · rw [hfloor']
      exact min_le_right _ _


private theorem checked_source_post (s : QueueState) (hs : SourceSafe s)
    (id fid : Nat) (d : Demand) (f : Fulfillment)
    (dEnd fEnd width dAssets fAssets newPosition newAmount cap hint retrValue : Nat)
    (hvd : validDemand s id = .ok d)
    (hvf : validFulfillment s fid = .ok f)
    (hm : _isMatchingFulfillment d.position f = .ok true)
    (hde : checkedAdd d.position d.amountIn = .ok dEnd)
    (hfe : checkedAdd f.position f.filledAmountIn = .ok fEnd)
    (how : checkedSub (min dEnd fEnd) (max d.position f.position) = .ok width)
    (hmul : mulDivFloor width f.amountOut f.filledAmountIn = .ok fAssets)
    (hnpos : checkedAdd d.position width = .ok newPosition)
    (hnamount : checkedSub d.amountIn width = .ok newAmount) :
    SourceSafe ({s with retrievable := retrValue, demands := s.demands.set! (id - 1) (Demand.mk newPosition newAmount cap hint), allocations := s.allocations.push (Allocation.mk id fid d.position width (min dAssets fAssets))}) := by
  obtain ⟨hid, hsize, hdeq⟩ := valid_demand_ok hvd
  obtain ⟨hfid, hfsize, hfeq⟩ := valid_fulfillment_ok hvf
  obtain ⟨hw, hstart, hend, hpay⟩ :=
    checked_overlap_bounds d f dEnd fEnd width fAssets dAssets hm hde hfe how hmul
  have hj : id - 1 < s.demands.size := by omega
  have hnew : 0 < fid ∧ fid ≤ s.fulfillments.size ∧
      (s.fulfillments[fid - 1]!).position ≤ (s.demands[id - 1]!).position ∧
      (s.demands[id - 1]!).position + width ≤
        (s.fulfillments[fid - 1]!).position +
        (s.fulfillments[fid - 1]!).filledAmountIn ∧
      min dAssets fAssets ≤ width * (s.fulfillments[fid - 1]!).amountOut /
        (s.fulfillments[fid - 1]!).filledAmountIn := by
    simpa only [hdeq, hfeq] using
      (show 0 < fid ∧ fid ≤ s.fulfillments.size ∧ f.position ≤ d.position ∧
        d.position + width ≤ f.position + f.filledAmountIn ∧
        min dAssets fAssets ≤ width * f.amountOut / f.filledAmountIn from
          ⟨hfid, hfsize, hstart, hend, hpay⟩)
  have hstep := safe_consumption s hs (id - 1) fid width (min dAssets fAssets)
    cap hint hj (by simpa only [hdeq] using hw) hnew
  have hret : ∀ q : QueueState, SourceSafe q →
      SourceSafe {q with retrievable := retrValue} := by
    intro q hq
    simpa only [SourceSafe, SourceGeometrySafe, OrderedDemandEnds,
      AllocationHistoryBounds, disjointAllocations, SourceFundingSafe] using hq
  have hpos := (checked_add_ok hnpos).1
  have hamount := (checked_sub_ok hnamount).2
  have hid' : id - 1 + 1 = id := Nat.sub_add_cancel hid
  simpa only [geometryStep, hid', hdeq, hpos, hamount] using hret _ hstep

theorem redeem_one_preserves (id len : Nat) (c out : RedeemCursor)
    (hs : SourceSafe c.state) (he : _redeemOne id len c = .ok out) :
    SourceSafe out.state := by
  simp only [_redeemOne, bind, Except.bind, pure, Except.pure] at he
  repeat' (split at he <;> try simp_all)
  all_goals
    subst out
    first
    | simpa using hs
    | eapply checked_source_post c.state hs id c.fulfillmentId
      all_goals assumption


/-- An arbitrary finite checked iteration list preserves the strengthened
source invariant; instantiate this with the actual `List.range 32`. -/
theorem redeem_fold_preserves (id len : Nat) (xs : List Nat)
    (c out : RedeemCursor) (hs : SourceSafe c.state)
    (he : xs.foldlM (fun cursor _ => _redeemOne id len cursor) c = .ok out) :
    SourceSafe out.state := by
  induction xs generalizing c with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure] at he
    cases he
    exact hs
  | cons step rest ih =>
    simp only [List.foldlM_cons, bind, Except.bind] at he
    cases hstep : _redeemOne id len c with
    | «error» msg => simp [hstep] at he
    | ok next =>
      simp only [hstep] at he
      exact ih next (redeem_one_preserves id len c next hs hstep) he

/-- The exact source 32-fold preserves safety across repeated calls. -/
theorem redeem_demand_preserves (s post : QueueState) (id first paid : Nat)
    (hs : SourceSafe s)
    (he : _redeemDemandWithFulfillments s id first = .ok (post, paid)) :
    SourceSafe post := by
  simp only [_redeemDemandWithFulfillments, bind, Except.bind, pure,
    Except.pure] at he
  split at he
  · simp at he
  · rename_i cursor hcursor
    obtain ⟨rfl, _⟩ := Except.ok.inj he
    exact redeem_fold_preserves id s.fulfillments.size (List.range 32)
      ⟨s, first, 0, false⟩ cursor hs hcursor


/-- The source's lookup, guards and post-loop transfer add no further
accounting writes. -/
theorem redeem_preserves (s post : QueueState) (calls : Array ExternalCall)
    (caller id : Nat) (hs : SourceSafe s)
    (he : redeem s caller id = .ok (post, calls)) : SourceSafe post := by
  simp only [redeem, bind, Except.bind, pure, Except.pure] at he
  repeat' (split at he <;> try simp_all)
  all_goals
    have hresult : ∃ first : Nat, ∃ result : QueueState × Nat,
        _redeemDemandWithFulfillments s id first = .ok result ∧ result.1 = post :=
      ⟨_, _, by assumption, he.1⟩
    obtain ⟨first, ⟨q, paid⟩, hfold, rfl⟩ := hresult
    exact redeem_demand_preserves s q id first paid hs hfold


/-- Resolve changes a search hint alone, so every demand interval, recorded
allocation and immutable funding value remain identical. -/
private theorem hint_preserves (s : QueueState) (hs : SourceSafe s)
    (j hint : Nat) (hj : j < s.demands.size) :
    SourceSafe ({s with demands := s.demands.set! j ({(s.demands[j]!) with highestFulfillmentId := hint})}) := by
  let d' : Demand := {(s.demands[j]!) with highestFulfillmentId := hint}
  change SourceSafe {s with demands := s.demands.set! j d'}
  have hposition (i : Nat) : (s.demands.set! j d')[i]!.position =
      (s.demands[i]!).position := by
    by_cases hij : i = j
    · subst i
      simp only [get_set_bang_self s.demands j d' hj, d']
    · simp only [get_set_bang_ne s.demands j i d' (Ne.symm hij)]
  have hamount (i : Nat) : (s.demands.set! j d')[i]!.amountIn =
      (s.demands[i]!).amountIn := by
    by_cases hij : i = j
    · subst i
      simp only [get_set_bang_self s.demands j d' hj, d']
    · simp only [get_set_bang_ne s.demands j i d' (Ne.symm hij)]
  rcases hs with ⟨⟨ho, hb, ha⟩, hf⟩
  refine ⟨⟨?_, ?_, ha⟩, by simpa only [SourceFundingSafe] using hf⟩
  · intro i k hik hk
    have hk' : k < s.demands.size := by simpa only [size_set_bang] using hk
    simpa only [hposition, hamount] using ho i k hik hk'
  · intro a ha'
    obtain ⟨hid, hsize, hbound, hbefore⟩ := hb a ha'
    refine ⟨hid, by simpa only [size_set_bang] using hsize, ?_, ?_⟩
    · simpa only [hposition] using hbound
    · intro i hi
      simpa only [hposition, hamount] using hbefore i hi

private theorem resolve_preserves (s post : QueueState) (calls : Array ExternalCall)
    (id fid : Nat) (hs : SourceSafe s)
    (he : resolve s id fid = .ok (post, calls)) : SourceSafe post := by
  simp only [resolve, bind, Except.bind, pure, Except.pure] at he
  repeat' (split at he <;> try simp_all)
  all_goals
    obtain ⟨hpost, _⟩ := he
    subst post
    obtain ⟨hid, hsize, hd⟩ :=
      valid_demand_ok (by assumption : validDemand s id = .ok _)
    have hj : id - 1 < s.demands.size := by omega
    simpa only [hd, Array.set!] using hint_preserves s hs (id - 1) fid hj


private theorem initialize_preserves (s post : QueueState) (calls : Array ExternalCall)
    (parent manager assetIn assetOut : Nat) (hasIn hasOut : Bool)
    (decIn decOut : Nat) (hs : SourceSafe s)
    (he : «initialize» s parent manager assetIn assetOut hasIn hasOut decIn decOut =
      .ok (post, calls)) : SourceSafe post := by
  simp only [«initialize», throw_except, bind, Except.bind, pure,
    Except.pure] at he
  split_ifs at he
  simp_all
  obtain ⟨rfl, _⟩ := he
  simpa only [SourceSafe, SourceGeometrySafe, OrderedDemandEnds,
    AllocationHistoryBounds, disjointAllocations, SourceFundingSafe] using hs

private theorem retrieve_preserves (s post : QueueState) (calls : Array ExternalCall)
    (caller amount : Nat) (hs : SourceSafe s)
    (he : retrieve s caller amount = .ok (post, calls)) : SourceSafe post := by
  simp only [retrieve, bind, Except.bind, pure, Except.pure] at he
  repeat' (split at he <;> try simp_all)
  all_goals
    obtain ⟨hpost, _⟩ := he
    subst post
    simpa only [SourceSafe, SourceGeometrySafe, OrderedDemandEnds,
      AllocationHistoryBounds, disjointAllocations, SourceFundingSafe] using hs

/-- Every successful operation of the literal source interpreter preserves
the strengthened safety invariant; no condition on the operation is added. -/
theorem execute_preserves_source (s post : QueueState) (op : QueueOperation)
    (calls : Array ExternalCall) (hs : SourceSafe s)
    (he : execute s op = .ok (post, calls)) : SourceSafe post := by
  cases op with
  | «initialize» parent manager assetIn assetOut hasIn hasOut decIn decOut =>
    exact initialize_preserves s post calls parent manager assetIn assetOut
      hasIn hasOut decIn decOut hs he
  | demand caller amount cap =>
    exact demand_preserves s post calls caller amount cap hs he
  | fulfill caller amount supplied =>
    exact fulfill_preserves s post calls caller amount supplied hs he
  | redeem caller id =>
    exact redeem_preserves s post calls caller id hs he
  | resolve id fid =>
    exact resolve_preserves s post calls id fid hs he
  | retrieve caller amount =>
    exact retrieve_preserves s post calls caller amount hs he
  | redeemable id =>
    simp only [execute, bind, Except.bind, pure, Except.pure] at he
    split at he <;> simp_all
  | pending id =>
    simp only [execute, bind, Except.bind, pure, Except.pure] at he
    split at he <;> simp_all
  | demandFromId id =>
    simp only [execute, bind, Except.bind, pure, Except.pure] at he
    split at he <;> simp_all
  | fulfillmentFromId id =>
    simp only [execute, bind, Except.bind, pure, Except.pure] at he
    split at he <;> simp_all
  | lookup id =>
    simp only [execute, bind, Except.bind, pure, Except.pure] at he
    split at he <;> simp_all
  | unredeemable =>
    simp only [execute, bind, Except.bind, pure, Except.pure] at he
    split at he <;> simp_all
  | demandsCount | fulfillmentsCount | retrievable | multiVehicle | assetIn | assetOut =>
    simp only [execute] at he
    cases he
    exact hs

end Benchmark.Cases.RailnetV2.QueryRedeemQueueV2

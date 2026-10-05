import Benchmark.Cases.RailnetV2.QueryRedeemQueueV2.SourceInvariant

namespace Benchmark.Cases.RailnetV2.QueryRedeemQueueV2

/-- Source-derived strengthened invariant for every unrestricted reachable
state, including source reverts. -/
theorem sourceSafe_of_reachable (s : QueueState) (h : Reachable s) : SourceSafe s := by
  induction h with
  | init s hi => exact initialized_source_safe s hi
  | success s s' op calls _ he ih =>
    exact execute_preserves_source s s' op calls ih he
  | «revert» s op err _ he ih => exact ih

/-- Disjointness and per-fulfillment capacity are consequences of the source
transition induction, not hypotheses supplied by callers. -/
theorem derived_queue_induction_targets (s : QueueState) (hr : Reachable s) :
    queueInductionTargets s := by
  have hs := sourceSafe_of_reachable s hr
  have hinside : ∀ a ∈ s.allocations.toList,
      0 < a.fulfillmentId ∧ a.fulfillmentId ≤ s.fulfillments.size ∧
      (s.fulfillments[a.fulfillmentId - 1]!).position ≤ a.start ∧
      a.start + a.length ≤ (s.fulfillments[a.fulfillmentId - 1]!).position +
        (s.fulfillments[a.fulfillmentId - 1]!).filledAmountIn := by
    intro a ha
    obtain ⟨hid, hvalid, hstart, hend, _⟩ := hs.2.2 a ha
    exact ⟨hid, hvalid, hstart, hend⟩
  exact ⟨conservation_of_geometry_and_funding s hs.1 hs.2,
    hs.1.2.2,
    noDoubleSpend_of_disjoint_contained s hs.1.2.2 hinside⟩

/-- No premise on coverage, fulfillment budgets, redeem order or trace length. -/
theorem conservation_for_every_finite_history : conservationForEveryFiniteHistory := by
  intro s hi ops
  have hs := preserveHistory SourceSafe
    (fun pre op post calls => execute_preserves_source pre post op calls) s ops
    (initialized_source_safe s hi)
  exact conservation_of_geometry_and_funding _ hs.1 hs.2

/-- The same conservation result for the source-defined Reachable relation. -/
theorem conservation_for_every_reachable_state : conservationForEveryReachableState := by
  intro s hr
  have hs := sourceSafe_of_reachable s hr
  exact conservation_of_geometry_and_funding s hs.1 hs.2

/-- Structurally recursive callback trees preserve the same source-derived
invariant at every emitted transfer boundary, including the second fulfill
transfer. Any reverted invocation leaves its prestate intact. -/
theorem conservation_for_callbacks : conservationForCallbacks := by
  intro s hi schedule
  have hs := preserveCallbackHistory SourceSafe
    (fun pre op post calls => execute_preserves_source pre post op calls) s
    schedule (initialized_source_safe s hi)
  exact conservation_of_geometry_and_funding _ hs.1 hs.2

/-- Matching the benchmark task's agent-facing declaration without editing
its `?_` placeholder. This module is the separately built reference proof. -/
theorem nominal_conservation_all_histories : conservationForEveryFiniteHistory :=
  conservation_for_every_finite_history

end Benchmark.Cases.RailnetV2.QueryRedeemQueueV2

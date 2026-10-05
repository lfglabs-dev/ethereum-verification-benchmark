import Benchmark.Cases.RailnetV2.QueryRedeemQueueV2.Specs

namespace Benchmark.Cases.RailnetV2.QueryRedeemQueueV2

/-! The following three proofs follow the actual mutually structurally recursive
callback evaluator. They quantify over arbitrary finite nesting and arbitrary
finite sequences at each actual transfer site; failures restore the prestate. -/

mutual
  theorem preserveScheduled (P : QueueState → Prop)
      (hstep : ∀ s op post calls, P s → execute s op = .ok (post, calls) → P post)
      (s : QueueState) (n : ScheduledOperation) (hs : P s) :
      P (executeScheduled s n) := by
    cases n with
    | node op sites tokenOk =>
      simp only [executeScheduled]
      split
      · exact hs
      · rename_i post calls he
        split
        · exact hs
        · exact preserveCallSites P hstep post calls.toList sites
            (hstep s op post calls hs he)

  theorem preserveCallSites (P : QueueState → Prop)
      (hstep : ∀ s op post calls, P s → execute s op = .ok (post, calls) → P post)
      (s : QueueState) (calls : List ExternalCall) (sites : CallbackSites)
      (hs : P s) : P (executeCallSites s calls sites) := by
    cases sites with
    | nil => simpa only [executeCallSites] using hs
    | cons atSite rest =>
      cases calls with
      | nil => simpa only [executeCallSites] using hs
      | cons call remaining =>
        simpa only [executeCallSites] using
          preserveCallSites P hstep (executeCallbackSequence s atSite) remaining rest
            (preserveCallbackSequence P hstep s atSite hs)

  theorem preserveCallbackSequence (P : QueueState → Prop)
      (hstep : ∀ s op post calls, P s → execute s op = .ok (post, calls) → P post)
      (s : QueueState) (seq : CallbackSequence) (hs : P s) :
      P (executeCallbackSequence s seq) := by
    cases seq with
    | nil => simpa only [executeCallbackSequence] using hs
    | cons first rest =>
      simpa only [executeCallbackSequence] using
        preserveCallbackSequence P hstep (executeScheduled s first) rest
          (preserveScheduled P hstep s first hs)
end

/-- No bound on the outer schedule either. -/
theorem preserveCallbackHistory (P : QueueState → Prop)
    (hstep : ∀ s op post calls, P s → execute s op = .ok (post, calls) → P post)
    (s : QueueState) (schedule : List ScheduledOperation) (hs : P s) :
    P (executeCallbackHistory s schedule) := by
  unfold executeCallbackHistory
  induction schedule generalizing s with
  | nil => simpa using hs
  | cons first rest ih =>
    simpa only [List.foldl_cons] using
      ih (executeScheduled s first) (preserveScheduled P hstep s first hs)

/-- A matching unrestricted ordinary-history induction. -/
theorem preserveHistory (P : QueueState → Prop)
    (hstep : ∀ s op post calls, P s → execute s op = .ok (post, calls) → P post)
    (s : QueueState) (ops : List QueueOperation) (hs : P s) :
    P (executeHistory s ops) := by
  unfold executeHistory
  induction ops generalizing s with
  | nil => simpa using hs
  | cons op rest ih =>
    simp only [List.foldl_cons]
    apply ih
    unfold attempt
    split
    · rename_i post calls he
      simpa using hstep s op post calls hs he
    · exact hs

end Benchmark.Cases.RailnetV2.QueryRedeemQueueV2

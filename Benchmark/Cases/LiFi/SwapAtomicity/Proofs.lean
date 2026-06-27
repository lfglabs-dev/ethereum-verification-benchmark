import Benchmark.Cases.LiFi.SwapAtomicity.Specs
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Cases.LiFi.SwapAtomicity

open Verity
open Verity.EVM.Uint256

theorem failed_step_reverts
    (steps : List SwapStep) :
    failed_step_reverts_spec steps := by
  unfold failed_step_reverts_spec
  induction steps with
  | nil =>
      intro h
      rcases h with ⟨step, hMem, _hFail⟩
      cases hMem
  | cons head tail ih =>
      intro h
      rcases h with ⟨bad, hMem, hFail⟩
      simp [executeSwapsCount] at *
      rcases hMem with hHead | hTail
      · subst bad
        simp [hFail]
      · by_cases hHeadSucceeds : stepSucceeds head
        · simp [hHeadSucceeds, ih bad hTail hFail]
        · simp [hHeadSucceeds]

theorem no_final_transfer_on_failed_step
    (route : RouteGuards) (steps : List SwapStep)
    (minAmount outputAmount : Nat) :
    no_final_transfer_on_failed_step_spec route steps minAmount outputAmount := by
  unfold no_final_transfer_on_failed_step_spec
  intro hFailed
  have hExecNone := failed_step_reverts steps hFailed
  unfold finalTransferCommitted depositAndSwap
  by_cases hReceiver : route.receiverNonzero
  · simp [hReceiver]
    by_cases hReentrant : route.nonReentrantEntered
    · simp [hReentrant]
      by_cases hEmpty : steps = []
      · simp [hEmpty]
      · simp [hEmpty]
        by_cases hPre : route.preSwapBalanceReadsSucceed
        · simp [hPre]
          by_cases hDeposits : depositsSucceed steps
          · simp [hDeposits, hExecNone]
          · simp [hDeposits]
        · simp [hPre]
    · simp [hReentrant]
  · simp [hReceiver]

theorem final_transfer_implies_all_steps_succeeded
    (route : RouteGuards) (steps : List SwapStep)
    (minAmount outputAmount : Nat) :
    final_transfer_implies_all_steps_succeeded_spec
      route steps minAmount outputAmount := by
  unfold final_transfer_implies_all_steps_succeeded_spec allStepsSucceeded
  intro hFinal step hMem
  cases hStep : stepSucceeds step
  · have hNoFinal :=
      no_final_transfer_on_failed_step route steps minAmount outputAmount
        ⟨step, hMem, hStep⟩
    rw [hFinal] at hNoFinal
    cases hNoFinal
  · rfl

theorem committed_route_executes_every_step
    (route : RouteGuards) (steps : List SwapStep)
    (minAmount outputAmount : Nat) :
    committed_route_executes_every_step_spec route steps minAmount outputAmount := by
  unfold committed_route_executes_every_step_spec
  intro hFinal
  unfold committedSwapCount finalTransferCommitted depositAndSwap at *
  by_cases hReceiver : route.receiverNonzero
  · simp [hReceiver] at hFinal ⊢
    by_cases hReentrant : route.nonReentrantEntered
    · simp [hReentrant] at hFinal ⊢
      by_cases hEmpty : steps = []
      · simp [hEmpty] at hFinal
      · simp [hEmpty] at hFinal ⊢
        by_cases hPre : route.preSwapBalanceReadsSucceed
        · simp [hPre] at hFinal ⊢
          by_cases hDeposits : depositsSucceed steps
          · simp [hDeposits] at hFinal ⊢
            cases hExec : executeSwapsCount steps
            · simp [hExec] at hFinal
            · simp [hExec] at hFinal ⊢
              by_cases hLeftover : route.leftoverRefundsSucceed
              · simp [hLeftover] at hFinal ⊢
                by_cases hPost : route.postSwapBalanceReadSucceeds
                · simp [hPost] at hFinal ⊢
                  by_cases hMin : minAmount ≤ outputAmount
                  · simp [hMin] at hFinal ⊢
                    by_cases hTransfers :
                        route.finalTransferSucceeds = true ∧
                          route.excessNativeRefundSucceeds = true
                    · simp [hTransfers]
                    · simp [hTransfers] at hFinal
                  · simp [hMin] at hFinal
                · simp [hPost] at hFinal
              · simp [hLeftover] at hFinal
          · simp [hDeposits] at hFinal
        · simp [hPre] at hFinal
    · simp [hReentrant] at hFinal
  · simp [hReceiver] at hFinal

theorem min_output_required_for_commit
    (route : RouteGuards) (steps : List SwapStep)
    (minAmount outputAmount : Nat) :
    min_output_required_for_commit_spec route steps minAmount outputAmount := by
  unfold min_output_required_for_commit_spec
  intro hLt
  unfold finalTransferCommitted depositAndSwap
  by_cases hReceiver : route.receiverNonzero
  · simp [hReceiver]
    by_cases hReentrant : route.nonReentrantEntered
    · simp [hReentrant]
      by_cases hEmpty : steps = []
      · simp [hEmpty]
      · simp [hEmpty]
        by_cases hPre : route.preSwapBalanceReadsSucceed
        · simp [hPre]
          by_cases hDeposits : depositsSucceed steps
          · simp [hDeposits]
            cases executeSwapsCount steps
            · simp
            · simp
              by_cases hLeftover : route.leftoverRefundsSucceed
              · simp [hLeftover]
                by_cases hPost : route.postSwapBalanceReadSucceeds
                · simp [hPost]
                  have hNotLe : ¬ minAmount ≤ outputAmount :=
                    Nat.not_le_of_gt hLt
                  simp [hNotLe]
                · simp [hPost]
              · simp [hLeftover]
          · simp [hDeposits]
        · simp [hPre]
    · simp [hReentrant]
  · simp [hReceiver]

theorem route_gate_failure_prevents_commit
    (route : RouteGuards) (steps : List SwapStep)
    (minAmount outputAmount : Nat) :
    route_gate_failure_prevents_commit_spec
      route steps minAmount outputAmount := by
  unfold route_gate_failure_prevents_commit_spec routeGateFails
  intro hFail
  unfold finalTransferCommitted depositAndSwap
  rcases hFail with
    hEmpty | hReceiver | hReentrant | hPre | hDeposits | hLeftover | hPost |
    hFinal | hExcess
  · by_cases hReceiver : route.receiverNonzero <;> simp [hReceiver, hEmpty]
  · simp [hReceiver]
  · by_cases hReceiver : route.receiverNonzero <;> simp [hReceiver]
    simp [hReentrant]
  · by_cases hReceiver : route.receiverNonzero <;> simp [hReceiver]
    by_cases hReentrant : route.nonReentrantEntered <;> simp [hReentrant]
    by_cases hEmpty : steps = [] <;> simp [hEmpty]
    simp [hPre]
  · by_cases hReceiver : route.receiverNonzero <;> simp [hReceiver]
    by_cases hReentrant : route.nonReentrantEntered <;> simp [hReentrant]
    by_cases hEmpty : steps = [] <;> simp [hEmpty]
    by_cases hPre : route.preSwapBalanceReadsSucceed <;> simp [hPre]
    simp [hDeposits]
  · by_cases hReceiver : route.receiverNonzero <;> simp [hReceiver]
    by_cases hReentrant : route.nonReentrantEntered <;> simp [hReentrant]
    by_cases hEmpty : steps = [] <;> simp [hEmpty]
    by_cases hPre : route.preSwapBalanceReadsSucceed <;> simp [hPre]
    by_cases hDeposits : depositsSucceed steps <;> simp [hDeposits]
    cases executeSwapsCount steps <;> simp
    simp [hLeftover]
  · by_cases hReceiver : route.receiverNonzero <;> simp [hReceiver]
    by_cases hReentrant : route.nonReentrantEntered <;> simp [hReentrant]
    by_cases hEmpty : steps = [] <;> simp [hEmpty]
    by_cases hPre : route.preSwapBalanceReadsSucceed <;> simp [hPre]
    by_cases hDeposits : depositsSucceed steps <;> simp [hDeposits]
    cases executeSwapsCount steps <;> simp
    by_cases hLeftover : route.leftoverRefundsSucceed <;> simp [hLeftover]
    simp [hPost]
  · by_cases hReceiver : route.receiverNonzero <;> simp [hReceiver]
    by_cases hReentrant : route.nonReentrantEntered <;> simp [hReentrant]
    by_cases hEmpty : steps = [] <;> simp [hEmpty]
    by_cases hPre : route.preSwapBalanceReadsSucceed <;> simp [hPre]
    by_cases hDeposits : depositsSucceed steps <;> simp [hDeposits]
    cases executeSwapsCount steps <;> simp
    by_cases hLeftover : route.leftoverRefundsSucceed <;> simp [hLeftover]
    by_cases hPost : route.postSwapBalanceReadSucceeds <;> simp [hPost]
    by_cases hMin : minAmount ≤ outputAmount <;> simp [hMin]
    simp [hFinal]
  · by_cases hReceiver : route.receiverNonzero <;> simp [hReceiver]
    by_cases hReentrant : route.nonReentrantEntered <;> simp [hReentrant]
    by_cases hEmpty : steps = [] <;> simp [hEmpty]
    by_cases hPre : route.preSwapBalanceReadsSucceed <;> simp [hPre]
    by_cases hDeposits : depositsSucceed steps <;> simp [hDeposits]
    cases executeSwapsCount steps <;> simp
    by_cases hLeftover : route.leftoverRefundsSucceed <;> simp [hLeftover]
    by_cases hPost : route.postSwapBalanceReadSucceeds <;> simp [hPost]
    by_cases hMin : minAmount ≤ outputAmount <;> simp [hMin]
    simp [hExcess]

end Benchmark.Cases.LiFi.SwapAtomicity

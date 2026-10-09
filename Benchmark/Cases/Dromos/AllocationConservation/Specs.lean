import Benchmark.Cases.Dromos.AllocationConservation.Contract

/-! The Dromos Labs team's selected claim is allocationConserved. Set/support
validity is auxiliary induction machinery, not a second published guarantee.
Sums are ordinary natural-number sums over finite nonzero support. Completeness
connects that support to every full-width uint256 chain key, including zero.
No conservation theorem is assumed in the operational model. -/
namespace Benchmark.Cases.Dromos.AllocationConservation
open Verity

set_option maxHeartbeats 1000000

def allocationSum (s : ContractState) (tokenId : Uint256) : Nat :=
  (allocationChainIds s tokenId).foldr (fun chainId total => allocationChainAmounts s tokenId chainId + total) 0

def allocationConserved (s : ContractState) (tokenId : Uint256) : Prop :=
  allocationSum s tokenId = (tokenStates s tokenId).committed

def supportValid (s : ContractState) (tokenId : Uint256) : Prop :=
  (allocationChainIds s tokenId).Nodup ∧
  ∀ chainId : Uint256, chainId ∈ allocationChainIds s tokenId ↔ allocationChainAmounts s tokenId chainId > 0

def allocationRange (s : ContractState) (tokenId : Uint256) : Prop :=
  ∀ chainId : Uint256, allocationChainAmounts s tokenId chainId < amountLimit

-- OZ index-plus-one representation, distinct from amount support. This is a
-- proof predicate only: operations read stored positions, never this predicate.
def expectedPosition (ids : List Uint256) (chainId : Uint256) : Nat :=
  match ids.findIdx? (fun c => c == chainId) with
  | none => 0
  | some i => i + 1

def setRepresentationValid (s : ContractState) (tokenId : Uint256) : Prop :=
  (allocationChainIds s tokenId).Nodup ∧
  (allocationChainIds s tokenId).length < 2 ^ 256 ∧
  ∀ c : Uint256, allocationChainPositions s tokenId c = expectedPosition (allocationChainIds s tokenId) c

def ledgerInvariant (s : ContractState) : Prop :=
  ∀ tokenId : Uint256, allocationConserved s tokenId ∧ supportValid s tokenId ∧
    allocationRange s tokenId ∧ setRepresentationValid s tokenId

-- A sum over a finite superset of the support equals allocationSum when support
-- is valid and both enumerations have no duplicates. Phase 3 must prove the
-- corresponding independence theorem, not define off-set nonzero slots away.
def sumOver (s : ContractState) (tokenId : Uint256) (chains : List Uint256) : Nat :=
  chains.foldr (fun chainId total => allocationChainAmounts s tokenId chainId + total) 0

def allChainInterpretation (s : ContractState) (tokenId : Uint256) : Prop :=
  ∀ chains : List Uint256, chains.Nodup →
    (∀ c : Uint256, allocationChainAmounts s tokenId c > 0 → c ∈ chains) →
    sumOver s tokenId chains = (tokenStates s tokenId).committed

-- Constructor target-field postcondition; configuration, roles and timestamp
-- writes do not affect this condition. Source correspondence is manual.
def initializedLedger (s : ContractState) : Prop :=
  ∀ t : Uint256, allocationChainIds s t = [] ∧
    (tokenStates s t).committed = 0 ∧
    (∀ c : Uint256, allocationChainAmounts s t c = 0) ∧
    (∀ c : Uint256, allocationChainPositions s t c = 0)

inductive RootEntry where
  | allocateChains (tokenId : Uint256) (allocations : List ChainAllocation)
  | allocate (tokenId : Uint256) (allocations : List ChainAllocation)
      (gaugeBatchNonempty gaugeChecksPass : Bool)
  | burn (amount : Nat)
  | rebalanceChain0 (sources : List SourceDelta) (destinations : List DestinationDelta)
  | processDeallocation (message : DeallocationReturn)
  | emergencyDeallocate (tokenId chainId : Uint256) (registeredSuspended allowed gasProvided : Bool)
  | parkOnChain0 (tokenId : Uint256)
  | clearToken (tokenId : Uint256)
  | nonwriterWithReturns (returns : List DeallocationReturn)

def entryProgram (env : Environment) : RootEntry → Contract Unit
  | .allocateChains t xs => allocateChains env t xs
  | .allocate t xs nonempty checks => allocate env t xs nonempty checks
  | .burn x => burn env x
  | .rebalanceChain0 src dst => rebalanceChain0 env src dst
  | .processDeallocation r => processDeallocation env r
  | .emergencyDeallocate t c suspended allowed gas => emergencyDeallocate env t c suspended allowed gas
  | .parkOnChain0 t => parkOnChain0 env t
  | .clearToken t => clearToken env t
  | .nonwriterWithReturns rs => nonwriterWithReturns env rs

def preservesLedger (op : Contract Unit) : Prop :=
  ∀ before after : ContractState, ledgerInvariant before →
    op.run before = ContractResult.success () after → ledgerInvariant after

-- Operational success, not an invariant-constrained arbitrary post-state.
inductive Reachable : ContractState → Prop where
  | init {s : ContractState} : initializedLedger s → Reachable s
  | step {before after : ContractState} (env : Environment) (entry : RootEntry) :
      Reachable before → (entryProgram env entry).run before = ContractResult.success () after → Reachable after

def transactionConservation : Prop :=
  ∀ s : ContractState, Reachable s → ∀ t : Uint256, allChainInterpretation s t

end Benchmark.Cases.Dromos.AllocationConservation

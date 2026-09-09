import Benchmark.Cases.Paraclear.DirectDepositBacking.Execution

namespace Benchmark.Cases.Paraclear.DirectDepositBacking.Regression

def initial (decimals : Nat := 8) (balance : Int := 0) (custody : Nat := 100) :
    State (Fin 3) (Fin 3) where
  internalBalance := fun a t => if a = 1 ∧ t = 1 then balance else 0
  custodyRaw := fun _ => custody
  registeredAccounts := ∅
  reentrancyEntered := false
  globalDepositsAllowed := true
  assetsManagerConfigured := false
  tokenDepositsPaused := fun _ => false
  assetSupported := fun _ => true
  registryConfigured := true
  registryAllows := fun _ _ _ => true
  tokenDecimals := fun _ => decimals

def request (d : Nat := 8) (amount : Nat := 1) (custody : Nat := 100) :
    DirectDepositInput (Fin 3) (Fin 3) where
  kind := .self
  caller := 1
  requestedRecipient := 1
  token := 1
  amount8 := amount
  transfer := ⟨u256Max, true, custody, custody + toRaw amount d⟩

def failedAt (s : State (Fin 3) (Fin 3)) (i : DirectDepositInput (Fin 3) (Fin 3))
    (phase : DepositPhase) (calls := Dispatches.completed) : Bool :=
  firstFailure (sourceChecks s i calls) == some phase

def credited (s : State (Fin 3) (Fin 3)) (i : DirectDepositInput (Fin 3) (Fin 3))
    (expected : Int) : Bool :=
  match runOrderedDeposit s i .completed with
  | .error _ => false
  | .ok s' => s'.internalBalance 1 1 == expected && s'.custodyRaw 1 == i.transfer.balanceAfter
      && s'.internalBalance 2 1 == s.internalBalance 2 1
      && s'.custodyRaw 2 == s.custodyRaw 2
      && decide ((1 : Fin 3) ∈ s'.registeredAccounts) && !s'.reentrancyEntered

def checks : List (String × Bool) :=
  [("plain deposit", credited (initial) (request) 1),
   ("zero receipt still registers", credited (initial 6) (request 6 99) 0),
   ("six-decimal flooring", credited (initial 6) (request 6 101) 100),
   ("repay negative", credited (initial 8 (-5)) (request 8 3) (-2)),
   ("cross zero", credited (initial 8 (-2)) (request 8 5) 3),
   ("remove at zero", credited (initial 8 (-1)) (request) 0),
   ("registry absent", failedAt { initial with registryConfigured := false } (request) .registryConfigured),
   ("registry denies", failedAt { initial with registryAllows := fun _ _ _ => false } (request) .registry),
   ("registry reverts", failedAt (initial) (request) .registry { Dispatches.completed with registry := .reverted }),
   ("metadata malformed", failedAt (initial) (request) .decimals { Dispatches.completed with decimals := .malformed }),
   ("unconfigured manager not called", credited (initial) (request) 1 &&
     (firstFailure (sourceChecks (initial) (request)
       { Dispatches.completed with pause := .reverted }) == none)),
   ("configured manager reverts", failedAt { initial with assetsManagerConfigured := true }
     (request) .pause { Dispatches.completed with pause := .reverted }),
   ("paused", failedAt { initial with globalDepositsAllowed := false } (request) .globalPause),
   ("reentrant", failedAt { initial with reentrancyEntered := true } (request) .guard),
   ("unsupported before unset registry", failedAt
     { initial with assetSupported := fun _ => false, registryConfigured := false } (request) .support),
   ("amount cast overflow", failedAt (initial) (request 8 (i128MaxNat + 1)) .amountCast),
   ("raw multiplication overflow", failedAt (initial 9) (request 9 i128MaxNat) .scaling),
   ("33 decimals", failedAt (initial 33) (request 33 0) .scaling),
   ("signed addition overflow", failedAt (initial 8 i128Max) (request) .balanceUpdate),
   ("false transfer", failedAt (initial)
     { request with transfer := ⟨u256Max, false, 100, 101⟩ } .transfer),
   ("short receipt", failedAt (initial)
     { request with transfer := ⟨u256Max, true, 100, 100⟩ } .receipt),
   ("excess receipt", failedAt (initial)
     { request with transfer := ⟨u256Max, true, 100, 102⟩ } .receipt),
   ("decreasing receipt", failedAt (initial)
     { request with transfer := ⟨u256Max, true, 100, 99⟩ } .afterBalance),
   ("on behalf zero", failedAt (initial)
     { request with kind := .onBehalf, requestedRecipient := 0 } .recipient),
   ("on behalf distinct payer", credited (initial)
     { request with kind := .onBehalf, caller := 2 } 1),
   ("insufficient allowance", failedAt (initial)
     { request with transfer := ⟨0, true, 100, 101⟩ } .allowance),
   ("record create", (upsertRecord (1 : Fin 3) ⟨0, 0⟩ 7).amount == 7),
   ("record remove", (upsertRecord (1 : Fin 3) ⟨1, -7⟩ 7).tokenAddress == 0),
   ("malformed record witness", (upsertRecord (1 : Fin 3) ⟨0, 5⟩ 1).amount == 1)] ++
  ([0, 6, 8, 18, 32].map fun d =>
    (s!"precision {d}", credited (initial d) (request d 100000000)
      (depositCredit 100000000 d)))

def run : IO Unit := do
  for (name, passed) in checks do
    unless passed do throw (IO.userError s!"Paraclear regression failed: {name}")
  IO.println s!"Paraclear: {checks.length} model regressions passed (not Cairo execution)."

#eval run

end Benchmark.Cases.Paraclear.DirectDepositBacking.Regression

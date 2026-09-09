import Benchmark.Cases.Paraclear.DirectDepositBacking.Regression

/-! JSONL oracle for an independent, private Cairo integration runner.
All large integers are decimal strings. No expected result is sent to the runner.
This executable does not execute Cairo and is not itself a differential test. -/

open Benchmark.Cases.Paraclear.DirectDepositBacking
open Benchmark.Cases.Paraclear.DirectDepositBacking.Regression

private def fixture (id : String) (d a : Nat) (b : Int := 0) (custody : Nat := 100)
    (registry : Bool := true) (receiptDelta : Int := 0) (transferOk : Bool := true)
    (onBehalf : Bool := false) : Lean.Json := Id.run do
  let s := { initial d b custody with registryConfigured := registry }
  let i₀ := request d a custody
  let after := ((i₀.transfer.balanceAfter : Int) + receiptDelta).toNat
  let i := { i₀ with
    kind := (if onBehalf then .onBehalf else .self)
    caller := (if onBehalf then 2 else 1)
    transfer := { i₀.transfer with balanceAfter := after, transferSucceeded := transferOk } }
  let expected := match runSourceDeposit s i .completed with
    | .error _ => Lean.Json.mkObj [
        ("success", .bool false), ("custody_raw", .str (toString custody)),
        ("recipient_balance", .str (toString b)), ("registered", .bool false),
        ("guard_entered", .bool false)]
    | .ok s' => Lean.Json.mkObj [
        ("success", .bool true), ("custody_raw", .str (toString (s'.custodyRaw 1))),
        ("recipient_balance", .str (toString (s'.internalBalance 1 1))),
        ("registered", .bool (decide ((1 : Fin 3) ∈ s'.registeredAccounts))),
        ("guard_entered", .bool s'.reentrancyEntered)]
  return Lean.Json.mkObj [("id", .str id), ("input", Lean.Json.mkObj [
    ("decimals", Lean.toJson d), ("amount8", .str (toString a)),
    ("balance", .str (toString b)), ("custody_raw", .str (toString custody)),
    ("registry_configured", .bool registry), ("observed_after", .str (toString after)),
    ("transfer_ok", .bool transferOk), ("on_behalf", .bool onBehalf)]),
    ("expected", expected)]

def main : IO Unit := do
  let fixtures := ([0, 6, 8, 18, 32, 33].flatMap fun d =>
    [0, 1, 99, 100, 101, 100000000].map fun a => fixture s!"d{d}-a{a}" d a) ++
    [fixture "negative" 8 3 (-5), fixture "zero-removal" 8 5 (-5),
     fixture "cross-zero" 8 7 (-5), fixture "amount-overflow" 8 (i128MaxNat + 1),
     fixture "raw-overflow" 9 i128MaxNat, fixture "addition-overflow" 8 1 i128Max,
     fixture "registry-unset" 8 1 0 100 false,
     fixture "short-receipt" 8 1 0 100 true (-1),
     fixture "excess-receipt" 8 1 0 100 true 1,
     fixture "decreasing-balance" 8 1 0 100 true (-2),
     fixture "false-transfer" 8 1 0 100 true 0 false,
     fixture "on-behalf" 8 1 0 100 true 0 true true,
     fixture "custody-overflow" 8 1 0 u256Max]
  for row in fixtures do IO.println row.compress

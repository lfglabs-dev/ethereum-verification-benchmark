import Verity.Specs.Common
import Benchmark.Cases.Zama.ERC7984UpgradeableExactSource.Contract

namespace Benchmark.Cases.Zama.ERC7984UpgradeableExactSource

open Verity
open Verity.EVM.Uint256

/-- Logical plaintext-equivalent balance in the semantic model. -/
def balanceOf (s : ContractState) (account : Address) : Uint256 :=
  s.storageMap 1 account

/-- Logical model of `FHE.isInitialized($._balances[account])`. -/
def balanceIsInitialized (s : ContractState) (account : Address) : Prop :=
  s.storageMap 2 account ≠ 0

/-- Plaintext-equivalent amount selected by `FHE.select(success, amount, 0)`. -/
def selectedTransferAmount
    (s : ContractState) (sender : Address) (amount : Uint256) : Uint256 :=
  if balanceOf s sender >= amount then amount else 0

/--
The exact public-call result is the source guard's custom-error class with the
original pre-call state. Equality of the full `ContractResult` establishes both
reversion and rollback/no writes, rather than relying only on `.snd`.
-/
def uninitialized_sender_reverts_without_writes_spec
    (result : ContractResult Uint256) (preState : ContractState) : Prop :=
  result = ContractResult.revert "ERC7984ZeroBalance" preState

/--
With wrapper and plaintext address checks passed and the sender handle
initialized, transfer execution does not revert based on balance sufficiency.
No sufficient-balance hypothesis is present.
-/
def initialized_transfer_no_balance_revert_spec
    (result : ContractResult Uint256) : Prop :=
  result.isSuccess = true

/--
An initialized sender with insufficient balance gets a successful zero transfer.
The sender and recipient plaintext-equivalent balances are unchanged. This does
not claim that all logical storage is byte-for-byte unchanged: the source still
writes fresh ciphertext handles/ACL state, and the model records destination
initialization.
-/
def initialized_insufficient_transfer_zero_spec
    (sender recipient : Address) (preState : ContractState)
    (result : ContractResult Uint256) : Prop :=
  result.isSuccess = true ∧
  result.fst = 0 ∧
  balanceOf result.snd sender = balanceOf preState sender ∧
  balanceOf result.snd recipient = balanceOf preState recipient

/--
Pairwise transfer accounting is conserved only under explicit hypotheses used
by the theorem: distinct accounts, initialized sender, and no destination
addition wrap for the amount actually selected by the confidential comparison.
-/
def initialized_transfer_pair_conservation_spec
    (sender recipient : Address) (preState postState : ContractState) : Prop :=
  add (balanceOf postState sender) (balanceOf postState recipient) =
    add (balanceOf preState sender) (balanceOf preState recipient)

end Benchmark.Cases.Zama.ERC7984UpgradeableExactSource

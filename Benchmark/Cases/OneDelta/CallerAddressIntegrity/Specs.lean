import Verity.Specs.Common
import Benchmark.Cases.OneDelta.CallerAddressIntegrity.Contract

namespace Benchmark.Cases.OneDelta.CallerAddressIntegrity

open Verity
open Verity.EVM.Uint256

def outerCaller (s : ContractState) : Uint256 := s.storage 0
def erc20PullFrom (s : ContractState) : Uint256 := s.storage 1
def permit2PullFrom (s : ContractState) : Uint256 := s.storage 2
def flashCallbackCaller (s : ContractState) : Uint256 := s.storage 3
def swapCallbackCaller (s : ContractState) : Uint256 := s.storage 4
def v3CallbackPullFrom (s : ContractState) : Uint256 := s.storage 5
def erc20PullOccurred (s : ContractState) : Uint256 := s.storage 6
def permit2PullOccurred (s : ContractState) : Uint256 := s.storage 7
def v3CallbackPullOccurred (s : ContractState) : Uint256 := s.storage 8

def outerCallerWord (s : ContractState) : Uint256 :=
  addressToWord s.sender

def delta_compose_captures_outer_caller_spec (s s' : ContractState) : Prop :=
  outerCaller s' = outerCallerWord s

def erc20_pull_uses_outer_caller_spec (s s' : ContractState) : Prop :=
  erc20PullOccurred s' = 1 → erc20PullFrom s' = outerCallerWord s

def permit2_pull_uses_outer_caller_spec (s s' : ContractState) : Prop :=
  permit2PullOccurred s' = 1 → permit2PullFrom s' = outerCallerWord s

def flash_callback_preserves_outer_caller_spec (s s' : ContractState) : Prop :=
  flashCallbackCaller s' = outerCallerWord s

def swap_callback_preserves_outer_caller_spec (s s' : ContractState) : Prop :=
  swapCallbackCaller s' = outerCallerWord s

def v3_callback_direct_pull_uses_outer_caller_spec (s s' : ContractState) : Prop :=
  v3CallbackPullOccurred s' = 1 → v3CallbackPullFrom s' = outerCallerWord s

def all_path_batch_caller_integrity_spec (s s' : ContractState) : Prop :=
  outerCaller s' = outerCallerWord s ∧
  erc20PullOccurred s' = 1 ∧
  erc20PullFrom s' = outerCallerWord s ∧
  permit2PullOccurred s' = 1 ∧
  permit2PullFrom s' = outerCallerWord s ∧
  flashCallbackCaller s' = outerCallerWord s ∧
  swapCallbackCaller s' = outerCallerWord s ∧
  v3CallbackPullOccurred s' = 1 ∧
  v3CallbackPullFrom s' = outerCallerWord s

end Benchmark.Cases.OneDelta.CallerAddressIntegrity

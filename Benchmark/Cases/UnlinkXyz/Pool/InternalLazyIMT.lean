/-
  Verity model of `InternalLazyIMT` — the append-only Lazy Incremental
  Merkle Tree used by `UnlinkPool` for note commitments.

  Upstream: unlink-xyz/monorepo@7617b3eebcf37ab42124fe570eb7e065cf8c8461
  Source:   protocol/contracts/src/lib/InternalLazyIMT.sol
            (vendored from @zk-kit/lazy-imt.sol@2.0.0-beta.12)

  The on-chain `LazyIMTData` storage struct holds
  `(uint40 maxIndex, uint40 numberOfLeaves, mapping<uint=>uint> elements)`.
  In Lean we model this as a record where `elements` is a function
  `Nat -> Uint256` (matching EVM mapping semantics: missing keys read as
  zero). Poseidon hashing is delegated to `PoseidonT3.hash` from
  `Specs.lean` (assumed boundary).

  This module is pure Lean (not a `verity_contract` declaration); it is
  the trusted-base spec that the pool's `_insertLeaves` /
  `_validateContext` / `_verifyProof` paths consume.
-/
import Contracts.Common
import Benchmark.Cases.UnlinkXyz.Pool.Specs

namespace Benchmark.Cases.UnlinkXyz.Pool

open Verity hiding pure bind
open Verity.EVM.Uint256

/-! ### Vendored sibling `Constants.sol`

The vendored Lazy-IMT library carries its own `SNARK_SCALAR_FIELD` /
`MAX_DEPTH` constants to keep the upstream copy self-contained.
Numerically identical to `PoolConstants.SNARK_SCALAR_FIELD`. -/

namespace LazyIMTConstants
  def SNARK_SCALAR_FIELD : Uint256 :=
    PoolConstants.SNARK_SCALAR_FIELD
  def MAX_DEPTH : Nat := 32
end LazyIMTConstants

/-! ### struct LazyIMTData -/

structure LazyIMTData where
  maxIndex       : Uint256
  numberOfLeaves : Uint256
  elements       : Nat → Uint256
  deriving Inhabited

namespace InternalLazyIMT

/-- `uint40 internal constant MAX_INDEX = (1 << 32) - 1;`
    Note: the literal is `1 << 32 - 1`, not `(1 << 40) - 1` — this mirrors
    the source verbatim. -/
def MAX_INDEX : Uint256 :=
  Verity.Core.Uint256.sub (Verity.Core.Uint256.shl 32 1) 1

/-! ### Default zero subtree roots Z_0 .. Z_32 -/

def Z_0  : Uint256 := 0
def Z_1  : Uint256 := 14744269619966411208579211824598458697587494354926760081771325075741142829156
def Z_2  : Uint256 := 7423237065226347324353380772367382631490014989348495481811164164159255474657
def Z_3  : Uint256 := 11286972368698509976183087595462810875513684078608517520839298933882497716792
def Z_4  : Uint256 := 3607627140608796879659380071776844901612302623152076817094415224584923813162
def Z_5  : Uint256 := 19712377064642672829441595136074946683621277828620209496774504837737984048981
def Z_6  : Uint256 := 20775607673010627194014556968476266066927294572720319469184847051418138353016
def Z_7  : Uint256 := 3396914609616007258851405644437304192397291162432396347162513310381425243293
def Z_8  : Uint256 := 21551820661461729022865262380882070649935529853313286572328683688269863701601
def Z_9  : Uint256 := 6573136701248752079028194407151022595060682063033565181951145966236778420039
def Z_10 : Uint256 := 12413880268183407374852357075976609371175688755676981206018884971008854919922
def Z_11 : Uint256 := 14271763308400718165336499097156975241954733520325982997864342600795471836726
def Z_12 : Uint256 := 20066985985293572387227381049700832219069292839614107140851619262827735677018
def Z_13 : Uint256 := 9394776414966240069580838672673694685292165040808226440647796406499139370960
def Z_14 : Uint256 := 11331146992410411304059858900317123658895005918277453009197229807340014528524
def Z_15 : Uint256 := 15819538789928229930262697811477882737253464456578333862691129291651619515538
def Z_16 : Uint256 := 19217088683336594659449020493828377907203207941212636669271704950158751593251
def Z_17 : Uint256 := 21035245323335827719745544373081896983162834604456827698288649288827293579666
def Z_18 : Uint256 := 6939770416153240137322503476966641397417391950902474480970945462551409848591
def Z_19 : Uint256 := 10941962436777715901943463195175331263348098796018438960955633645115732864202
def Z_20 : Uint256 := 15019797232609675441998260052101280400536945603062888308240081994073687793470
def Z_21 : Uint256 := 11702828337982203149177882813338547876343922920234831094975924378932809409969
def Z_22 : Uint256 := 11217067736778784455593535811108456786943573747466706329920902520905755780395
def Z_23 : Uint256 := 16072238744996205792852194127671441602062027943016727953216607508365787157389
def Z_24 : Uint256 := 17681057402012993898104192736393849603097507831571622013521167331642182653248
def Z_25 : Uint256 := 21694045479371014653083846597424257852691458318143380497809004364947786214945
def Z_26 : Uint256 := 8163447297445169709687354538480474434591144168767135863541048304198280615192
def Z_27 : Uint256 := 14081762237856300239452543304351251708585712948734528663957353575674639038357
def Z_28 : Uint256 := 16619959921569409661790279042024627172199214148318086837362003702249041851090
def Z_29 : Uint256 := 7022159125197495734384997711896547675021391130223237843255817587255104160365
def Z_30 : Uint256 := 4114686047564160449611603615418567457008101555090703535405891656262658644463
def Z_31 : Uint256 := 12549363297364877722388257367377629555213421373705596078299904496781819142130
def Z_32 : Uint256 := 21443572485391568159800782191812935835534334817699172242223315142338162256601

/-- `_defaultZero(uint8 index)` returns `Z_index` for `0 <= index <= 32`,
    and reverts ("LazyIMT: defaultZero bad index") otherwise. -/
def _defaultZero (index : Uint256) : Contract Uint256 := do
  if index == 0  then return Z_0
  if index == 1  then return Z_1
  if index == 2  then return Z_2
  if index == 3  then return Z_3
  if index == 4  then return Z_4
  if index == 5  then return Z_5
  if index == 6  then return Z_6
  if index == 7  then return Z_7
  if index == 8  then return Z_8
  if index == 9  then return Z_9
  if index == 10 then return Z_10
  if index == 11 then return Z_11
  if index == 12 then return Z_12
  if index == 13 then return Z_13
  if index == 14 then return Z_14
  if index == 15 then return Z_15
  if index == 16 then return Z_16
  if index == 17 then return Z_17
  if index == 18 then return Z_18
  if index == 19 then return Z_19
  if index == 20 then return Z_20
  if index == 21 then return Z_21
  if index == 22 then return Z_22
  if index == 23 then return Z_23
  if index == 24 then return Z_24
  if index == 25 then return Z_25
  if index == 26 then return Z_26
  if index == 27 then return Z_27
  if index == 28 then return Z_28
  if index == 29 then return Z_29
  if index == 30 then return Z_30
  if index == 31 then return Z_31
  if index == 32 then return Z_32
  require false "LazyIMT: defaultZero bad index"
  return 0

/-- `_init(self, depth)`: requires `depth <= MAX_DEPTH`, sets
    `maxIndex := (1 << depth) - 1`, sets `numberOfLeaves := 0`. -/
def _init (self : LazyIMTData) (depth : Uint256) : Contract LazyIMTData := do
  require ((depth : Nat) <= LazyIMTConstants.MAX_DEPTH) "LazyIMT: Tree too large"
  let newMax : Uint256 :=
    Verity.Core.Uint256.sub (Verity.Core.Uint256.shl (depth : Nat) 1) 1
  return { self with maxIndex := newMax, numberOfLeaves := 0 }

/-- `_reset(self)`: zero `numberOfLeaves`. -/
def _reset (self : LazyIMTData) : LazyIMTData :=
  { self with numberOfLeaves := 0 }

/-- `_indexForElement(level, index) = MAX_INDEX * level + index`.
    Sparsely stores elements in the underlying `(uint256 => uint256)`
    mapping. -/
def _indexForElement (level index : Uint256) : Uint256 :=
  add (Verity.Core.Uint256.mul MAX_INDEX level) index

/-- Update helper: store `v` at key `k` in the elements mapping. -/
def setElement (self : LazyIMTData) (k : Uint256) (v : Uint256) : LazyIMTData :=
  { self with elements := fun n => if n == (k : Nat) then v else self.elements n }

/-- `_insert(self, leaf)`: append a leaf, fold-hash up the right spine. -/
partial def _insertLoop
    (self : LazyIMTData) (i : Uint256) (index : Uint256) (hash : Uint256) :
    LazyIMTData :=
  let self' := setElement self (_indexForElement i index) hash
  if Verity.Core.Uint256.and index 1 == 0 then
    self'
  else
    let elementIndex := _indexForElement i (sub index 1)
    let newHash := PoseidonT3.hash (self'.elements (elementIndex : Nat), hash)
    _insertLoop self' (add i 1) (Verity.Core.Uint256.shr 1 index) newHash

def _insert (self : LazyIMTData) (leaf : Uint256) : Contract LazyIMTData := do
  let index := self.numberOfLeaves
  require ((leaf : Nat) < (LazyIMTConstants.SNARK_SCALAR_FIELD : Nat))
    "LazyIMT: leaf must be < SNARK_SCALAR_FIELD"
  require ((index : Nat) < (self.maxIndex : Nat)) "LazyIMT: tree is full"
  let self' := { self with numberOfLeaves := add index 1 }
  return _insertLoop self' 0 index leaf

/-- `_update(self, leaf, index)`: overwrite an existing leaf and re-hash. -/
partial def _updateLoop
    (self : LazyIMTData) (numberOfLeaves : Uint256)
    (i : Uint256) (index : Uint256) (hash : Uint256) : LazyIMTData :=
  let self' := setElement self (_indexForElement i index) hash
  let levelCount := Verity.Core.Uint256.shr (add i 1) numberOfLeaves
  if levelCount <= Verity.Core.Uint256.shr 1 index then
    self'
  else
    let newHash :=
      if Verity.Core.Uint256.and index 1 == 0 then
        let elementIndex := _indexForElement i (add index 1)
        PoseidonT3.hash (hash, self'.elements (elementIndex : Nat))
      else
        let elementIndex := _indexForElement i (sub index 1)
        PoseidonT3.hash (self'.elements (elementIndex : Nat), hash)
    _updateLoop self' numberOfLeaves (add i 1) (Verity.Core.Uint256.shr 1 index) newHash

def _update (self : LazyIMTData) (leaf : Uint256) (index : Uint256) :
    Contract LazyIMTData := do
  require ((leaf : Nat) < (LazyIMTConstants.SNARK_SCALAR_FIELD : Nat))
    "LazyIMT: leaf must be < SNARK_SCALAR_FIELD"
  let numberOfLeaves := self.numberOfLeaves
  require ((index : Nat) < (numberOfLeaves : Nat)) "LazyIMT: leaf must exist"
  return _updateLoop self numberOfLeaves 0 index leaf

/-- `_levels` writes the spine from the rightmost leaf upward. -/
partial def _levelsLoop
    (self : LazyIMTData) (numberOfLeaves : Uint256) (depth : Uint256)
    (i : Uint256) (index : Uint256) (levels : Nat → Uint256) :
    Contract (Nat → Uint256) := do
  if (i : Nat) >= (depth : Nat) then
    return levels
  let newLevels : Nat → Uint256 ←
    if Verity.Core.Uint256.and index 1 == 0 then do
      let z ← _defaultZero i
      let lhs := levels (i : Nat)
      let v := PoseidonT3.hash (lhs, z)
      pure (fun n => if n == ((i : Nat) + 1) then v else levels n)
    else do
      let levelCount := Verity.Core.Uint256.shr (add i 1) numberOfLeaves
      if levelCount > Verity.Core.Uint256.shr 1 index then
        let parent :=
          self.elements ((_indexForElement (add i 1) (Verity.Core.Uint256.shr 1 index)) : Nat)
        pure (fun n => if n == ((i : Nat) + 1) then parent else levels n)
      else
        let sibling := self.elements ((_indexForElement i (sub index 1)) : Nat)
        let v := PoseidonT3.hash (sibling, levels (i : Nat))
        pure (fun n => if n == ((i : Nat) + 1) then v else levels n)
  _levelsLoop self numberOfLeaves depth
    (add i 1) (Verity.Core.Uint256.shr 1 index) newLevels

def _levels (self : LazyIMTData) (numberOfLeaves : Uint256) (depth : Uint256)
    (levels : Nat → Uint256) : Contract (Nat → Uint256) := do
  require ((depth : Nat) <= LazyIMTConstants.MAX_DEPTH) "LazyIMT: depth must be <= MAX_DEPTH"
  require ((numberOfLeaves : Nat) > 0) "LazyIMT: number of leaves must be > 0"
  let index := sub numberOfLeaves 1
  let levels0 : Nat → Uint256 ←
    if Verity.Core.Uint256.and index 1 == 0 then
      pure (fun n => if n == 0 then self.elements ((_indexForElement 0 index) : Nat) else levels n)
    else do
      let z ← _defaultZero 0
      pure (fun n => if n == 0 then z else levels n)
  _levelsLoop self numberOfLeaves depth 0 index levels0

/-- `_root(self, numberOfLeaves, depth)` — explicit-depth root. -/
def _rootAt (self : LazyIMTData) (numberOfLeaves : Uint256) (depth : Uint256) :
    Contract Uint256 := do
  require ((depth : Nat) <= LazyIMTConstants.MAX_DEPTH) "LazyIMT: depth must be <= MAX_DEPTH"
  if numberOfLeaves == 0 then
    _defaultZero depth
  else do
    let levels ← _levels self numberOfLeaves depth (fun _ => 0)
    return levels (depth : Nat)

/-- Dynamic-depth descent: find the smallest depth such that
    `2^depth >= numberOfLeaves`. -/
partial def _rootDynamicDepth (numberOfLeaves : Uint256) (depth : Uint256) : Uint256 :=
  let pow := Verity.Core.Uint256.shl (depth : Nat) 1
  if pow < numberOfLeaves then
    _rootDynamicDepth numberOfLeaves (add depth 1)
  else
    depth

def _root (self : LazyIMTData) : Contract Uint256 := do
  let numberOfLeaves := self.numberOfLeaves
  let depth := _rootDynamicDepth numberOfLeaves 1
  _rootAt self numberOfLeaves depth

/-- Explicit-depth `_root(self, depth)`. -/
def _rootWithDepth (self : LazyIMTData) (depth : Uint256) : Contract Uint256 := do
  require ((depth : Nat) > 0) "LazyIMT: depth must be > 0"
  require ((depth : Nat) <= LazyIMTConstants.MAX_DEPTH) "LazyIMT: depth must be <= MAX_DEPTH"
  let numberOfLeaves := self.numberOfLeaves
  let pow := Verity.Core.Uint256.shl (depth : Nat) 1
  require ((pow : Nat) >= (numberOfLeaves : Nat)) "LazyIMT: ambiguous depth"
  _rootAt self numberOfLeaves depth

/-- Merkle-proof element extraction (tail loop). -/
partial def _proofTailLoop
    (self : LazyIMTData) (numberOfLeaves : Uint256) (depth : Uint256)
    (i : Uint256) (index : Uint256) (elements : Nat → Uint256) :
    Contract (Nat → Uint256) := do
  if (i : Nat) >= (depth : Nat) then
    return elements
  let currentLevelCount := Verity.Core.Uint256.shr (i : Nat) numberOfLeaves
  let elements' : Nat → Uint256 ←
    if Verity.Core.Uint256.and index 1 == 0 then
      if (add index 1 : Nat) < (currentLevelCount : Nat) then
        let v := self.elements ((_indexForElement i (add index 1)) : Nat)
        pure (fun n => if n == (i : Nat) then v else elements n)
      else if (Verity.Core.Uint256.shr (i : Nat) (sub numberOfLeaves 1) : Nat) <= (index : Nat) then do
        let z ← _defaultZero i
        pure (fun n => if n == (i : Nat) then z else elements n)
      else
        pure elements
    else
      let v := self.elements ((_indexForElement i (sub index 1)) : Nat)
      pure (fun n => if n == (i : Nat) then v else elements n)
  _proofTailLoop self numberOfLeaves depth
    (add i 1) (Verity.Core.Uint256.shr 1 index) elements'

def _merkleProofElements (self : LazyIMTData) (index : Uint256) (depth : Uint256) :
    Contract (Nat → Uint256) := do
  let numberOfLeaves := self.numberOfLeaves
  require ((index : Nat) < (numberOfLeaves : Nat)) "LazyIMT: leaf must exist"
  let targetDepth := _rootDynamicDepth numberOfLeaves 1
  require ((depth : Nat) >= (targetDepth : Nat)) "LazyIMT: proof depth"
  let elementsInit ← _levels self numberOfLeaves (sub targetDepth 1) (fun _ => 0)
  let bottom : Nat → Uint256 ←
    if Verity.Core.Uint256.and index 1 == 0 then
      if (add index 1 : Nat) >= (numberOfLeaves : Nat) then do
        let z ← _defaultZero 0
        pure (fun n => if n == 0 then z else elementsInit n)
      else
        let v := self.elements ((_indexForElement 0 (add index 1)) : Nat)
        pure (fun n => if n == 0 then v else elementsInit n)
    else
      let v := self.elements ((_indexForElement 0 (sub index 1)) : Nat)
      pure (fun n => if n == 0 then v else elementsInit n)
  _proofTailLoop self numberOfLeaves depth 1 (Verity.Core.Uint256.shr 1 index) bottom

end InternalLazyIMT

end Benchmark.Cases.UnlinkXyz.Pool

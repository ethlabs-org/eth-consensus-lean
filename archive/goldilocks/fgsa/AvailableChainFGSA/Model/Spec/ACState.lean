module
public import AvailableChainFGSA.Model.Spec.Objects -- shake: keep (re-export)
public import AvailableChainFGSA.Model.Store
public import Mathlib.Order.WithBot -- shake: keep (re-export)
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace AvailableChain.FGSA.Spec

/-- [spec 973–1039] AC state A. Blocks here are shared geometric names, not a store.
A block timestamp of `some ⊥` is genesis; `none` is an unseen name.
Negative slots are represented explicitly. Receipt stamps use continuous time;
lock deadlines remain public (integer) times. The head is computed at read time. -/
structure ACState (n : Nat) where
  pool : Int → List (HeadWire n) := fun _ => []
  voteStamp : HeadWire n → Option ℝ := fun _ => none
  blockStamp : AvailableChain.Block → Option (WithBot ℝ) :=
    fun B => if B = .genesis then some ⊥ else none
  saved : Int → Option AvailableChain.Block := fun _ => none
  locks : List (AvailableChain.Block × Time) := []
  fast_confirmed : List AvailableChain.Block := []
  record : AvailableChain.Block := .genesis

/-- [spec 993–1013] Live lock entries, projected to the current frame tree. -/
def liveEntries (tree : List AvailableChain.Block) (t : Time)
    (entries : List (AvailableChain.Block × Time)) : List (AvailableChain.Block × Time) :=
  entries.filter (fun e => decide (t < e.2 ∧ e.1 ∈ tree))

/-- [spec 993–999; Lean notes 78–108] A per-block deadline is the maximum
entry deadline above the block. The empty maximum is minus infinity. -/
def lockMap (entries : List (AvailableChain.Block × Time)) (B : AvailableChain.Block) :
    WithBot Time :=
  entries.foldr (fun e d => if AvailableChain.Block.preceq B e.1 then
    max (e.2 : WithBot Time) d else d) ⊥

/-- [spec 995–996] A block is locked by a live entry at or above it. -/
def locked (tree : List AvailableChain.Block) (t : Time)
    (entries : List (AvailableChain.Block × Time)) (B : AvailableChain.Block) : Prop :=
  ∃ e ∈ liveEntries tree t entries, AvailableChain.Block.Preceq B e.1

/-- [spec 1022–1029; Lean notes 120–127] The core record C, before output clamping.
The admitted-store relation identifies tree membership with this prefix test. -/
def normalizeRecord (F C : AvailableChain.Block) : AvailableChain.Block :=
  if AvailableChain.Block.preceq F C then C else F

/-- [spec 993–1013; Lean notes 84–108] Pointwise lease correspondence only on
non-genesis blocks of the current tree. No equality below F is required. -/
def LeaseRelation (st : State n) (tree : List AvailableChain.Block) (t : Time)
    (entries : List (AvailableChain.Block × Time)) : Prop :=
  ∀ B ∈ tree, B ≠ .genesis →
    ((leaseOf st B).map (fun d => (d : WithBot Time))).getD ⊥ =
      lockMap (liveEntries tree t entries) B

-- Generate equations in their owning model module (BUILD B3a).
private theorem liveEntries_eq_1_export :
    type_of% (@liveEntries.eq_1) := @liveEntries.eq_1
private theorem lockMap_eq_1_export :
    type_of% (@lockMap.eq_1) := @lockMap.eq_1
private theorem locked_eq_1_export :
    type_of% (@locked.eq_1) := @locked.eq_1
private theorem normalizeRecord_eq_1_export :
    type_of% (@normalizeRecord.eq_1) := @normalizeRecord.eq_1
private theorem LeaseRelation_eq_1_export :
    type_of% (@LeaseRelation.eq_1) := @LeaseRelation.eq_1

end AvailableChain.FGSA.Spec
end

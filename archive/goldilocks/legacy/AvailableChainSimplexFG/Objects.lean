module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import AvailableChainModel.Objects.Blocks -- shake: keep (re-export)
public import AvailableChainModel.Objects.Identifiers
public import AvailableChainModel.Objects.Time

@[expose] public section

namespace AvailableChain.SimplexFG

open AvailableChain

abbrev Height := Nat

-- port: DC/DecoupledConsensusModel/Objects/NamedBlocks.lean:31–48
/-- The height pair of a row, bound to an entry. -/
inductive NamedHeightPair where
  | empty
  | vote (height : Height) (entry : BlockId) (timeout : Bool)
  deriving DecidableEq, Repr

namespace NamedHeightPair
/-- Targets and timeouts use the same height and entry match. -/
def matchesEntry (height : Height) (entry : BlockId) : NamedHeightPair → Bool
  | .empty => false
  | .vote h target _ => decide (h = height ∧ target = entry)
end NamedHeightPair

/-- The finality pair `(h_f, T_f)` (port: DC/DecoupledConsensusModel/Objects/Blocks.lean:60–66). -/
structure FinalityPair where
  height : Height
  target : BlockId
  deriving DecidableEq, Repr

/-- One FG row: signer, height pair, finality pair. No SG field. -/
structure Row (V : Type) where
  signer : V
  height_pair : NamedHeightPair
  finality_pair : Option FinalityPair
  deriving DecidableEq, Repr

/-- [ROOT-DIGEST W1; DC NamedBlocks and RootInjectiveOnAncestors]
An injective code of signer identities (D10). The row code reads it, so one
fixed code for each `V` gives one body serialization. -/
class RowCodec (V : Type) where
  encodeSigner : V → Nat
  encodeSigner_inj : Function.Injective encodeSigner

/-- The signer code of `Fin n` is the value. -/
instance {n : Nat} : RowCodec (Fin n) := ⟨Fin.val, Fin.val_injective⟩

/-! ### Row codes

Each code is built from `epair`, `encList`, `encOption` and `encBool`
(`Objects/Codec.lean`). A structure is a nested pair in its field order. The
code of a row holds every field of the row, so every root that a row names
enters the code: the entry of the height pair and the target of the finality
pair. A list keeps its order and its duplicates. -/

/-- The height-pair code: `0` for the empty pair; the height, the entry root
and the timeout bit, plus one, for a vote. -/
def encHeightPair : NamedHeightPair → Nat
  | .empty => 0
  | .vote h e t => epair h (epair e.value (encBool t)) + 1

/-- The finality-pair code: the height and the target root. -/
def encFinalityPair (p : FinalityPair) : Nat := epair p.height p.target.value

/-- The row code: the signer, the height pair and the optional finality pair. -/
def encRow {V : Type} [RowCodec V] (r : Row V) : Nat :=
  epair (RowCodec.encodeSigner r.signer)
    (epair (encHeightPair r.height_pair) (encOption encFinalityPair r.finality_pair))

/-- The domain tag of an FG body code (`encFGBody`). -/
def fgBodyTag : Nat := 1

/-- The body code of an FG node: the domain tag `fgBodyTag`, the body `x` and
the ordered row list. The tag reserves typed domains for base application
bodies: a later plan can give another domain a different tag, and the codes of
two domains do not collide. The code is not `0` (the honest base body), because
the first component of the pair is not `0`. -/
def encFGBody {V : Type} [RowCodec V] (x : Nat) (rows : List (Row V)) : Nat :=
  epair fgBodyTag (epair x (encList encRow rows))

theorem encHeightPair_inj : Function.Injective encHeightPair := by
  intro a b hab
  cases a with
  | empty => cases b <;> simp_all [encHeightPair]
  | vote h₁ e₁ t₁ =>
    cases b with
    | empty => simp [encHeightPair] at hab
    | vote h₂ e₂ t₂ =>
      simp only [encHeightPair, Nat.add_right_cancel_iff] at hab
      obtain ⟨rfl, hrest⟩ := epair_inj hab
      obtain ⟨he, ht⟩ := epair_inj hrest
      rw [BlockId.ext he, encBool_inj ht]

theorem encFinalityPair_inj : Function.Injective encFinalityPair := by
  intro a b h
  obtain ⟨h₁, h₂⟩ := epair_inj h
  cases a; cases b
  cases h₁; cases BlockId.ext h₂; rfl

theorem encRow_inj {V : Type} [RowCodec V] : Function.Injective (encRow (V := V)) := by
  intro a b h
  obtain ⟨hs, h⟩ := epair_inj h
  obtain ⟨hh, hf⟩ := epair_inj h
  cases a; cases b
  cases RowCodec.encodeSigner_inj hs
  cases encHeightPair_inj hh
  cases encOption_inj encFinalityPair_inj hf
  rfl

/-- The body code is injective in the pair: the body and the ordered rows. -/
theorem encFGBody_inj {V : Type} [RowCodec V] {x y : Nat} {rs ts : List (Row V)}
    (h : encFGBody x rs = encFGBody y ts) : x = y ∧ rs = ts := by
  obtain ⟨-, h⟩ := epair_inj h
  obtain ⟨hx, hr⟩ := epair_inj h
  exact ⟨hx, encList_inj encRow_inj hr⟩

/-- A block as the FG reads it. The AP maps its blocks to this type later. A
node carries a body, its rows, and its root (ROOT-DIGEST W1; DC NamedBlocks). -/
inductive FGBlock (V : Type) where
  | genesis
  | node (parent : FGBlock V) (slot : Slot) (root : BlockId) (body : Nat) (rows : List (Row V))
  deriving DecidableEq, Repr

namespace FGBlock
variable {V : Type}
def slot : FGBlock V → Slot
  | .genesis => 0
  | .node _ s _ _ _ => s
/-- The body of a node (`0` for genesis). -/
def body : FGBlock V → Nat
  | .genesis => 0
  | .node _ _ _ x _ => x
def parent : FGBlock V → FGBlock V
  | .genesis => .genesis
  | .node p _ _ _ _ => p
def rows : FGBlock V → List (Row V)
  | .genesis => []
  | .node _ _ _ _ rs => rs

section Root

/-- [ROOT-DIGEST W1; DC NamedBlocks] Read the stored root. -/
def root [RowCodec V] : FGBlock V → BlockId
  | .genesis => genesisRoot
  | .node _ _ r _ _ => r

/-- [ROOT-DIGEST W1; DC NamedRootCollisionFree] Scoped node/genesis separation. -/
theorem root_ne_genesis_of_node [RowCodec V] (p : FGBlock V) (s : Slot) (r : BlockId)
    (x : Nat) (rs : List (Row V))
    (hr : (FGBlock.node p s r x rs).root = genesisRoot →
      FGBlock.node p s r x rs = .genesis) :
    (FGBlock.node p s r x rs).root ≠ genesisRoot := by
  intro h
  have he := hr h
  cases he

end Root

variable [DecidableEq V]
def preceq (A : FGBlock V) : FGBlock V → Bool
  | .genesis => decide (A = .genesis)
  | B@(.node p _ _ _ _) => decide (A = B) || preceq A p
def Preceq (A B : FGBlock V) : Prop := preceq A B = true
instance (A B : FGBlock V) : Decidable (Preceq A B) :=
  inferInstanceAs (Decidable (preceq A B = true))
def compatible (A B : FGBlock V) : Bool := preceq A B || preceq B A
end FGBlock

-- port: DC/DecoupledConsensusModel/Protocol/Evidence.lean `chain_attestations`
/-- The rows carried by the chain that ends at `B`. -/
def chainRows {V : Type} [DecidableEq V] : FGBlock V → Finset (Row V)
  | .genesis => ∅
  | .node p _ _ _ rs => rs.toFinset ∪ chainRows p

-- port: DC/DecoupledConsensusModel/Objects/Weights.lean:49–78
/-- Fixed positive weights. FG-SA uses weight 1. -/
structure Electorate (V : Type) [Fintype V] where
  weight : V → Nat
  weight_pos : ∀ i, 0 < weight i

namespace Electorate
variable {V : Type} [Fintype V] [DecidableEq V]
def totalWeight (E : Electorate V) : Nat := ∑ i, E.weight i
def weightOf (E : Electorate V) (S : Finset V) : Nat := ∑ i ∈ S, E.weight i
/-- `q = ⌈2W/3⌉`; with unit weights this is FG-SA's `q_F = (2n+2) div 3`. -/
def q (E : Electorate V) : Nat := (2 * E.totalWeight + 2) / 3
def IsQuorum (E : Electorate V) (S : Finset V) : Prop := E.q ≤ E.weightOf S
end Electorate

example : (FGBlock.genesis : FGBlock (Fin 1)).preceq .genesis = true := by decide
example : (NamedHeightPair.vote 2 ⟨5⟩ true).matchesEntry 2 ⟨5⟩ = true := by decide
example : (⟨fun _ => 1, fun _ => Nat.one_pos⟩ : Electorate (Fin 4)).q = 3 := by decide

/-- An FG body code is never the honest base body `0`. -/
example : encFGBody (V := Fin 1) 0 [] ≠ 0 := by decide

/-- The body code separates rows that differ only in the signer, the timeout
bit or the finality pair, and row lists that differ only in order or in a
duplicate. -/
example :
    let r : Row (Fin 2) := ⟨0, .vote 1 ⟨3⟩ false, none⟩
    let r₁ : Row (Fin 2) := ⟨1, .vote 1 ⟨3⟩ false, none⟩
    let rt : Row (Fin 2) := ⟨0, .vote 1 ⟨3⟩ true, none⟩
    let rf : Row (Fin 2) := ⟨0, .vote 1 ⟨3⟩ false, some ⟨0, ⟨0⟩⟩⟩
    encFGBody 0 [r] ≠ encFGBody 0 [r₁] ∧ encFGBody 0 [r] ≠ encFGBody 0 [rt] ∧
      encFGBody 0 [r] ≠ encFGBody 0 [rf] ∧ encFGBody 0 [r, r₁] ≠ encFGBody 0 [r₁, r] ∧
      encFGBody 0 [r] ≠ encFGBody 0 [r, r] := by
  decide

end AvailableChain.SimplexFG
end

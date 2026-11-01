module
public import AvailableChainKitFG.NoEarlyMixed -- shake: keep (axioms)

set_option linter.privateModule false

namespace AvailableChain.KitFG.Tests.NoEarlyMixedAxioms

open AvailableChain.SimplexFG

#print axioms no_mixed_cross_before_maturity
#print axioms first_height_crossing_edge
#print axioms crossing_honest_matching_row
#print axioms justification_eq_on_plateau

def j3UnitElectorateOne : Electorate (Fin 1) := ⟨fun _ => 1, fun _ => Nat.one_pos⟩
def j3UnitElectorateEmpty : Electorate (Fin 0) := ⟨fun _ => 1, fun _ => Nat.one_pos⟩
def j3TimeoutThree : FGConfig := ⟨3⟩
def j3TargetRow : Row (Fin 1) := ⟨0, .vote 1 genesisRoot false, none⟩
def j3TimeoutRow : Row (Fin 1) := ⟨0, .vote 1 genesisRoot true, none⟩
def j3EarlyTarget : FGBlock (Fin 1) := .node .genesis 2 ⟨100⟩ 0 [j3TargetRow]

-- A single target row crosses before maturity, with U = X.parent = genesis.
example : (derive j3UnitElectorateOne j3TimeoutThree j3EarlyTarget).J = .genesis ∧
    (derive j3UnitElectorateOne j3TimeoutThree j3EarlyTarget).h_j = 1 := by
  exact no_mixed_cross_before_maturity j3UnitElectorateOne j3TimeoutThree 1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

-- The same singleton row is a transition from the initial state.
example :
    (transition j3UnitElectorateOne j3TimeoutThree .initial
      j3EarlyTarget [j3TargetRow]).h = 2 ∧
    (transition j3UnitElectorateOne j3TimeoutThree .initial
      j3EarlyTarget [j3TargetRow]).h_j = 1 := by decide +kernel

-- A non-genesis entry is justified at its own height before it matures.
def j3SecondTarget : FGBlock (Fin 1) :=
  .node j3EarlyTarget 3 ⟨101⟩ 0 [⟨0, .vote 2 j3EarlyTarget.root false, none⟩]

example : (derive j3UnitElectorateOne j3TimeoutThree j3SecondTarget).J = j3EarlyTarget ∧
    (derive j3UnitElectorateOne j3TimeoutThree j3SecondTarget).h_j = 2 := by
  exact no_mixed_cross_before_maturity j3UnitElectorateOne j3TimeoutThree 2
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

-- The conclusion excludes a justified height below the crossing height.
example {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]
    (E : Electorate V) (cfg : FGConfig) {U X : FGBlock V} (y : Height)
    (hX : X ≠ .genesis) (hUX : FGBlock.Preceq U X.parent)
    (hU : (derive E cfg U).h = y) (hentry : (derive E cfg U).T_h = U)
    (hparent : (derive E cfg X.parent).h = y)
    (hearly : X.slot < U.slot + cfg.timeoutDelay)
    (hcross : (derive E cfg X).h = y + 1) : ¬ (derive E cfg X).h_j < y := by
  rw [(no_mixed_cross_before_maturity E cfg y hX hUX hU hentry hparent hearly hcross).2]
  exact Nat.lt_irrefl _

-- Timeout progress stays put one slot before maturity, but crosses at equality.
example :
    (derive j3UnitElectorateOne j3TimeoutThree
      (.node .genesis 2 ⟨102⟩ 0 [j3TimeoutRow])).h = 1 ∧
    (derive j3UnitElectorateOne j3TimeoutThree
      (.node .genesis 3 ⟨103⟩ 0 [j3TimeoutRow])).h = 2 ∧
    (derive j3UnitElectorateOne j3TimeoutThree
      (.node .genesis 3 ⟨103⟩ 0 [j3TimeoutRow])).h_j = 0 := by decide +kernel

-- Zero delay permits an immediate timeout crossing at slot zero.
example :
    (derive j3UnitElectorateOne ⟨0⟩ (.node .genesis 0 ⟨104⟩ 0 [j3TimeoutRow])).h = 2 ∧
    (derive j3UnitElectorateOne ⟨0⟩ (.node .genesis 0 ⟨104⟩ 0 [j3TimeoutRow])).h_j = 0 := by
  decide +kernel

-- An empty electorate has an empty quorum; target priority still justifies.
example : j3UnitElectorateEmpty.IsQuorum ∅ := by
  unfold Electorate.IsQuorum
  decide +kernel

example :
    (derive j3UnitElectorateEmpty j3TimeoutThree (.node .genesis 0 ⟨105⟩ 0 [])).J = .genesis ∧
    (derive j3UnitElectorateEmpty j3TimeoutThree (.node .genesis 0 ⟨105⟩ 0 [])).h_j = 1 := by
  exact no_mixed_cross_before_maturity j3UnitElectorateEmpty j3TimeoutThree 1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

-- The honest-row premise excludes the empty electorate.
example : ¬ j3UnitElectorateEmpty.weightOf ∅ < j3UnitElectorateEmpty.q := by decide +kernel

-- A one-edge path supplies its crossing edge.
example : ∃ C : FGBlock (Fin 1), C ≠ .genesis ∧ FGBlock.Preceq .genesis C.parent ∧
    FGBlock.Preceq C j3EarlyTarget ∧
    (derive j3UnitElectorateOne j3TimeoutThree C.parent).h = 1 ∧
    (derive j3UnitElectorateOne j3TimeoutThree C).h = 2 := by
  exact first_height_crossing_edge j3UnitElectorateOne j3TimeoutThree 1
    (by decide) (by decide) (by decide)

-- Search through a later crossing still finds an edge that leaves height one.
example : ∃ C : FGBlock (Fin 1), C ≠ .genesis ∧ FGBlock.Preceq .genesis C.parent ∧
    FGBlock.Preceq C j3SecondTarget ∧
    (derive j3UnitElectorateOne j3TimeoutThree C.parent).h = 1 ∧
    (derive j3UnitElectorateOne j3TimeoutThree C).h = 2 := by
  exact first_height_crossing_edge j3UnitElectorateOne j3TimeoutThree 1
    (by decide) (by decide) (by decide)

-- On a zero-length path, the strict crossing premise is impossible.
example {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]
    (E : Electorate V) (cfg : FGConfig) (D : FGBlock V) :
    ¬ (derive E cfg D).h < (derive E cfg D).h := Nat.lt_irrefl _

-- Plateau retention includes a zero-length path.
example {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]
    (E : Electorate V) (cfg : FGConfig) (D : FGBlock V) :
    (derive E cfg D).J = (derive E cfg D).J ∧
    (derive E cfg D).h_j = (derive E cfg D).h_j :=
  justification_eq_on_plateau E cfg (preceq_refl D) rfl

-- A retained timeout row can supply the witness from a strict ancestor.
def j3TimeoutCarrier : FGBlock (Fin 1) := .node .genesis 1 ⟨106⟩ 0 [j3TimeoutRow]
def j3RetainedCrossing : FGBlock (Fin 1) := .node j3TimeoutCarrier 3 ⟨107⟩ 0 []

example : ∃ W : FGBlock (Fin 1), ∃ a : Row (Fin 1),
    FGBlock.Preceq W j3RetainedCrossing ∧ a ∈ W.rows ∧ a.signer ∉ (∅ : Finset (Fin 1)) ∧
    a.height_pair.matchesEntry 1
      (derive j3UnitElectorateOne j3TimeoutThree j3RetainedCrossing.parent).T_h.root = true := by
  exact crossing_honest_matching_row j3UnitElectorateOne j3TimeoutThree ∅ 1
    (by decide) (by decide) (by decide) (by decide)

example : j3RetainedCrossing.rows = [] ∧
    FGBlock.Preceq j3TimeoutCarrier j3RetainedCrossing ∧
    j3TimeoutCarrier ≠ j3RetainedCrossing ∧ j3TimeoutRow ∈ j3TimeoutCarrier.rows := by
  decide +kernel

-- A two-edge plateau can advance finality while it keeps J and h_j.
def j3FinalityOnly : FGBlock (Fin 1) :=
  .node j3EarlyTarget 3 ⟨108⟩ 0 [⟨0, .empty, some ⟨1, genesisRoot⟩⟩]
def j3PlateauEnd : FGBlock (Fin 1) := .node j3FinalityOnly 4 ⟨109⟩ 0 []

example : (derive j3UnitElectorateOne j3TimeoutThree j3PlateauEnd).J =
      (derive j3UnitElectorateOne j3TimeoutThree j3EarlyTarget).J ∧
    (derive j3UnitElectorateOne j3TimeoutThree j3PlateauEnd).h_j =
      (derive j3UnitElectorateOne j3TimeoutThree j3EarlyTarget).h_j := by
  exact justification_eq_on_plateau j3UnitElectorateOne j3TimeoutThree (by decide) (by decide)

example : j3PlateauEnd.parent.parent = j3EarlyTarget ∧
    (derive j3UnitElectorateOne j3TimeoutThree j3EarlyTarget).h_F = 0 ∧
    (derive j3UnitElectorateOne j3TimeoutThree j3PlateauEnd).h_F = 1 := by decide +kernel

end AvailableChain.KitFG.Tests.NoEarlyMixedAxioms

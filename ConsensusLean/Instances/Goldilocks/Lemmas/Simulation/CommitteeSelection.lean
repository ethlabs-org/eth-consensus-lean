module
public import ConsensusLean.Spec.Shape.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.RoleBinding
public import Mathlib.Data.Set.Card

public section

/-! # Committee projections of a compiled run

The run's actual selection determines the dictionary. Honest code does not read this dictionary. -/

namespace Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace

open Model Shape

/-- Package the compiled run's slot-indexed selection as a committee dictionary. -/
def voteK {n : Nat} (select : Nat → Finset (Fin n)) : SA.CommitteeDict n :=
  ⟨fun s => {k | k ∈ select s}⟩

variable {V : Type} [Fintype V] {E : Env V}
variable {O : OutputSchema} {I : Type} [DecidableEq I] [Countable I]
variable {F : ChainShapeFamily O I} (rho : Model.Run (compiled F) E)
variable (voteRole : Nat → ShapeRole (F (pubOf E)).skel.Kind)

/-- This dictionary binds the role selection of the run that defined it. -/
theorem voteK_bindsSel : (voteK (rho.sel ∘ voteRole)).BindsSel rho voteRole :=
  ((voteK (rho.sel ∘ voteRole)).bindsSel_iff _ _).2 fun _ _ => Iff.rfl

/-- The size specified for the role is the size of its admissible selection. -/
theorem voteK_ncard (hsel : rho.SelValid) (s : Nat) :
    ((voteK (rho.sel ∘ voteRole)).committee s).ncard =
    match (F (pubOf E)).skel.selSpec (voteRole s) with
    | .fixed T => T.card
    | .sized m => min m (Fintype.card V) := by
  have h := hsel (voteRole s)
  change ((F (pubOf E)).skel.selSpec (voteRole s)).Admits _ at h
  change (↑(rho.sel (voteRole s)) : Set (Fin (Fintype.card V))).ncard = _
  rw [Set.ncard_coe_finset]
  revert h
  cases (F (pubOf E)).skel.selSpec (voteRole s) with
  | fixed T => exact fun h => congrArg Finset.card h
  | sized m => exact fun h => h

/-- A positive specified committee size guarantees a nonempty selected committee. -/
theorem voteK_nonempty (hsel : rho.SelValid) (s : Nat)
    (hpos : 0 < match (F (pubOf E)).skel.selSpec (voteRole s) with
      | .fixed T => T.card
      | .sized m => min m (Fintype.card V)) :
    ((voteK (rho.sel ∘ voteRole)).committee s).Nonempty :=
  Set.nonempty_of_ncard_ne_zero ((voteK_ncard rho voteRole hsel s).trans_ne hpos.ne')

/-- A shape with a population-wide poll selector selects every key for poll in a valid run. -/
theorem selValid_poll (hsel : rho.SelValid)
    (hpoll : (F (pubOf E)).skel.pollSel = .fixed Finset.univ) : rho.sel .poll = Finset.univ := by
  have h := hsel .poll
  change (F (pubOf E)).skel.pollSel.Admits (rho.sel .poll) at h
  rw [hpoll] at h
  exact h

/-- Participation on the run's key indices, using the shape's actual role at each time.
Without a participation role the whole population is selected. -/
def runCommittee (t : Time) : Finset (Fin (Fintype.card V)) :=
  match (protoOf (compiled F) E).participationRole t with
  | none => Finset.univ
  | some role => rho.sel role

/-- Read the key committee from the protocol's participation role. -/
theorem runCommittee_eq (t : Time) : runCommittee rho t =
    match (protoOf (compiled F) E).participationRole t with
    | none => Finset.univ
    | some role => rho.sel role := by rfl

/-- Participation on key indices is exactly the external selection after applying the PKI. -/
theorem mem_runCommittee_iff_selected [DecidableEq V] (t : Time) (k : Fin (Fintype.card V)) :
    k ∈ runCommittee rho t ↔
      rho.key k ∈ (sysExternal O (compiled F) V).selected E (rho.key, rho.sel) t := by
  simp only [runCommittee_eq, sysExternal]
  cases (protoOf (compiled F) E).participationRole t <;> simp

end Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace

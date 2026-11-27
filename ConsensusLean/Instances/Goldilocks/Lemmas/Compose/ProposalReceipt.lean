module
public import ConsensusLean.Instances.Goldilocks.Spec.AC.Instance
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Node.Handlers

public section

/-! # Read-only proposal construction and ordinary own-block receipt -/

namespace Consensus.Goldilocks
open AC

theorem AC.acProposal_state (sp : ACParams) {FGP : Type}
    (a : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (AC.acProposal sp a Φ t).1 = a := by
  unfold AC.acProposal
  split_ifs <;> rfl

namespace Node
variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- The proposal cut is read-only, including when no proposal is returned. -/
theorem acProposal_state (st : NodeState (goldilocksAC sp (List (FG.Att sp.n)) ro)) (t : Time) :
    (acProposal st t).1 = st := by
  simp only [acProposal, goldilocksAC, AC.acProposal_state]

/-- Building a proposal adds just its read-only cut before ordinary own-block receipt. -/
theorem proposal_step_eq_onBlock
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (self : Fin sp.n) (st : NodeState (goldilocksAC sp (List (FG.Att sp.n)) ro))
    (t : Time) (x : Nat)
    (d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)) (p : Payload sp.n)
    (hduty : Proposes proposer self t)
    (hbuild : (acProposal st t).2.2 = some (d, p)) :
    tickStep proposer dg self st t x .proposal =
      let r := onBlock self st t (mkBlock dg self st.fg t x d.head p)
      (r.1, (acProposal st t).2.1 :: r.2) := by
  simp only [tickStep, ite_eq_left hduty, hbuild, proposeBlock, acProposal_state]

/-- Removing the read-only proposal cut gives ordinary receipt in both state and cuts.
No acceptance, frame-well-formedness or reachability premise is needed. -/
theorem proposal_step_strip_eq_onBlock
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (self : Fin sp.n) (st : NodeState (goldilocksAC sp (List (FG.Att sp.n)) ro))
    (t : Time) (x : Nat)
    (d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)) (p : Payload sp.n)
    (hduty : Proposes proposer self t)
    (hbuild : (acProposal st t).2.2 = some (d, p)) :
    let r := tickStep proposer dg self st t x .proposal
    (r.1, r.2.tail) = onBlock self st t (mkBlock dg self st.fg t x d.head p) := by
  rw [proposal_step_eq_onBlock proposer dg self st t x d p hduty hbuild]
  rfl

/-- An unavailable proposal stutters, emitting only the read-only proposal cut. -/
theorem proposal_step_none
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (self : Fin sp.n) (st : NodeState (goldilocksAC sp (List (FG.Att sp.n)) ro))
    (t : Time) (x : Nat)
    (hduty : Proposes proposer self t)
    (hbuild : (acProposal st t).2.2 = none) :
    tickStep proposer dg self st t x .proposal = (st, [(acProposal st t).2.1]) := by
  simp only [tickStep, ite_eq_left hduty, hbuild, acProposal_state]

/-- Without a proposal duty the step emits no cut and changes no state. -/
theorem proposal_step_no_duty
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (self : Fin sp.n) (st : NodeState (goldilocksAC sp (List (FG.Att sp.n)) ro))
    (t : Time) (x : Nat)
    (hduty : ¬ Proposes proposer self t) :
    tickStep proposer dg self st t x .proposal = (st, []) := by
  simp only [tickStep, ite_eq_right hduty]

end Node
end Consensus.Goldilocks

end

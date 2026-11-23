module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.TimeShiftedJoined
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Views

public section

namespace Consensus.Goldilocks.SA.TimeShifted

variable {sp : SAParams} {FGP : Type}

private theorem attempt_early (y : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (early : t < sp.ts (sp.slot t) + sp.Δ) {e : Em sp FGP} (emit : e ∈ (tryVote sp y A Φ t).2) :
    ∃ P ∈ Φ.tree, P.slot = sp.slot t ∧ e.msg.head = P.root := by
  classical
  unfold tryVote at emit
  dsimp only at emit
  split_ifs at emit with h₀ hz h₁ h₂ <;> try contradiction
  all_goals simp_all only [Option.isNone_none, List.mem_singleton]
  all_goals simp_all
  all_goals subst e
  all_goals
    generalize h : deepest Φ {P | accepts sp _ Φ t P} = p at *
    cases p with
    | none => contradiction
    | some P =>
      obtain ⟨hs, hm, _⟩ := (deepest_mem h).1
      exact ⟨P, voteDomain_subset_tree hm.1, hs, rfl⟩

/-- Before timeout, an actual emission cannot be fallback. If the slot has a unique
proposal in the reader's frame, every such emission names it. No timely delivery of the
proposer's whole vote pool is needed at an early cast. -/
theorem early_cast_head {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)}
    {tr : ACTrace (instanceAC sp FGP)} {ini : Fin sp.n → SAState sp.n}
    (hr : ACLocalRun (instanceAC sp FGP) H U tr ini) {y : Fin sp.n} (hy : y ∈ H)
    {j r} (rc : tr.CallAt y j r) {e : Em sp FGP} (emit : e ∈ r.emits)
    (early : tr.time j < sp.ts (sp.slot (tr.time j)) + sp.Δ) {P : Blk sp.n FGP}
    (unique : ∀ B ∈ r.frame.tree, B.slot = sp.slot (tr.time j) → B = P) : e.msg.head = P.root := by
  have exec := congrArg Prod.snd (hr.exec j r rc.2 (rc.1 ▸ hy))
  dsimp only at exec
  rw [← exec, rc.1] at emit
  generalize r.call = c at emit
  have attempt (A : SAState sp.n) (m : e ∈ (tryVote sp y A r.frame (tr.time j)).2) :
      e.msg.head = P.root := by
    obtain ⟨B, hb, hs, eq⟩ := attempt_early _ _ _ _ early m
    exact eq.trans (congrArg Block.root (unique B hb hs))
  cases c with
  | block B | message v => exact attempt _ emit
  | proposal | toFG | restart => exact (List.not_mem_nil emit).elim
  | tick =>
    simp only [ACInterface.step, instanceAC, Id.run, pure] at emit
    split_ifs at emit <;> first | contradiction | exact (early.ne ‹_›).elim

end Consensus.Goldilocks.SA.TimeShifted

end

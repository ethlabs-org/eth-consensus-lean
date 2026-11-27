module
public import ConsensusLean.Instances.Goldilocks.Spec.AC.Actions
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The proposal head belongs to the virtually unlocked working copy -/

namespace Consensus.Goldilocks.AC

/-- At a slot start, the proposal head is the served head of the unlocked working copy,
not necessarily of the unchanged state returned by `acProposal`. -/
theorem proposal_head_eq_acHead_unlocked {sp : ACParams} {FGP : Type}
    {A A' : ACState sp.n} {Φ : Frm sp.n FGP} {σ : Nat}
    {d : DutyHead sp.n FGP (Payload sp.n)} {p : Payload sp.n}
    (hp : acProposal sp A Φ (sp.toParams.slotTime σ) = (A', some (d, p))) :
    d.head = acHead sp
      { A with locks := (unlock sp A.locks Φ (sp.toParams.slotTime σ) ((σ : Int) - 1)
          (View.ofLists (voteViewList A Φ ((σ : Int) - 1) ⊤))) }
      Φ (sp.toParams.slotTime σ) := by
  have hts : sp.toParams.slotTime σ = sp.ts σ := by
    rw [sp.slotTime_eq]; simp [ACParams.ts]
  have hsl : sp.slot (sp.toParams.slotTime σ) = σ := by
    rw [hts]
    exact slot_of_mem sp σ le_rfl ((ts_lt_iff sp).2 (by push_cast; omega))
  have hlt : ¬ (sp.ts (σ : Int) + 2 * sp.Δ ≤ sp.toParams.slotTime σ) := by
    rw [hts]; have := sp.toParams.hΔ; linarith
  unfold acProposal at hp
  dsimp only at hp
  split_ifs at hp
  swap
  · simp at hp
  · simp only [Prod.mk.injEq, Option.some.injEq] at hp
    obtain ⟨_, ⟨rfl, _⟩, _⟩ := hp
    unfold acHead latestView
    simp only [hsl, hlt, ↓reduceIte]
    rfl

end Consensus.Goldilocks.AC

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Phase
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Growing.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.HeldSafety

public section

/-! # Justification agreement across independently honest observations

The readers need only be honest at their own observations. Quorum intersection is charged
at the later observation; the intersecting signer's two historical signatures are genuine
and cannot be slashable (`held_atts_safe_local`, the safety premise of the store-level
`Store.J_eq_of_hj_eq_of_safe`).
-/

namespace Consensus.Goldilocks.Healing.Growing

variable {P : Params} {ACP : Type} {acp₀ : ACP} {H : Time → Set (Fin P.n)}
  {U : Set (NodeBlock P ACP)} {tr : FGTrace P ACP}

/-- An attestation on a block held at an observation honest at its cut, with a signer honest
there, was signed before the cut. -/
private theorem held_att_signed (hr : Consensus.Goldilocks.Growing.FGLocalRun acp₀ H U tr)
    {y : Fin P.n} {i : Nat} (hy : y ∈ H (tr.time i)) {a : FG.Att P.n}
    (ha : ∃ Y ∈ (tr.store y i).tree, a ∈ Y.fgPayload) (hav : a.val ∈ H (tr.time i)) :
    ∃ k < i, tr.SignAt a.val k a := by
  obtain ⟨X, hX, haX⟩ := ha
  rcases hr.tree_accepted hy hX with rfl | ⟨k, hk, hacc⟩
  · cases haX
  · have hki := hr.time_mono hk.le
    obtain ⟨k', hk', hs⟩ := hr.unforgeable y k a (hr.antitone hki hy)
      ⟨_, hacc, haX⟩ (hr.antitone hki hav)
    exact ⟨k', hk'.trans hk, hs⟩

/-- Attestations on blocks held at two observations honest at their cuts, with a signer honest at
the later cut, are not slashable (non-framing). -/
private theorem held_atts_safe_local (hr : Consensus.Goldilocks.Growing.FGLocalRun acp₀ H U tr)
    {y z : Fin P.n} {i j : Nat} (hy : y ∈ H (tr.time i)) (hz : z ∈ H (tr.time j))
    (a b : FG.Att P.n) (ha : ∃ Y ∈ (tr.store y i).tree, a ∈ Y.fgPayload)
    (hb : ∃ Y ∈ (tr.store z j).tree, b ∈ Y.fgPayload)
    (hav : a.val ∈ H (max (tr.time i) (tr.time j))) : ¬ FG.slashable a b := fun hab => by
  obtain ⟨k, hk, hka⟩ := held_att_signed hr hy ha (hr.antitone (le_max_left _ _) hav)
  obtain ⟨l, hl, hlb⟩ := held_att_signed hr hz hb (hab.1 ▸ hr.antitone (le_max_right _ _) hav)
  rw [← hab.1] at hlb
  have hkl : max (tr.time k) (tr.time l) ≤ max (tr.time i) (tr.time j) :=
    max_le ((hr.time_mono hk.le).trans (le_max_left _ _))
      ((hr.time_mono hl.le).trans (le_max_right _ _))
  exact hr.non_framing hka hlb (hr.antitone hkl hav) hab

/-- HR.2(a): equal justified heights agree when readers are honest at their own cuts.
The quorum bound is charged at the later observation, not the earlier reader's cut. -/
theorem J_eq_of_hj_eq_at (hr : Consensus.Goldilocks.Growing.FGLocalRun acp₀ H U tr)
    {y z : Fin P.n} {i j : Nat} (hy : y ∈ H (tr.time i)) (hz : z ∈ H (tr.time j))
    (hf : (H (max (tr.time i) (tr.time j)))ᶜ.ncard < 2 * P.fg.q - P.n)
    {B B' : NodeBlock P ACP}
    (hB : B ∈ (tr.store y i).tree) (hB' : B' ∈ (tr.store z j).tree)
    (he : ((tr.store y i).σ B.root).hj = ((tr.store z j).σ B'.root).hj) :
    ((tr.store y i).σ B.root).J = ((tr.store z j).σ B'.root).J :=
  Store.J_eq_of_hj_eq_of_safe (hr.store_reachable hy) (hr.store_reachable hz) hf
    (held_atts_safe_local hr hy hz) hB hB' he

/-- HR.2, including independent honesty at the two observations in part (a). -/
theorem phase_count (P : Params) (ACP : Type) : PhaseCount P ACP := by
  intro acp₀ H U tr hr
  exact ⟨fun y z i j hy hz hf B hB B' hB' he => J_eq_of_hj_eq_at hr hy hz hf hB hB' he,
    phase_count_at hr⟩

end Consensus.Goldilocks.Healing.Growing

end

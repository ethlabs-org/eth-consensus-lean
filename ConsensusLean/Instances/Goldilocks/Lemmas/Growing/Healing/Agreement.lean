module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Phase
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Growing.Run

public section

/-! # Justification agreement across independently honest observations

The readers need only be honest at their own observations. Quorum intersection is charged
at the later observation; the intersecting signer's two historical signatures are genuine
and cannot be slashable. The pure chain certificate induction follows `Healing/Phase`.
-/

namespace Consensus.Goldilocks.Healing.Growing

private theorem mem_foldl_target {n : Nat} {σ : FG.ChainState n} {atts : List (FG.Att n)}
    {v : Fin n} (h : v ∈ (atts.foldl FG.ChainState.processAtt σ).target) :
    v ∈ σ.target ∨ ∃ a ∈ atts, a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th ∧ a.timeout = false := by
  induction atts generalizing σ with
  | nil => exact Or.inl h
  | cons a as ih =>
    obtain ⟨f, p, t, he⟩ := FG.ChainState.foldl_processAtt_eq σ [a]
    have hh : (σ.processAtt a).h = σ.h := by simpa using congrArg FG.ChainState.h he
    have hT : (σ.processAtt a).Th = σ.Th := by simpa using congrArg FG.ChainState.Th he
    rcases ih h with h | ⟨b, hb, hb'⟩
    · have : v ∈ σ.target ∨ (a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th ∧ a.timeout = false) := by
        unfold FG.ChainState.processAtt at h
        dsimp only at h
        repeat' split at h
        all_goals aesop
      exact this.imp_right fun h => ⟨a, List.mem_cons_self, h⟩
    · rw [hh, hT] at hb'
      exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, hb'⟩

private theorem justification_quorum (gp : FG.FGParams) {c : List (FG.FGBlock gp.n)}
    {σ : FG.ChainState gp.n} (h : gp.chainState c = some σ) :
    (∀ v ∈ σ.target, ∃ a ∈ gp.chainAtts c,
      a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th ∧ a.timeout = false) ∧
    (1 ≤ σ.hj → ∃ Q : Finset (Fin gp.n), gp.q ≤ Q.card ∧ ∀ v ∈ Q, ∃ a ∈ gp.chainAtts c,
      a.val = v ∧ a.h = σ.hj ∧ a.T = σ.J ∧ a.timeout = false) := by
  refine gp.chainState_induction (P := fun c σ =>
    (∀ v ∈ σ.target, ∃ a ∈ gp.chainAtts c,
      a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th ∧ a.timeout = false) ∧
    (1 ≤ σ.hj → ∃ Q : Finset (Fin gp.n), gp.q ≤ Q.card ∧ ∀ v ∈ Q, ∃ a ∈ gp.chainAtts c,
      a.val = v ∧ a.h = σ.hj ∧ a.T = σ.J ∧ a.timeout = false))
    ⟨by simp [FG.ChainState.init], by simp [FG.ChainState.init]⟩ ?_ h
  intro c σ B σ' _ ⟨ht, hq⟩ hB
  have liftA : ∀ {a}, a ∈ gp.chainAtts c → a ∈ gp.chainAtts (c ++ [B]) := fun h => by
    simp only [FG.FGParams.chainAtts, List.flatMap_append, List.mem_append] at h ⊢
    exact Or.inl h
  have liftB : ∀ {a}, a ∈ B.atts → a ∈ gp.chainAtts (c ++ [B]) := fun h => by
    simp only [FG.FGParams.chainAtts, List.flatMap_append, List.mem_append]
    exact Or.inr (by simpa using h)
  obtain ⟨-, rfl⟩ := gp.stateTransition_eq_some.1 hB
  have hT := fun v => @mem_foldl_target _ { σ with s := B.slot } B.atts v
  obtain ⟨f, p, t, he⟩ := FG.ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [he] at hT ⊢
  dsimp only at hT
  have ht₀ : ∀ v ∈ t, ∃ a ∈ gp.chainAtts (c ++ [B]),
      a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th ∧ a.timeout = false := by
    intro v hv
    rcases hT v hv with hv | ⟨a, ha, h'⟩
    · obtain ⟨a, ha, h'⟩ := ht v hv
      exact ⟨a, liftA ha, h'⟩
    · exact ⟨a, liftB ha, h'⟩
  have hq₀ : 1 ≤ σ.hj → ∃ Q : Finset (Fin gp.n), gp.q ≤ Q.card ∧
      ∀ v ∈ Q, ∃ a ∈ gp.chainAtts (c ++ [B]),
        a.val = v ∧ a.h = σ.hj ∧ a.T = σ.J ∧ a.timeout = false := fun h1 =>
    let ⟨Q, hQ, hv⟩ := hq h1
    ⟨Q, hQ, fun v h => let ⟨a, ha, h'⟩ := hv v h; ⟨a, liftA ha, h'⟩⟩
  obtain ⟨F, hF', σ₁, rfl, -, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, L := B.root, fin := f, prog := p, target := t }
  rcases hcase with ⟨⟨hq', -⟩, he'⟩ | ⟨-, -, he'⟩ | ⟨-, -, he'⟩ <;> rw [he']
  · exact ⟨by simp [FG.ChainState.advance], fun _ => ⟨t, hq', ht₀⟩⟩
  · exact ⟨by simp [FG.ChainState.advance], hq₀⟩
  · exact ⟨ht₀, hq₀⟩

variable {P : Params} {ACP : Type} {acp₀ : ACP} {H : Time → Set (Fin P.n)}
  {U : Set (NodeBlock P ACP)} {tr : FGTrace P ACP}

private theorem held_chain (hr : Consensus.Goldilocks.Growing.FGLocalRun acp₀ H U tr)
    {y : Fin P.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {B : NodeBlock P ACP} (hB : B ∈ (tr.store y i).tree) :
    ∃ c : List (NodeBlock P ACP),
      P.fg.chainState (c.map Block.fgView) = some ((tr.store y i).σ B.root) ∧
      ∀ a ∈ P.fg.chainAtts (c.map Block.fgView), a.val ∈ H (tr.time i) →
        ∃ k < i, tr.SignAt a.val k a := by
  obtain ⟨c, hc, -, -, hσ⟩ := Store.chain_state_of_chain P ACP acp₀ _ (hr.store_reachable hy) B hB
  refine ⟨c, hσ, fun a ha hav => ?_⟩
  obtain ⟨_, hX, haX⟩ := List.mem_flatMap.1 ha
  obtain ⟨X, hXc, rfl⟩ := List.mem_map.1 hX
  rcases hr.tree_accepted hy (hc X hXc) with rfl | ⟨k, hk, hacc⟩
  · cases haX
  · have hki := hr.time_mono hk.le
    obtain ⟨k', hk', hs⟩ := hr.unforgeable y k a (hr.antitone hki hy)
      ⟨_, hacc, haX⟩ (hr.antitone hki hav)
    exact ⟨k', hk'.trans hk, hs⟩

/-- HR.2(a): equal justified heights agree when readers are honest at their own cuts.
The quorum bound is charged at the later observation, not the earlier reader's cut. -/
theorem J_eq_of_hj_eq_at (hr : Consensus.Goldilocks.Growing.FGLocalRun acp₀ H U tr)
    {y z : Fin P.n} {i j : Nat} (hy : y ∈ H (tr.time i)) (hz : z ∈ H (tr.time j))
    (hf : (H (max (tr.time i) (tr.time j)))ᶜ.ncard < 2 * P.fg.q - P.n)
    {B B' : NodeBlock P ACP}
    (hB : B ∈ (tr.store y i).tree) (hB' : B' ∈ (tr.store z j).tree)
    (he : ((tr.store y i).σ B.root).hj = ((tr.store z j).σ B'.root).hj) :
    ((tr.store y i).σ B.root).J = ((tr.store z j).σ B'.root).J := by
  obtain ⟨c₁, h₁, ha₁⟩ := held_chain hr hy hB
  obtain ⟨c₂, h₂, ha₂⟩ := held_chain hr hz hB'
  rcases Nat.eq_zero_or_pos ((tr.store y i).σ B.root).hj with h0 | h0
  · rw [(FG.chain_invariants P.fg _ _ h₁).2.2.2.1 h0,
      (FG.chain_invariants P.fg _ _ h₂).2.2.2.1 (he ▸ h0)]
  by_contra hne
  obtain ⟨Q₁, hQ₁, hv₁⟩ := (justification_quorum P.fg h₁).2 h0
  obtain ⟨Q₂, hQ₂, hv₂⟩ := (justification_quorum P.fg h₂).2 (he ▸ h0)
  obtain ⟨v, hvQ, hv⟩ : ∃ v ∈ Q₁ ∩ Q₂, v ∈ H (max (tr.time i) (tr.time j)) := by
    by_contra! hS
    have h1 := (FG.quorum_intersection P.fg Q₁ Q₂ hQ₁ hQ₂).1
    have hcard := Set.ncard_le_ncard
      (s := ((Q₁ ∩ Q₂ : Finset _) : Set (Fin P.fg.n)))
      (t := (H (max (tr.time i) (tr.time j)))ᶜ) hS
    rw [Set.ncard_coe_finset] at hcard
    have : ((H (max (tr.time i) (tr.time j)))ᶜ : Set (Fin P.fg.n)).ncard =
        ((H (max (tr.time i) (tr.time j)))ᶜ : Set (Fin P.n)).ncard := rfl
    have : P.fg.n = P.n := rfl
    omega
  obtain ⟨a, ha, rfl, hah, haT, hat⟩ := hv₁ v (Finset.mem_inter.1 hvQ).1
  obtain ⟨b, hb, hvb, hbh, hbT, hbt⟩ := hv₂ a.val (Finset.mem_inter.1 hvQ).2
  obtain ⟨k, hk, hka⟩ := ha₁ a ha (hr.antitone (le_max_left _ _) hv)
  obtain ⟨l, hl, hlb⟩ := ha₂ b hb (hvb ▸ hr.antitone (le_max_right _ _) hv)
  rw [hvb] at hlb
  have hkl : max (tr.time k) (tr.time l) ≤ max (tr.time i) (tr.time j) :=
    max_le ((hr.time_mono hk.le).trans (le_max_left _ _))
      ((hr.time_mono hl.le).trans (le_max_right _ _))
  exact hr.non_framing hka hlb (hr.antitone hkl hv)
    ⟨hvb.symm, Or.inr (Or.inr ⟨by rw [hah, hbh, he], hat, hbt,
      by rw [haT, hbT]; exact hne⟩)⟩

/-- HR.2, including independent honesty at the two observations in part (a). -/
theorem phase_count (P : Params) (ACP : Type) : PhaseCount P ACP := by
  intro acp₀ H U tr hr
  exact ⟨fun y z i j hy hz hf B hB B' hB' he => J_eq_of_hj_eq_at hr hy hz hf hB hB' he,
    phase_count_at hr⟩

end Consensus.Goldilocks.Healing.Growing

end

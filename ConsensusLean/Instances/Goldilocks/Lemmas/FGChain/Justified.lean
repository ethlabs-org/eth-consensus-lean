module
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Quorum
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Transition

public section

/-! # Goldilocks FG: one justified block per height

The justification witness of a chain: when `h_j ≥ 1`, the chain carries a quorum of target
votes (`timeout = false`) for `(h_j, J)`. It follows from the target bits, each of which comes
from a target vote for the current entry. Two chains whose justifications are at one height
but name different blocks therefore give `2q − n` validators with two target votes at that
height for different blocks (E2): with fewer faulty validators, the justified block of a height
is unique (workbench `fg-liveness/r14-end-to-end`, s3 L3.0U, s4 L4.2a). -/

namespace Consensus.Goldilocks.FG

namespace ChainState

variable {n : Nat}

/-- Counting one attestation adds its signer to the target bits exactly when it is a target
vote for the current entry. -/
private theorem processAtt_target (σ : ChainState n) (a : Att n) :
    (σ.processAtt a).target =
      if a.h = σ.h ∧ a.T = σ.Th ∧ a.timeout = false then insert a.val σ.target
      else σ.target := by
  rcases ha : a.fin with _ | p
  · by_cases hc : a.h = σ.h ∧ a.T = σ.Th <;> cases ht : a.timeout <;>
      simp [processAtt, ha, hc, ht]
  · by_cases hp : p ∈ σ.pending <;> by_cases hc : a.h = σ.h ∧ a.T = σ.Th <;>
      cases ht : a.timeout <;> simp [processAtt, ha, hp, hc, ht]

/-- Every target bit after counting was a target bit before, or comes from a counted target
vote for the entry. -/
theorem mem_target_foldl {atts : List (Att n)} :
    ∀ {σ : ChainState n} {v : Fin n}, v ∈ (atts.foldl processAtt σ).target →
      v ∈ σ.target ∨ ∃ a ∈ atts, a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th ∧ a.timeout = false := by
  induction atts with
  | nil => intro σ v h; exact Or.inl h
  | cons a as ih =>
    intro σ v h
    rw [List.foldl_cons] at h
    obtain ⟨f, p, t, he⟩ := foldl_processAtt_eq σ [a]
    simp only [List.foldl_cons, List.foldl_nil] at he
    have hh : (σ.processAtt a).h = σ.h := by rw [he]
    have hT : (σ.processAtt a).Th = σ.Th := by rw [he]
    rcases ih h with h' | ⟨b, hb, hbv, hbh, hbT, hbt⟩
    · rw [processAtt_target] at h'
      split_ifs at h' with hc
      · rcases Finset.mem_insert.1 h' with rfl | h''
        · exact Or.inr ⟨a, List.mem_cons_self, rfl, hc.1, hc.2.1, hc.2.2⟩
        · exact Or.inl h''
      · exact Or.inl h'
    · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, hbv, hbh.trans hh, hbT.trans hT, hbt⟩

end ChainState

namespace FGParams

variable (gp : FGParams)

/-- **The justification witness.** On a chain, every target bit has a target vote for the
entry on the chain, and a justification at `h_j ≥ 1` has a quorum of target votes for
`(h_j, J)` on the chain. -/
theorem justified_evidence {c : List (FGBlock gp.n)} {σ : ChainState gp.n}
    (h : gp.chainState c = some σ) :
    (∀ v ∈ σ.target, ∃ a ∈ gp.chainAtts c, a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th ∧
      a.timeout = false) ∧
    (1 ≤ σ.hj → ∃ Q : Finset (Fin gp.n), gp.q ≤ Q.card ∧ ∀ v ∈ Q,
      ∃ a ∈ gp.chainAtts c, a.val = v ∧ a.h = σ.hj ∧ a.T = σ.J ∧ a.timeout = false) := by
  refine gp.chainState_induction
    (P := fun c σ => (∀ v ∈ σ.target, ∃ a ∈ gp.chainAtts c, a.val = v ∧ a.h = σ.h ∧
      a.T = σ.Th ∧ a.timeout = false) ∧
      (1 ≤ σ.hj → ∃ Q : Finset (Fin gp.n), gp.q ≤ Q.card ∧ ∀ v ∈ Q,
        ∃ a ∈ gp.chainAtts c, a.val = v ∧ a.h = σ.hj ∧ a.T = σ.J ∧ a.timeout = false))
    ⟨fun v hv => by simp [ChainState.init] at hv, fun h => by simp [ChainState.init] at h⟩
    (fun c σ B σ' _ ih hB => ?_) h
  have hatts : ∀ a, a ∈ gp.chainAtts c ∨ a ∈ B.atts → a ∈ gp.chainAtts (c ++ [B]) := by
    intro a ha
    simp only [chainAtts, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.mem_append]
    exact ha
  obtain ⟨-, he⟩ := gp.stateTransition_eq_some.1 hB
  obtain ⟨f, p, t, hf⟩ := ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  have ht : ∀ v ∈ t, ∃ a ∈ gp.chainAtts (c ++ [B]), a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th ∧
      a.timeout = false := by
    intro v hv
    have hv' : v ∈ (B.atts.foldl ChainState.processAtt { σ with s := B.slot }).target := by
      rw [hf]; exact hv
    rcases ChainState.mem_target_foldl hv' with hv | ⟨a, ha, h1, h2, h3, h4⟩
    · obtain ⟨a, ha, h1, h2, h3, h4⟩ := ih.1 v hv
      exact ⟨a, hatts a (Or.inl ha), h1, h2, h3, h4⟩
    · exact ⟨a, hatts a (Or.inr ha), h1, h2, h3, h4⟩
  have hold : 1 ≤ σ.hj → ∃ Q : Finset (Fin gp.n), gp.q ≤ Q.card ∧ ∀ v ∈ Q,
      ∃ a ∈ gp.chainAtts (c ++ [B]), a.val = v ∧ a.h = σ.hj ∧ a.T = σ.J ∧
        a.timeout = false := by
    intro h1
    obtain ⟨Q, hQ, hv⟩ := ih.2 h1
    exact ⟨Q, hQ, fun v hvQ => let ⟨a, ha, h⟩ := hv v hvQ; ⟨a, hatts a (Or.inl ha), h⟩⟩
  rw [hf] at he
  obtain ⟨F, hF, σ₁, rfl, -, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, fin := f, prog := p, target := t, L := B.root }
  rcases hcase with ⟨hj, he'⟩ | ⟨-, -, he'⟩ | ⟨-, -, he'⟩ <;> rw [he'] at he <;> subst he
  · refine ⟨fun v hv => by simp [ChainState.advance] at hv, fun _ => ⟨t, hj.1, ?_⟩⟩
    intro v hv
    obtain ⟨a, ha, h1, h2, h3, h4⟩ := ht v hv
    exact ⟨a, ha, h1, h2, h3, h4⟩
  · exact ⟨fun v hv => by simp [ChainState.advance] at hv, hold⟩
  · exact ⟨ht, hold⟩

/-- **One justified block per height (r14 s3 L3.0U, s4 L4.2a).** Two chains whose
justifications are at one height `j ≥ 1` but name different blocks give `2q − n` validators
with two target votes at `j` for different blocks (E2). -/
theorem justified_unique {c₁ c₂ : List (FGBlock gp.n)} {σ₁ σ₂ : ChainState gp.n}
    (h₁ : gp.chainState c₁ = some σ₁) (h₂ : gp.chainState c₂ = some σ₂) (hj : 1 ≤ σ₁.hj)
    (heq : σ₁.hj = σ₂.hj) (hne : σ₁.J ≠ σ₂.J) :
    ∃ S : Finset (Fin gp.n), 2 * gp.q - gp.n ≤ S.card ∧
      ∀ v ∈ S, ∃ a ∈ gp.chainAtts c₁, ∃ b ∈ gp.chainAtts c₂, a.val = v ∧ slashable a b := by
  obtain ⟨Q₁, hQ₁, hv₁⟩ := (gp.justified_evidence h₁).2 hj
  obtain ⟨Q₂, hQ₂, hv₂⟩ := (gp.justified_evidence h₂).2 (heq ▸ hj)
  refine ⟨Q₁ ∩ Q₂, (quorum_intersection gp Q₁ Q₂ hQ₁ hQ₂).1, fun v hv => ?_⟩
  obtain ⟨a, ha, rfl, hah, haT, hat⟩ := hv₁ v (Finset.mem_inter.1 hv).1
  obtain ⟨b, hb, hbv, hbh, hbT, hbt⟩ := hv₂ a.val (Finset.mem_inter.1 hv).2
  refine ⟨a, ha, b, hb, rfl, hbv.symm, Or.inr (Or.inr ⟨by rw [hah, hbh, heq], hat, hbt, ?_⟩)⟩
  rw [haT, hbT]
  exact hne

/-- The attestations of a prefix of a chain are attestations of the chain. -/
theorem chainAtts_subset_of_prefix {c' c : List (FGBlock gp.n)} (hp : c' <+: c) :
    ∀ a ∈ gp.chainAtts c', a ∈ gp.chainAtts c := by
  obtain ⟨d, rfl⟩ := hp
  intro a ha
  simp only [chainAtts, List.flatMap_append, List.mem_append] at ha ⊢
  exact Or.inl ha

/-- **One justified block per height, also for past justifications (r14 s4 L4.2b).** If prefixes
of two chains justify one height `j ≥ 1` with different blocks, `2q − n` validators have an E2
pair among the attestations of the two chains. -/
theorem justified_unique_prefix {c₁ c₂ c₁' c₂' : List (FGBlock gp.n)} {τ₁ τ₂ : ChainState gp.n}
    (hp₁ : c₁' <+: c₁) (hp₂ : c₂' <+: c₂)
    (h₁ : gp.chainState c₁' = some τ₁) (h₂ : gp.chainState c₂' = some τ₂) (hj : 1 ≤ τ₁.hj)
    (heq : τ₁.hj = τ₂.hj) (hne : τ₁.J ≠ τ₂.J) :
    ∃ S : Finset (Fin gp.n), 2 * gp.q - gp.n ≤ S.card ∧
      ∀ v ∈ S, ∃ a ∈ gp.chainAtts c₁, ∃ b ∈ gp.chainAtts c₂, a.val = v ∧ slashable a b := by
  obtain ⟨S, hS, hv⟩ := gp.justified_unique h₁ h₂ hj heq hne
  exact ⟨S, hS, fun v hvS => let ⟨a, ha, b, hb, h⟩ := hv v hvS
    ⟨a, gp.chainAtts_subset_of_prefix hp₁ a ha, b, gp.chainAtts_subset_of_prefix hp₂ b hb, h⟩⟩

end FGParams

end Consensus.Goldilocks.FG

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.FG.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Safety

public section

/-! # FG finalized safety under growing faults

Each reader is honest at its own cut. Certificate intersection is charged at the later
observation, and only the intersecting signer's execution is retained through that time.
-/

namespace Consensus.Goldilocks.Growing

variable {P : Params} {ACP : Type} {acp₀ : ACP} {H : Time → Set (Fin P.n)}
  {U : Set (NodeBlock P ACP)} {tr : FGTrace P ACP}

/-- An honest store supplies a finalized chain and genuine signatures for signers still
honest at its observation. Its reader need not remain honest after that observation. -/
theorem FGLocalRun.finalized_chain (hr : FGLocalRun acp₀ H U tr)
    {y : Fin P.n} {i : Nat} (hy : y ∈ H (tr.time i)) :
    ∃ c σ, P.fg.chainState c = some σ ∧ σ.F = (tr.store y i).F.root ∧
      (tr.store y i).F ∈ U ∧ (∀ X ∈ U, X.root ∈ P.fg.roots c → Compatible U X (tr.store y i).F) ∧
      (∀ a ∈ P.fg.chainAtts c, a.val ∈ H (tr.time i) → ∃ k < i, tr.SignAt a.val k a) ∧
      ∃ B ∈ (tr.store y i).tree, ∀ a ∈ P.fg.chainAtts c,
        ∃ Y ∈ (tr.store y i).tree, (tr.store y i).Anc Y B ∧ a ∈ Y.fgPayload := by
  have hs := Trace.upTo_state tr y (i := i) (fun k hk => hr.time_mono hk.le)
  obtain ⟨c, σ, hc, hF, hU, hcompat, hsign, hchain⟩ :=
    Store.finalized_chain (hr.upTo (hr.time_nonneg i)) hy i
  simp only [FGTrace.store, hs] at hF hU hcompat hchain
  refine ⟨c, σ, hc, hF, hU, hcompat, fun a ha hv => ?_, hchain⟩
  obtain ⟨k, hk, src, hcall⟩ := hsign a ha hv
  exact ⟨k, hk, src, ((Trace.upTo_callAt tr).mp hcall).2⟩

/-- Two finalized tips agree when fewer than `2q − n` validators are faulty at the later
observation. The readers are required honest only at their respective observations. -/
theorem FGLocalRun.finalized_safety (hr : FGLocalRun acp₀ H U tr)
    {y z : Fin P.n} {i j : Nat} (hy : y ∈ H (tr.time i)) (hz : z ∈ H (tr.time j))
    (hf : (H (max (tr.time i) (tr.time j)))ᶜ.ncard < 2 * P.fg.q - P.n) :
    Compatible U (tr.store y i).F (tr.store z j).F := by
  by_contra hne
  obtain ⟨c₁, σ₁, h₁, hF₁, hU₁, hc₁, ha₁, -⟩ := hr.finalized_chain hy
  obtain ⟨c₂, σ₂, h₂, hF₂, hU₂, hc₂, ha₂, -⟩ := hr.finalized_chain hz
  obtain ⟨S, hS, hSv⟩ := FG.accountable_safety P.fg c₁ c₂ σ₁ σ₂ h₁ h₂
    (fun h => hne (hc₂ _ hU₁ (hF₁ ▸ h))) (fun h => hne (hc₁ _ hU₂ (hF₂ ▸ h)).symm)
  obtain ⟨v, hvS, hv⟩ : ∃ v ∈ S, v ∈ H (max (tr.time i) (tr.time j)) := by
    by_contra! hS'
    have hcard := Set.ncard_le_ncard
      (s := (S : Set (Fin P.fg.n))) (t := (H (max (tr.time i) (tr.time j)))ᶜ) hS'
    rw [Set.ncard_coe_finset] at hcard
    have : ((H (max (tr.time i) (tr.time j)))ᶜ : Set (Fin P.fg.n)).ncard =
        ((H (max (tr.time i) (tr.time j)))ᶜ : Set (Fin P.n)).ncard := rfl
    have : P.fg.n = P.n := rfl
    omega
  obtain ⟨a, ha, b, hb, rfl, hab⟩ := hSv v hvS
  have signs : ∀ x ∈ P.fg.chainAtts c₁ ++ P.fg.chainAtts c₂, x.val = a.val →
      ∃ k, tr.time k ≤ max (tr.time i) (tr.time j) ∧ tr.SignAt a.val k x := by
    intro x hx hxv
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨k, hk, hs⟩ := ha₁ x hx (hxv ▸ hr.antitone (le_max_left _ _) hv)
      exact ⟨k, (hr.time_mono hk.le).trans (le_max_left _ _), hxv ▸ hs⟩
    · obtain ⟨k, hk, hs⟩ := ha₂ x hx (hxv ▸ hr.antitone (le_max_right _ _) hv)
      exact ⟨k, (hr.time_mono hk.le).trans (le_max_right _ _), hxv ▸ hs⟩
  obtain ⟨k, hk, hka⟩ := signs a ha rfl
  obtain ⟨l, hl, hlb⟩ := signs b hb hab.1.symm
  exact hr.non_framing hka hlb (hr.antitone (max_le hk hl) hv) hab

end Consensus.Goldilocks.Growing

end

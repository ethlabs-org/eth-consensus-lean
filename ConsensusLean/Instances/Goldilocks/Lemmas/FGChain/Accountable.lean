module
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Quorum
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Invariants

public section

/-! # Goldilocks FG: accountable safety, chain level (G1.3)

The quorum witnesses of a chain (G0.2 (f), (g), not transcribed in `M₁`): every height
`1 ≤ j < h` that the chain left has a quorum of attestations on the chain whose height pair
is `(j, E)` for a root `E` of the chain, and a finalized `h_F ≥ 1` has a quorum of
attestations on the chain whose finality pair is `(h_F, F)`. They follow from the bits
of the chain state (each progress bit and each finality bit of a pending pair has its
attestation on the chain) by induction over the chain.

Then G1.2 and G1.3: take the chain with the lower finalized height `j ≥ 1` (neither
finalized block is genesis, which is on both chains); the other chain left height `j`, with
a root that is not the finalized block; quorum intersection gives `2q − n` validators with a
finality pair `(j, F)` and a height pair `(j, E)`, `E ≠ F`: E1. -/

namespace Consensus.Goldilocks.FG

namespace ChainState

variable {n : Nat}

private theorem processAtt_fields (σ : ChainState n) (a : Att n) :
    (σ.processAtt a).h = σ.h ∧ (σ.processAtt a).Th = σ.Th ∧
      (σ.processAtt a).pending = σ.pending := by
  obtain ⟨f, p, t, he⟩ := foldl_processAtt_eq σ [a]
  simp only [List.foldl_cons, List.foldl_nil] at he
  simp [he]

/-- A progress bit after counting is old or set by a counted attestation on the entry. -/
private theorem mem_foldl_processAtt_prog {σ : ChainState n} {atts : List (Att n)} {v : Fin n}
    (h : v ∈ (atts.foldl processAtt σ).prog) :
    v ∈ σ.prog ∨ ∃ a ∈ atts, a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th := by
  induction atts generalizing σ with
  | nil => exact Or.inl h
  | cons a as ih =>
    obtain ⟨hh, hT, -⟩ := σ.processAtt_fields a
    rcases ih h with h | ⟨b, hb, hb'⟩
    · have : v ∈ σ.prog ∨ (a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th) := by
        unfold processAtt at h
        dsimp only at h
        repeat' split at h
        all_goals aesop
      exact this.imp_right fun h => ⟨a, List.mem_cons_self, h⟩
    · rw [hh, hT] at hb'
      exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, hb'⟩

/-- A finality bit after counting is old or set by a counted attestation whose finality pair
is pending at that height. -/
private theorem mem_foldl_processAtt_fin {σ : ChainState n} {atts : List (Att n)} {v : Fin n}
    {j : Nat} (h : v ∈ (atts.foldl processAtt σ).fin j) :
    v ∈ σ.fin j ∨ ∃ a ∈ atts, a.val = v ∧ ∃ p ∈ σ.pending, a.fin = some p ∧ p.1 = j := by
  induction atts generalizing σ with
  | nil => exact Or.inl h
  | cons a as ih =>
    obtain ⟨-, -, hp⟩ := σ.processAtt_fields a
    rcases ih h with h | ⟨b, hb, hb'⟩
    · have : v ∈ σ.fin j ∨ (a.val = v ∧ ∃ p ∈ σ.pending, a.fin = some p ∧ p.1 = j) := by
        unfold processAtt at h
        dsimp only at h
        repeat' split at h
        all_goals aesop (add simp Function.update_apply)
      exact this.imp_right fun h => ⟨a, List.mem_cons_self, h⟩
    · rw [hp] at hb'
      exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, hb'⟩

end ChainState

namespace FGParams

variable (gp : FGParams)

/-- The quorum witnesses of a chain: each height left has a quorum of height pairs on a root
of the chain, and a finalized height `h_F ≥ 1` a quorum of finality pairs `(h_F, F)`. -/
private def Witnessed (c : List (FGBlock gp.n)) (σ : ChainState gp.n) : Prop :=
  (∀ j, 1 ≤ j → j < σ.h → ∃ E ∈ gp.roots c, ∃ Q : Finset (Fin gp.n), gp.q ≤ Q.card ∧
    ∀ v ∈ Q, ∃ a ∈ gp.chainAtts c, a.val = v ∧ a.h = j ∧ a.T = E) ∧
  (1 ≤ σ.hF → ∃ Q : Finset (Fin gp.n), gp.q ≤ Q.card ∧
    ∀ v ∈ Q, ∃ a ∈ gp.chainAtts c, a.val = v ∧ a.fin = some (σ.hF, σ.F))

/-- The witnesses and the bits they come from: each progress bit and each finality bit of a
pending pair has its attestation on the chain, and the entry is a root of the chain. -/
private structure Evidence (c : List (FGBlock gp.n)) (σ : ChainState gp.n) : Prop where
  witnessed : gp.Witnessed c σ
  Th_mem : σ.Th ∈ gp.roots c
  prog : ∀ v ∈ σ.prog, ∃ a ∈ gp.chainAtts c, a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th
  fin : ∀ p ∈ σ.pending, ∀ v ∈ σ.fin p.1, ∃ a ∈ gp.chainAtts c, a.val = v ∧ a.fin = some p

private theorem evidence_step {c : List (FGBlock gp.n)} {σ σ' : ChainState gp.n}
    {B : FGBlock gp.n} (hc : gp.chainState c = some σ) (hE : gp.Evidence c σ)
    (h : gp.stateTransition σ B = some σ') : gp.Evidence (c ++ [B]) σ' := by
  have hI := chain_invariants gp c σ hc
  obtain ⟨hh1, -, hjh, -, -, -, hpw, hmem, -, hts⟩ := hI
  have roots_append : gp.roots (c ++ [B]) = gp.roots c ++ [B.root] := by simp [roots]
  have atts_append : gp.chainAtts (c ++ [B]) = gp.chainAtts c ++ B.atts := by
    simp [chainAtts]
  have liftR : ∀ {E}, E ∈ gp.roots c → E ∈ gp.roots (c ++ [B]) := fun h => by
    rw [roots_append]; exact List.mem_append_left _ h
  have liftA : ∀ {a}, a ∈ gp.chainAtts c → a ∈ gp.chainAtts (c ++ [B]) := fun h => by
    rw [atts_append]; exact List.mem_append_left _ h
  have liftB : ∀ {a}, a ∈ B.atts → a ∈ gp.chainAtts (c ++ [B]) := fun h => by
    rw [atts_append]; exact List.mem_append_right _ h
  obtain ⟨⟨hcross, hfinal⟩, hTh, hprog, hfin⟩ := hE
  obtain ⟨-, rfl⟩ := gp.stateTransition_eq_some.1 h
  have hsub := ChainState.foldl_processAtt_target_subset { σ with s := B.slot } B.atts hts
  have hP := fun v => @ChainState.mem_foldl_processAtt_prog _ { σ with s := B.slot } B.atts v
  have hF := fun v j => @ChainState.mem_foldl_processAtt_fin _ { σ with s := B.slot } B.atts v j
  obtain ⟨f, p, t, he⟩ := ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [he] at hsub hP hF ⊢
  dsimp only at hsub hP hF
  have hprog₀ : ∀ v ∈ p, ∃ a ∈ gp.chainAtts (c ++ [B]), a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th := by
    intro v hv
    rcases hP v hv with hv | ⟨a, ha, h'⟩
    · obtain ⟨a, ha, h'⟩ := hprog v hv; exact ⟨a, liftA ha, h'⟩
    · exact ⟨a, liftB ha, h'⟩
  have hfin₀ : ∀ r ∈ σ.pending, ∀ v ∈ f r.1, ∃ a ∈ gp.chainAtts (c ++ [B]), a.val = v ∧
      a.fin = some r := by
    intro r hr v hv
    rcases hF v r.1 hv with hv | ⟨a, ha, hav, r', hr', hfa, hre⟩
    · obtain ⟨a, ha, h'⟩ := hfin r hr v hv; exact ⟨a, liftA ha, h'⟩
    · exact ⟨a, liftB ha, hav, eq_of_pairwise_fst_lt hpw hr' hr hre ▸ hfa⟩
  obtain ⟨F, hF', σ₁, rfl, hcase₁, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, L := B.root, fin := f, prog := p, target := t }
  have hcross₁ : ∀ j, 1 ≤ j → j < σ.h → ∃ E ∈ gp.roots (c ++ [B]), ∃ Q : Finset (Fin gp.n),
      gp.q ≤ Q.card ∧ ∀ v ∈ Q, ∃ a ∈ gp.chainAtts (c ++ [B]), a.val = v ∧ a.h = j ∧ a.T = E := by
    intro j h1 h2
    obtain ⟨E, hE, Q, hQ, hv⟩ := hcross j h1 h2
    exact ⟨E, liftR hE, Q, hQ, fun v h => let ⟨a, ha, h'⟩ := hv v h; ⟨a, liftA ha, h'⟩⟩
  have hfinal₁ : 1 ≤ hF' → ∃ Q : Finset (Fin gp.n), gp.q ≤ Q.card ∧
      ∀ v ∈ Q, ∃ a ∈ gp.chainAtts (c ++ [B]), a.val = v ∧ a.fin = some (hF', F) := by
    intro h1
    rcases hcase₁ with ⟨rfl, rfl⟩ | ⟨hm, hq⟩
    · obtain ⟨Q, hQ, hv⟩ := hfinal h1
      exact ⟨Q, hQ, fun v h => let ⟨a, ha, h'⟩ := hv v h; ⟨a, liftA ha, h'⟩⟩
    · exact ⟨f hF', hq, hfin₀ (hF', F) hm⟩
  have hfin₁ : ∀ r ∈ σ.pending.filter (fun r => hF' < r.1), ∀ v ∈ f r.1,
      ∃ a ∈ gp.chainAtts (c ++ [B]), a.val = v ∧ a.fin = some r :=
    fun r hr => hfin₀ r (List.mem_of_mem_filter hr)
  -- the entry crossed by an advance: a progress quorum on `(σ.h, σ.Th)`
  have hcrossed : gp.q ≤ p.card → ∀ j, 1 ≤ j → j < σ.h + 1 → ∃ E ∈ gp.roots (c ++ [B]),
      ∃ Q : Finset (Fin gp.n), gp.q ≤ Q.card ∧
        ∀ v ∈ Q, ∃ a ∈ gp.chainAtts (c ++ [B]), a.val = v ∧ a.h = j ∧ a.T = E := by
    intro hq j h1 h2
    rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | rfl
    · exact hcross₁ j h1 h2
    · exact ⟨σ.Th, liftR hTh, p, hq, hprog₀⟩
  have hBroot : B.root ∈ gp.roots (c ++ [B]) := by simp [roots_append]
  rcases hcase with ⟨⟨hq, -⟩, he⟩ | ⟨-, ⟨hq, -⟩, he⟩ | ⟨-, -, he⟩ <;> rw [he]
  · refine ⟨⟨hcrossed (hq.trans (Finset.card_le_card hsub)), hfinal₁⟩, hBroot,
    by simp [ChainState.advance], ?_⟩
    intro r hr v hv
    rcases List.mem_append.1 (List.mem_of_mem_drop hr) with hr | hr
    · have hne : r.1 ≠ σ.h := by
        have := hmem r (List.mem_of_mem_filter hr); omega
      simp only [ChainState.advance, Function.update_of_ne hne] at hv
      exact hfin₁ r hr v hv
    · simp only [List.mem_singleton] at hr
      subst hr
      simp [ChainState.advance] at hv
  · exact ⟨⟨hcrossed hq, hfinal₁⟩, hBroot, by simp [ChainState.advance], hfin₁⟩
  · exact ⟨⟨hcross₁, hfinal₁⟩, liftR hTh, hprog₀, hfin₁⟩

private theorem evidence {c : List (FGBlock gp.n)} {σ : ChainState gp.n}
    (h : gp.chainState c = some σ) : gp.Evidence c σ :=
  gp.chainState_induction (P := fun c σ => gp.chainState c = some σ → gp.Evidence c σ)
    (fun _ => ⟨⟨fun j h1 h2 => by simp [ChainState.init] at h2; omega,
      fun h => by simp [ChainState.init] at h⟩, by simp [ChainState.init, roots],
      by simp [ChainState.init], by simp [ChainState.init]⟩)
    (fun c σ B σ' hc ih hB _ => gp.evidence_step hc (ih hc) hB) h h

/-- **G1.2.** A finalization at `j ≥ 1` on one chain meets the crossing of `j` on a chain
without the finalized block in `2q − n` validators with an E1 pair. -/
private theorem finalization_meets_crossing {c₁ c₂ : List (FGBlock gp.n)}
    {σ₁ σ₂ : ChainState gp.n} (h₁ : gp.chainState c₁ = some σ₁)
    (h₂ : gp.chainState c₂ = some σ₂) (hF : 1 ≤ σ₁.hF) (hlt : σ₁.hF < σ₂.h)
    (hnot : σ₁.F ∉ gp.roots c₂) :
    ∃ S : Finset (Fin gp.n), 2 * gp.q - gp.n ≤ S.card ∧
      ∀ v ∈ S, ∃ a ∈ gp.chainAtts c₁, ∃ b ∈ gp.chainAtts c₂, a.val = v ∧ slashable a b := by
  obtain ⟨Q₁, hQ₁, hv₁⟩ := (gp.evidence h₁).witnessed.2 hF
  obtain ⟨E, hE, Q₂, hQ₂, hv₂⟩ := (gp.evidence h₂).witnessed.1 _ hF hlt
  refine ⟨Q₁ ∩ Q₂, (quorum_intersection gp Q₁ Q₂ hQ₁ hQ₂).1, fun v hv => ?_⟩
  obtain ⟨a, ha, rfl, hfa⟩ := hv₁ v (Finset.mem_inter.1 hv).1
  obtain ⟨b, hb, hvb, hbh, rfl⟩ := hv₂ a.val (Finset.mem_inter.1 hv).2
  refine ⟨a, ha, b, hb, rfl, hvb.symm, Or.inl ⟨(σ₁.hF, σ₁.F), by simp [hfa], hbh, ?_⟩⟩
  intro he
  exact hnot (by simpa [he] using hE)

end FGParams

/-- **G1.3** (with G1.2 as its core). -/
theorem accountable_safety (gp : FGParams) : AccountableSafety gp := by
  intro c₁ c₂ σ₁ σ₂ h₁ h₂ hn₁ hn₂
  obtain ⟨-, -, -, -, hg₁, -⟩ := chain_invariants gp c₁ σ₁ h₁
  obtain ⟨-, hFj₂, hjh₂, -, hg₂, -⟩ := chain_invariants gp c₂ σ₂ h₂
  obtain ⟨-, hFj₁, hjh₁, -⟩ := chain_invariants gp c₁ σ₁ h₁
  have hgen : ∀ c, gp.genesis ∈ gp.roots c := fun c => List.mem_cons_self
  have hF₁ : 1 ≤ σ₁.hF := Nat.one_le_iff_ne_zero.2 fun h => hn₁ (hg₁ h ▸ hgen c₂)
  have hF₂ : 1 ≤ σ₂.hF := Nat.one_le_iff_ne_zero.2 fun h => hn₂ (hg₂ h ▸ hgen c₁)
  rcases le_total σ₁.hF σ₂.hF with hle | hle
  · obtain ⟨S, hS, hv⟩ := gp.finalization_meets_crossing h₁ h₂ hF₁ (by omega) hn₁
    exact ⟨S, hS, fun v h => let ⟨a, ha, b, hb, h⟩ := hv v h
      ⟨a, List.mem_append_left _ ha, b, List.mem_append_right _ hb, h⟩⟩
  · obtain ⟨S, hS, hv⟩ := gp.finalization_meets_crossing h₂ h₁ hF₂ (by omega) hn₂
    exact ⟨S, hS, fun v h => let ⟨a, ha, b, hb, h⟩ := hv v h
      ⟨a, List.mem_append_right _ ha, b, List.mem_append_left _ hb, h⟩⟩

end Consensus.Goldilocks.FG
end

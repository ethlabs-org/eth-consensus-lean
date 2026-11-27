module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.DeclaredVoteTransfer

public section

/-! # Goldilocks AC: stable resolution and the merged view's opponents (A0.2, A0.3)

Stable resolution follows from stable stamps (A0.1) and root injectivity in `U`. The merged
view's opponents rest on a reachable-state invariant (every pool vote has a finite stamp, the
tree blocks have valid payloads and are not of a later slot than the last call) and on the merged
view counting a declared head vote only when it is held in its pool or its validator equivocates
there. -/

namespace Consensus.Goldilocks.AC

variable (sp : ACParams)

/-- A finite stamp is below `+∞`. -/
private theorem etime_lt_top (t : Time) : ETime.of t < ⊤ :=
  WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top t)

section Invariant

variable {sp} {FGP : Type}

/-- Every pool vote has a finite stamp. -/
private def PoolStamped (A : ACState sp.n) : Prop := ∀ σ, ∀ x ∈ A.pool σ, A.voteStamp x ≠ ⊤

private theorem voteClosed_poolStamped : VoteClosed (PoolStamped (sp := sp)) := by
  refine ⟨fun A t v h σ x hx => ?_, fun A A' hp hv h σ x hx => ?_⟩
  · unfold admitVote at hx ⊢
    split_ifs at hx ⊢
    · exact h σ x hx
    · exact h σ x hx
    · dsimp only at hx ⊢
      rw [Function.update_apply]
      split_ifs with hxv
      · exact (etime_lt_top t).ne
      · rw [Function.update_apply] at hx
        split_ifs at hx with hσ
        · rcases List.mem_append.mp hx with hx | hx
          · exact h _ x hx
          · exact absurd (List.mem_singleton.mp hx) hxv
        · exact h σ x hx
  · rw [hv]
    exact h σ x (hp ▸ hx)

/-- The invariant of a reachable state `A` with frame `Φ` and last time `t₀` inside `U`. -/
private structure MInv (U : Set (Blk sp.n FGP)) (A : ACState sp.n) (Φ : Frm sp.n FGP)
    (t₀ : Time) : Prop where
  frame : FrameOK Φ ∧ Φ.tree ⊆ U
  genesis : ∃ G ∈ U, G.root = sp.genesisRoot ∧ declaredHeadVotes G = []
  time : 0 ≤ t₀
  stamped : PoolStamped A
  slot_le : ∀ B ∈ Φ.tree, B.slot ≤ sp.slot t₀
  payload : ∀ B ∈ Φ.tree, validPayload B

end Invariant

private theorem minv_of_reachable {FGP : Type} {ro : ReplayOrder sp FGP} {self : Fin sp.n}
    {U : Set (Blk sp.n FGP)} {A : (goldilocksAC sp FGP ro).State}
    {Φ : (goldilocksAC sp FGP ro).Frm} {t₀ : Time}
    (h : (goldilocksAC sp FGP ro).ReachableAt self U A Φ t₀) : MInv U A Φ t₀ := by
  induction h with
  | init Φ hi hf =>
    obtain ⟨htree, hroot, hs0, -, hpay⟩ := hi
    have hF : ∀ B ∈ Φ.tree, B = Φ.F := fun B hB => by rw [htree] at hB; exact hB
    have hnil : declaredHeadVotes Φ.F = [] ∧ declaredSupportVotes Φ.F = [] := by
      simp [declaredHeadVotes, declaredSupportVotes, hpay]
    refine ⟨hf, ⟨Φ.F, hf.2 (htree ▸ rfl), hroot, hnil.1⟩, le_rfl, fun σ x hx => ?_,
      fun B hB => by rw [hF B hB, hs0]; exact Nat.zero_le _, fun B hB => ?_⟩
    · change x ∈ (ACState.initial sp.genesisRoot : ACState sp.n).pool σ at hx
      simp [ACState.initial] at hx
    · rw [hF B hB]
      simp [validPayload, hnil.1, hnil.2]
  | @step A Φ Φ' t t' c hr ht hok ih =>
    have h0 : 0 ≤ t' := ih.time.trans ht
    have hsl : sp.slot t ≤ sp.slot t' := slot_mono sp ih.time ht
    by_cases hc : c = .restart
    · subst hc
      have hΦe : Φ' = Φ := hok.2
      subst hΦe
      have hrs := restart_state sp FGP ro self A Φ' t' ih.frame.1 h0
      refine ⟨ih.frame, ih.genesis, h0, fun σ x hx => ?_, fun B hB => (ih.slot_le B hB).trans hsl,
        ih.payload⟩
      change x ∈ (acRestart sp ro self A Φ' t').1.pool σ at hx
      rw [hrs.2.2.2.2.2.2.2.1 σ] at hx
      cases hx
    have hst := voteClosed_poolStamped.step ro self Φ' t' hc ih.stamped
    by_cases hb : ∃ B, c = .block B
    · obtain ⟨B, rfl⟩ := hb
      obtain ⟨hΦ', hfs, hpay, hBs⟩ := hok
      have hmem : ∀ P ∈ Φ'.tree, P = B ∨ P ∈ Φ.tree := fun P hP => by
        rw [hfs.tree_eq] at hP
        exact Set.mem_insert_iff.mp hP.1
      refine ⟨hΦ', ih.genesis, h0, hst, fun P hP => ?_, fun P hP => ?_⟩
      · rcases hmem P hP with rfl | hP
        · exact hBs
        · exact (ih.slot_le P hP).trans hsl
      · rcases hmem P hP with rfl | hP
        · exact hpay
        · exact ih.payload P hP
    · have hΦe : Φ' = Φ := by
        cases c with
        | block B => exact absurd ⟨B, rfl⟩ hb
        | message m => exact hok.2.1
        | restart => exact absurd rfl hc
        | tick => exact hok.2
        | proposal => exact hok.2
        | toFG => exact hok.2
      subst hΦe
      exact ⟨ih.frame, ih.genesis, h0, hst, fun P hP => (ih.slot_le P hP).trans hsl, ih.payload⟩

/-- **A0.2, resolution is stable.** -/
theorem resolution_stable : ResolutionStable sp := by
  intro FGP ro self U hU A Φ t₀ hr A' Φ' t' hpath v hv hin'
  have hlk : ∀ {Ψ : Frm sp.n FGP} {H : Blk sp.n FGP}, Ψ.tree ⊆ U → InTree Ψ v.head →
      H ∈ U → H.root = v.head → lookup Ψ v.head = some H := by
    intro Ψ H hΨ hin hH hHr
    cases hl : lookup Ψ v.head with
    | none => exact absurd hin (lookup_eq_none hl)
    | some H' =>
      obtain ⟨hH', hH'r⟩ := lookup_eq_some hl
      rw [hU.1 (hΨ hH') hH (hH'r.trans hHr.symm)]
  obtain ⟨H, hl⟩ : ∃ H, lookup Φ v.head = some H := by
    cases hl : lookup Φ v.head with
    | none => simp [resolutionTime, hl] at hv
    | some H => exact ⟨H, rfl⟩
  obtain ⟨hH, hHr⟩ := lookup_eq_some hl
  have hfin : A.voteStamp v ≠ ⊤ ∧ A.blockStamp v.head ≠ ⊤ := by
    simp only [resolutionTime, hl] at hv
    split_ifs at hv
    · exact absurd rfl hv
    · exact ⟨fun h => hv (top_le_iff.mp (h ▸ le_max_left _ _)),
        fun h => hv (top_le_iff.mp (h ▸ le_max_right _ _))⟩
  -- along the path: reachable, and the two stamps unchanged
  have key : ∀ q : ACState sp.n × Frm sp.n FGP × Time, Relation.ReflTransGen
      (fun p q => ∃ c, c ≠ ACInterface.Call.restart ∧
        (goldilocksAC sp FGP ro).CallStep self U p c q) (A, Φ, t₀) q →
      (goldilocksAC sp FGP ro).ReachableAt self U q.1 q.2.1 q.2.2 ∧
        q.1.voteStamp v = A.voteStamp v ∧ q.1.blockStamp v.head = A.blockStamp v.head := by
    intro q hq
    induction hq with
    | refl => exact ⟨hr, rfl, rfl⟩
    | @tail b q _ hbq ih =>
      obtain ⟨c, hc, ht, hok, hq⟩ := hbq
      obtain ⟨hb, hbv, hbb⟩ := ih
      have hs := stamp_stable sp FGP ro self U hU b.1 b.2.1 b.2.2 hb c q.2.1 q.2.2 ht hok hc
      rw [hq]
      exact ⟨hb.step c ht hok, ((hs.1 v (hbv ▸ hfin.1)).trans hbv),
        (hs.2 v.head (hbb ▸ hfin.2)).trans hbb⟩
  obtain ⟨hreach, hvs, hbs⟩ := key _ hpath
  have hΦU : ∀ {A₁ : (goldilocksAC sp FGP ro).State} {Φ₁ : (goldilocksAC sp FGP ro).Frm} {t₁},
      (goldilocksAC sp FGP ro).ReachableAt self U A₁ Φ₁ t₁ → Φ₁.tree ⊆ U := by
    intro A₁ Φ₁ t₁ h
    cases h with
    | init _ _ hf => exact hf.2
    | step _ _ _ hok => exact hok.1.2
  have hHU := hΦU hr hH
  dsimp only at hvs hbs
  simp only [resolutionTime, hl, hlk (hΦU hreach) hin' hHU hHr]
  rw [hvs, hbs]

/-- **A0.3, the merged view's opponents.** -/
theorem merged_opponents : MergedOpponents sp := by
  intro FGP ro self U hU A Φ t₀ hr σ B hσ
  have h := minv_of_reachable sp hr
  have hle := tree_blockStamp_le sp hU hr
  have hpool : ∀ x, x ∈ A.poolAt (σ : Int) ↔ x ∈ A.pool σ := fun x => by
    simp [ACState.poolAt]
  have hpool' : ∀ x, x ∈ A.poolAt (((σ + 1 : Nat) : Int) - 1) ↔ x ∈ A.pool σ := fun x => by
    simp [ACState.poolAt]
  -- the full view holds every pool vote, and its support every resolved one
  have hfull : ∀ x ∈ A.pool σ, x ∈ (voteView A Φ σ ⊤).votes := fun x hx => by
    simp only [voteView, voteViewList, View.ofLists, Set.mem_ofPred_eq, List.mem_filter,
      decide_eq_true_eq]
    exact ⟨(hpool x).mpr hx, lt_top_iff_ne_top.mpr (h.stamped σ x hx)⟩
  have hfs : ∀ x ∈ A.pool σ, resolutionTime A Φ x < ⊤ →
      x ∈ (voteView A Φ σ ⊤).support := fun x hx hres => by
    simp only [voteView, voteViewList, View.ofLists, Set.mem_ofPred_eq, List.mem_filter,
      decide_eq_true_eq]
    exact ⟨⟨(hpool x).mpr hx, lt_top_iff_ne_top.mpr (h.stamped σ x hx)⟩, hres⟩
  have heq : equivocators {x | x ∈ A.pool σ} ⊆ equivocators (voteView A Φ σ ⊤).votes :=
    equivocators_mono fun x hx => hfull x hx
  -- a counted vote of the merged view is held, or its validator equivocates in the pool
  have hheld : ∀ u ∈ (mergedVoteView sp A Φ (σ + 1)).votes,
      u ∈ A.pool σ ∨ u.val ∈ equivocators {x | x ∈ A.pool σ} := by
    intro u hu
    rcases hu with hu' | ⟨P, hP, hPs, hu', hc⟩
    · exact Or.inl ((hpool' u).mp (List.mem_filter.1 hu').1)
    · have hus : u.slot = σ := by have := (h.payload P hP).1 u hu'; omega
      exact merged_declared_backing hus (Or.inr ⟨P, hP, hPs, hu', hc⟩)
  rintro i (⟨x, hx, y, hy, hxy, hxi, hyi⟩ | ⟨x, hx, hxi, hxs, H, hH, hHr, hc⟩)
  · rcases hheld x hx with hx' | hx'
    · rcases hheld y hy with hy' | hy'
      · exact Or.inl ⟨x, hfull x hx', y, hfull y hy', hxy, hxi, hyi⟩
      · exact Or.inl (heq (hyi ▸ hy'))
    · exact Or.inl (heq (hxi ▸ hx'))
  have hopp : x ∈ (voteView A Φ σ ⊤).support →
      i ∈ opponents sp Φ (voteView A Φ σ ⊤) σ B := fun hs =>
    Or.inr ⟨x, hs, hxi, hxs, H, hH, hHr, hc⟩
  simp only [mergedVoteView, voteView, voteViewList, View.ofLists, Set.mem_union,
    Set.mem_ofPred_eq, List.mem_filter, decide_eq_true_eq] at hx
  rcases hx with ⟨⟨hx, -⟩, hres⟩ | ⟨P, hP, hPs, hxP, hxc, hxs', H', hH', hH'r, hH's⟩
  · exact hopp (hfs x ((hpool' x).mp hx) (hres.trans (etime_lt_top _)))
  have hxσ : x.slot = σ := by omega
  obtain hx' | hx' := merged_declared_backing (Φ := Φ) hxσ
    (Or.inr ⟨P, hP, hPs, (h.payload P hP).2.1.subset hxP, hxc⟩)
  · refine hopp (hfs x hx' ?_)
    have hl : lookup Φ x.head = some H' := by
      cases hl : lookup Φ x.head with
      | none => exact absurd ⟨H', hH', hH'r⟩ (lookup_eq_none hl)
      | some H'' =>
        obtain ⟨hH'', hH''r⟩ := lookup_eq_some hl
        rw [h.frame.1.coherent.1 hH'' hH' (hH''r.trans hH'r.symm)]
    simp only [resolutionTime, hl]
    split_ifs with hlt
    · omega
    · exact max_lt (lt_top_iff_ne_top.mpr (h.stamped σ x hx'))
        (hH'r ▸ (hle H' hH').trans_lt (etime_lt_top _))
  · exact Or.inl (heq (hxi ▸ hx'))

end Consensus.Goldilocks.AC

end

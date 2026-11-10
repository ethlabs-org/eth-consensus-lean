module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Base
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Compatible
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Unlocked
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Nodes
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Opponents
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Source age at an honest call

The source's lock history is local to the caller, so retention at the call preserves it.
-/

namespace Consensus.Goldilocks.SA.Growing

theorem source_age (sp : SAParams) : SourceAge sp := by
  intro FGP ro H U tr hr τ x i ℓ C hx hto hslot
  obtain ⟨j, hji, s, B, CV, hfl, ht, hs, hanc⟩ :=
    SA.source_age sp FGP ro (H (tr.time i)) U (tr.upTo (tr.time i))
      (hr.upTo (hr.time_nonneg i)) τ x i ℓ C hx
      ((upTo_toFGAt hr.time_mono).mpr ⟨le_rfl, hto⟩) hslot
  exact ⟨j, hji, s, B, CV, (upTo_fastLockAt hr.time_mono).mp hfl |>.2, ht, hs, hanc⟩

private theorem toFG_some {sp : SAParams} {FGP : Type} {A : SAState sp.n}
    {Φ : Frm sp.n FGP} {t : Time} {C : Blk sp.n FGP} (h : (acToFG sp A Φ t).2 = some C) :
    C ∈ toFGCandidates sp A Φ t ∧ joined sp A t ∧
      (acToFG sp A Φ t).1.restartTime = A.restartTime := by
  unfold acToFG at h ⊢
  split_ifs at h ⊢ with hj
  split at h
  · cases h
  · rename_i C' hC'
    split_ifs at h ⊢
    cases h
    exact ⟨(deepest_mem hC').1, hj, rfl⟩

/-- Source compatibility for an ancestor of the block stored by a historical fast lock. -/
theorem source_compatible_stored (sp : SAParams) (FGP : Type) (ro : ReplayOrder sp FGP)
    (proposer : Nat → Fin sp.n) (H : Time → Set (Fin sp.n))
    (U : Set (Blk sp.n FGP)) (tr : SATrace sp FGP ro)
    (hrun : ACRun proposer tr H U) (s m : Nat) (w x : Fin sp.n) (i₀ i : Nat)
    (B D : Blk sp.n FGP) (CV : Set (Vote sp.n))
    (ℓ : ACLabel (goldilocksSA sp FGP ro)) (C : Blk sp.n FGP)
    (hw : w ∈ H (tr.time i₀)) (hfl : FastLockAt tr w i₀ s D CV) (hBD : Anc U B D)
    (hsync : SyncACAt (goldilocksSA sp FGP ro) H U
      (sp.ts s) (sp.ts (s + 1 : Nat) + sp.Δ) tr)
    (hcarry : Carry tr H U s CV) (hf : 2 * (H (tr.time i))ᶜ.ncard < sp.n)
    (hx : x ∈ H (tr.time i)) (hto : ToFGAt tr x i ℓ C)
    (hlo : sp.ts (s + 1 : Nat) + sp.Δ < tr.time i) (hhi : tr.time i ≤ sp.ts m + sp.Δ)
    (hvotes : ∀ z j, j < i → z ∈ H (tr.time j) → ∀ e,
      VoteAt tr z j e → s < e.msg.slot → e.msg.slot ≤ m → VoteExtends U e.msg B)
    (hcase : (∃ j < i, ∃ ℓ' e, CastAt tr x j ℓ' e ∧ e.msg.slot = s + 1 ∧
        Compatible U ℓ'.frame.F B) ∨ (∃ k < i, tr.RestartAt x k ∧ sp.ts s < tr.time k)) :
    Compatible U C B := by
  have hr := hrun.localRun
  have hU := hr.coherent
  have hri := hrun.upTo (hr.time_nonneg i)
  obtain ⟨hc, hcall, hC⟩ := hto
  have hc' := (Trace.upTo_callAt tr).mpr ⟨le_rfl, hc⟩
  obtain ⟨⟨hCv, l, hl, hlb, hlf, hls⟩, hjoin, hrt⟩ := toFG_some hC
  obtain ⟨l₀, hl₀, B₀, hB₀, hB₀r, _, rfl⟩ := hl
  simp only at hlb hlf hls
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_call hri.localRun hx hc'
  have hCe : C = ℓ.frame.viableAncestor B₀ :=
    hU.1 (hΦU hCv.1) (hΦU (viableAncestor_anc hΦ hB₀).1) hlb.symm
  subst hCe
  have down : ∀ {X Y}, Anc U X Y → Compatible U Y B → Compatible U X B := by
    rintro X Y hXY (h | h)
    · exact Or.inl (hXY.trans h)
    · exact anc_total hU hXY h
  refine down (Anc.mono hΦU (anc_viableAncestor _ B₀)) ?_
  have hΔ := sp.toParams.hΔ
  have ht0 := hr.time_nonneg i
  have hσlo : s + 1 ≤ sp.slot (tr.time i) := by
    have := ((ts_le_iff_le_slot sp ht0) (s + 1 : Nat)).1 (by linarith)
    exact_mod_cast this
  have hσhi : sp.slot (tr.time i) ≤ m := by
    by_contra h
    have := ((ts_le_iff_le_slot sp ht0) (m + 1 : Nat)).2 (by push_cast; omega)
    simp only [SAParams.ts] at this hhi
    push_cast at this
    linarith
  have hstate : (tr.upTo (tr.time i)).state x i = tr.state x i :=
    Trace.upTo_state tr x fun _ hk => hr.time_mono hk.le
  obtain ⟨j, hj, B', CV', hfl', hxj, L, hL, hLr, hLB'⟩ :=
    fast_lock_provenance hr hx (hstate ▸ hl₀) hlf
  obtain rfl : B₀ = L := hU.1 (hΦU hB₀) hL (hB₀r.trans hLr.symm)
  have hs'σ : l₀.slot ≤ sp.slot (tr.time i) := by
    have hmono := slot_mono sp (hr.time_nonneg j) (hr.time_mono hj.le)
    rcases hfl' with ⟨ℓ', C', ⟨_, _, ht, _⟩, _⟩ | ⟨ℓ', A', _, hsl, _⟩
    · have : sp.ts (l₀.slot + 1 : Nat) ≤ tr.time j := by
        rw [ht]; simp only [SAParams.ts]; push_cast; linarith
      have := ((ts_le_iff_le_slot sp (hr.time_nonneg j)) _).1 this
      push_cast at this
      omega
    · omega
  rcases lt_trichotomy s l₀.slot with hlt | heq | hgt
  · refine down hLB' (fastLock_compatible_of_votes hrun hxj hj hfl' hf ?_)
    intro z k hki hz e hv hes
    exact hvotes z k hki hz e hv (hes ▸ hlt) (by omega)
  · subst heq
    have hwtime : OptimisticLockAt tr w i₀ l₀.slot D CV → tr.time i₀ ≤ tr.time i := by
      rintro ⟨ℓw, Aw, hp, hsl, hsel, _⟩
      unfold optimisticSelect at hsel
      dsimp only at hsel
      split_ifs at hsel with hcond
      have ht : tr.time i₀ < sp.ts l₀.slot + 2 * sp.Δ := by
        rw [hsl] at hcond
        exact not_le.1 (not_or.1 (not_or.1 hcond).2).2
      simp only [SAParams.ts] at hlo ht
      push_cast at hlo
      linarith
    refine down hLB' ?_
    rcases fastLock_same_slot hrun hw hfl hxj hfl' hsync hwtime (hr.time_mono hj.le) hf with h | h
    exacts [Or.inr (hBD.trans h), anc_total hU h hBD]
  · have hσ : sp.slot (tr.time i) = s + 1 := by omega
    rcases hcase with ⟨j₁, hj₁, ℓ₁, e₁, hc₁, hs₁, hF₁⟩ | ⟨k, hk, hrk, htk⟩
    · exact locks_after_unlock hrun hw hfl hBD hcarry hx hc₁ hs₁ hF₁ hj₁ l₀
        (hstate ▸ hl₀) hgt B₀ (hΦU hB₀) hB₀r
    · exfalso
      have he := hri.localRun.exec i ℓ hc'.2 (hc'.1 ▸ hx)
      rw [hc'.1, hcall] at he
      have hpost : joined sp ((tr.upTo (tr.time i)).post i) (tr.time i) := by
        have : (tr.upTo (tr.time i)).post i =
            (acToFG sp ((tr.upTo (tr.time i)).state x i) ℓ.frame (tr.time i)).1 :=
          (congrArg Prod.fst he).symm
        unfold joined at hjoin ⊢
        rw [this, hstate, hrt]
        exact hjoin
      have hh := (SA.joined_awake sp FGP ro _ U _ hri.localRun x hx i ℓ hc' hpost).2 k hk.le
        ((ACTrace.upTo_restartAt (A := goldilocksSA sp FGP ro)).mpr ⟨hr.time_mono hk.le, hrk⟩)
      simp only [Trace.upTo_time, hσ] at hh
      have hcσ : ((s + 1 : Nat) : Int) - 1 = (s : Int) := by push_cast; ring
      rw [hcσ] at hh
      linarith

theorem source_compatible (sp : SAParams) : SourceCompatible sp := by
  intro FGP ro H U tr proposer hrun s m w x i₀ i B CV ℓ C hw hfl
  exact source_compatible_stored sp FGP ro proposer H U tr hrun s m w x i₀ i B B CV ℓ C
    hw hfl .refl

end Consensus.Goldilocks.SA.Growing

end

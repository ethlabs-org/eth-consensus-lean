module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Locks
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Unlocked
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Opponents
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Unlocking with the counted votes of a historical writer -/

namespace Consensus.Goldilocks.SA.Growing

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP}
  {tr : SATrace sp FGP ro} {H : Time → Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {proposer : Nat → Fin sp.n}

private theorem genesis_mem_U {K : Set (Fin sp.n)}
    (hr : ACLocalRun (goldilocksSA sp FGP ro) K U tr) {y : Fin sp.n}
    (hy : y ∈ K) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ℓ) :
    ∃ G ∈ U, G.root = sp.genesisRoot ∧ G.parent = none := by
  induction i using Nat.strong_induction_on generalizing ℓ with
  | _ i ih =>
    rcases hr.frameLaw y hy i ℓ hc with
      ⟨_, Φ₀, ⟨htree, hroot, _, hpar, _⟩, ⟨_, hΦ₀U⟩, _⟩ | ⟨j, ℓ', hj, hc', _, _⟩
    · exact ⟨Φ₀.F, hΦ₀U (htree ▸ Set.mem_singleton _), hroot, hpar⟩
    · exact ih j hj hc'

/-- The receiving node's lock history is retained at `b`; the writer is only required
to have been honest at `i₀`, when its counted votes were fixed. -/
theorem locks_after_unlock (hrun : ACRun proposer tr H U)
    {s : Nat} {w x : Fin sp.n} {i₀ j b : Nat} {B D : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (hw : w ∈ H (tr.time i₀)) (hfl : FastLockAt tr w i₀ s D CV) (hBD : Anc U B D)
    (hcarry : Carry tr H U s CV) (hx : x ∈ H (tr.time b))
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr x j ℓ e)
    (hs : e.msg.slot = s + 1) (hF : Compatible U ℓ.frame.F B) (hjb : j < b) :
    ∀ l ∈ (tr.state x b).locks, l.slot < s → ∀ L ∈ U, L.root = l.block → Compatible U L B := by
  have hm := hrun.localRun.time_mono
  have hb := hrun.localRun.time_nonneg b
  have hrun' := hrun.upTo hb
  have hr := hrun'.localRun
  have hU := hr.coherent
  have hc' := upTo_castAt.mpr ⟨hm hjb.le, hc⟩
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_call hr hx hc'.1
  obtain ⟨hn, hcv⟩ := fastLock_counted hrun hw hfl
  replace hcv : ∀ v ∈ CV, v.slot = s ∧ ∃ R ∈ U, R.root = v.head ∧ R.slot ≤ s ∧ Anc U B R :=
    fun v hv => (hcv v hv).imp_right fun ⟨R, hR, h₁, h₂, h₃⟩ =>
      ⟨R, hR, h₁, h₂, hBD.trans h₃⟩
  have hcar := hcarry x j e (hrun.localRun.antitone (hm hjb.le) hx) ⟨ℓ, hc⟩ hs
  have hsj : sp.slot (tr.time j) = s + 1 := by
    have h := (castAt_spec hr hx hc').2.1
    change e.msg.slot = sp.slot (tr.time j) at h
    exact h.symm.trans hs
  have htj : sp.ts (s + 1 : Nat) ≤ tr.time j := by
    have hsj := (castAt_spec hr hx hc').2.1
    exact ((ts_le_iff_le_slot sp (hr.time_nonneg j)) _).2 (by rw [← hsj, hs])
  have hfreeze : sp.ts s + 3 * sp.Δ ≤ tr.time b := by
    have hΔ := sp.toParams.hΔ
    have ht := hm hjb.le
    simp only [SAParams.ts] at htj ⊢
    push_cast at htj
    linarith
  have hcar := carryAt_upTo (d := tr.time b) (hm hjb.le) hfreeze hcar
  have down : ∀ {X Y}, Anc U X Y → Compatible U Y B → Compatible U X B := by
    rintro X Y hXY (h | h)
    · exact Or.inl (hXY.trans h)
    · exact anc_total hU hXY h
  have hΔ := sp.toParams.hΔ
  have hA : ∀ l ∈ e.readPoint.locks, l.slot < s → ∀ X ∈ ℓ.frame.tree, X.root = l.block →
      Compatible U X B := by
    rcases hF with hFB | hBF
    swap
    · intro l _ _ X hX _
      exact Or.inr (hBF.trans (Anc.mono hΦU (hΦ.rooted.2 X hX)))
    have hBt : B ∈ ℓ.frame.tree := by
      have hpos : 0 < sp.n := Fin.pos x
      obtain ⟨u, v, hv, _⟩ := Set.nonempty_of_ncard_ne_zero
        (s := {u | ∃ v ∈ CV, v.val = u}) (by omega)
      obtain ⟨_, R, hR, hRr, _, hBR⟩ := hcv v hv
      obtain ⟨Hv, hHv, hHvr, hacc⟩ := hcar.heads v hv
      obtain rfl : R = Hv := hU.1 hR hHv (hRr.trans hHvr.symm)
      rcases hacc B hBR with hg | ⟨k, hk, hkt⟩
      · rcases Relation.ReflTransGen.cases_tail hFB with heq | ⟨c, _, hcB⟩
        · exact heq ▸ hΦ.rooted.1
        · obtain ⟨G, hG, hGr, hGp⟩ := genesis_mem_U hr hx hc'.1
          obtain rfl : B = G := hU.1 hcB.2.1 hG (hg.trans hGr.symm)
          exact absurd (hcB.2.2.symm.trans hGp) (by simp)
      · refine mem_tree_of_acceptAt sp hr hx hk ?_ hc'.1 hFB
        by_contra hkj
        have ht := hr.time_mono (le_of_lt (not_le.1 hkj))
        simp only [Trace.upTo_time] at ht hkt
        simp only [SAParams.ts] at htj hkt
        push_cast at htj
        linarith
    obtain ⟨L₀, hL₀⟩ := readPoint_locks hr hx hc' (by omega)
    have hσ : ((s + 1 : Nat) : Int) - 1 = s := by push_cast; ring
    have hm' : ∀ u, u.slot = s → HeldBefore e.readPoint u (sp.ts s + 3 * sp.Δ) →
        u ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes := by
      intro u hus hu
      refine Or.inl (List.mem_filter.2 ⟨?_, ?_⟩)
      · simp only [SAState.poolAt, show ¬ (((s + 1 : Nat) : Int) - 1 < 0) by omega, ite_false]
        simpa [hus] using hu.1
      · simpa [freeze] using hu.2
    intro l hl hls X hX hXr
    rw [hL₀, hs, hσ] at hl
    refine (unlock_compatible hΦ hBt (S := {u | ∃ v ∈ CV, v.val = u}) ?_ hn L₀ (tr.time j) l hl
      (by exact_mod_cast hls) X hX hXr).imp (Anc.mono hΦU) (Anc.mono hΦU)
    rintro u ⟨v, hv, rfl⟩
    obtain ⟨hvs, R, hR, hRr, hRs, hBR⟩ := hcv v hv
    rcases hcar.holds v hv with hheld | ⟨v₁, v₂, h12, _, _, hv₁, hv₂, hs₁, hs₂, hh₁, hh₂⟩
    · by_cases heq : v.val ∈ equivocators (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes
      · exact Or.inl heq
      · obtain ⟨Hv, hHv, hHvr, hacc⟩ := hcar.heads v hv
        obtain rfl : R = Hv := hU.1 hR hHv (hRr.trans hHvr.symm)
        obtain ⟨_, x', hx', hx'v, hx's, hanc⟩ := carried_supporter hrun' hx hc' hs hBt hvs hheld
          ⟨R, hR, hRr, hRs, hBR, hacc R Relation.ReflTransGen.refl⟩ heq
        exact Or.inr ⟨x', hx', hx'v, hx's, hanc⟩
    · exact Or.inl ⟨v₁, hm' v₁ hs₁ hh₁, v₂, hm' v₂ hs₂ hh₂, h12, hv₁, hv₂⟩
  have hB' : ∀ l ∈ ((tr.upTo (tr.time b)).state x (j + 1)).locks, l.slot < s →
      ∃ Y ∈ ℓ.frame.tree, Y.root = l.block ∧ Compatible U Y B := by
    rw [state_succ_of_call hc'.1, post_of_castAt hr hx hc']
    have hrb : ∀ l ∈ e.readPoint.locks, ∃ Y ∈ ℓ.frame.tree, Y.root = l.block := by
      obtain ⟨L₀, hL₀⟩ := readPoint_locks hr hx hc' (by omega)
      intro l hl
      rw [hL₀] at hl
      obtain ⟨_, _, _, _, _, _, _, _, Y, hY, hYr, _⟩ :=
        ((locks_move_back sp) FGP ℓ.frame L₀ (tr.time j) hΦ).2.2 _ _ l hl
      exact ⟨Y, hY, hYr⟩
    intro l hl hls
    unfold optimisticConfirmation at hl
    split at hl
    · rw [admitVote_locks_eq] at hl
      obtain ⟨Y, hY, hYr⟩ := hrb l hl
      exact ⟨Y, hY, hYr, hA l hl hls Y hY hYr⟩
    · rw [updateLatestConfirmed_keeps_locks] at hl
      obtain ⟨l₀, hl₀, hsl, _, _, X, hX, hXr, Y, hY, hYr, hYX⟩ :=
        ((locks_move_back sp) FGP ℓ.frame _ (tr.time j) hΦ).2.1 _ _ l hl
      rcases hl₀ with hl₀ | ⟨p, hp, rfl⟩
      · rw [admitVote_locks_eq] at hl₀
        exact ⟨Y, hY, hYr, down (Anc.mono hΦU hYX) (hA l₀ hl₀ (hsl ▸ hls) X hX hXr)⟩
      · rw [Set.mem_singleton_iff] at hp
        subst hp
        simp only [Trace.upTo_time] at hsl
        omega
  intro l hl hls L hL hLr
  have hstate : (tr.upTo (tr.time b)).state x b = tr.state x b :=
    Trace.upTo_state tr x fun _ hk => hm hk.le
  rw [← hstate] at hl
  rcases lock_provenance_from hr hx (Nat.succ_le_of_lt hjb) l hl with
    ⟨l', hl', hsl, h⟩ | ⟨j', hj', _, B'', horig, _⟩
  · obtain ⟨Y, hY, hYr, hYB⟩ := hB' l' hl' (hsl ▸ hls)
    rcases h with rfl | ⟨L₁, hL₁, hL₁r, L₂, hL₂, hL₂r, hLL⟩
    · obtain rfl : L = Y := hU.1 hL (hΦU hY) (hLr.trans hYr.symm)
      exact hYB
    · obtain rfl : L = L₁ := hU.1 hL hL₁ (hLr.trans hL₁r.symm)
      obtain rfl : L₂ = Y := hU.1 hL₂ (hΦU hY) (hL₂r.trans hYr.symm)
      exact down hLL hYB
  · exfalso
    have hmono := hr.time_mono (show j ≤ j' by omega)
    simp only [Trace.upTo_time] at hmono
    rcases horig with ⟨CV', ℓ', A', _, hsl', _⟩ | ⟨ℓ', _, _, ht', _⟩
    · have hslot := slot_mono sp (hr.time_nonneg j) hmono
      simp only [Trace.upTo_time] at hslot
      simp only [Trace.upTo_time] at hsl'
      omega
    · have hls' : (l.slot : Int) + 1 ≤ s := by exact_mod_cast hls
      simp only [Trace.upTo_time] at ht'
      simp only [SAParams.ts] at htj ht'
      push_cast at htj
      have h4 : (0 : Time) ≤ 4 * sp.Δ := by linarith [sp.toParams.hΔ]
      linarith [mul_le_mul_of_nonneg_left hls' h4]

end Consensus.Goldilocks.SA.Growing

end

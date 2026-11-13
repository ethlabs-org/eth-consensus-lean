module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Unlock
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Opponents
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks SA: the locks of a node after its slot-`(s+1)` unlocking (A1.9, case (i))

Let an honest node write a fast lock of slot `s` on `D ⪰ B` with counted votes `CV`, under
`Carry(s, S, B)`. At an honest `x`'s slot-`(s+1)` vote, the counted validators (at least half of
the committee) are supporters of `B` in `x`'s merged view or equivocate there, so its unlocking
moves every lock of a slot below `s` to a block compatible with `B` (`unlock_compatible`; when
`B` is below the frame's `Φ.F`, every block of the tree extends it). Later, locks only move back,
and the fast locks written after the vote are of slot `s` or later: every lock of a slot below
`s` that `x` holds after the vote is on a block compatible with `B`. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {proposer : Nat → Fin sp.n}

private theorem genesis_mem_U (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ℓ) :
    ∃ G ∈ U, G.root = sp.genesisRoot ∧ G.parent = none := by
  induction i using Nat.strong_induction_on generalizing ℓ with
  | _ i ih =>
    rcases hr.frameLaw y hy i ℓ hc with
      ⟨-, Φ₀, ⟨htree, hroot, -, hpar, -⟩, ⟨-, hΦ₀U⟩, -⟩ | ⟨j, ℓ', hj, hc', -, -⟩
    · exact ⟨Φ₀.F, hΦ₀U (htree ▸ Set.mem_singleton _), hroot, hpar⟩
    · exact ih j hj hc'

/-- The counted votes of an honest fast lock of slot `s` on `B`: their validators are at least
half of the committee, and each is a slot-`s` vote whose head, of slot at most `s`, extends `B`
inside `U`. -/
theorem fastLock_counted (hrun : ACRun proposer tr H U)
    {w : Fin sp.n} (hw : w ∈ H) {i₀ s : Nat}
    {B : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hfl : FastLockAt tr w i₀ s B CV) :
    sp.n ≤ 2 * {u | ∃ v ∈ CV, v.val = u}.ncard ∧
      ∀ v ∈ CV, v.slot = s ∧ ∃ R ∈ U, R.root = v.head ∧ R.slot ≤ s ∧ Anc U B R := by
  have hr := hrun.localRun
  rcases hfl with ⟨ℓ, C, ⟨hc, -, -, -⟩, -, hD, rfl⟩ | ⟨ℓ, A, hpt, hsl, hsel, rfl⟩
  · obtain ⟨hΦ, hΦU⟩ := frameIn_of_call hr hw hc
    refine ⟨?_, ?_⟩
    · have hfast := (deepest_mem hD).1.2.2
      unfold FastTest confirmationScore at hfast
      rw [hrun.stock] at hfast
      refine hfast.trans (Nat.mul_le_mul_left 2 (Set.ncard_le_ncard ?_))
      rintro u ⟨hu, x, ⟨hx, hres⟩, hval, -, hanc⟩
      exact ⟨x, ⟨hx, hval ▸ hu, hres, hanc⟩, hval⟩
    · rintro v ⟨hvp, -, hres, R, hR, hRr, hBR⟩
      refine ⟨state_pool_slot sp hr hw i₀ s v hvp, R, hΦU hR, hRr, ?_, Anc.mono hΦU hBR⟩
      have hvs := state_pool_slot sp hr hw i₀ s v hvp
      unfold resolutionTime at hres
      split at hres
      · exact absurd hres (by simp [ETime.of])
      · rename_i Hd hl
        obtain ⟨hHd, hHdr⟩ := lookup_eq_some hl
        obtain rfl : Hd = R := hΦ.coherent.1 hHd hR (hHdr.trans hRr.symm)
        split_ifs at hres with hlt
        · exact absurd hres (by simp [ETime.of])
        · omega
  · obtain ⟨hΦ, hΦU⟩ := frameIn_of_call hr hw hpt.1
    unfold optimisticSelect at hsel
    dsimp only at hsel
    split_ifs at hsel
    have h34 := (deepest_mem hsel).1.2.1
    rw [hrun.stock] at h34
    refine ⟨?_, ?_⟩
    · have hsub : optimisticVoters sp A ℓ.frame (sp.slot (tr.time i₀)) B ⊆
          {u | ∃ v ∈ {v | v ∈ A.pool s ∧ AncR ℓ.frame B v.head}, v.val = u} := by
        rintro u ⟨v, hv, rfl, hanc⟩
        exact ⟨v, ⟨hsl ▸ hv, hanc⟩, rfl⟩
      have := Set.ncard_le_ncard hsub
      omega
    · rintro v ⟨hv, R, hR, hRr, hBR⟩
      refine ⟨optimisticPoint_pool_slot hr hw hpt hv, R, hΦU hR, hRr, ?_, Anc.mono hΦU hBR⟩
      have := frame_slot_le sp hr hw hpt.1 R hR
      omega

/-- **The locks after the unlocking of slot `s + 1`**, for a fast lock on `D` and any `B ⪯ D`
(the block the lock stores). -/
theorem locks_after_unlock
    (hrun : ACRun proposer tr H U) {s : Nat} {w x : Fin sp.n} {i₀ j b : Nat}
    {B D : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hw : w ∈ H) (hfl : FastLockAt tr w i₀ s D CV)
    (hBD : Anc U B D) (hcarry : Carry tr H U s CV) (hx : x ∈ H)
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr x j ℓ e)
    (hs : e.msg.slot = s + 1) (hF : Compatible U ℓ.frame.F B) (hjb : j < b) :
    ∀ l ∈ (tr.state x b).locks, l.slot < s → ∀ L ∈ U, L.root = l.block → Compatible U L B := by
  have hr := hrun.localRun
  have hU := hr.coherent
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_call hr hx hc.1
  obtain ⟨hn, hcv⟩ := fastLock_counted hrun hw hfl
  replace hcv : ∀ v ∈ CV, v.slot = s ∧ ∃ R ∈ U, R.root = v.head ∧ R.slot ≤ s ∧ Anc U B R :=
    fun v hv => (hcv v hv).imp_right fun ⟨R, hR, h₁, h₂, h₃⟩ =>
      ⟨R, hR, h₁, h₂, hBD.trans h₃⟩
  have hcar := hcarry x hx j e ⟨ℓ, hc⟩ hs
  have down : ∀ {X Y}, Anc U X Y → Compatible U Y B → Compatible U X B := by
    rintro X Y hXY (h | h)
    · exact Or.inl (hXY.trans h)
    · exact anc_total hU hXY h
  have hΔ := sp.toParams.hΔ
  obtain ⟨-, hsj, -, -⟩ := castAt_spec hr hx hc
  have htj : sp.ts (s + 1 : Nat) ≤ tr.time j :=
    ((ts_le_iff_le_slot sp (hr.time_nonneg j)) _).2 (by rw [← hsj, hs])
  -- at the read point, every lock of a slot below `s` is on a block compatible with `B`
  have hA : ∀ l ∈ e.readPoint.locks, l.slot < s → ∀ X ∈ ℓ.frame.tree, X.root = l.block →
      Compatible U X B := by
    rcases hF with hFB | hBF
    swap
    · intro l _ _ X hX _
      exact Or.inr (hBF.trans (Anc.mono hΦU (hΦ.rooted.2 X hX)))
    -- `B` is in the tree: a counted head extends it, and `x` accepted it before `t_s + 3Δ`
    have hBt : B ∈ ℓ.frame.tree := by
      have hpos : 0 < sp.n := Fin.pos x
      obtain ⟨u, v, hv, -⟩ := Set.nonempty_of_ncard_ne_zero
        (s := {u | ∃ v ∈ CV, v.val = u}) (by omega)
      obtain ⟨-, R, hR, hRr, -, hBR⟩ := hcv v hv
      obtain ⟨Hv, hHv, hHvr, hacc⟩ := hcar.heads v hv
      obtain rfl : R = Hv := hU.1 hR hHv (hRr.trans hHvr.symm)
      rcases hacc B hBR with hg | ⟨k, hk, hkt⟩
      · rcases Relation.ReflTransGen.cases_tail hFB with heq | ⟨c, -, hcB⟩
        · exact heq ▸ hΦ.rooted.1
        · obtain ⟨G, hG, hGr, hGp⟩ := genesis_mem_U hr hx hc.1
          obtain rfl : B = G := hU.1 hcB.2.1 hG (hg.trans hGr.symm)
          exact absurd (hcB.2.2.symm.trans hGp) (by simp)
      · refine mem_tree_of_acceptAt sp hr hx hk ?_ hc.1 hFB
        by_contra hkj
        have := hr.time_mono (le_of_lt (not_le.1 hkj))
        simp only [SAParams.ts] at htj hkt
        push_cast at htj
        linarith
    obtain ⟨L₀, hL₀⟩ := readPoint_locks hr hx hc (by omega)
    have hσ : ((s + 1 : Nat) : Int) - 1 = s := by push_cast; ring
    have hm : ∀ u, u.slot = s → HeldBefore e.readPoint u (sp.ts s + 3 * sp.Δ) →
        u ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes := by
      intro u hus hu
      refine Or.inl (List.mem_filter.2 ⟨?_, ?_⟩)
      · simp only [SAState.poolAt, show ¬ (((s + 1 : Nat) : Int) - 1 < 0) by omega, ite_false]
        simpa [hus] using hu.1
      · simpa [freeze] using hu.2
    intro l hl hls X hX hXr
    rw [hL₀, hs, hσ] at hl
    refine (unlock_compatible hΦ hBt (S := {u | ∃ v ∈ CV, v.val = u}) ?_
      (by simpa only [hrun.stock] using hn) L₀ (tr.time j) l hl
      (by exact_mod_cast hls) X hX hXr).imp (Anc.mono hΦU) (Anc.mono hΦU)
    rintro u ⟨v, hv, rfl⟩
    obtain ⟨hvs, R, hR, hRr, hRs, hBR⟩ := hcv v hv
    rcases hcar.holds v hv with hheld | ⟨v₁, v₂, h12, -, -, hv₁, hv₂, hs₁, hs₂, hh₁, hh₂⟩
    · by_cases heq : v.val ∈ equivocators (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes
      · exact Or.inl heq
      · obtain ⟨Hv, hHv, hHvr, hacc⟩ := hcar.heads v hv
        obtain rfl : R = Hv := hU.1 hR hHv (hRr.trans hHvr.symm)
        obtain ⟨-, x', hx', hx'v, hx's, hanc⟩ := carried_supporter hrun hx hc hs hBt hvs hheld
          ⟨R, hR, hRr, hRs, hBR, hacc R Relation.ReflTransGen.refl⟩ heq
        exact Or.inr ⟨x', hx', hx'v, hx's, hanc⟩
    · exact Or.inl ⟨v₁, hm v₁ hs₁ hh₁, v₂, hm v₂ hs₂ hh₂, h12, hv₁, hv₂⟩
  -- after the vote's own optimistic check, the locks of a slot below `s` sit below those
  have hB' : ∀ l ∈ (tr.state x (j + 1)).locks, l.slot < s →
      ∃ Y ∈ ℓ.frame.tree, Y.root = l.block ∧ Compatible U Y B := by
    rw [show tr.state x (j + 1) = tr.post j by simp [Trace.state, hc.1.1, hc.1.2],
      post_of_castAt hr hx hc]
    have hrb : ∀ l ∈ e.readPoint.locks, ∃ Y ∈ ℓ.frame.tree, Y.root = l.block := by
      obtain ⟨L₀, hL₀⟩ := readPoint_locks hr hx hc (by omega)
      intro l hl
      rw [hL₀] at hl
      obtain ⟨-, -, -, -, -, -, -, -, Y, hY, hYr, -⟩ :=
        ((locks_move_back sp) FGP ℓ.frame L₀ (tr.time j) hΦ).2.2 _ _ l hl
      exact ⟨Y, hY, hYr⟩
    intro l hl hls
    unfold optimisticConfirmation at hl
    split at hl
    · rw [admitVote_locks_eq] at hl
      obtain ⟨Y, hY, hYr⟩ := hrb l hl
      exact ⟨Y, hY, hYr, hA l hl hls Y hY hYr⟩
    · rw [updateLatestConfirmed_keeps_locks] at hl
      obtain ⟨l₀, hl₀, hsl, -, -, X, hX, hXr, Y, hY, hYr, hYX⟩ :=
        ((locks_move_back sp) FGP ℓ.frame _ (tr.time j) hΦ).2.1 _ _ l hl
      rcases hl₀ with hl₀ | ⟨p, hp, rfl⟩
      · rw [admitVote_locks_eq] at hl₀
        exact ⟨Y, hY, hYr, down (Anc.mono hΦU hYX) (hA l₀ hl₀ (hsl ▸ hls) X hX hXr)⟩
      · rw [Set.mem_singleton_iff] at hp
        subst hp
        simp only at hsl
        omega
  -- later, locks only move back, and no lock of a slot below `s` is written
  intro l hl hls L hL hLr
  rcases lock_provenance_from hr hx (Nat.succ_le_of_lt hjb) l hl with
    ⟨l', hl', hsl, h⟩ | ⟨j', hj', -, B'', horig, -⟩
  · obtain ⟨Y, hY, hYr, hYB⟩ := hB' l' hl' (hsl ▸ hls)
    rcases h with rfl | ⟨L₁, hL₁, hL₁r, L₂, hL₂, hL₂r, hLL⟩
    · obtain rfl : L = Y := hU.1 hL (hΦU hY) (hLr.trans hYr.symm)
      exact hYB
    · obtain rfl : L = L₁ := hU.1 hL hL₁ (hLr.trans hL₁r.symm)
      obtain rfl : L₂ = Y := hU.1 hL₂ (hΦU hY) (hL₂r.trans hYr.symm)
      exact down hLL hYB
  · exfalso
    have hmono := hr.time_mono (show j ≤ j' by omega)
    rcases horig with ⟨CV', ℓ', A', -, hsl', -⟩ | ⟨ℓ', -, -, ht', -⟩
    · have := slot_mono sp (hr.time_nonneg j) hmono
      omega
    · have hls' : (l.slot : Int) + 1 ≤ s := by exact_mod_cast hls
      simp only [SAParams.ts] at htj ht'
      push_cast at htj
      have h4 : (0 : Time) ≤ 4 * sp.Δ := by linarith [sp.toParams.hΔ]
      linarith [mul_le_mul_of_nonneg_left hls' h4]

end Consensus.Goldilocks.SA

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ResultAnc
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.PreAdvance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Geo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Batch
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.SupplierFrames
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.FloorUpdate
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Supplier
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Honest votes, early pools and older-lock compatibility under finite service

* `honest_votes_of_joined_before`: finite service and joinedness at the actual vote deadline
  supply an honest vote, with no `4Δ` warm-start margin.
* `honest_vote_early_pool_before`: an actual honest vote emitted after GST is held with its strict
  early stamp.
* `confirmation_of_unanimous_early_pool`: the unique early honest batch of the slot-`u` committee
  forces the raw result and fast selection.
* `older_locks_compatible_after_unlock`: a half-committee supporting a block at an actual
  next-slot unlock makes all older lock labels compatible at every later cut.
-/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g b : Time}
  {proposer : Nat → Fin sp.n}

/-- Finite service and joinedness at the actual vote deadline supply an honest vote.
No `4Δ` warm-start margin is needed when joinedness is supplied explicitly. -/
theorem honest_votes_of_joined_before (hS : HealthyBaseUpTo tr H U proposer g b)
    {u : Nat} (hgu : gbar g ≤ sp.ts u) (hub : sp.ts u + sp.Δ ≤ b)
    (hjoin : ∀ x ∈ H, JoinedAt tr x (sp.ts u + sp.Δ)) :
    ∀ x ∈ H, ∃ j e, VoteAt tr x j e ∧ e.msg.slot = u ∧ tr.time j ≤ sp.ts u + sp.Δ := by
  have hr := hS.run.localRun
  have hDelta := sp.toParams.hΔ
  have hg0 := gbar_nonneg g
  intro x hx
  have hslot : sp.slot (sp.ts u + sp.Δ) = u := by
    apply slot_of_mem sp u (by linarith)
    simp only [SAParams.ts]; push_cast; linarith
  obtain ⟨c, ell, hc, hcall, htc⟩ := hS.driven.tick x hx (sp.ts u + sp.Δ) (by linarith)
    ⟨4 * u + 1, by simp only [SAParams.ts]; ring⟩ (hS.awake x hx _ (by linarith) hub)
  have hj : joined sp (tr.state x c) (tr.time c) := by
    unfold joined
    rcases restartTime_state hr hx c with h | ⟨r, hrc, hrs, h⟩
    · rw [h]; exact bot_le
    · rw [h]
      apply WithBot.coe_le_coe.mpr
      rw [htc]
      exact hjoin x hx r hrs ((hr.time_mono hrc.le).trans htc.le)
  by_cases hv : (tr.state x c).votedSlot = (sp.slot (tr.time c) : Int)
  · obtain ⟨j, hjc, e, he, hes⟩ :=
      (cast_of_votedSlot hr (fun _ => voteStart_initial _) hx c _ hv).resolve_right
        (by rw [trace_mayVote_stock hr hx c]; decide)
    exact ⟨j, e, he, by rw [hes, htc, hslot], (hr.time_mono hjc.le).trans htc.le⟩
  · have hT : tr.time c = sp.ts (sp.slot (tr.time c)) + sp.Δ := by rw [htc, hslot]
    obtain ⟨e, hem, hes⟩ := tryVote_votes x ell.frame hj hv hT (trace_mayVote_stock hr hx c _)
    have he := hr.exec c ell hc.2 (hc.1 ▸ hx)
    rw [hc.1, hcall] at he
    have h2 : (acOnTick sp x (tr.state x c) ell.frame (tr.time c)).2 = ell.emits :=
      congrArg Prod.snd he
    have h3 : (acOnTick sp x (tr.state x c) ell.frame (tr.time c)).2 =
        (tryVote sp x (tr.state x c) ell.frame (tr.time c)).2 := by
      unfold acOnTick
      dsimp only
      split_ifs
      all_goals first | rfl | exact absurd hj ‹_›
    exact ⟨c, e, ⟨ell, hc, h2 ▸ h3 ▸ hem⟩, by rw [hes, htc, hslot], htc.le⟩

/-- An actual honest vote emitted after GST is held with its strict early stamp.
The restart and deadline premises concern only cuts through the receiving call. -/
theorem honest_vote_early_pool_before (hS : HealthyBaseUpTo tr H U proposer g b)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ell : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y j ell) {u : Nat}
    (hgu : gbar g ≤ sp.ts u) (ht : sp.ts u + 2 * sp.Δ ≤ tr.time j)
    (hjb : tr.time j ≤ b)
    (hdeadline : ∀ k ≤ j, ∀ t, gbar g ≤ t → tr.deadline y k t ≤ max t (sp.ts u) + sp.Δ)
    (hrestart : ∀ k ≤ j, tr.RestartAt y k → tr.time k < sp.ts u)
    {x : Fin sp.n} (hx : x ∈ H) {i : Nat} {e : Em sp FGP}
    (hv : VoteAt tr x i e) (hes : e.msg.slot = u) :
    ∀ c, (c = j ∨ c = j + 1) → e.msg ∈ (tr.state y c).pool u ∧
      (tr.state y c).voteStamp e.msg < ETime.of (sp.ts u + 2 * sp.Δ) := by
  have hr := hS.run.localRun
  have hDelta := sp.toParams.hΔ
  obtain ⟨ellx, hcx, hex⟩ := hv
  obtain ⟨hval, hslot, -, -⟩ := castAt_spec hr hx ⟨hcx, hex⟩
  have hti : tr.time i ≤ sp.ts u + sp.Δ := by
    have hh := vote_time_le hr hx ⟨ellx, hcx, hex⟩
    rwa [← hslot, hes] at hh
  have hti0 : sp.ts u ≤ tr.time i :=
    (ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by rw [← hslot, hes])
  have hgi : gbar g ≤ tr.time i := hgu.trans hti0
  have hdl := hdeadline j le_rfl (tr.time i) hgi
  rw [max_eq_left hti0] at hdl
  obtain ⟨q, hqj, hiq, hproc, hqt⟩ := hS.sync.message x hx i e.msg
    ⟨ellx, hcx, Or.inl ⟨e, hex, rfl⟩⟩ hgi y hy j ell hc
    (by linarith only [ht, hjb, hti, hdl]) (by linarith only [ht, hti, hdl])
  have hqT : tr.time q < sp.ts u + 2 * sp.Δ := by
    have hqdl := hdeadline q hqj (tr.time i) hgi
    rw [max_eq_left hti0] at hqdl
    linarith only [hti, hqt, hqdl]
  have hqj' : q < j := lt_of_le_of_ne hqj (by rintro rfl; linarith only [hqT, ht])
  have hts : sp.ts (u + 1 : Nat) = sp.ts u + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hqs : sp.slot (tr.time q) = u :=
    slot_of_mem sp u (by linarith only [hti0, hiq]) (by rw [hts]; linarith only [hti, hti0, hqT])
  have hxH : e.msg.val ∈ H := hval ▸ hx
  have hheld : e.msg ∈ (tr.state y (q + 1)).pool u := by
    rcases held_of_processAt hr hy hproc (by rw [hqs, hes]; (clear * -; omega)) (by
        rw [hqs, hes]) with
      h | ⟨v, hv, w, hw, hne, hvval, hwval⟩
    · rwa [hes] at h
    · exfalso
      rw [hes] at hv hw
      obtain ⟨iv, -, ev, hev, rfl⟩ := hS.run.honest.pool_vote y hy (q + 1) u _ hv (hvval ▸ hxH)
      obtain ⟨iw, -, ew, hew, rfl⟩ := hS.run.honest.pool_vote y hy (q + 1) u _ hw (hwval ▸ hxH)
      have hsv := state_pool_slot sp hr hy (q + 1) u _ hv
      have hsw := state_pool_slot sp hr hy (q + 1) u _ hw
      rw [hvval] at hev
      rw [hwval] at hew
      obtain ⟨-, rfl⟩ := (one_vote_per_slot sp) FGP ro H U tr hr _ hxH iv iw ev ew hev hew
        (hsv.trans hsw.symm)
      exact hne rfl
  intro c hcj
  have hst := stamp_lt_of_held_of_run hr hy (a := q + 1) (b := c) (by clear * - hqj' hcj; omega)
    (w := e.msg) (by rw [hes]; exact hheld) (T := sp.ts u + 2 * sp.Δ)
    (fun k hk => lt_of_le_of_lt (hr.time_mono (Nat.lt_succ_iff.1 hk)) hqT)
    (by rw [hes]; linarith only [hti0, hqT, hiq])
    (fun k hk hrs => lt_trans (hrestart k (by clear * - hcj hk; omega) hrs) (by
        linarith only [hti0, hqT, hiq]))
    (fun k hqk hkc hrs => by
      have := hrestart k (by clear * - hcj hkc; omega) hrs
      have := hr.time_mono (show q ≤ k by clear * - hqk; omega)
      linarith)
  rwa [hes] at hst

/-- The unique early honest batch of the slot-`u` committee forces the raw result and fast
selection, when every pool vote is a committee member's and fewer than a third of the committee
is faulty. This is a pool calculation, independent of any lock-veto premise. -/
theorem confirmation_of_unanimous_early_pool
    {A : SAState sp.n} {Phi : Frm sp.n FGP} {u : Nat} {P : Blk sp.n FGP}
    (hPhi : FrameOK Phi) (hPt : P ∈ Phi.tree) (hPg : P.root ≠ sp.genesisRoot)
    (K : CommitteeDict sp.n) (hsize : (K.committee u).ncard = sp.committeeSize)
    (hP : ∀ v ∈ A.pool u, v.val ∈ K.committee u)
    (hf : 3 * (K.committee u ∩ Hᶜ).ncard < sp.committeeSize)
    (hslots : ∀ v ∈ A.pool u, v.slot = u)
    (hpool : ∀ x ∈ H, x ∈ K.committee u → ∃ v ∈ A.pool u, v.val = x ∧ v.head = P.root ∧
      resolutionTime A Phi v < ETime.of (sp.ts u + 2 * sp.Δ) ∧
      ∀ v' ∈ A.pool u, v'.val = x → v' = v) :
    getConfirmation sp A Phi u = some P ∧ fastSelect sp A Phi u P = some P := by
  have hHvot : K.committee u ∩ H ⊆ voters {v | v ∈ A.pool u} := fun x hx => by
    obtain ⟨v, hv, hvx, -⟩ := hpool x hx.2 hx.1
    exact ⟨v, hv, hvx⟩
  have hvle : (voters {v | v ∈ A.pool u}).ncard ≤ sp.committeeSize := by
    rw [← hsize]
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    rintro x ⟨v, hv, rfl⟩
    exact hP v hv
  have hsplit : (K.committee u ∩ H).ncard + (K.committee u ∩ Hᶜ).ncard =
      (K.committee u).ncard :=
    Set.ncard_inter_add_ncard_sdiff_eq_ncard _ H (Set.toFinite _)
  have hHle := Set.ncard_le_ncard hHvot
  have hscore : (K.committee u ∩ H).ncard ≤ confirmationScore sp A Phi u P := by
    unfold confirmationScore
    apply Set.ncard_le_ncard (ht := Set.toFinite _)
    intro x hx
    obtain ⟨v, hv, hvx, hvh, hres, huniq⟩ := hpool x hx.2 hx.1
    refine ⟨?_, v, ⟨hv, hres⟩, hvx, ?_, P, hPt, hvh.symm, .refl⟩
    · rintro ⟨v', hv', w, hw, hne, hv'x, hwx⟩
      exact hne ((huniq v' hv' hv'x).trans (huniq w hw hwx).symm)
    · exact_mod_cast hslots v hv
  have hconf : getConfirmation sp A Phi u = some P := by
    unfold getConfirmation
    have hPS : P ∈ {B | B ∈ Phi.tree ∧ Phi.Anc Phi.F B ∧
        (voters {v | v ∈ A.pool u}).ncard < 2 * confirmationScore sp A Phi u B} :=
      ⟨hPt, hPhi.rooted.2 P hPt, by omega⟩
    have hall : ∀ B ∈ {B | B ∈ Phi.tree ∧ Phi.Anc Phi.F B ∧
        (voters {v | v ∈ A.pool u}).ncard < 2 * confirmationScore sp A Phi u B},
        Phi.Anc B P := by
      rintro B ⟨hBt, -, hmaj⟩
      by_contra hBP
      unfold confirmationScore at hmaj
      dsimp only at hmaj
      refine absurd hmaj (not_lt.2 (le_trans (Nat.mul_le_mul_left 2
        (Set.ncard_le_ncard (t := K.committee u ∩ Hᶜ) ?_)) (by omega)))
      rintro x ⟨-, v, ⟨hv, -⟩, rfl, -, R, hR, hRr, hBR⟩
      refine ⟨hP v hv, fun hx => ?_⟩
      obtain ⟨w, -, -, hwh, -, huniq⟩ := hpool _ hx (hP v hv)
      obtain rfl := huniq v hv rfl
      obtain rfl : R = P := hPhi.coherent.1 hR hPt (hRr.trans hwh)
      exact hBP hBR
    obtain ⟨D, hD⟩ := exists_deepest hPhi (fun B hB => hB.1) ⟨P, hPS⟩
    have hDP := hall D (deepest_mem hD).1
    have hPD := anc_deepest hPhi (fun B hB => hB.1)
      (fun B hB C hC => anc_total hPhi.coherent (hall B hB) (hall C hC)) hD P hPS
    rw [hD, Anc.antisymm hPhi.coherent hDP hPD]
  exact ⟨hconf, fastSelect_eq_result hPhi hPt hPg (by
      unfold FastTest; (clear * - hf hsplit hsize hscore; omega))⟩

/-- A half-committee supporting a block at an actual next-slot unlock makes all
older lock labels compatible at every later cut. Provenance excludes intervening
writes of those old labels; equal-time calls are ordered by their actual cuts. -/
theorem older_locks_compatible_after_unlock
    (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {y : Fin sp.n} (hy : y ∈ H) {j k u : Nat}
    {ell : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y j ell e) (hs : e.msg.slot = u + 1) (hjk : j < k)
    {P : Blk sp.n FGP} (hPt : P ∈ ell.frame.tree) {S : Set (Fin sp.n)}
    (hS : ∀ x ∈ S, x ∈ equivocators (mergedVoteView sp e.readPoint ell.frame (u + 1)).votes ∨
      ∃ v ∈ (mergedVoteView sp e.readPoint ell.frame (u + 1)).support,
        v.val = x ∧ (v.slot : Int) = u ∧ AncR ell.frame P v.head)
    (hhalf : sp.committeeSize ≤ 2 * S.ncard) :
    ∀ l ∈ (tr.state y k).locks, l.slot < u →
      ∀ L ∈ U, L.root = l.block → Compatible U L P := by
  obtain ⟨hPhi, hPhiU⟩ := frameIn_of_callAt hr hy hc.1
  have hU := hr.coherent
  have hDelta := sp.toParams.hΔ
  have hslot := (castAt_spec hr hy hc).2.1
  have htj : sp.ts (u + 1 : Nat) ≤ tr.time j :=
    (ts_le_iff_le_slot sp (hr.time_nonneg j) _).2 (by rw [← hslot, hs])
  have down : ∀ {X Y}, Anc U X Y → Compatible U Y P → Compatible U X P := by
    rintro X Y hXY (h | h)
    · exact Or.inl (hXY.trans h)
    · exact anc_total hU hXY h
  obtain ⟨L₀, hL₀⟩ := readPoint_locks hr hy hc (by clear * - hs; omega)
  have hsig : ((u + 1 : Nat) : Int) - 1 = u := by clear * -; omega
  have hA : ∀ l ∈ e.readPoint.locks, l.slot < u →
      ∀ X ∈ ell.frame.tree, X.root = l.block → Compatible U X P := by
    intro l hl hls X hX hXr
    rw [hL₀, hs, hsig] at hl
    exact (unlock_compatible hPhi hPt hS hhalf L₀ (tr.time j) l hl
      (by exact_mod_cast hls) X hX hXr).imp (Anc.mono hPhiU) (Anc.mono hPhiU)
  have hpost : ∀ l ∈ (tr.state y (j + 1)).locks, l.slot < u →
      ∃ Y ∈ ell.frame.tree, Y.root = l.block ∧ Compatible U Y P := by
    rw [show tr.state y (j + 1) = tr.post j by simp [Trace.state, hc.1.1, hc.1.2],
      post_of_castAt hr hy hc]
    have hrb : ∀ l ∈ e.readPoint.locks, ∃ Y ∈ ell.frame.tree, Y.root = l.block := by
      intro l hl
      rw [hL₀] at hl
      obtain ⟨_, _, _, _, _, _, _, _, Y, hY, hYr, _⟩ :=
        ((locks_move_back sp) FGP ell.frame L₀ (tr.time j) hPhi).2.2 _ _ l hl
      exact ⟨Y, hY, hYr⟩
    intro l hl hls
    unfold optimisticConfirmation at hl
    split at hl
    · rw [admitVote_locks_eq] at hl
      obtain ⟨Y, hY, hYr⟩ := hrb l hl
      exact ⟨Y, hY, hYr, hA l hl hls Y hY hYr⟩
    · rw [updateLatestConfirmed_keeps_locks] at hl
      obtain ⟨l₀, hl₀, hsl, _, _, X, hX, hXr, Y, hY, hYr, hYX⟩ :=
        ((locks_move_back sp) FGP ell.frame _ (tr.time j) hPhi).2.1 _ _ l hl
      rcases hl₀ with hl₀ | ⟨p, hp, rfl⟩
      · rw [admitVote_locks_eq] at hl₀
        exact ⟨Y, hY, hYr, down (Anc.mono hPhiU hYX)
          (hA l₀ hl₀ (hsl ▸ hls) X hX hXr)⟩
      · rw [Set.mem_singleton_iff] at hp
        subst hp
        simp only at hsl
        omega
  intro l hl hls L hL hLr
  rcases lock_provenance_from hr hy (Nat.succ_le_of_lt hjk) l hl with
    ⟨l', hl', hsl, h⟩ | ⟨j', hj', _, B, horig, _⟩
  · obtain ⟨Y, hY, hYr, hYP⟩ := hpost l' hl' (hsl ▸ hls)
    rcases h with rfl | ⟨L₁, hL₁, hL₁r, L₂, hL₂, hL₂r, hLL⟩
    · have hLY : L = Y := hU.1 hL (hPhiU hY) (hLr.trans hYr.symm)
      exact hLY.symm ▸ hYP
    · have hLL₁ : L = L₁ := hU.1 hL hL₁ (hLr.trans hL₁r.symm)
      have hL₂Y : L₂ = Y := hU.1 hL₂ (hPhiU hY) (hL₂r.trans hYr.symm)
      rw [← hLL₁, hL₂Y] at hLL
      exact down hLL hYP
  · exfalso
    have hmono := hr.time_mono (show j ≤ j' by clear * - hj'; omega)
    rcases horig with ⟨CV, ell', A', _, hsl', _⟩ | ⟨ell', _, _, ht', _⟩
    · have := slot_mono sp (hr.time_nonneg j) hmono
      omega
    · have hls' : (l.slot : Int) + 1 ≤ u := by exact_mod_cast hls
      simp only [SAParams.ts] at htj ht'
      push_cast at htj
      have h4 : (0 : Time) ≤ 4 * sp.Δ := by linarith [sp.toParams.hΔ]
      linarith [mul_le_mul_of_nonneg_left hls' h4]

end Consensus.Goldilocks.SA

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF b : Time}

end Consensus.Goldilocks.Healing

end

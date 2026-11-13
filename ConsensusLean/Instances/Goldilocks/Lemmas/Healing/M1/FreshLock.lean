module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.OptimisticBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.FloorUpdate
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Supplier
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Fresh fast locks under finite service

Actual votes and strict early resolution are separate from unanimous vote agreement.
The vote deadline uses explicit joinedness, rather than a stronger GST margin.
This is the no-restart-from `ts(u−1)` premise for all honest nodes; the
frame-window caller's schedule supplies it from no restart and `gbar ≤ ts(u−1)`.
The caller's sufficient bound is
`slot(gbar)+5 ≤ u`. A restart between `ts(u−1)` and `ts u−2Δ` explains why the
independent `+2Δ` margin is not a joinedness proof; this is premise analysis,
not a constructed counterexample satisfying every execution premise.

The upstream producer of `hun` is `FrameWindow.honest_vote_heads_eq`
(`AnchorPrefix`), with its slot `s+1 = u`, `gbar+4Δ ≤ ts s₀`, `s₀+2k ≤ u`
and frame window `[ts s₀, ts u+Δ]`. The frame-window caller must supply that wider warm
window; this leaf's shorter `[ts u, ts(u+1)+2Δ]` window does not imply it.
The producer's `k > 0` follows from `SAParams.two_le_k`, and its service
endpoint follows from this leaf's closed endpoint. No new unanimity induction
is needed for slot `u`; the induction below only transfers its votes to `u+1`.

All service uses in these proofs are through `T = ts(u+1)+2Δ = ts u+6Δ`.
`ResetService` itself retains its existing unbounded AC service fields; this
file does not claim to replace that interface with a strictly bounded one.
The FG delay `ΔF` is generic, distinct from protocol `Δ` (engine delay plus one);
no small-`ΔF` substitution or bound is used. If `u < m_e`, monotonicity of `ts`
gives `T ≤ ts m_e+2Δ`, including equality when `u+1 = m_e`.
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

/-- Actual joined votes on an honest proposal give a unique, strictly early-resolved
honest batch. Acceptance relay uses the observing frame's finalized ancestor guard. -/
theorem unanimous_early_pool_of_proposal (hS : HealthyBaseUpTo tr H U proposer g b)
    {u : Nat} (hgu : gbar g ≤ sp.ts u)
    (hjoin : ∀ x ∈ H, JoinedAt tr x (sp.ts u + sp.Δ))
    {P : Blk sp.n FGP} (hPs : P.slot = u)
    (hun : ∀ x ∈ H, ∀ i e, VoteAt tr x i e → e.msg.slot = u → e.msg.head = P.root)
    {z : Fin sp.n} (hz : z ∈ H) {a : Nat} (hacc : tr.AcceptAt z a P)
    (hta : tr.time a = sp.ts u)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ell : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y j ell)
    (ht : sp.ts u + 2 * sp.Δ ≤ tr.time j) (hjb : tr.time j ≤ b)
    (hdeadline : ∀ k ≤ j, ∀ t, gbar g ≤ t → tr.deadline y k t ≤ max t (sp.ts u) + sp.Δ)
    (hrestart : ∀ k ≤ j, tr.RestartAt y k → tr.time k < sp.ts u)
    (hPt : P ∈ ell.frame.tree) :
    ∀ x ∈ H, ∃ v ∈ (tr.state y j).pool u, v.val = x ∧ v.head = P.root ∧
      resolutionTime (tr.state y j) ell.frame v < ETime.of (sp.ts u + 2 * sp.Δ) ∧
      ∀ v' ∈ (tr.state y j).pool u, v'.val = x → v' = v := by
  have hr := hS.run.localRun
  have hDelta := sp.toParams.hΔ
  obtain ⟨hPhi, hPhiU⟩ := frameIn_of_callAt hr hy hc
  have hga : gbar g ≤ tr.time a := hta ▸ hgu
  have hdl := hdeadline j le_rfl (tr.time a) hga
  rw [hta, max_self] at hdl
  obtain ⟨q, hqj, haq, hqt⟩ := hS.sync.relay z hz a P hacc hga y hy j ell hc
    (by rw [hta]; linarith only [ht, hjb, hDelta, hdl]) (by
        rw [hta]; linarith only [ht, hDelta, hdl]) ((hPhi.rooted.2 P hPt).mono hPhiU)
  rw [hta] at hqt
  have hqT : tr.time q < sp.ts u + 2 * sp.Δ := by
    have hdq := hdeadline q hqj (tr.time a) hga
    rw [hta, max_self] at hdq
    linarith only [hDelta, hqt, hdq]
  have hbs := blockStamp_lt_of_acceptedBefore sp hr hy hc hPt (Or.inr ⟨q, haq, hqT⟩)
    (fun k hk hrs => (hrestart k hk hrs).trans_le (by linarith only [hDelta])) (Or.inl ht)
  intro x hx
  obtain ⟨i, e, hv, hes, _⟩ := honest_votes_of_joined_before hS hgu (by
      linarith only [ht, hjb, hDelta]) hjoin x hx
  have heP := hun x hx i e hv hes
  obtain ⟨hmem, hvs⟩ := honest_vote_early_pool_before hS hy hc hgu ht hjb hdeadline hrestart
    hx hv hes j (Or.inl rfl)
  obtain ⟨hval, -⟩ := castAt_spec hr hx ⟨hv.choose_spec.1, hv.choose_spec.2⟩
  refine ⟨e.msg, hmem, hval, heP,
    resolutionTime_lt_of hPhi hPt heP.symm (by clear * - hPs hes; omega) hvs (heP ▸ hbs), ?_⟩
  intro v' hv' hv'x
  obtain ⟨q', -, e', he', rfl⟩ := hS.run.honest.pool_vote y hy j u v' hv' (hv'x ▸ hx)
  rw [hv'x] at he'
  obtain ⟨-, rfl⟩ := (one_vote_per_slot sp) FGP ro H U tr hr x hx q' i e' e he' hv
    ((state_pool_slot sp hr hy j u _ hv').trans hes.symm)
  rfl

/-- Finite relay of the actual proposal and message delivery carry the unanimous
batch to the next-slot read point. This needs no stronger GST margin. -/
theorem unanimous_proposal_carry_before (hS : HealthyBaseUpTo tr H U proposer g b)
    {u : Nat} (hgu : gbar g ≤ sp.ts u) {P : Blk sp.n FGP}
    (hun : ∀ x ∈ H, ∀ i e, VoteAt tr x i e → e.msg.slot = u → e.msg.head = P.root)
    {z : Fin sp.n} (hz : z ∈ H) {a : Nat} (hacc : tr.AcceptAt z a P)
    (hta : tr.time a = sp.ts u) {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ell : ACLabel (goldilocksSA sp FGP ro)} {e' : Em sp FGP}
    (hc : CastAt tr y j ell e') (hs : e'.msg.slot = u + 1)
    (ht : sp.ts u + 2 * sp.Δ ≤ tr.time j) (hjb : tr.time j ≤ b)
    (hdeadline : ∀ k ≤ j, ∀ t, gbar g ≤ t → tr.deadline y k t ≤ max t (sp.ts u) + sp.Δ)
    (hrestart : ∀ k ≤ j, tr.RestartAt y k → tr.time k < sp.ts u)
    (hPt : P ∈ ell.frame.tree) :
    CarryAt tr U y j e' u
      {v | ∃ x ∈ H, ∃ i e, VoteAt tr x i e ∧ e.msg = v ∧ v.slot = u} := by
  have hr := hS.run.localRun
  have hDelta := sp.toParams.hΔ
  obtain ⟨hPhi, hPhiU⟩ := frameIn_of_callAt hr hy hc.1
  have hga : gbar g ≤ tr.time a := hta ▸ hgu
  have hdl := hdeadline j le_rfl (tr.time a) hga
  rw [hta, max_self] at hdl
  obtain ⟨q, hqj, haq, hqt⟩ := hS.sync.relay z hz a P hacc hga y hy j ell hc.1
    (by rw [hta]; linarith only [ht, hjb, hDelta, hdl]) (by
        rw [hta]; linarith only [ht, hDelta, hdl]) ((hPhi.rooted.2 P hPt).mono hPhiU)
  have hqT : tr.time q < sp.ts u + 2 * sp.Δ := by
    have hdq := hdeadline q hqj (tr.time a) hga
    rw [hta, max_self] at hdq
    rw [hta] at hqt
    linarith only [hDelta, hqt, hdq]
  refine ⟨hr.awake_of_call y hy j ell hc.1, (castAt_spec hr hy hc).2.2.1, ?_, ?_⟩
  · rintro v ⟨x, hx, i, e, hv, rfl, hes⟩
    refine ⟨P, hPhiU hPt, (hun x hx i e hv hes).symm, fun X hX => ?_⟩
    rcases acceptedBefore_ancestor hr hy hc.1 (hPhiU hPt) (Or.inr ⟨q, haq, hqT⟩) hX with
      hg | ⟨r, hrX, hrT⟩
    · exact Or.inl hg
    · exact Or.inr ⟨r, hrX, by linarith only [hDelta, hrT]⟩
  · rintro v ⟨x, hx, i, e, hv, rfl, hes⟩
    have hheld : HeldBefore e'.readPoint e.msg (sp.ts u + 2 * sp.Δ) := by
      apply heldBefore_readPoint hr hy hc (by clear * - hs hes; omega)
      simpa only [hes] using honest_vote_early_pool_before hS hy hc.1 hgu ht hjb
        hdeadline hrestart hx hv hes (j + 1) (Or.inr rfl)
    exact Or.inl ⟨hheld.1, lt_trans hheld.2
      (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (by linarith only [hDelta])))⟩

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

/-- The `FrameWindow` carries the actual honest proposal from a joined slot vote to every later
call through the closed update endpoint. -/
theorem FrameWindow.proposal_viable_after_votes
    {u floor : Nat} {kindJ : Prop} {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H)
      (sp.ts u) (sp.ts (u + 1 : Nat) + 2 * sp.Δ) floor kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g)) (hgu : gbar g ≤ sp.ts u) (hu0 : 0 < u)
    (hjoin : ∀ y ∈ H, SA.JoinedAt tr.projAC y (sp.ts u + sp.Δ))
    (hTb : sp.ts (u + 1 : Nat) + 2 * sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H) (hdesignated : z = proposer u)
    {kP : Nat} (hactual : tr.ProposesAt z kP P) (hPs : P.slot = u)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y k ell)
    (hlo : sp.ts u + 2 * sp.Δ ≤ tr.time k)
    (hhi : tr.time k ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ) :
    P ∈ ell.frame.viableTree ell.frame.tree ∧ ell.frame.viableAncestor P = P ∧
      P ∈ ell.frame.viableHeads := by
  have hS := healthy_base_of_service_catch_before hrun hnc hsvc hawake hf hcatch
  have hr := hS.run.localRun
  have hDelta := sp.toParams.hΔ
  have hts : sp.ts (u + 1 : Nat) = sp.ts u + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hshortT : sp.ts u + sp.Δ ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ := by
    rw [hts]; linarith only [hlo, hhi, hts]
  have hub := hshortT.trans hTb
  have hshort : FrameWindow (tr := tr) (H := H) (sp.ts u) (sp.ts u + sp.Δ)
      floor kindJ J :=
    ⟨fun x hx i hlo hhi => hframe.floor_eq x hx i hlo (hhi.trans hshortT),
      fun x hx i hlo hhi => hframe.kind_iff x hx i hlo (hhi.trans hshortT),
      fun x hx i hlo hhi => hframe.root_eq x hx i hlo (hhi.trans hshortT)⟩
  obtain ⟨q, e, ⟨ellq, hcq⟩, hes, hqt⟩ := SA.honest_votes_of_joined_before hS hgu hub hjoin y hy
  have hPv := (hshort.proposal_viable_at_cast hrun hnc hsvc hawake hf hcatch hnr hgu
    le_rfl hu0 hub hz hdesignated hactual hPs hy hcq hes).1
  have hqlo : sp.ts u ≤ tr.time q :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg q) _).2 (by
      rw [← (SA.castAt_spec hr hy hcq).2.1, hes])
  have hqk : q ≤ k := by
    by_contra h
    have htime := hrun.time_mono (show k ≤ q by clear * - h; omega)
    change tr.time q ≤ _ at hqt
    linarith only [hlo, hDelta, htime, hqt]
  have hmf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    have hn := sp.toParams.hn
    change 0 < sp.n at hn
    change Hᶜ.ncard < 2 * ((2 * sp.n + 2) / 3) - sp.n
    clear * - hf hn; omega
  obtain ⟨hPt, hroot, hPv⟩ := hframe.viableHead_persists hrun hnc hmf hy hqk hqlo hhi hcq.1 hPv
  rw [← Compose.frame_of_projAC hrun hy hc] at hPt hroot hPv
  have hvi : P ∈ ell.frame.viableTree ell.frame.tree := ⟨hPt, hroot, P, hPt, hPv, .refl⟩
  exact ⟨hvi, SA.viableAncestor_self (SA.frameIn_of_callAt hr hy hc).1 hPt (Or.inl hvi), hPv⟩

/-- The actual update is included in the finite viability window, at equality. -/
theorem FrameWindow.proposal_viable_at_update
    {u floor : Nat} {kindJ : Prop} {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H)
      (sp.ts u) (sp.ts (u + 1 : Nat) + 2 * sp.Δ) floor kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g)) (hgu : gbar g ≤ sp.ts u) (hu0 : 0 < u)
    (hjoin : ∀ y ∈ H, SA.JoinedAt tr.projAC y (sp.ts u + sp.Δ))
    (hTb : sp.ts (u + 1 : Nat) + 2 * sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H) (hdesignated : z = proposer u)
    {kP : Nat} (hactual : tr.ProposesAt z kP P) (hPs : P.slot = u)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hu : SA.UpdateAt tr.projAC y k u ell) :
    P ∈ ell.frame.viableTree ell.frame.tree ∧ ell.frame.viableAncestor P = P := by
  obtain ⟨hvi, hva, _⟩ := hframe.proposal_viable_after_votes hrun hnc hsvc hawake hf hcatch hnr
    hgu hu0 hjoin hTb hz hdesignated hactual hPs hy hu.1
    (by rw [show tr.time k = sp.ts u + 6 * sp.Δ from hu.2.2.1]; linarith only [sp.toParams.hΔ])
    (by rw [show tr.time k = sp.ts u + 6 * sp.Δ from hu.2.2.1]
        simp only [SAParams.ts]; push_cast; linarith only [])
  exact ⟨hvi, hva⟩

/-- Finite unanimity and an actual honest proposal force confirmation and fast
selection at each actual update. Lock compatibility is deliberately not an input
or a conclusion here: it is a separate obligation for fresh-lock creation. -/
theorem FrameWindow.unanimous_update_selection
    {u floor : Nat} {kindJ : Prop} {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H)
      (sp.ts u) (sp.ts (u + 1 : Nat) + 2 * sp.Δ) floor kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g)) (hmargin : gbar g + 2 * sp.Δ ≤ sp.ts u)
    (hjoin : ∀ y ∈ H, SA.JoinedAt tr.projAC y (sp.ts u + sp.Δ))
    (hTb : sp.ts (u + 1 : Nat) + 2 * sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H) (hdesignated : z = proposer u)
    {kP : Nat} (hactual : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hun : Unanimous tr H u P)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hu : SA.UpdateAt tr.projAC y k u ell) :
    P ∈ ell.frame.viableTree ell.frame.tree ∧
      SA.getConfirmation sp (tr.projAC.state y k) ell.frame u = some P ∧
      SA.fastSelect sp (tr.projAC.state y k) ell.frame u P = some P ∧
      ell.frame.viableAncestor P = P := by
  have hDelta := sp.toParams.hΔ
  have hgu : gbar g ≤ sp.ts u := by linarith only [hmargin, hDelta]
  have hu0 : 0 < u := by
    by_contra h
    have hu : u = 0 := by clear * - h; omega
    rw [hu] at hmargin
    simp only [Nat.cast_zero, SAParams.ts, mul_zero] at hmargin
    linarith only [SA.gbar_nonneg g, hDelta, hmargin]
  obtain ⟨hvi, hva⟩ := hframe.proposal_viable_at_update hrun hnc hsvc hawake hf hcatch hnr
    hgu hu0 hjoin hTb hz hdesignated hactual hPs hy hu
  have hS := healthy_base_of_service_catch_before hrun hnc hsvc hawake hf hcatch
  have hr := hS.run.localRun
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, a, _, hacc, hta⟩ :=
    honestProposalRun_of_proposesAt hrun hnc hz hdesignated hactual hPs
  rw [← hdesignated] at hacc
  have hPg := SA.accept_ne_genesis sp hr hz hacc
  have hdeadline : ∀ r ≤ k, ∀ t, gbar g ≤ t →
      tr.projAC.deadline y r t ≤ max t (sp.ts u) + sp.Δ := by
    intro r _ t _
    exact Compose.ac_deadline_le_of_restarts
      (fun q _ hrs => (hnr y hy q (Compose.projAC_restartAt.mp hrs)).trans hgu) t
  have hrestart : ∀ r ≤ k, tr.projAC.RestartAt y r → tr.projAC.time r < sp.ts u := by
    intro r _ hrs
    have := hnr y hy r (Compose.projAC_restartAt.mp hrs)
    change tr.time r < _
    linarith only [hmargin, hDelta, this]
  have hkt : tr.time k = sp.ts u + 6 * sp.Δ := hu.2.2.1
  have hts : sp.ts (u + 1 : Nat) = sp.ts u + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hkb : tr.projAC.time k ≤ b := by
    have hb := hTb
    rw [hts] at hb
    change tr.time k ≤ b
    rw [hkt]
    linarith only [hTb, hts]
  have hpool := SA.unanimous_early_pool_of_proposal hS hgu hjoin hPs hun hz hacc hta hy hu.1
    (by change sp.ts u + 2 * sp.Δ ≤ tr.time k; rw [hkt]; linarith only [hDelta])
    hkb hdeadline hrestart hvi.1
  obtain ⟨hconf, hfast⟩ := SA.confirmation_of_unanimous_early_pool
    (SA.frameIn_of_callAt hr hy hu.1).1 hvi.1 hPg (SA.CommitteeDict.full sp.n)
    (SA.size_binding_full hrun.stock u) (fun _ _ => SA.mem_full _ _)
    (SA.third_full hrun.stock (by have hn := sp.toParams.hn; change 1 ≤ sp.n at hn; omega))
    (SA.state_pool_slot sp hr hy k u) (fun x hx _ => hpool x hx)
  exact ⟨hvi, hconf, hfast, hva⟩

/-- Unanimity transfers one slot forward using only the finite proposal window.
The induction is on strictly earlier next-slot casts, not on a whole-run invariant. -/
theorem FrameWindow.unanimous_next_votes
    {u floor : Nat} {kindJ : Prop} {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H)
      (sp.ts u) (sp.ts (u + 1 : Nat) + 2 * sp.Δ) floor kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g)) (hmargin : gbar g + 2 * sp.Δ ≤ sp.ts u)
    (hjoin : ∀ y ∈ H, SA.JoinedAt tr.projAC y (sp.ts u + sp.Δ))
    (hTb : sp.ts (u + 1 : Nat) + 2 * sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H) (hdesignated : z = proposer u)
    {kP : Nat} (hactual : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hun : Unanimous tr H u P) :
    ∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e → e.msg.slot = u + 1 →
      SA.VoteExtends (tr.HonestBlocks H) e.msg P := by
  have hS := healthy_base_of_service_catch_before hrun hnc hsvc hawake hf hcatch
  have hr := hS.run.localRun
  have hDelta := sp.toParams.hΔ
  have hgu : gbar g ≤ sp.ts u := by linarith only [hmargin, hDelta]
  have hu0 : 0 < u := by
    by_contra h
    have hu : u = 0 := by clear * - h; omega
    rw [hu] at hmargin
    simp only [Nat.cast_zero, SAParams.ts, mul_zero] at hmargin
    linarith only [SA.gbar_nonneg g, hDelta, hmargin]
  have hts : sp.ts (u + 1 : Nat) = sp.ts u + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hTb' := hTb
  rw [hts] at hTb'
  have hex := SA.honest_votes_of_joined_before hS hgu (by linarith only [hTb, hDelta, hts]) hjoin
  have hhalf : sp.n ≤ 2 * {x | x ∈ H ∧ ∃ i e,
      SA.VoteAt tr.projAC x i e ∧ e.msg.slot = u}.ncard := by
    have hle := Set.ncard_le_ncard (s := H)
      (t := {x | x ∈ H ∧ ∃ i e, SA.VoteAt tr.projAC x i e ∧ e.msg.slot = u}) (by
        intro x hx
        obtain ⟨i, e, hv, hs, _⟩ := hex x hx
        exact ⟨hx, i, e, hv, hs⟩)
    have hn : H.ncard + Hᶜ.ncard = sp.n := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    have := sp.toParams.hn
    omega
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, a, _, hacc, hta⟩ :=
    honestProposalRun_of_proposesAt hrun hnc hz hdesignated hactual hPs
  rw [← hdesignated] at hacc
  suffices hall : ∀ i, ∀ y ∈ H, ∀ e, SA.VoteAt tr.projAC y i e → e.msg.slot = u + 1 →
      SA.VoteExtends (tr.HonestBlocks H) e.msg P by
    exact fun y hy i e hv hs => hall i y hy e hv hs
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro y hy e hv hs
    obtain ⟨ell, hc⟩ := hv
    have hslot : sp.slot (tr.time i) = u + 1 := (SA.castAt_spec hr hy hc).2.1.symm.trans hs
    have hlo : sp.ts (u + 1 : Nat) ≤ tr.time i :=
      (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by
        change ((u + 1 : Nat) : Int) ≤ sp.slot (tr.time i)
        rw [hslot])
    have hhi : tr.time i ≤ sp.ts (u + 1 : Nat) + sp.Δ := by
      have ht := SA.vote_time_le hr hy ⟨ell, hc⟩
      change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at ht
      rwa [hslot] at ht
    have hdl : ∀ q ≤ i, ∀ t, gbar g ≤ t →
        tr.projAC.deadline y q t ≤ max t (sp.ts u) + sp.Δ := by
      intro q _ t _
      exact Compose.ac_deadline_le_of_restarts
        (fun r _ hrs => (hnr y hy r (Compose.projAC_restartAt.mp hrs)).trans hgu) t
    have hrs : ∀ q ≤ i, tr.projAC.RestartAt y q → tr.projAC.time q < sp.ts u := by
      intro q _ hq
      have := hnr y hy q (Compose.projAC_restartAt.mp hq)
      change tr.time q < _
      linarith only [hmargin, hDelta, this]
    have hlate : sp.ts u + 2 * sp.Δ ≤ tr.time i := by rw [hts] at hlo; linarith only [hts, hlo, hhi]
    have hfinite : tr.time i ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ := by linarith only [hlo, hhi]
    obtain ⟨hvi, _, hPv⟩ := hframe.proposal_viable_after_votes hrun hnc hsvc hawake hf hcatch
      hnr hgu hu0 hjoin hTb hz hdesignated hactual hPs hy hc.1 hlate hfinite
    have hPhi := SA.frameIn_of_callAt hr hy hc.1
    have hcarry := SA.unanimous_proposal_carry_before hS hgu hun hz hacc hta hy hc hs
      hlate (hfinite.trans hTb) hdl hrs hvi.1
    obtain ⟨q, ev, hv, hes, _⟩ := hex y hy
    obtain ⟨B, hB, hBr, haccB⟩ := hcarry.heads ev.msg ⟨y, hy, q, ev, hv, rfl, hes⟩
    have hBP : B = P := hr.coherent.1 hB (hPhi.2 hvi.1) (hBr.trans (hun y hy q ev hv hes))
    rw [hBP] at haccB
    have hfreeze : SA.freeze sp e.msg.slot = sp.ts u + 3 * sp.Δ := by
      rw [hs]; simp only [SA.freeze]; congr 1; congr 1; (clear * -; omega)
    have hdom := SA.voterBlockTree_of_acceptedBefore hr hy hc hvi.1
      (by rw [hfreeze]; exact haccB P .refl)
      (fun r hri hrst => by rw [hfreeze]; have := hrs r hri hrst; linarith only [hlo, hhi, this])
      (by change SA.freeze sp e.msg.slot ≤ tr.time i
          rw [hfreeze]; rw [hts] at hlo; linarith only [hts, hlo, hhi])
    rw [hs] at hdom
    have hfb := faultBound_of_service hawake hf hnr (hr.time_nonneg i)
      (by change gbar g ≤ sp.ts ((sp.slot (tr.time i) : Int) - 1)
          rw [hslot, show ((u + 1 : Nat) : Int) - 1 = u by clear * -; omega]
          exact hgu) (hfinite.trans hTb)
    apply SA.next_transfer_of_carry sp hS.run (SA.CommitteeDict.full sp.n) SA.CommitteeP.full
      SA.CommitteeT.full (SA.size_binding_full hS.stock) hy hc hs
      (fun x hx q ev hv hes => ⟨P, hPhi.2 hvi.1, (hun x hx q ev hv hes).symm, .refl⟩)
      (by rw [hS.stock]; exact hhalf) hcarry ((SA.faultBoundK_full_iff _ _).2 hfb)
      (SA.cs2_full_of_faultBound sp hS.stock hfb)
      (Or.inl ⟨hdom, hvi.2.1, P, hdom, hPv, .refl⟩)
      (fun x hx q hqi ev hv hes => ih q hqi x hx ev hv hes)

/-- The receiver's actual next-slot cast clears incompatible older labels before
the update. In particular, the previous slot's intervening update is not skipped. -/
theorem FrameWindow.older_locks_compatible_at_update
    {u floor : Nat} {kindJ : Prop} {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H)
      (sp.ts u) (sp.ts (u + 1 : Nat) + 2 * sp.Δ) floor kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g)) (hmargin : gbar g + 2 * sp.Δ ≤ sp.ts u)
    (hjoin : ∀ y ∈ H, SA.JoinedAt tr.projAC y (sp.ts u + sp.Δ))
    (hTb : sp.ts (u + 1 : Nat) + 2 * sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H) (hdesignated : z = proposer u)
    {kP : Nat} (hactual : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hun : Unanimous tr H u P)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hu : SA.UpdateAt tr.projAC y k u ell) :
    ∀ l ∈ (tr.projAC.state y k).locks, l.slot < u →
      ∀ L ∈ tr.HonestBlocks H, L.root = l.block → Compatible (tr.HonestBlocks H) L P := by
  have hS := healthy_base_of_service_catch_before hrun hnc hsvc hawake hf hcatch
  have hr := hS.run.localRun
  have hDelta := sp.toParams.hΔ
  have hgu : gbar g ≤ sp.ts u := by linarith only [hmargin, hDelta]
  have hu0 : 0 < u := by
    by_contra h
    have hu : u = 0 := by clear * - h; omega
    rw [hu] at hmargin
    simp only [Nat.cast_zero, SAParams.ts, mul_zero] at hmargin
    linarith only [SA.gbar_nonneg g, hDelta, hmargin]
  have hts : sp.ts (u + 1 : Nat) = sp.ts u + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hTb' := hTb
  rw [hts] at hTb'
  have hslot : sp.slot (sp.ts (u + 1 : Nat) + sp.Δ) = u + 1 := by
    apply SA.slot_of_mem sp (u + 1) (by linarith only [hDelta])
    simp only [SAParams.ts]; push_cast; linarith only [hDelta]
  have hjn : ∀ x ∈ H, SA.JoinedAt tr.projAC x (sp.ts (u + 1 : Nat) + sp.Δ) := by
    intro x hx r hrs _
    change tr.time r ≤ sp.ts ((sp.slot (sp.ts (u + 1 : Nat) + sp.Δ) : Int) - 1)
    rw [hslot, show ((u + 1 : Nat) : Int) - 1 = u by clear * -; omega]
    exact (hnr x hx r (Compose.projAC_restartAt.mp hrs)).trans hgu
  obtain ⟨j, e, ⟨ellj, hc⟩, hs, hjt⟩ := SA.honest_votes_of_joined_before hS
    (by rw [hts]; linarith only [hmargin, hDelta]) (by
        rw [hts]; linarith only [hTb, hDelta, hts]) hjn y hy
  have hjslot : sp.slot (tr.time j) = u + 1 := (SA.castAt_spec hr hy hc).2.1.symm.trans hs
  have hjlo : sp.ts (u + 1 : Nat) ≤ tr.time j :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg j) _).2 (by
      change ((u + 1 : Nat) : Int) ≤ sp.slot (tr.time j); rw [hjslot])
  change tr.time j ≤ _ at hjt
  have hkt : tr.time k = sp.ts u + 6 * sp.Δ := hu.2.2.1
  have hjk : j < k := by
    by_contra h
    have := hrun.time_mono (show k ≤ j by clear * - h; omega)
    rw [hts] at hjt
    linarith only [hDelta, hjt, hkt, this]
  have hjlate : sp.ts u + 2 * sp.Δ ≤ tr.time j := by
    rw [hts] at hjlo; linarith only [hts, hjlo, hjt]
  have hjfinite : tr.time j ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ := by linarith only [hjlo, hjt]
  obtain ⟨hvi, _⟩ := hframe.proposal_viable_after_votes hrun hnc hsvc hawake hf hcatch hnr
    hgu hu0 hjoin hTb hz hdesignated hactual hPs hy hc.1 hjlate hjfinite
  have hPhi := SA.frameIn_of_callAt hr hy hc.1
  have hdl : ∀ q ≤ j, ∀ t, gbar g ≤ t →
      tr.projAC.deadline y q t ≤ max t (sp.ts u) + sp.Δ := by
    intro q _ t _
    exact Compose.ac_deadline_le_of_restarts
      (fun r _ hrs => (hnr y hy r (Compose.projAC_restartAt.mp hrs)).trans hgu) t
  have hrs : ∀ q ≤ j, tr.projAC.RestartAt y q → tr.projAC.time q < sp.ts u := by
    intro q _ hq
    have := hnr y hy q (Compose.projAC_restartAt.mp hq)
    change tr.time q < _
    linarith only [hmargin, hDelta, this]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, a, _, hacc, hta⟩ :=
    honestProposalRun_of_proposesAt hrun hnc hz hdesignated hactual hPs
  rw [← hdesignated] at hacc
  have hcarry := SA.unanimous_proposal_carry_before hS hgu hun hz hacc hta hy hc hs
    hjlate (hjfinite.trans hTb) hdl hrs hvi.1
  have hhalf : sp.n ≤ 2 * H.ncard := by
    have hn : H.ncard + Hᶜ.ncard = sp.n := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    have := sp.toParams.hn
    clear * - hf hn; omega
  apply SA.older_locks_compatible_after_unlock hr hy hc hs hjk hvi.1 (S := H) _
    (by simpa only [hrun.stock] using hhalf)
  intro x hx
  obtain ⟨q, ev, hv, hes, _⟩ := SA.honest_votes_of_joined_before hS hgu (by
      linarith only [hTb, hts, hjlo, hjt]) hjoin x hx
  have hval := (SA.castAt_spec hr hx ⟨hv.choose_spec.1, hv.choose_spec.2⟩).1
  have hheld : SA.HeldBefore e.readPoint ev.msg (sp.ts u + 2 * sp.Δ) := by
    apply SA.heldBefore_readPoint hr hy hc (by clear * - hs hes; omega)
    simpa only [hes] using SA.honest_vote_early_pool_before hS hy hc.1 hgu hjlate
      (hjfinite.trans hTb) hdl hrs hx hv hes (j + 1) (Or.inr rfl)
  obtain ⟨B, hB, hBr, haccB⟩ := hcarry.heads ev.msg ⟨x, hx, q, ev, hv, rfl, hes⟩
  have hBP : B = P := hr.coherent.1 hB (hPhi.2 hvi.1) (hBr.trans (hun x hx q ev hv hes))
  rw [hBP] at haccB
  have hsupp := SA.carried_supporter hS.run hy hc hs hvi.1 hes
    ⟨hheld.1, lt_trans hheld.2
      (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (by linarith only [hDelta])))⟩
    ⟨P, hPhi.2 hvi.1, (hun x hx q ev hv hes).symm, hPs.le, .refl, haccB P .refl⟩
    (SA.honest_not_equivocator hS.run hy hc (hval ▸ hx))
  rw [hval] at hsupp
  exact Or.inr hsupp.2

/-- Finite no-veto at the actual update. Old labels use the receiver's next-slot
unlock; new fast labels use honest support in slots `u` and `u+1`, and new slow
labels use the independently established raw slot-`u` result. -/
theorem FrameWindow.unanimous_update_no_veto
    {u floor : Nat} {kindJ : Prop} {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H)
      (sp.ts u) (sp.ts (u + 1 : Nat) + 2 * sp.Δ) floor kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g)) (hmargin : gbar g + 2 * sp.Δ ≤ sp.ts u)
    (hjoin : ∀ y ∈ H, SA.JoinedAt tr.projAC y (sp.ts u + sp.Δ))
    (hTb : sp.ts (u + 1 : Nat) + 2 * sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H) (hdesignated : z = proposer u)
    {kP : Nat} (hactual : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hun : Unanimous tr H u P)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hu : SA.UpdateAt tr.projAC y k u ell) :
    ¬ SA.conflictsWithLock sp (tr.projAC.state y k).locks ell.frame (tr.time k) P := by
  have hS := healthy_base_of_service_catch_before hrun hnc hsvc hawake hf hcatch
  have hr := hS.run.localRun
  have hU := hr.coherent
  have hDelta := sp.toParams.hΔ
  have hf2 : 2 * Hᶜ.ncard < sp.n := by have := sp.toParams.hn; (clear * - hf hdesignated; omega)
  have hkt : tr.time k = sp.ts u + 6 * sp.Δ := hu.2.2.1
  have hslot : sp.slot (tr.time k) = u + 1 := by
    apply SA.slot_of_mem sp (u + 1)
    all_goals rw [hkt]; simp only [SAParams.ts]; push_cast; linarith only [hDelta]
  have hPhi := SA.frameIn_of_callAt hr hy hu.1
  obtain ⟨hvi, _⟩ := hframe.unanimous_update_selection hrun hnc hsvc hawake hf hcatch hnr
    hmargin hjoin hTb hz hdesignated hactual hPs hun hy hu
  have hnext := hframe.unanimous_next_votes hrun hnc hsvc hawake hf hcatch hnr
    hmargin hjoin hTb hz hdesignated hactual hPs hun
  have hold := hframe.older_locks_compatible_at_update hrun hnc hsvc hawake hf hcatch hnr
    hmargin hjoin hTb hz hdesignated hactual hPs hun hy hu
  have down : ∀ {X Y}, Anc (tr.HonestBlocks H) X Y → Compatible (tr.HonestBlocks H) Y P →
      Compatible (tr.HonestBlocks H) X P := by
    rintro X Y hXY (h | h)
    · exact Or.inl (hXY.trans h)
    · exact SA.anc_total hU hXY h
  have hlocks : ∀ l ∈ (tr.projAC.state y k).locks,
      ∀ L ∈ tr.HonestBlocks H, L.root = l.block → Compatible (tr.HonestBlocks H) L P := by
    intro l hl L hL hLr
    by_cases hlt : l.slot < u
    · exact hold l hl hlt L hL hLr
    have hle : l.slot ≤ u + 1 := by
      obtain ⟨r, hrk, B, horig, _⟩ := SA.lock_provenance hr hy k l hl
      have hmono := SA.slot_mono sp (hr.time_nonneg r) (hr.time_mono hrk.le)
      change sp.slot (tr.time r) ≤ sp.slot (tr.time k) at hmono
      rw [hslot] at hmono
      rcases horig with ⟨CV, ellr, A, _, hsl, _⟩ | ⟨ellr, _, _, hrt, _⟩
      · change sp.slot (tr.time r) = l.slot at hsl
        omega
      · have hls : (l.slot : Int) ≤ sp.slot (tr.projAC.time r) :=
          (SA.ts_le_iff_le_slot sp (hr.time_nonneg r) _).1 (by rw [hrt]; linarith only [hDelta])
        change (l.slot : Int) ≤ sp.slot (tr.time r) at hls
        omega
    cases hfast : l.fast
    · obtain ⟨r, hrk, B, ⟨ellr, C, hup, hC, hB⟩, L₁, hL₁, hL₁r, hLB⟩ :=
        SA.slow_lock_provenance hr hy k l hl hfast
      have hmono := hr.time_mono hrk.le
      have hrt : tr.projAC.time r = sp.ts l.slot + 6 * sp.Δ := hup.2.2.1
      have hku : tr.projAC.time k = sp.ts u + 6 * sp.Δ := hu.2.2.1
      have hls : l.slot = u := by
        have := (SA.ts_le_iff sp).1 (show sp.ts l.slot ≤ sp.ts u by linarith only [hrt, hku, hmono])
        clear * - hlt this; omega
      rw [hls] at hup hC
      have hCP : C = P := Option.some.inj (hC.symm.trans
        (hframe.unanimous_update_selection hrun hnc hsvc hawake hf hcatch hnr hmargin
          hjoin hTb hz hdesignated hactual hPs hun hy hup).2.1)
      have hBP := (SA.deepest_mem hB).1.1.2.2
      rw [hCP] at hBP
      have hLL₁ : L = L₁ := hU.1 hL hL₁ (hLr.trans hL₁r.symm)
      rw [← hLL₁] at hLB
      exact Or.inl (hLB.trans (hBP.mono (SA.frameIn_of_callAt hr hy hup.1).2))
    · obtain ⟨r, _, B, CV, hfl, L₁, hL₁, hL₁r, hLB⟩ :=
        SA.fast_lock_provenance hr hy k l hl hfast
      have hLL₁ : L = L₁ := hU.1 hL hL₁ (hLr.trans hL₁r.symm)
      rw [← hLL₁] at hLB
      obtain ⟨x, hx, q, e, hv, hes, D, hD, hDr, hBD⟩ :=
        SA.fastLock_honest_vote hS.run hf2 hy hfl
      apply down hLB
      rcases (show l.slot = u ∨ l.slot = u + 1 by clear * - hlt hle; omega) with hs | hs
      · have hDP : D = P := hU.1 hD (hPhi.2 hvi.1) (hDr.trans (hun x hx q e hv (hes.trans hs)))
        rw [hDP] at hBD
        exact Or.inl hBD
      · obtain ⟨D', hD', hD'r, hPD⟩ := hnext x hx q e hv (hes.trans hs)
        have hDD' : D = D' := hU.1 hD hD' (hDr.trans hD'r.symm)
        rw [← hDD'] at hPD
        exact SA.anc_total hU hBD hPD
  rintro ⟨L, hLive, hconflict⟩
  obtain ⟨hLt, l', ⟨l, hl, B, hB, hBr, _, rfl⟩, hLr⟩ := hLive
  have hanc := SA.anc_viableAncestor ell.frame B
  have hLva : L = ell.frame.viableAncestor B :=
    hPhi.1.coherent.1 hLt (SA.mem_of_anc hanc hB) hLr.symm
  have hcomp := down (hLva ▸ hanc.mono hPhi.2) (hlocks l hl B (hPhi.2 hB) hBr)
  apply hconflict
  rcases hcomp with h | h
  · exact Or.inr (SA.anc_tree_of_anc_U hU hPhi.1 hPhi.2 hLt h hvi.1)
  · exact Or.inl (SA.anc_tree_of_anc_U hU hPhi.1 hPhi.2 hvi.1 h hLt)

/-- The fresh fast lock at every actual update: the raw result and fast selection are the actual
honest proposal, it is not vetoed, and the post-state contains its fresh fast lock.
The frame/service endpoint `ts(u+1)+2Δ` is closed, including the update itself. -/
theorem fresh_fast_lock_at_update
    {u floor : Nat} {kindJ : Prop} {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    {z : Fin sp.n} {kP : Nat}
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g))
    (hmargin : gbar g + 2 * sp.Δ ≤ sp.ts u)
    (hjoin : ∀ y ∈ H, SA.JoinedAt tr.projAC y (sp.ts u + sp.Δ))
    (hTb : sp.ts (u + 1 : Nat) + 2 * sp.Δ ≤ b)
    (hframe : FrameWindow (tr := tr) (H := H)
      (sp.ts u) (sp.ts (u + 1 : Nat) + 2 * sp.Δ) floor kindJ J)
    (hz : z ∈ H) (hdesignated : z = proposer u)
    (hactual : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hun : Unanimous tr H u P)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hu : SA.UpdateAt tr.projAC y k u ell) :
    P ∈ ell.frame.tree ∧
      SA.getConfirmation sp (tr.projAC.state y k) ell.frame u = some P ∧
      ¬ SA.conflictsWithLock sp (tr.projAC.state y k).locks ell.frame (tr.time k) P ∧
      SA.fastSelect sp (tr.projAC.state y k) ell.frame u P = some P ∧
      ell.frame.viableAncestor P = P ∧
      ∃ e, u + 2 ≤ e ∧ (⟨P.root, u, true, e⟩ : SA.Lock) ∈ (tr.projAC.post k).locks := by
  obtain ⟨hvi, hconf, hfast, hva⟩ := hframe.unanimous_update_selection hrun hnc hsvc hawake hf
    hcatch hnr hmargin hjoin hTb hz hdesignated hactual hPs hun hy hu
  have hnv := hframe.unanimous_update_no_veto hrun hnc hsvc hawake hf hcatch hnr
    hmargin hjoin hTb hz hdesignated hactual hPs hun hy hu
  have hr := (healthy_base_of_service_catch_before hrun hnc hsvc hawake hf hcatch).run.localRun
  have hDelta := sp.toParams.hΔ
  have hkt : tr.projAC.time k = sp.ts u + 6 * sp.Δ := hu.2.2.1
  have hts : sp.ts (u + 1 : Nat) = sp.ts u + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hslot : sp.slot (tr.projAC.time k) = u + 1 := by
    apply SA.slot_of_mem sp (u + 1)
    all_goals rw [hkt]; simp only [SAParams.ts]; push_cast; linarith only [hDelta]
  have hpost : tr.projAC.post k =
      SA.updateConfirmation sp (tr.projAC.state y k) ell.frame (tr.projAC.time k) u := by
    have he := hr.exec k ell hu.1.2 (hu.1.1 ▸ hy)
    rw [hu.1.1, hu.2.1] at he
    have hpost : tr.projAC.post k =
        (SA.acOnTick sp y (tr.projAC.state y k) ell.frame (tr.projAC.time k)).1 :=
      (congrArg Prod.fst he).symm
    rw [hpost]
    unfold SA.acOnTick
    dsimp only
    rw [hslot]
    have ht1 : ¬ tr.projAC.time k = sp.ts (u + 1 : Nat) + sp.Δ := by
      rw [hkt, hts]; linarith only [hDelta]
    have ht2 : tr.projAC.time k = sp.ts (u + 1 : Nat) + 2 * sp.Δ := by
      rw [hkt, hts]; ring
    rw [ite_eq_right (not_not.mpr hu.2.2.2), ite_eq_right ht1,
      ite_eq_left ⟨ht2, Nat.succ_pos u⟩]
    simp only [Nat.add_sub_cancel]
  refine ⟨hvi.1, hconf, hnv, hfast, hva, ?_⟩
  rw [hpost]
  exact SA.fastLock_mem_updateConfirmation_floor hvi.1 hva hconf hnv hfast
    (by rw [hslot]; have := sp.two_le_k; (clear * -; omega))

/-- The fresh fast lock of `fresh_fast_lock_at_update` is present at the immediately adjacent actual
to-FG pre-state, not merely at an unrelated call sharing the same timestamp. -/
theorem fresh_fast_lock_update_toFG
    {u floor : Nat} {kindJ : Prop} {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    {z : Fin sp.n} {kP : Nat}
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g))
    (hmargin : gbar g + 2 * sp.Δ ≤ sp.ts u)
    (hjoin : ∀ y ∈ H, SA.JoinedAt tr.projAC y (sp.ts u + sp.Δ))
    (hTb : sp.ts (u + 1 : Nat) + 2 * sp.Δ ≤ b)
    (hframe : FrameWindow (tr := tr) (H := H)
      (sp.ts u) (sp.ts (u + 1 : Nat) + 2 * sp.Δ) floor kindJ J)
    (hz : z ∈ H) (hdesignated : z = proposer u)
    (hactual : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hun : Unanimous tr H u P) {y : Fin sp.n} (hy : y ∈ H) :
    ∃ k ell ell', SA.UpdateAt tr.projAC y k u ell ∧
      tr.projAC.CallAt y (k + 1) ell' ∧ ell'.call = .toFG ∧
      tr.time (k + 1) = sp.ts (u + 1 : Nat) + 2 * sp.Δ ∧
      ell'.frame = ell.frame ∧
      SA.getConfirmation sp (tr.projAC.state y k) ell.frame u = some P ∧
      ¬ SA.conflictsWithLock sp (tr.projAC.state y k).locks ell.frame (tr.time k) P ∧
      SA.fastSelect sp (tr.projAC.state y k) ell.frame u P = some P ∧
      ell'.frame.viableAncestor P = P ∧
      ∃ e, u + 2 ≤ e ∧ (⟨P.root, u, true, e⟩ : SA.Lock) ∈ (tr.projAC.post k).locks ∧
        (⟨P.root, u, true, e⟩ : SA.Lock) ∈ (tr.projAC.state y (k + 1)).locks := by
  have hr := (healthy_base_of_service_catch_before hrun hnc hsvc hawake hf hcatch).run.localRun
  have hDelta := sp.toParams.hΔ
  have hT : sp.ts (u + 1 : Nat) + 2 * sp.Δ = sp.ts u + 6 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hslot : sp.slot (sp.ts u + 6 * sp.Δ) = u + 1 := by
    apply SA.slot_of_mem sp (u + 1)
    all_goals simp only [SAParams.ts]; push_cast; linarith only [hDelta]
  have hj : ∀ i, tr.time i = sp.ts u + 6 * sp.Δ →
      SA.joined sp (tr.projAC.state y i) (tr.time i) := by
    intro i hi
    unfold SA.joined
    rcases SA.restartTime_state hr hy i with h | ⟨r, _, hrs, h⟩
    · rw [h]; exact bot_le
    · rw [h]
      apply WithBot.coe_le_coe.mpr
      rw [hi, hslot, show ((u + 1 : Nat) : Int) - 1 = u by clear * -; omega]
      have := hnr y hy r (Compose.projAC_restartAt.mp hrs)
      change tr.time r ≤ _
      linarith only [hmargin, hDelta, this]
  obtain ⟨k, ell, ell', hu, hcall, hto, htime, hframe', _⟩ := update_toFG_calls_of_awake hrun hy
    (hawake y hy _ (by linarith only [hmargin, hDelta]) (by rwa [hT] at hTb)) hj
  obtain ⟨_, hconf, hnv, hfast, hva, e, he, hlock⟩ := fresh_fast_lock_at_update hrun hnc hsvc
    hawake hf hcatch hnr hmargin hjoin hTb hframe hz hdesignated hactual hPs hun hy hu
  refine ⟨k, ell, ell', hu, hcall, hto, htime.trans hT.symm, hframe', hconf, hnv,
    hfast, hframe'.symm ▸ hva, e, he, hlock, ?_⟩
  simpa [Trace.state, hu.1.1, hu.1.2] using hlock

end Consensus.Goldilocks.Healing

end

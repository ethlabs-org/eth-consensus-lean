module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLock
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Opponents
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: the confirmed tip after an honest proposal, the first update

The late honest votes held at a call, the results extended by their honest supporters
(`result_extendedU`) and the first update at `t_p + 6Δ` after an honest proposal `P` of slot `p`
(`first_update_post`: result `P`, not vetoed, with `P` passing the fast test, so its own fast
selection, `fastSelect_eq_result`). -/

namespace Consensus.Goldilocks.AC

variable {wm : AC.WriteMode}

variable {FGP : Type} {sp : ACParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : GTrace sp FGP ro} {g : Time} {proposer : Nat → Fin sp.n}

/-- Finite message service retains an actual honest vote with its strict early stamp.
Only deadlines and restarts through the receiving call are used. -/
theorem late_vote_pool_before {K : AC.CommitteeDict sp.n}
    {b : Time} (hS : HealthyBaseUpTo K tr H U proposer g b)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ell : ACLabel (goldilocksAC sp FGP ro)} (hc : tr.CallAt y j ell) {s : Nat}
    (hs : gbar g + 4 * sp.Δ ≤ sp.ts s) (ht : sp.ts s + 2 * sp.Δ ≤ tr.time j)
    (hjb : tr.time j ≤ b)
    (hdeadline : ∀ k ≤ j, ∀ t, gbar g ≤ t → tr.deadline y k t ≤ max t (sp.ts s) + sp.Δ)
    (hrestart : ∀ k ≤ j, tr.RestartAt y k → tr.time k < sp.ts s)
    {x : Fin sp.n} (hx : x ∈ H) {i : Nat} {e : Em sp FGP}
    (hv : VoteAt tr x i e) (hes : e.msg.slot = s) :
    ∀ c, (c = j ∨ c = j + 1) → e.msg ∈ (tr.state y c).pool s ∧
      (tr.state y c).voteStamp e.msg < ETime.of (sp.ts s + 2 * sp.Δ) := by
  have hr := hS.run.localRun
  have hDelta := sp.toParams.hΔ
  obtain ⟨ellx, hcx, hex⟩ := hv
  obtain ⟨hval, hslot, -, -⟩ := castAt_spec hr hx ⟨hcx, hex⟩
  have hti : tr.time i ≤ sp.ts s + sp.Δ := by
    have hh := vote_time_le hr hx ⟨ellx, hcx, hex⟩
    rwa [← hslot, hes] at hh
  have hti0 : sp.ts s ≤ tr.time i :=
    (ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by rw [← hslot, hes])
  have hgi : gbar g ≤ tr.time i := by linarith only [hs, hti, hti0]
  have hdl := hdeadline j le_rfl (tr.time i) hgi
  rw [max_eq_left hti0] at hdl
  obtain ⟨q, hqj, hiq, hproc, hqt⟩ := hS.sync.message x hx i e.msg
    ⟨ellx, hcx, Or.inl ⟨e, hex, rfl⟩⟩ hgi y hy j ell hc
    (by linarith only [ht, hjb, hti, hdl]) (by linarith only [ht, hti, hdl])
  have hqT : tr.time q < sp.ts s + 2 * sp.Δ := by
    have hqdl := hdeadline q hqj (tr.time i) hgi
    rw [max_eq_left hti0] at hqdl
    linarith only [hti, hqt, hqdl]
  have hqj' : q < j := lt_of_le_of_ne hqj (by rintro rfl; linarith only [hqT, ht])
  have hqs : sp.slot (tr.time q) = s :=
    slot_of_mem sp s (by linarith only [hti0, hiq]) (by
        rw [AC.ts_succ]; linarith only [hti, hti0, hqT])
  have hxH : e.msg.val ∈ H := hval ▸ hx
  have hheld : e.msg ∈ (tr.state y (q + 1)).pool s := by
    rcases held_of_processAt hr hy hproc (by rw [hqs, hes]; omega) (by rw [hqs, hes]) with
      h | ⟨v, hv, w, hw, hne, hvval, hwval⟩
    · rwa [hes] at h
    · exfalso
      rw [hes] at hv hw
      obtain ⟨iv, -, ev, hev, rfl⟩ := hS.run.honest.pool_vote y hy (q + 1) s _ hv (hvval ▸ hxH)
      obtain ⟨iw, -, ew, hew, rfl⟩ := hS.run.honest.pool_vote y hy (q + 1) s _ hw (hwval ▸ hxH)
      have hsv := state_pool_slot sp hr hS.run.vstart hy (q + 1) s _ hv
      have hsw := state_pool_slot sp hr hS.run.vstart hy (q + 1) s _ hw
      rw [hvval] at hev
      rw [hwval] at hew
      obtain ⟨-, rfl⟩ := one_vote_per_slotU sp FGP ro H U tr hr.toU _ hxH iv iw ev ew hev hew
        (hsv.trans hsw.symm)
      exact hne rfl
  intro c hcj
  have hst := stamp_lt_of_held_of_run hr hS.run.vstart hy (a := q + 1) (b := c) (by omega)
    (w := e.msg) (by rw [hes]; exact hheld) (T := sp.ts s + 2 * sp.Δ)
    (fun k hk => lt_of_le_of_lt (hr.time_mono (Nat.lt_succ_iff.1 hk)) hqT)
    (by rw [hes]; linarith only [hti0, hqT, hiq])
    (fun k hk hrs => lt_trans (hrestart k (by omega) hrs) (by linarith only [hti0, hqT, hiq]))
    (fun k hqk hkc hrs => by
      have := hrestart k (by omega) hrs
      have := hr.time_mono (show q ≤ k by omega)
      linarith)
  rwa [hes] at hst

/-- Finite message service carries an earlier-slot honest vote to the read point of a
next-slot vote, not just to the receiving call's pre-state. -/
theorem late_vote_readPoint_before {K : AC.CommitteeDict sp.n}
    {b : Time} (hS : HealthyBaseUpTo K tr H U proposer g b)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ell : ACLabel (goldilocksAC sp FGP ro)} {e' : Em sp FGP}
    (hc : CastAt tr y j ell e') {s : Nat} (hs' : e'.msg.slot = s + 1)
    (hs : gbar g + 4 * sp.Δ ≤ sp.ts s) (ht : sp.ts s + 2 * sp.Δ ≤ tr.time j)
    (hjb : tr.time j ≤ b)
    (hdeadline : ∀ k ≤ j, ∀ t, gbar g ≤ t → tr.deadline y k t ≤ max t (sp.ts s) + sp.Δ)
    (hrestart : ∀ k ≤ j, tr.RestartAt y k → tr.time k < sp.ts s)
    {x : Fin sp.n} (hx : x ∈ H) {i : Nat} {e : Em sp FGP}
    (hv : VoteAt tr x i e) (hes : e.msg.slot = s) :
    HeldBefore e'.readPoint e.msg (sp.ts s + 2 * sp.Δ) := by
  apply heldBefore_readPoint hS.run.localRun hy hc (by omega)
  simpa only [hes] using late_vote_pool_before hS hy hc.1 hs ht hjb hdeadline hrestart
    hx hv hes (j + 1) (Or.inr rfl)

/-- Acceptance before a deadline carries every global ancestor before that deadline too. -/
theorem acceptedBefore_ancestor {ini} (hr : ACLocalRun (goldilocksAC sp FGP ro) H U tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksAC sp FGP ro)} (hc : tr.CallAt y i ell)
    {B X : Blk sp.n FGP} (hB : B ∈ U)
    {T : Time} (hacc : AcceptedBefore tr y B T) (hX : Anc U X B) :
    AcceptedBefore tr y X T := by
  rcases hacc with hg | ⟨k, ⟨ell, hc, hcall⟩, ht⟩
  · obtain ⟨G, hGU, hGr, hGp⟩ := genesis_mem_of_call sp hr hy i ell hc
    obtain rfl : B = G := hr.coherent.1 hB hGU (hg.trans hGr.symm)
    rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hX with rfl | ⟨Q, -, hQ⟩
    · exact Or.inl hGr
    · exact absurd (hQ.2.2.symm.trans hGp) (Option.some_ne_none _)
  · rcases Compose.frame_anc_accepted hr hy k ell hc B
      ((accept_new sp hr hy ⟨ell, hc, hcall⟩).1 ell hc) X hX with hg | ⟨j, hj, hjX⟩
    · exact Or.inl hg
    · exact Or.inr ⟨j, hjX, lt_of_le_of_lt (hr.time_mono hj) ht⟩

/-- Guarded finite acceptance service resolves the head of an actual honest vote before
the same strict deadline as its message, retaining the acceptance witness. -/
theorem late_vote_accepted_of_frame_before {K : AC.CommitteeDict sp.n}
    {b : Time} (hS : HealthyBaseUpTo K tr H U proposer g b)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ell : ACLabel (goldilocksAC sp FGP ro)} (hc : tr.CallAt y j ell) {s : Nat}
    (hs : gbar g + 4 * sp.Δ ≤ sp.ts s) (ht : sp.ts s + 2 * sp.Δ ≤ tr.time j)
    (hjb : tr.time j ≤ b)
    (hdeadline : ∀ k ≤ j, ∀ t, gbar g ≤ t → tr.deadline y k t ≤ max t (sp.ts s) + sp.Δ)
    (hrestart : ∀ k ≤ j, tr.RestartAt y k → tr.time k < sp.ts s)
    {x : Fin sp.n} (hx : x ∈ H) {i : Nat} {e : Em sp FGP}
    (hv : VoteAt tr x i e) (hes : e.msg.slot = s)
    (hF : ∀ B ∈ U, B.root = e.msg.head → Anc U ell.frame.F B) :
    ∃ B ∈ ell.frame.tree, B.root = e.msg.head ∧ B.slot ≤ s ∧
      e.msg ∈ (tr.state y j).pool s ∧
      (tr.state y j).voteStamp e.msg < ETime.of (sp.ts s + 2 * sp.Δ) ∧
      (tr.state y j).blockStamp e.msg.head < ETime.of (sp.ts s + 2 * sp.Δ) ∧
      AcceptedBefore tr y B (sp.ts s + 2 * sp.Δ) := by
  have hpool := late_vote_pool_before hS hy hc hs ht hjb hdeadline hrestart hx hv hes j (Or.inl rfl)
  have hr := hS.run.localRun
  have hDelta := sp.toParams.hΔ
  obtain ⟨hPhi, hPhiU⟩ := frameIn_of_callAt hr hy hc
  obtain ⟨ellx, hcx, hex⟩ := hv
  obtain ⟨-, hslx, -, hhead⟩ := castAt_spec hr hx ⟨hcx, hex⟩
  have hti : tr.time i ≤ sp.ts s + sp.Δ := by
    have hh := vote_time_le hr hx ⟨ellx, hcx, hex⟩
    rwa [← hslx, hes] at hh
  obtain ⟨hPhix, hPhixU⟩ := frameIn_of_callAt hr hx hcx
  obtain ⟨B, hB, hBr⟩ : ∃ B ∈ ellx.frame.tree, B.root = e.msg.head :=
    ⟨_, getHead_mem hPhix (fun _ h => (voteDomain_subset_tree h.1)) e.readPoint (tr.time i)
      (mergedVoteView sp e.readPoint ellx.frame e.msg.slot) ((e.msg.slot : Int) - 1)
      (T := ellx.frame.viableTree (voteDomain sp e.readPoint ellx.frame e.msg.slot)),
      hhead.symm⟩
  have hBs : B.slot ≤ s := by
    have hh := frame_slot_le sp hr hx hcx B hB
    rwa [← hslx, hes] at hh
  have hFB := hF B (hPhixU hB) hBr
  obtain ⟨hBy, hAB⟩ : B ∈ ell.frame.tree ∧ AcceptedBefore tr y B (sp.ts s + 2 * sp.Δ) := by
    rcases Compose.frame_anc_accepted hr hx i ellx hcx B hB B .refl with
      hg | ⟨q, hqi, hacc⟩
    · refine ⟨?_, Or.inl hg⟩
      obtain ⟨G, hGU, hGr, hGp⟩ := genesis_mem_of_call sp hr hy j ell hc
      obtain rfl : B = G := hr.coherent.1 (hPhixU hB) hGU (hg.trans hGr.symm)
      rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hFB with he | ⟨C, -, hpar⟩
      · exact he ▸ hPhi.rooted.1
      · exact absurd (hpar.2.2.symm.trans hGp) (Option.some_ne_none _)
    have hqtime := (hr.time_mono hqi).trans hti
    have hmax : max (tr.time q) (sp.ts s) ≤ sp.ts s + sp.Δ := max_le hqtime (by
        linarith only [hDelta])
    obtain ⟨r, hrj, har, hrt⟩ : ∃ r ≤ j, tr.AcceptAt y r B ∧ tr.time r < sp.ts s + 2 * sp.Δ := by
      by_cases hgq : gbar g ≤ tr.time q
      · have hdl := hdeadline j le_rfl (tr.time q) hgq
        obtain ⟨r, hrj, har, hrt⟩ := hS.sync.relay x hx q B hacc hgq y hy j ell hc
          (by linarith only [ht, hjb, hmax, hdl]) (by linarith only [ht, hmax, hdl]) hFB
        exact ⟨r, hrj, har, by
            have := hdeadline r hrj (tr.time q) hgq; linarith only [hmax, hrt, this]⟩
      · obtain ⟨r, hrj, har, hrt⟩ := hS.catchUp.relay x hx q B hacc (lt_of_not_ge hgq)
          y hy j ell hc (by linarith only [hs, ht, hDelta]) hjb hFB
        exact ⟨r, hrj, har, by linarith only [hs, hDelta, hrt]⟩
    exact ⟨mem_tree_of_acceptAt sp hr hy har hrj hc hFB, Or.inr ⟨r, har, hrt⟩⟩
  have hstamp := blockStamp_lt_of_acceptedBefore sp hr hS.run.vstart hy hc hBy hAB
    (fun k hk hrs => lt_trans (hrestart k (by omega) hrs) (by linarith only [hDelta])) (Or.inl ht)
  exact ⟨B, hBy, hBr, hBs, hpool.1, hpool.2, hBr ▸ hstamp, hAB⟩

/-- Guarded finite acceptance service resolves the head of an actual honest vote before
the same strict deadline as its message. The output is at the observing pre-state. -/
theorem late_vote_held_of_frame_before {K : AC.CommitteeDict sp.n}
    {b : Time} (hS : HealthyBaseUpTo K tr H U proposer g b)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ell : ACLabel (goldilocksAC sp FGP ro)} (hc : tr.CallAt y j ell) {s : Nat}
    (hs : gbar g + 4 * sp.Δ ≤ sp.ts s) (ht : sp.ts s + 2 * sp.Δ ≤ tr.time j)
    (hjb : tr.time j ≤ b)
    (hdeadline : ∀ k ≤ j, ∀ t, gbar g ≤ t → tr.deadline y k t ≤ max t (sp.ts s) + sp.Δ)
    (hrestart : ∀ k ≤ j, tr.RestartAt y k → tr.time k < sp.ts s)
    {x : Fin sp.n} (hx : x ∈ H) {i : Nat} {e : Em sp FGP}
    (hv : VoteAt tr x i e) (hes : e.msg.slot = s)
    (hF : ∀ B ∈ U, B.root = e.msg.head → Anc U ell.frame.F B) :
    ∃ B ∈ ell.frame.tree, B.root = e.msg.head ∧ B.slot ≤ s ∧
      e.msg ∈ (tr.state y j).pool s ∧
      (tr.state y j).voteStamp e.msg < ETime.of (sp.ts s + 2 * sp.Δ) ∧
      (tr.state y j).blockStamp e.msg.head < ETime.of (sp.ts s + 2 * sp.Δ) := by
  obtain ⟨B, hB, hr, hh, hp, hvs, hb, -⟩ := late_vote_accepted_of_frame_before hS hy hc
    hs ht hjb hdeadline hrestart hx hv hes hF
  exact ⟨B, hB, hr, hh, hp, hvs, hb⟩

/-- Finite service carries the honest preceding-slot batch at an actual next-slot vote.
The frame-dependent delivery input uses the receiver's own F. -/
theorem honest_batch_carry_before {K : AC.CommitteeDict sp.n}
    {b : Time} (hS : HealthyBaseUpTo K tr H U proposer g b)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ell : ACLabel (goldilocksAC sp FGP ro)} {e' : Em sp FGP}
    (hc : CastAt tr y j ell e') {s : Nat} (hs' : e'.msg.slot = s + 1)
    (hs : gbar g + 4 * sp.Δ ≤ sp.ts s) (ht : sp.ts s + 2 * sp.Δ ≤ tr.time j)
    (hjb : tr.time j ≤ b)
    (hdeadline : ∀ k ≤ j, ∀ t, gbar g ≤ t → tr.deadline y k t ≤ max t (sp.ts s) + sp.Δ)
    (hrestart : ∀ k ≤ j, tr.RestartAt y k → tr.time k < sp.ts s)
    (hF : ∀ x ∈ H, ∀ i e, VoteAt tr x i e → e.msg.slot = s →
      ∀ B ∈ U, B.root = e.msg.head → Anc U ell.frame.F B) :
    CarryAt tr U y j e' s
      {v | ∃ x ∈ H, ∃ i e, VoteAt tr x i e ∧ e.msg = v ∧ v.slot = s} := by
  have hr := hS.run.localRun
  have hDelta := sp.toParams.hΔ
  obtain ⟨hPhi, hPhiU⟩ := frameIn_of_callAt hr hy hc.1
  refine ⟨hr.awake_of_call y hy j ell hc.1, (castAt_spec hr hy hc).2.2.1, ?_, ?_⟩
  · rintro v ⟨x, hx, i, e, hv, rfl, hes⟩
    obtain ⟨B, hB, hBr, -, -, -, -, hacc⟩ := late_vote_accepted_of_frame_before hS hy hc.1
      hs ht hjb hdeadline hrestart hx hv hes (hF x hx i e hv hes)
    refine ⟨B, hPhiU hB, hBr, fun X hX => ?_⟩
    rcases acceptedBefore_ancestor hr hy hc.1 (hPhiU hB) hacc hX with hg | ⟨k, hk, hkt⟩
    · exact Or.inl hg
    · exact Or.inr ⟨k, hk, by linarith only [hDelta, hkt]⟩
  · rintro v ⟨x, hx, i, e, hv, rfl, hes⟩
    obtain ⟨hp, hst⟩ := late_vote_readPoint_before hS hy hc hs' hs ht hjb hdeadline hrestart
      hx hv hes
    exact Or.inl ⟨hp, lt_trans hst
      (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (by linarith only [hDelta])))⟩

/-- **A late honest vote is held**: for a slot `s ≥ r` and an honest call at a time
`≥ t_s + 2Δ`, every honest slot-`s` vote is held, with a stamp before `t_s + 2Δ`, before and after
the call, with the unlock given. -/
theorem late_vote_poolU
    {u : Nat → Set Lock} (hS : HealthyBaseU wm u tr H U proposer g) {y : Fin sp.n} (hy : y ∈ H)
        {j : Nat}
    {ℓ : ACLabel (goldilocksAC sp FGP ro)} (hc : tr.CallAt y j ℓ) {s : Nat}
    (hs : gbar g + 4 * sp.Δ ≤ sp.ts s) (ht : sp.ts s + 2 * sp.Δ ≤ tr.time j) {x : Fin sp.n}
    (hx : x ∈ H) {i : Nat} {e : Em sp FGP} (hv : VoteAt tr x i e) (hes : e.msg.slot = s) :
    ∀ c, (c = j ∨ c = j + 1) → e.msg ∈ (tr.state y c).pool s ∧
      (tr.state y c).voteStamp e.msg < ETime.of (sp.ts s + 2 * sp.Δ) := by
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  have hg0 := gbar_nonneg g
  obtain ⟨ℓx, hcx, hex⟩ := hv
  obtain ⟨hval, hslx, -, -⟩ := castAt_specU hr hx ⟨hcx, hex⟩
  have hti : tr.time i ≤ sp.ts s + sp.Δ := by
    have := vote_time_leU hr hx ⟨ℓx, hcx, hex⟩
    rwa [← hslx, hes] at this
  have hti' : sp.ts s ≤ tr.time i :=
    (ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by rw [← hslx, hes])
  -- the vote reaches `y` before `t_s + 2Δ`
  have hgi : g ≤ tr.time i := (le_gbar g).trans (by linarith only [hs, hti, hti'])
  have hmax : max (tr.time i) g = tr.time i := max_eq_left hgi
  have hdl : ∀ c, tr.deadline y c (tr.time i) ≤ tr.time i + sp.Δ := fun c =>
    (hS.deadline_le hy c _).trans (by rw [max_eq_left (by
        linarith only [hs, hti, hti'] : gbar g ≤ tr.time i)])
  obtain ⟨k', hk'j, hik', hproc, hk'dl⟩ := hS.healthy.message x hx i e.msg
    ⟨ℓx, hcx, Or.inl ⟨e, hex, rfl⟩⟩ y hy j ℓ hc (by rw [hmax]; linarith only [hdl j, ht, hti])
  rw [hmax] at hk'dl
  have hk'T : tr.time k' < sp.ts s + 2 * sp.Δ := by linarith only [hdl k', hti, hk'dl]
  have hk'j' : k' < j := lt_of_le_of_ne hk'j (by rintro rfl; linarith only [hk'T, ht])
  have hsl' : sp.slot (tr.time k') = s :=
    slot_of_mem sp s (by linarith only [hti', hik']) (by
        rw [AC.ts_succ]; linarith only [hti, hti', hk'T])
  have hxH : e.msg.val ∈ H := hval ▸ hx
  have hheld : e.msg ∈ (tr.state y (k' + 1)).pool s := by
    rcases held_of_processAtU hr hy hproc (by rw [hsl', hes]; omega) (by rw [hsl', hes]) with
      h | ⟨a, ha, b, hb, hab, hav, hbv⟩
    · rwa [hes] at h
    · exfalso
      rw [hes] at ha hb
      obtain ⟨ja, -, ea, hva, rfl⟩ := hS.run.honest.pool_vote y hy (k' + 1) s _ ha (hav ▸ hxH)
      obtain ⟨jb, -, eb, hvb, rfl⟩ := hS.run.honest.pool_vote y hy (k' + 1) s _ hb (hbv ▸ hxH)
      have hsa := state_pool_slotU sp hr (fun _ => voteStart_initial _) hy (k' + 1) s _ ha
      have hsb := state_pool_slotU sp hr (fun _ => voteStart_initial _) hy (k' + 1) s _ hb
      rw [hav] at hva
      rw [hbv] at hvb
      obtain ⟨-, rfl⟩ := (one_vote_per_slotU sp) FGP ro H U tr hr _ hxH ja jb ea eb hva hvb
        (hsa.trans hsb.symm)
      exact hab rfl
  intro c hcj
  have hst := stamp_lt_of_heldU hS hy (a := k' + 1) (b := c) (by omega) (w := e.msg)
    (by rw [hes]; exact hheld) (T := sp.ts s + 2 * sp.Δ)
    (fun k hk => lt_of_le_of_lt (hr.time_mono (Nat.lt_succ_iff.1 hk)) hk'T)
    (by rw [hes]; linarith only [hti', hk'T, hik']) (by
        linarith only [hs, hti', hk'T, hik']) fun k h1 _ hrk => by
      have := hS.restart_le hy hrk
      have := hr.time_mono (show k' ≤ k by omega)
      linarith
  rwa [hes] at hst

/-- `late_vote_held_of_frame` with the unlock given. -/
theorem late_vote_held_of_frameU
    {u : Nat → Set Lock} (hS : HealthyBaseU wm u tr H U proposer g) {y : Fin sp.n} (hy : y ∈ H)
    {j : Nat} {ℓ : ACLabel (goldilocksAC sp FGP ro)} (hc : tr.CallAt y j ℓ) {s : Nat}
    (hs : gbar g + 4 * sp.Δ ≤ sp.ts s) (ht : sp.ts s + 2 * sp.Δ ≤ tr.time j) {x : Fin sp.n}
    (hx : x ∈ H) {i : Nat} {e : Em sp FGP} (hv : VoteAt tr x i e) (hes : e.msg.slot = s)
    (hF : ∀ Hd ∈ U, Hd.root = e.msg.head → Anc U ℓ.frame.F Hd) :
    ∃ Hd ∈ ℓ.frame.tree, Hd.root = e.msg.head ∧ Hd.slot ≤ s ∧
      ∀ c, (c = j ∨ c = j + 1) → e.msg ∈ (tr.state y c).pool s ∧
        (tr.state y c).voteStamp e.msg < ETime.of (sp.ts s + 2 * sp.Δ) ∧
        (tr.state y c).blockStamp e.msg.head < ETime.of (sp.ts s + 2 * sp.Δ) := by
  have hpool := late_vote_poolU hS hy hc hs ht hx hv hes
  have hr := hS.run.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  have hg0 := gbar_nonneg g
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hy hc
  obtain ⟨ℓx, hcx, hex⟩ := hv
  obtain ⟨-, hslx, -, hhead⟩ := castAt_specU hr hx ⟨hcx, hex⟩
  have hti : tr.time i ≤ sp.ts s + sp.Δ := by
    have := vote_time_leU hr hx ⟨ℓx, hcx, hex⟩
    rwa [← hslx, hes] at this
  -- the head: in `x`'s frame, accepted by `y` before `t_s + 2Δ`
  obtain ⟨hΦx, hΦxU⟩ := frameIn_of_callAtU hr hx hcx
  obtain ⟨Hx, hHx, hHxr⟩ : ∃ Hx ∈ ℓx.frame.tree, Hx.root = e.msg.head :=
    ⟨_, getHead_mem hΦx (fun _ hX => (voteDomain_subset_tree hX.1)) e.readPoint (tr.time i)
      (mergedVoteView sp e.readPoint ℓx.frame e.msg.slot) ((e.msg.slot : Int) - 1)
      (T := ℓx.frame.viableTree (voteDomain sp e.readPoint ℓx.frame e.msg.slot)),
      hhead.symm⟩
  have hHxs : Hx.slot ≤ s := by
    have := frame_slot_leU sp hr hx hcx Hx hHx
    rwa [← hslx, hes] at this
  have hF : Anc U ℓ.frame.F Hx := hF Hx (hΦxU hHx) hHxr
  obtain ⟨hHt, hAB⟩ : Hx ∈ ℓ.frame.tree ∧
      AcceptedBefore tr y Hx (sp.ts s + 2 * sp.Δ) := by
    rcases Compose.frame_anc_acceptedU hr hx i ℓx hcx Hx hHx Hx Relation.ReflTransGen.refl with
      hg | ⟨kh, hkh, hacc⟩
    · refine ⟨?_, Or.inl hg⟩
      obtain ⟨G, hGU, hGr, hGp⟩ := genesis_mem_of_callU sp hr hy j ℓ hc
      obtain rfl : Hx = G := hU.1 (hΦxU hHx) hGU (hg.trans hGr.symm)
      obtain h | ⟨c, -, hcp⟩ := (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hF
      · exact h ▸ hΦ.rooted.1
      · exact absurd (hcp.2.2.symm.trans hGp) (Option.some_ne_none _)
    have htkh : tr.time kh ≤ sp.ts s + sp.Δ := (hr.time_mono hkh).trans hti
    obtain ⟨ka, hkaj, hacc', hlt⟩ : ∃ ka ≤ j, tr.AcceptAt y ka Hx ∧
        tr.time ka < sp.ts s + 2 * sp.Δ := by
      by_cases hgk : g ≤ tr.time kh
      · have hmx : max (tr.time kh) (gbar g) ≤ sp.ts s + sp.Δ := max_le htkh (by
          linarith only [hs, hΔ])
        obtain ⟨ka, hkaj, hacc', hlt⟩ := hS.healthy.relay x hx kh Hx hacc hgk y hy j ℓ hc
          (by linarith only [hS.deadline_le hy j (tr.time kh), ht, hmx]) hF
        exact ⟨ka, hkaj, hacc', by linarith only [hS.deadline_le hy ka (tr.time kh), hmx, hlt]⟩
      · obtain ⟨ka, hkaj, hacc', hlt⟩ := hS.catchUp x hx kh Hx hacc
          (lt_of_lt_of_le (not_le.1 hgk) (le_gbar g)) y hy j ℓ hc (by linarith only [hs, ht, hΔ]) hF
        exact ⟨ka, hkaj, hacc', by linarith only [hs, hΔ, hlt]⟩
    exact ⟨mem_tree_of_acceptAtU sp hr hy hacc' hkaj hc hF, Or.inr ⟨ka, hacc', hlt⟩⟩
  have hbs := blockStamp_lt_of_acceptedBeforeU sp hr (fun _ => voteStart_initial _) hy hc hHt hAB
    (fun k _ hrk => lt_of_le_of_lt (hS.restart_le hy hrk) (by linarith only [hs, hΔ])) (Or.inl ht)
  have hpost : (tr.state y (j + 1)).blockStamp Hx.root = (tr.state y j).blockStamp Hx.root := by
    have hst : tr.state y (j + 1) = tr.post j := by simp [Trace.state, hc.1, hc.2]
    have he := hr.exec j ℓ hc.2 (hc.1 ▸ hy)
    rw [hc.1] at he
    have hp' : tr.post j =
        (stepWithM sp ro wm y (u j) (tr.state y j) ℓ.frame (tr.time j) ℓ.call).1 := by
      rw [he]
    obtain ⟨hblk, -, hoth⟩ := stepWith_blockStamp_eq ro y (u j) (tr.state y j) hΦ (hr.time_nonneg j)
      ℓ.call
    rw [hst, hp']
    by_cases hb : ∃ B, ℓ.call = .block B
    · obtain ⟨B, hB⟩ := hb
      rw [hblk B hB, Function.update_apply]
      split_ifs with hr'
      swap
      · rfl
      exfalso
      have hBU : B ∈ U := hΦU ((accept_newU sp hr hy ⟨ℓ, hc, hB⟩).1 ℓ hc)
      obtain rfl : Hx = B := hU.1 (hΦU hHt) hBU hr'
      rcases hAB with hg | ⟨ka, hka, hlt⟩
      · exact accept_ne_genesisU sp hr hy ⟨ℓ, hc, hB⟩ hg
      · obtain rfl := accept_uniqueU sp hr hy hka ⟨ℓ, hc, hB⟩
        linarith
    · simp only [not_exists] at hb
      rw [hoth hb fun hrs => by
        have := hS.restart_le hy ⟨ℓ, hc, hrs⟩
        linarith only [hs, ht, hΔ, this]]
  refine ⟨Hx, hHt, hHxr, hHxs, fun c hcj => ⟨(hpool c hcj).1, (hpool c hcj).2, ?_⟩⟩
  rw [← hHxr]
  rcases hcj with rfl | rfl
  · exact hbs
  · rw [hpost]; exact hbs

/-- **A late honest batch**: for a slot `s ≥ r` and an honest call at a time
`≥ t_s + 2Δ` whose `Φ.F` the vote's head extends, every honest slot-`s` vote is held, with its
head in the call's frame (of slot at most `s`), and both its stamp and its head's are before
`t_s + 2Δ`, before and after the call. -/
theorem late_vote_held_of_frame (hS : HealthyBase tr H U proposer g) {y : Fin sp.n} (hy : y ∈ H)
    {j : Nat} {ℓ : ACLabel (goldilocksAC sp FGP ro)} (hc : tr.CallAt y j ℓ) {s : Nat}
    (hs : gbar g + 4 * sp.Δ ≤ sp.ts s) (ht : sp.ts s + 2 * sp.Δ ≤ tr.time j) {x : Fin sp.n}
    (hx : x ∈ H) {i : Nat} {e : Em sp FGP} (hv : VoteAt tr x i e) (hes : e.msg.slot = s)
    (hF : ∀ Hd ∈ U, Hd.root = e.msg.head → Anc U ℓ.frame.F Hd) :
    ∃ Hd ∈ ℓ.frame.tree, Hd.root = e.msg.head ∧ Hd.slot ≤ s ∧
      ∀ c, (c = j ∨ c = j + 1) → e.msg ∈ (tr.state y c).pool s ∧
        (tr.state y c).voteStamp e.msg < ETime.of (sp.ts s + 2 * sp.Δ) ∧
        (tr.state y c).blockStamp e.msg.head < ETime.of (sp.ts s + 2 * sp.Δ) :=
  late_vote_held_of_frameU (hS := hS.toU) (y := y) (hy := hy) (j := j) (ℓ := ℓ) (hc := hc)
      (s := s) (hs := hs) (ht := ht) (x := x) (hx := hx) (i := i) (e := e) (hv := hv) (hes := hes)
          (hF := hF)

/-- The resolution time of a vote whose head is a block of the frame of a slot at most the
vote's is the later of the two stamps. -/
theorem resolutionTime_lt_of {A : ACState sp.n} {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    {v : Vote sp.n} {Hd : Blk sp.n FGP} (hHd : Hd ∈ Φ.tree) (hr : Hd.root = v.head)
    (hsl : Hd.slot ≤ v.slot) {T : ETime} (h1 : A.voteStamp v < T)
    (h2 : A.blockStamp v.head < T) : resolutionTime A Φ v < T := by
  have hl : lookup Φ v.head = some Hd := by
    cases h : lookup Φ v.head with
    | none => exact absurd ⟨Hd, hHd, hr⟩ (lookup_eq_none h)
    | some Hd' =>
      obtain ⟨h1', h2'⟩ := lookup_eq_some h
      rw [hΦ.coherent.1 h1' hHd (h2'.trans hr.symm)]
  unfold resolutionTime
  rw [hl]
  dsimp only
  split_ifs
  · omega
  · exact max_lt h1 h2

/-! ## Honest votes and comparison with `P` -/

/-- An honest validator is not an equivocator in an honest node's pool of a slot, from any run
and vote start (its votes in the pool are actual votes of the slot, one per slot). -/
theorem honest_not_equivocator_pool_of_run
    {uL : Nat → Set Lock} {ini} (hrun : ACRunU wm uL proposer tr H U ini)
    {y : Fin sp.n} (hy : y ∈ H)
    (c s : Nat) {u : Fin sp.n} (hu : u ∈ H) :
    u ∉ equivocators {v | v ∈ (tr.state y c).pool s} := by
  have hr := hrun.localRun
  rintro ⟨a, ha, b, hb, hab, rfl, hbv⟩
  obtain ⟨ja, -, ea, hva, rfl⟩ := hrun.honest.pool_vote y hy c s _ ha hu
  obtain ⟨jb, -, eb, hvb, rfl⟩ := hrun.honest.pool_vote y hy c s _ hb (hbv ▸ hu)
  rw [hbv] at hvb
  obtain ⟨-, rfl⟩ := (one_vote_per_slotU sp) FGP ro H U tr hr _ hu ja jb ea eb hva hvb
    ((state_pool_slotU sp hr hrun.vstart hy c s _ ha).trans
      (state_pool_slotU sp hr hrun.vstart hy c s _ hb).symm)
  exact hab rfl

/-- **A majority of the votes of a set `M` meets `H`**: a set `T` inside a vote set `W ⊆ M` that
contains every member of `M ∩ H`, with `|W| < 2|T|`, has a member of `H` once at most `|M ∩ H|`
members of `M` are outside `H` (the faulty members of `T` are counted inside `W`, next to
`M ∩ H`). -/
private theorem exists_mem_of_majority {n : Nat} {M H T W : Set (Fin n)} (hHW : M ∩ H ⊆ W)
    (hTW : T ⊆ W) (hWM : W ⊆ M) (hmaj : W.ncard < 2 * T.ncard)
    (hf : (M ∩ Hᶜ).ncard ≤ (M ∩ H).ncard) : ∃ u ∈ H, u ∈ T := by
  by_contra hno
  have hdisj : Disjoint (M ∩ H) T := Set.disjoint_left.2 fun u hu huT => hno ⟨u, hu.2, huT⟩
  have h1 := Set.ncard_le_ncard (Set.union_subset hHW hTW)
  rw [Set.ncard_union_eq hdisj] at h1
  have h2 : T.ncard ≤ (M ∩ Hᶜ).ncard :=
    Set.ncard_le_ncard fun u hu => ⟨hWM (hTW hu), fun huH => hno ⟨u, huH, hu⟩⟩
  omega

/-- **A late result has an honest supporter, over a member set**: from any run and vote start, the
result `C` of an honest update of slot `s` is extended by an honest vote of slot `s`, given a set
`M` (the slot-`s` committee) that holds every voter of the reader's slot-`s` pool, every honest
member of which is such a voter, and at most half of which is faulty. -/
theorem result_extended_of_members
    {uL : Nat → Set Lock} {ini} (hrun : ACRunU wm uL proposer tr H U ini) {s : Nat}
    {M : Set (Fin sp.n)} {x : Fin sp.n} (hx : x ∈ H) {c : Nat}
    {ℓ : ACLabel (goldilocksAC sp FGP ro)} (hc : tr.CallAt x c ℓ)
    (hMv : M ∩ H ⊆ voters {v | v ∈ (tr.state x c).pool s})
    (hvM : voters {v | v ∈ (tr.state x c).pool s} ⊆ M)
    (hf : (M ∩ Hᶜ).ncard ≤ (M ∩ H).ncard) {C : Blk sp.n FGP}
    (hC : getConfirmation sp (tr.state x c) ℓ.frame s = some C) :
    ∃ z ∈ H, ∃ j e, VoteAt tr z j e ∧ e.msg.slot = s ∧ VoteExtends U e.msg C := by
  have hr := hrun.localRun
  obtain ⟨-, hΦU⟩ := frameIn_of_callAtU hr hx hc
  have hmaj := (deepest_mem hC).1.2.2
  unfold confirmationScore at hmaj
  dsimp only at hmaj
  obtain ⟨u, huH, ⟨-, v, ⟨hvp, -⟩, rfl, -, R, hR, hRr, hCR⟩⟩ := exists_mem_of_majority hMv
    (T := supporters ℓ.frame ⟨{v | v ∈ (tr.state x c).pool s}, {v | v ∈ (tr.state x c).pool s ∧
      resolutionTime (tr.state x c) ℓ.frame v < ETime.of (sp.ts s + 2 * sp.Δ)}⟩ s C)
    (fun u ⟨_, x, hx, hxu, _⟩ => ⟨x, hx.1, hxu⟩) hvM hmaj hf
  obtain ⟨j', -, e', hve, rfl⟩ := hrun.honest.pool_vote x hx c s _ hvp huH
  exact ⟨_, huH, j', e', hve, state_pool_slotU sp hr hrun.vstart hx c s _ hvp, R, hΦU hR, hRr,
    Anc.mono hΦU hCR⟩

set_option linter.unusedVariables false in
-- `HealthyBaseU` bounds the faults by `f < n/2` only; the bound `3f ≤ n − 1` is given.

/-- `result_extended` with the unlock given. -/
theorem result_extendedU
    {uL : Nat → Set Lock} (hS : HealthyBaseU wm uL tr H U proposer g) {s : Nat}
    (hs : gbar g + 4 * sp.Δ ≤ sp.ts s) {x : Fin sp.n} (hx : x ∈ H) {c : Nat}
    {ℓ : ACLabel (goldilocksAC sp FGP ro)} (hc : tr.CallAt x c ℓ)
    (ht : sp.ts s + 2 * sp.Δ ≤ tr.time c) {C : Blk sp.n FGP}
    (hC : getConfirmation sp (tr.state x c) ℓ.frame s = some C) :
    ∃ z ∈ H, ∃ j e, VoteAt tr z j e ∧ e.msg.slot = s ∧ VoteExtends U e.msg C := by
  have hr := hS.run.localRun
  refine result_extended_of_members hS.run (M := Set.univ) hx hc (fun u hu => ?_)
    (Set.subset_univ _) ?_ hC
  · obtain ⟨j, e, hv, hes⟩ := honest_votes_in_slotU hS hs u hu.2
    obtain ⟨hval, -⟩ := castAt_specU hr hu.2 ⟨hv.choose_spec.1, hv.choose_spec.2⟩
    exact ⟨e.msg, (late_vote_poolU hS hx hc hs ht hu.2 hv hes c (Or.inl rfl)).1, hval⟩
  · rw [Set.univ_inter, Set.univ_inter]
    have := hS.two_faulty_lt
    have hn : H.ncard + Hᶜ.ncard = sp.n := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    omega

/-- **A late result has an honest supporter**: the result `C` of an honest update of a slot
`s ≥ r` (read at a time `≥ t_s + 2Δ`) is extended by an honest vote of slot `s`: its supporters
are a strict majority of the voters, which include all honest validators. -/
theorem result_extended (hS : HealthyBase tr H U proposer g) {s : Nat}
    (hs : gbar g + 4 * sp.Δ ≤ sp.ts s) {x : Fin sp.n} (hx : x ∈ H) {c : Nat}
    {ℓ : ACLabel (goldilocksAC sp FGP ro)} (hc : tr.CallAt x c ℓ)
    (ht : sp.ts s + 2 * sp.Δ ≤ tr.time c) {C : Blk sp.n FGP}
    (hC : getConfirmation sp (tr.state x c) ℓ.frame s = some C) :
    ∃ z ∈ H, ∃ j e, VoteAt tr z j e ∧ e.msg.slot = s ∧ VoteExtends U e.msg C :=
  result_extendedU (hS := hS.toU) (s := s) (hs := hs) (x := x) (hx := hx) (c := c) (ℓ := ℓ)
      (hc := hc) (ht := ht) (C := C) (hC := hC)

/-! ## The first update at `t_p + 6Δ` -/

/-- **The first update, over a member set**: from any run and vote start, at an honest node's tick
at `t_p + 6Δ` from a joined state, with every honest slot-`p` vote exactly `P` and every live lock
comparing with `P`, the tick is the slot-`p` update, whose result is `P`, not vetoed, and `P` passes
the fast test, given a set `M` (the slot-`p` committee) that holds every voter of the node's
slot-`p` pool, each honest member of which has a vote there resolved before `t_p + 2Δ`, with fewer
faulty than honest members, and with its honest members at least half of the committee size. -/
theorem first_update_post_of_members
    {uL : Nat → Set Lock} {ini} (hrun : ACRunU wm uL proposer tr H U ini) {p : Nat}
    {P : Blk sp.n FGP}
    (hexact : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksAC sp FGP ro)}
    (hc : tr.CallAt y k ℓ) (hcall : ℓ.call = .tick) (htk : tr.time k = sp.ts p + 6 * sp.Δ)
    (hj : joined sp (tr.state y k) (tr.time k)) (hPt : P ∈ ℓ.frame.tree)
    (hlocks : ∀ L ∈ liveLockBlocks sp (tr.state y k).locks ℓ.frame (tr.time k),
      Compatible U L P)
    {M : Set (Fin sp.n)}
    (hheld : ∀ u ∈ M ∩ H, ∃ v ∈ (tr.state y k).pool p, v.val = u ∧
      resolutionTime (tr.state y k) ℓ.frame v < ETime.of (sp.ts p + 2 * sp.Δ))
    (hvM : voters {v | v ∈ (tr.state y k).pool p} ⊆ M)
    (hf : (M ∩ Hᶜ).ncard < (M ∩ H).ncard)
    (hfast : sp.committeeSize ≤ 2 * (M ∩ H).ncard) :
    getConfirmation sp (tr.state y k) ℓ.frame p = some P ∧
      ¬ conflictsWithLock sp (tr.state y k).locks ℓ.frame (tr.time k) P ∧
      FastTest sp (tr.state y k) ℓ.frame p P ∧
      tr.post k = updateConfirmationM sp wm (tr.state y k) ℓ.frame (tr.time k) p := by
  have hr := hrun.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hy hc
  have hts1 := AC.ts_succ (sp := sp) p
  have hslot : sp.slot (tr.time k) = p + 1 :=
    slot_of_mem sp (p + 1) (by rw [htk, hts1]; linarith only [hΔ]) (by
        rw [htk, AC.ts_succ, hts1]; linarith only [hΔ])
  have hT2 : tr.time k = sp.ts ((p + 1 : Nat) : Int) + 2 * sp.Δ := by rw [htk, hts1]; ring
  -- the tick is the slot-`p` update
  have he := hr.exec k ℓ hc.2 (hc.1 ▸ hy)
  rw [hc.1, hcall] at he
  have hpost : tr.post k = updateConfirmationM sp wm (tr.state y k) ℓ.frame (tr.time k) p := by
    have h1 : tr.post k = (acOnTickWithM sp wm y (uL k) (tr.state y k) ℓ.frame (tr.time k)).1 :=
      (congrArg Prod.fst he).symm
    rw [h1]
    unfold acOnTickWithM
    dsimp only
    rw [hslot]
    have hc1 : ¬ tr.time k = sp.ts ((p + 1 : Nat) : Int) + sp.Δ := by
      intro h; linarith only [htk, hΔ, hts1, h]
    have hc2 : (tr.time k = sp.ts ((p + 1 : Nat) : Int) + 2 * sp.Δ ∧ 0 < p + 1) = True :=
      eq_true ⟨hT2, Nat.succ_pos p⟩
    simp only [hj, not_true_eq_false, hc1, hc2, ↓reduceIte, Nat.add_sub_cancel]
  set A := tr.state y k with hA
  -- the honest slot-`p` votes in the pool are on `P`
  have hhead : ∀ v ∈ A.pool p, v.val ∈ H → v.head = P.root := fun v hv hvH => by
    obtain ⟨j', -, e', hve, rfl⟩ := hrun.honest.pool_vote y hy k p v hv hvH
    exact hexact _ hvH j' e' hve (state_pool_slotU sp hr hrun.vstart hy k p _ hv)
  have hMvot : M ∩ H ⊆ voters {v | v ∈ A.pool p} := fun u hu => by
    obtain ⟨v, hv, hvu, -⟩ := hheld u hu
    exact ⟨v, hv, hvu⟩
  have hvle := Set.ncard_le_ncard hvM
  have hMn : (M ∩ H).ncard + (M ∩ Hᶜ).ncard = M.ncard :=
    Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _ (Set.toFinite _)
  -- the honest members support `P`
  have hscore : (M ∩ H).ncard ≤ confirmationScore sp A ℓ.frame p P := by
    unfold confirmationScore
    dsimp only
    have hsub : M ∩ H ⊆ supporters ℓ.frame ⟨{v | v ∈ A.pool p}, {v | v ∈ A.pool p ∧
        resolutionTime A ℓ.frame v < ETime.of (sp.ts p + 2 * sp.Δ)}⟩ p P := by
      intro u hu
      obtain ⟨v, hv, hvu, hres⟩ := hheld u hu
      refine ⟨honest_not_equivocator_pool_of_run hrun hy k p hu.2, v, ⟨hv, hres⟩, hvu, ?_,
        P, hPt, (hhead v hv (hvu ▸ hu.2)).symm, Relation.ReflTransGen.refl⟩
      exact_mod_cast state_pool_slotU sp hr hrun.vstart hy k p v hv
    exact Set.ncard_le_ncard hsub
  -- the slot-`p` result is `P`
  have hconf : getConfirmation sp A ℓ.frame p = some P := by
    unfold getConfirmation
    have hPS : P ∈ {B | B ∈ ℓ.frame.tree ∧ ℓ.frame.Anc ℓ.frame.F B ∧
        (voters {v | v ∈ A.pool p}).ncard < 2 * confirmationScore sp A ℓ.frame p B} :=
      ⟨hPt, hΦ.rooted.2 P hPt, by omega⟩
    have hall : ∀ B ∈ {B | B ∈ ℓ.frame.tree ∧ ℓ.frame.Anc ℓ.frame.F B ∧
        (voters {v | v ∈ A.pool p}).ncard < 2 * confirmationScore sp A ℓ.frame p B},
        ℓ.frame.Anc B P := by
      rintro B ⟨hBt, -, hmaj⟩
      by_contra hBP
      unfold confirmationScore at hmaj
      dsimp only at hmaj
      obtain ⟨u, hu, ⟨-, x, ⟨hx, -⟩, rfl, -, R, hR, hRr, hBR⟩⟩ := exists_mem_of_majority hMvot
        (by rintro u ⟨-, x, hx, hxu, -⟩; exact ⟨x, hx.1, hxu⟩) hvM hmaj hf.le
      obtain rfl : R = P := hΦ.coherent.1 hR hPt (hRr.trans (hhead x hx hu))
      exact hBP hBR
    obtain ⟨D, hD⟩ := exists_deepest hΦ (fun B hB => hB.1) ⟨P, hPS⟩
    have hDP := hall D (deepest_mem hD).1
    have hPD := anc_deepest hΦ (fun B hB => hB.1)
      (fun B hB C hC => anc_total hΦ.coherent (hall B hB) (hall C hC)) hD P hPS
    rw [hD, Anc.antisymm hΦ.coherent hDP hPD]
  -- it is not vetoed
  have hnv : ¬ conflictsWithLock sp A.locks ℓ.frame (tr.time k) P := by
    rintro ⟨L, hL, hnc⟩
    apply hnc
    rcases hlocks L hL with h | h
    · exact Or.inr (anc_tree_of_anc_U hU hΦ hΦU hL.1 h hPt)
    · exact Or.inl (anc_tree_of_anc_U hU hΦ hΦU hPt h hL.1)
  exact ⟨hconf, hnv, by unfold FastTest; omega, hpost⟩

/-- `first_update_post` with the unlock given. -/
theorem first_update_postU
    {uL : Nat → Set Lock} (hS : HealthyBaseU wm uL tr H U proposer g) {p : Nat} {P : Blk sp.n FGP}
    (hp4 : gbar g + 4 * sp.Δ ≤ sp.ts p)
    (hexact : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksAC sp FGP ro)}
    (hc : tr.CallAt y k ℓ) (hcall : ℓ.call = .tick) (htk : tr.time k = sp.ts p + 6 * sp.Δ)
    (hPt : P ∈ ℓ.frame.tree)
    (hlocks : ∀ L ∈ liveLockBlocks sp (tr.state y k).locks ℓ.frame (tr.time k),
      Compatible U L P) :
    getConfirmation sp (tr.state y k) ℓ.frame p = some P ∧
      ¬ conflictsWithLock sp (tr.state y k).locks ℓ.frame (tr.time k) P ∧
      FastTest sp (tr.state y k) ℓ.frame p P ∧
      tr.post k = updateConfirmationM sp wm (tr.state y k) ℓ.frame (tr.time k) p := by
  have hr := hS.run.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hy hc
  have hts1 := AC.ts_succ (sp := sp) p
  have hslot : sp.slot (tr.time k) = p + 1 :=
    slot_of_mem sp (p + 1) (by rw [htk, hts1]; linarith only [hΔ]) (by
        rw [htk, AC.ts_succ, hts1]; linarith only [hΔ])
  have hj := hS.joined_state hy k (by
    rw [hslot, show (((p + 1 : Nat) : Int) - 1) = p by push_cast; ring]; linarith only [hp4, hΔ])
  have hHn : H.ncard + Hᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h2f := hS.two_faulty_lt
  refine first_update_post_of_members hS.run hexact hy hc hcall htk hj hPt hlocks
    (M := Set.univ) (fun u hu => ?_) (Set.subset_univ _) ?_ ?_
  · -- the honest slot-`p` votes: held, resolved before `t_p + 2Δ`
    obtain ⟨i, e, hv, hes⟩ := honest_votes_in_slotU hS hp4 u hu.2
    obtain ⟨Hd, hHdt, hHdr, hHds, hh⟩ := late_vote_held_of_frameU hS hy hc hp4
      (by rw [htk]; linarith only [hΔ]) hu.2 hv hes fun Hd hHd hHdr => by
        rw [hU.1 hHd (hΦU hPt) (hHdr.trans (hexact u hu.2 i e hv hes))]
        exact (hΦ.rooted.2 P hPt).mono hΦU
    obtain ⟨hmem, hvst, hbst⟩ := hh k (Or.inl rfl)
    obtain ⟨hval, -⟩ := castAt_specU hr hu.2 ⟨hv.choose_spec.1, hv.choose_spec.2⟩
    exact ⟨e.msg, hmem, hval, resolutionTime_lt_of hΦ hHdt hHdr (hes ▸ hHds) hvst hbst⟩
  · rw [Set.univ_inter, Set.univ_inter]
    omega
  · rw [Set.univ_inter, hS.stock]
    omega

/-- **The first update**: at an honest node's tick at `t_p + 6Δ`, with every honest
slot-`p` vote exactly `P` and every live lock comparing with `P`, the tick is the slot-`p` update,
whose result is `P` (its honest batch is a strict majority, and every other passing block has only
faulty supporters unless it is an ancestor of `P`), not vetoed, and `P` passes the fast test
(the honest batch is half of the committee or more). -/
theorem first_update_post
    (hS : HealthyBase tr H U proposer g) {p : Nat} {P : Blk sp.n FGP}
    (hp4 : gbar g + 4 * sp.Δ ≤ sp.ts p)
    (hexact : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksAC sp FGP ro)}
    (hc : tr.CallAt y k ℓ) (hcall : ℓ.call = .tick) (htk : tr.time k = sp.ts p + 6 * sp.Δ)
    (hPt : P ∈ ℓ.frame.tree)
    (hlocks : ∀ L ∈ liveLockBlocks sp (tr.state y k).locks ℓ.frame (tr.time k),
      Compatible U L P) :
    getConfirmation sp (tr.state y k) ℓ.frame p = some P ∧
      ¬ conflictsWithLock sp (tr.state y k).locks ℓ.frame (tr.time k) P ∧
      FastTest sp (tr.state y k) ℓ.frame p P ∧
      tr.post k = updateConfirmation sp (tr.state y k) ℓ.frame (tr.time k) p :=
  first_update_postU (hS := hS.toU) (p := p) (P := P) (hp4 := hp4) (hexact := hexact) (y := y)
      (hy := hy) (k := k) (ℓ := ℓ) (hc := hc) (hcall := hcall) (htk := htk) (hPt := hPt)
          (hlocks := hlocks)

/-! ## The slot committees over a finite healthy base -/

/-- **A late result has an honest supporter**, for the slot committees `K` of a finite healthy
base whose honest restarts within the horizon are by `ḡ`: the honest members of the slot-`s`
committee vote by `t_s + Δ` and are held at the reader by `t_s + 2Δ`, the reader's voters are
members (P), and fewer than half of the committee is faulty (CS2), so `result_extended_of_members`
applies at `M = K.committee s`. -/
theorem result_extended_before {K : CommitteeDict sp.n} {b : Time}
    (hS : HealthyBaseUpTo K tr H U proposer g b)
    (hrs : ∀ y ∈ H, ∀ k, tr.RestartAt y k → tr.time k ≤ b → tr.time k ≤ gbar g)
    {s : Nat} (hs : gbar g + 4 * sp.Δ ≤ sp.ts s) {x : Fin sp.n} (hx : x ∈ H) {c : Nat}
    {ℓ : ACLabel (goldilocksAC sp FGP ro)} (hc : tr.CallAt x c ℓ)
    (ht : sp.ts s + 2 * sp.Δ ≤ tr.time c) (hcb : tr.time c ≤ b) {C : Blk sp.n FGP}
    (hC : getConfirmation sp (tr.state x c) ℓ.frame s = some C) :
    ∃ z ∈ H, ∃ j e, VoteAt tr z j e ∧ e.msg.slot = s ∧ VoteExtends U e.msg C := by
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  have hs1 := ts_sub_one sp (s : Int)
  have hsplit : (K.committee s ∩ H).ncard + (K.committee s ∩ Hᶜ).ncard = sp.committeeSize := by
    rw [← hS.hsize s]
    exact Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _ (Set.toFinite _)
  have hf := hS.cs2 s (by linarith) (by linarith)
  have hrsx : ∀ q ≤ c, tr.RestartAt x q → tr.time q ≤ gbar g := fun q hq hrq =>
    hrs x hx q hrq ((hr.time_mono hq).trans hcb)
  refine result_extended_of_members hS.run.toU (M := K.committee s) hx hc (fun u hu => ?_)
    (by rintro _ ⟨v, hv, rfl⟩; exact hS.hP.1 x hx c s v hv) (by omega) hC
  obtain ⟨j, e, hv, hes, -⟩ := honest_votes_in_slot_before hS hs (by linarith)
    (fun z hz r hrt hrz => (hrs z hz r hrz (by linarith)).trans (by linarith)) u hu.2 hu.1
  obtain ⟨hval, -⟩ := castAt_spec hr hu.2 ⟨hv.choose_spec.1, hv.choose_spec.2⟩
  refine ⟨e.msg, (late_vote_pool_before hS hx hc hs ht hcb
    (fun q hq t _ => Compose.ac_deadline_le_of_restarts
      (fun q' hq' hrq' => (hrsx q' (hq'.trans hq) hrq').trans (by linarith)) t)
    (fun q hq hrq => (hrsx q hq hrq).trans_lt (by linarith)) hu.2 hv hes c (Or.inl rfl)).1, hval⟩

/-- **The first update**, for the slot committees `K` of a finite healthy base whose honest
restarts within the horizon are by `ḡ`: as `first_update_post`, at an honest tick at
`t_p + 6Δ ≤ b`, through `first_update_post_of_members` at `M = K.committee p` (the honest members'
votes held and resolved before `t_p + 2Δ`, the voters members, CS2). -/
theorem first_update_post_before {K : CommitteeDict sp.n} {b : Time}
    (hS : HealthyBaseUpTo K tr H U proposer g b)
    (hrs : ∀ y ∈ H, ∀ k, tr.RestartAt y k → tr.time k ≤ b → tr.time k ≤ gbar g)
    {p : Nat} {P : Blk sp.n FGP} (hp4 : gbar g + 4 * sp.Δ ≤ sp.ts p)
    (hexact : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksAC sp FGP ro)}
    (hc : tr.CallAt y k ℓ) (hcall : ℓ.call = .tick) (htk : tr.time k = sp.ts p + 6 * sp.Δ)
    (hkb : tr.time k ≤ b) (hPt : P ∈ ℓ.frame.tree)
    (hlocks : ∀ L ∈ liveLockBlocks sp (tr.state y k).locks ℓ.frame (tr.time k),
      Compatible U L P) :
    getConfirmation sp (tr.state y k) ℓ.frame p = some P ∧
      ¬ conflictsWithLock sp (tr.state y k).locks ℓ.frame (tr.time k) P ∧
      FastTest sp (tr.state y k) ℓ.frame p P ∧
      tr.post k = updateConfirmation sp (tr.state y k) ℓ.frame (tr.time k) p := by
  have hr := hS.run.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  have hp1 := ts_sub_one sp (p : Int)
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hy hc
  have hts1 := AC.ts_succ (sp := sp) p
  have hslot : sp.slot (tr.time k) = p + 1 :=
    slot_of_mem sp (p + 1) (by rw [htk, hts1]; linarith only [hΔ]) (by
        rw [htk, AC.ts_succ, hts1]; linarith only [hΔ])
  have hrsy : ∀ q ≤ k, tr.RestartAt y q → tr.time q ≤ gbar g := fun q hq hrq =>
    hrs y hy q hrq ((hr.time_mono hq).trans hkb)
  have hj := joined_state_of_restarts hS.run.toU.localRun hS.run.vstart hy k fun q hq hrq =>
    (hrsy q hq.le hrq).trans (by
      rw [hslot, show (((p + 1 : Nat) : Int) - 1) = p by push_cast; ring]; linarith only [hp4, hΔ])
  have hsplit : (K.committee p ∩ H).ncard + (K.committee p ∩ Hᶜ).ncard = sp.committeeSize := by
    rw [← hS.hsize p]
    exact Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _ (Set.toFinite _)
  have hf := hS.cs2 p (by linarith) (by linarith)
  refine first_update_post_of_members hS.run.toU hexact hy hc hcall htk hj hPt hlocks
    (M := K.committee p) (fun u hu => ?_)
    (by rintro _ ⟨v, hv, rfl⟩; exact hS.hP.1 y hy k p v hv) (by omega) (by omega)
  obtain ⟨i, e, hv, hes, -⟩ := honest_votes_in_slot_before hS hp4 (by linarith)
    (fun z hz r hrt hrz => (hrs z hz r hrz (by linarith)).trans (by linarith)) u hu.2 hu.1
  obtain ⟨Hd, hHdt, hHdr, hHds, hmem, hvst, hbst⟩ := late_vote_held_of_frame_before hS hy hc hp4
    (by rw [htk]; linarith only [hΔ]) hkb
    (fun q hq t _ => Compose.ac_deadline_le_of_restarts
      (fun q' hq' hrq' => (hrsy q' (hq'.trans hq) hrq').trans (by linarith)) t)
    (fun q hq hrq => (hrsy q hq hrq).trans_lt (by linarith)) hu.2 hv hes fun Hd hHd hHdr => by
      rw [hU.1 hHd (hΦU hPt) (hHdr.trans (hexact u hu.2 i e hv hes))]
      exact (hΦ.rooted.2 P hPt).mono hΦU
  obtain ⟨hval, -⟩ := castAt_spec hr hu.2 ⟨hv.choose_spec.1, hv.choose_spec.2⟩
  exact ⟨e.msg, hmem, hval, resolutionTime_lt_of hΦ hHdt hHdr (hes ▸ hHds) hvst hbst⟩

/-- **A result passing the fast test is its own fast selection**: the path of `P` holds only
non-genesis ancestors of `P` (no strict descendant), `P` is in the selection set (not genesis,
passing the fast test), and every other member is a strict ancestor, so shallower. -/
theorem fastSelect_eq_result {A : ACState sp.n} {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {p : Nat}
    {P : Blk sp.n FGP} (hPt : P ∈ Φ.tree) (hPg : P.root ≠ sp.genesisRoot)
    (hf : FastTest sp A Φ p P) : fastSelect sp A Φ p P = some P := by
  have hS : {B | B ∈ confirmationPath sp Φ P ∧ FastTest sp A Φ p B} ⊆ Φ.tree :=
    fun B hB => hB.1.1
  have hPS : P ∈ {B | B ∈ confirmationPath sp Φ P ∧ FastTest sp A Φ p B} :=
    ⟨⟨hPt, hPg, .refl⟩, hf⟩
  obtain ⟨D, hD⟩ := exists_deepest hΦ hS ⟨P, hPS⟩
  have hDP := (deepest_mem hD).1.1.2.2
  have hPD := anc_deepest hΦ hS (fun B hB C hC => anc_total hΦ.coherent hB.1.2.2 hC.1.2.2) hD P hPS
  unfold fastSelect
  rw [hD, Anc.antisymm hΦ.coherent hDP hPD]

end Consensus.Goldilocks.AC

end

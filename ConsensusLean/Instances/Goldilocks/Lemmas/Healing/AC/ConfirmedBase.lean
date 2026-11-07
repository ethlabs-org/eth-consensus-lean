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

The first part of the helpers of `proposal_confirmed` (`Confirmed`): the late honest votes held
at a call, `proposal_mem_tree`, the comparison of honest votes and locks with `P`
(`lock_compatible`, `liveLock_compatible`) and the first update at `t_p + 6Δ`
(`first_update_post`, `first_update_record`). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g : Time} {proposer : Nat → Fin sp.n}

/-- Finite message service retains an actual honest vote with its strict early stamp.
Only deadlines and restarts through the receiving call are used. -/
theorem late_vote_pool_before {b : Time} (hS : HealthyBaseUpTo tr H U proposer g b)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ell : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y j ell) {s : Nat}
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
        rw [SA.ts_succ]; linarith only [hti, hti0, hqT])
  have hxH : e.msg.val ∈ H := hval ▸ hx
  have hheld : e.msg ∈ (tr.state y (q + 1)).pool s := by
    rcases held_of_processAt hr hy hproc (by rw [hqs, hes]; omega) (by rw [hqs, hes]) with
      h | ⟨v, hv, w, hw, hne, hvval, hwval⟩
    · rwa [hes] at h
    · exfalso
      rw [hes] at hv hw
      obtain ⟨iv, -, ev, hev, rfl⟩ := hS.run.honest.pool_vote y hy (q + 1) s _ hv (hvval ▸ hxH)
      obtain ⟨iw, -, ew, hew, rfl⟩ := hS.run.honest.pool_vote y hy (q + 1) s _ hw (hwval ▸ hxH)
      have hsv := state_pool_slot sp hr hy (q + 1) s _ hv
      have hsw := state_pool_slot sp hr hy (q + 1) s _ hw
      rw [hvval] at hev
      rw [hwval] at hew
      obtain ⟨-, rfl⟩ := (one_vote_per_slot sp) FGP ro H U tr hr _ hxH iv iw ev ew hev hew
        (hsv.trans hsw.symm)
      exact hne rfl
  intro c hcj
  have hst := stamp_lt_of_held_of_run hr hy (a := q + 1) (b := c) (by omega)
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
theorem late_vote_readPoint_before {b : Time} (hS : HealthyBaseUpTo tr H U proposer g b)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ell : ACLabel (goldilocksSA sp FGP ro)} {e' : Em sp FGP}
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
theorem acceptedBefore_ancestor (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ell)
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
theorem late_vote_accepted_of_frame_before {b : Time} (hS : HealthyBaseUpTo tr H U proposer g b)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ell : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y j ell) {s : Nat}
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
  have hstamp := blockStamp_lt_of_acceptedBefore sp hr hy hc hBy hAB
    (fun k hk hrs => lt_trans (hrestart k (by omega) hrs) (by linarith only [hDelta])) (Or.inl ht)
  exact ⟨B, hBy, hBr, hBs, hpool.1, hpool.2, hBr ▸ hstamp, hAB⟩

/-- Guarded finite acceptance service resolves the head of an actual honest vote before
the same strict deadline as its message. The output is at the observing pre-state. -/
theorem late_vote_held_of_frame_before {b : Time} (hS : HealthyBaseUpTo tr H U proposer g b)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ell : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y j ell) {s : Nat}
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
theorem honest_batch_carry_before {b : Time} (hS : HealthyBaseUpTo tr H U proposer g b)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ell : ACLabel (goldilocksSA sp FGP ro)} {e' : Em sp FGP}
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

/-- `late_vote_pool` with the unlock given. -/
theorem late_vote_poolU
    {u : Nat → Set Lock} (hS : HealthyBaseU u tr H U proposer g) {y : Fin sp.n} (hy : y ∈ H)
        {j : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y j ℓ) {s : Nat}
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
  obtain ⟨k', hk'j, hik', hproc, hk'dl⟩ := hS.healthy.1 x hx i e.msg
    ⟨ℓx, hcx, Or.inl ⟨e, hex, rfl⟩⟩ y hy j ℓ hc (by rw [hmax]; linarith only [hdl j, ht, hti])
  rw [hmax] at hk'dl
  have hk'T : tr.time k' < sp.ts s + 2 * sp.Δ := by linarith only [hdl k', hti, hk'dl]
  have hk'j' : k' < j := lt_of_le_of_ne hk'j (by rintro rfl; linarith only [hk'T, ht])
  have hsl' : sp.slot (tr.time k') = s :=
    slot_of_mem sp s (by linarith only [hti', hik']) (by
        rw [SA.ts_succ]; linarith only [hti, hti', hk'T])
  have hxH : e.msg.val ∈ H := hval ▸ hx
  have hheld : e.msg ∈ (tr.state y (k' + 1)).pool s := by
    rcases held_of_processAtU hr hy hproc (by rw [hsl', hes]; omega) (by rw [hsl', hes]) with
      h | ⟨a, ha, b, hb, hab, hav, hbv⟩
    · rwa [hes] at h
    · exfalso
      rw [hes] at ha hb
      obtain ⟨ja, -, ea, hva, rfl⟩ := hS.run.honest.pool_vote y hy (k' + 1) s _ ha (hav ▸ hxH)
      obtain ⟨jb, -, eb, hvb, rfl⟩ := hS.run.honest.pool_vote y hy (k' + 1) s _ hb (hbv ▸ hxH)
      have hsa := state_pool_slotU sp hr hy (k' + 1) s _ ha
      have hsb := state_pool_slotU sp hr hy (k' + 1) s _ hb
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

/-- **A late honest vote is held**: for a slot `s ≥ r` and an honest call at a time
`≥ t_s + 2Δ`, every honest slot-`s` vote is held, with a stamp before `t_s + 2Δ`, before and after
the call. -/
theorem late_vote_pool (hS : HealthyBase tr H U proposer g) {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y j ℓ) {s : Nat}
    (hs : gbar g + 4 * sp.Δ ≤ sp.ts s) (ht : sp.ts s + 2 * sp.Δ ≤ tr.time j) {x : Fin sp.n}
    (hx : x ∈ H) {i : Nat} {e : Em sp FGP} (hv : VoteAt tr x i e) (hes : e.msg.slot = s) :
    ∀ c, (c = j ∨ c = j + 1) → e.msg ∈ (tr.state y c).pool s ∧
      (tr.state y c).voteStamp e.msg < ETime.of (sp.ts s + 2 * sp.Δ) :=
  late_vote_poolU (hS := hS.toU) (y := y) (hy := hy) (j := j) (ℓ := ℓ) (hc := hc) (s := s)
      (hs := hs) (ht := ht) (x := x) (hx := hx) (i := i) (e := e) (hv := hv) (hes := hes)

/-- `late_vote_held_of_frame` with the unlock given. -/
theorem late_vote_held_of_frameU
    {u : Nat → Set Lock} (hS : HealthyBaseU u tr H U proposer g) {y : Fin sp.n} (hy : y ∈ H)
    {j : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y j ℓ) {s : Nat}
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
        obtain ⟨ka, hkaj, hacc', hlt⟩ := hS.healthy.2.1 x hx kh Hx hacc hgk y hy j ℓ hc
          (by linarith only [hS.deadline_le hy j (tr.time kh), ht, hmx]) hF
        exact ⟨ka, hkaj, hacc', by linarith only [hS.deadline_le hy ka (tr.time kh), hmx, hlt]⟩
      · obtain ⟨ka, hkaj, hacc', hlt⟩ := hS.catchUp x hx kh Hx hacc
          (lt_of_lt_of_le (not_le.1 hgk) (le_gbar g)) y hy j ℓ hc (by linarith only [hs, ht, hΔ]) hF
        exact ⟨ka, hkaj, hacc', by linarith only [hs, hΔ, hlt]⟩
    exact ⟨mem_tree_of_acceptAtU sp hr hy hacc' hkaj hc hF, Or.inr ⟨ka, hacc', hlt⟩⟩
  have hbs := blockStamp_lt_of_acceptedBeforeU sp hr hy hc hHt hAB
    (fun k _ hrk => lt_of_le_of_lt (hS.restart_le hy hrk) (by linarith only [hs, hΔ])) (Or.inl ht)
  have hpost : (tr.state y (j + 1)).blockStamp Hx.root = (tr.state y j).blockStamp Hx.root := by
    have hst : tr.state y (j + 1) = tr.post j := by simp [Trace.state, hc.1, hc.2]
    have he := hr.exec j ℓ hc.2 (hc.1 ▸ hy)
    rw [hc.1] at he
    have hp' : tr.post j =
        (stepWith sp ro y (u j) (tr.state y j) ℓ.frame (tr.time j) ℓ.call).1 := by
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

/-- **A late honest batch** (also for H.2 (ii)): for a slot `s ≥ r` and an honest call at a time
`≥ t_s + 2Δ` whose `Φ.F` the vote's head extends, every honest slot-`s` vote is held, with its
head in the call's frame (of slot at most `s`), and both its stamp and its head's are before
`t_s + 2Δ`, before and after the call. -/
theorem late_vote_held_of_frame (hS : HealthyBase tr H U proposer g) {y : Fin sp.n} (hy : y ∈ H)
    {j : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y j ℓ) {s : Nat}
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
theorem resolutionTime_lt_of {A : SAState sp.n} {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
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

/-- `proposal_mem_tree` with the unlock given. -/
theorem proposal_mem_treeU
    {u : Nat → Set Lock} (hS : StandaloneRunU u tr H U proposer g) {p : Nat} {P : Blk sp.n FGP}
    (hpH : proposer p ∈ H) (hP : HonestProposalU u tr (proposer p) p P)
    (hpg : gbar g ≤ sp.ts p) {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y j ℓ)
    (ht : sp.ts p + sp.Δ ≤ tr.time j) :
    P ∈ ℓ.frame.tree ∧ ∃ ka ≤ j, tr.AcceptAt y ka P ∧ tr.time ka < sp.ts p + sp.Δ := by
  have hr := hS.run.localRun
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, j₀, -, ⟨ℓ₀, hc₀, hcall₀⟩, htj₀⟩ := hP
  obtain ⟨hΦ₀, hΦ₀U⟩ := frameIn_of_callAtU hr hpH hc₀
  have hP₀ := (accept_newU sp hr hpH ⟨ℓ₀, hc₀, hcall₀⟩).1 ℓ₀ hc₀
  have hF : Anc U ℓ.frame.F P := by
    rw [trivial_F_eqU hS hy hpH hc hc₀]; exact (hΦ₀.rooted.2 P hP₀).mono hΦ₀U
  have hmax : max (sp.ts p) (gbar g) = sp.ts p := max_eq_left hpg
  obtain ⟨ka, hkaj, hacc, hlt⟩ := hS.healthy.2.1 _ hpH j₀ P ⟨ℓ₀, hc₀, hcall₀⟩
    (by rw [htj₀]; exact (le_gbar g).trans hpg) y hy j ℓ hc
    (by
        rw [htj₀]; have := hS.deadline_le hy j
            (sp.ts p); rw [hmax] at this; linarith only [ht, this]) hF
  have hdl := hS.deadline_le hy ka (tr.time j₀)
  rw [htj₀, hmax] at hdl
  rw [htj₀] at hlt
  refine ⟨?_, ka, hkaj, hacc, by linarith only [hlt, hdl]⟩
  rw [(hS.trivial y hy j ℓ hc).2.2.2]
  exact Set.mem_insert_of_mem _ ⟨ka, hkaj, hacc⟩

/-- **The proposal is relayed**: an honest proposal `P` of slot `p` (with `ḡ ≤ t_p`) is in the
frame of every honest call from `t_p + Δ` on, accepted before `t_p + Δ`. -/
theorem proposal_mem_tree (hS : StandaloneRun tr H U proposer g) {p : Nat} {P : Blk sp.n FGP}
    (hpH : proposer p ∈ H) (hP : HonestProposal tr (proposer p) p P)
    (hpg : gbar g ≤ sp.ts p) {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y j ℓ)
    (ht : sp.ts p + sp.Δ ≤ tr.time j) :
    P ∈ ℓ.frame.tree ∧ ∃ ka ≤ j, tr.AcceptAt y ka P ∧ tr.time ka < sp.ts p + sp.Δ :=
  proposal_mem_treeU (hS := hS.toU) (p := p) (P := P) (hpH := hpH) (hP := hP.toU) (hpg := hpg)
      (y := y) (hy := hy) (j := j) (ℓ := ℓ) (hc := hc) (ht := ht)

/-! ## Honest votes and comparison with `P` -/

/-- `honest_not_equivocator_pool` with the unlock given. -/
theorem honest_not_equivocator_poolU
    {uL : Nat → Set Lock} (hS : HealthyBaseU uL tr H U proposer g)
    {y : Fin sp.n} (hy : y ∈ H)
    (c s : Nat) {u : Fin sp.n} (hu : u ∈ H) :
    u ∉ equivocators {v | v ∈ (tr.state y c).pool s} := by
  have hr := hS.run.localRun
  rintro ⟨a, ha, b, hb, hab, rfl, hbv⟩
  obtain ⟨ja, -, ea, hva, rfl⟩ := hS.run.honest.pool_vote y hy c s _ ha hu
  obtain ⟨jb, -, eb, hvb, rfl⟩ := hS.run.honest.pool_vote y hy c s _ hb (hbv ▸ hu)
  rw [hbv] at hvb
  obtain ⟨-, rfl⟩ := (one_vote_per_slotU sp) FGP ro H U tr hr _ hu ja jb ea eb hva hvb
    ((state_pool_slotU sp hr hy c s _ ha).trans (state_pool_slotU sp hr hy c s _ hb).symm)
  exact hab rfl

/-- An honest validator is not an equivocator in an honest node's pool of a slot. -/
theorem honest_not_equivocator_pool (hS : HealthyBase tr H U proposer g)
    {y : Fin sp.n} (hy : y ∈ H)
    (c s : Nat) {u : Fin sp.n} (hu : u ∈ H) :
    u ∉ equivocators {v | v ∈ (tr.state y c).pool s} :=
  honest_not_equivocator_poolU (hS := hS.toU) (y := y) (hy := hy) (c := c) (s := s) (u := u)
      (hu := hu)

/-- A block extended by an honest vote of a slot `≥ p` compares with `P` (whose extension by every
such vote is `hvotes`). -/
theorem compatible_of_vote {p : Nat} {P : Blk sp.n FGP} (hU : Coherent U)
    (hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P)
    {z : Fin sp.n} (hz : z ∈ H) {j : Nat} {e : Em sp FGP} (hv : VoteAt tr z j e)
    (hps : p ≤ e.msg.slot) {B : Blk sp.n FGP} (hB : VoteExtends U e.msg B) : Compatible U B P := by
  obtain ⟨Hd, hHd, hHdr, hBHd⟩ := hB
  obtain ⟨Hd', hHd', hHd'r, hPHd'⟩ := hvotes z hz j e hv hps
  obtain rfl : Hd = Hd' := hU.1 hHd hHd' (hHdr.trans hHd'r.symm)
  exact anc_total hU hBHd hPHd'

/-- `two_faulty_lt_honest` with the unlock given. -/
theorem two_faulty_lt_honestU
    {u : Nat → Set Lock} (hS : HealthyBaseU u tr H U proposer g) : 2 * Hᶜ.ncard < H.ncard := by
  have := hS.healthy.2.2.2
  have hn : H.ncard + Hᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have := sp.toParams.hn
  change 1 ≤ sp.n at this
  omega

/-- The honest validators are more than twice the faulty ones. -/
theorem two_faulty_lt_honest (hS : HealthyBase tr H U proposer g) : 2 * Hᶜ.ncard < H.ncard :=
  two_faulty_lt_honestU (hS := hS.toU)

/-- `result_extended` with the unlock given. -/
theorem result_extendedU
    {uL : Nat → Set Lock} (hS : HealthyBaseU uL tr H U proposer g) {s : Nat}
    (hs : gbar g + 4 * sp.Δ ≤ sp.ts s) {x : Fin sp.n} (hx : x ∈ H) {c : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x c ℓ)
    (ht : sp.ts s + 2 * sp.Δ ≤ tr.time c) {C : Blk sp.n FGP}
    (hC : getConfirmation sp (tr.state x c) ℓ.frame s = some C) :
    ∃ z ∈ H, ∃ j e, VoteAt tr z j e ∧ e.msg.slot = s ∧ VoteExtends U e.msg C := by
  have hr := hS.run.localRun
  obtain ⟨-, hΦU⟩ := frameIn_of_callAtU hr hx hc
  have hmaj := (deepest_mem hC).1.2.2
  unfold confirmationScore at hmaj
  dsimp only at hmaj
  have hHv : H ⊆ voters {v | v ∈ (tr.state x c).pool s} := by
    intro u hu
    obtain ⟨j, e, hv, hes⟩ := honest_votes_in_slotU hS hs u hu
    obtain ⟨hval, -⟩ := castAt_specU hr hu ⟨hv.choose_spec.1, hv.choose_spec.2⟩
    exact ⟨e.msg, (late_vote_poolU hS hx hc hs ht hu hv hes c (Or.inl rfl)).1, hval⟩
  have h1 := Set.ncard_le_ncard hHv
  have h2 := two_faulty_lt_honestU hS
  obtain ⟨u, ⟨-, v, ⟨hvp, -⟩, rfl, -, R, hR, hRr, hCR⟩, hu⟩ :=
    Set.exists_mem_notMem_of_ncard_lt_ncard (s := Hᶜ)
      (t := supporters ℓ.frame ⟨{v | v ∈ (tr.state x c).pool s}, {v | v ∈ (tr.state x c).pool s ∧
        resolutionTime (tr.state x c) ℓ.frame v < ETime.of (sp.ts s + 2 * sp.Δ)}⟩ s C)
      (by omega)
  have huH : v.val ∈ H := not_not.1 hu
  obtain ⟨j', -, e', hve, rfl⟩ := hS.run.honest.pool_vote x hx c s _ hvp huH
  exact ⟨_, huH, j', e', hve, state_pool_slotU sp hr hx c s _ hvp, R, hΦU hR, hRr,
    Anc.mono hΦU hCR⟩

/-- **A late result has an honest supporter**: the result `C` of an honest update of a slot
`s ≥ r` (read at a time `≥ t_s + 2Δ`) is extended by an honest vote of slot `s`: its supporters
are a strict majority of the voters, which include all honest validators. -/
theorem result_extended (hS : HealthyBase tr H U proposer g) {s : Nat}
    (hs : gbar g + 4 * sp.Δ ≤ sp.ts s) {x : Fin sp.n} (hx : x ∈ H) {c : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x c ℓ)
    (ht : sp.ts s + 2 * sp.Δ ≤ tr.time c) {C : Blk sp.n FGP}
    (hC : getConfirmation sp (tr.state x c) ℓ.frame s = some C) :
    ∃ z ∈ H, ∃ j e, VoteAt tr z j e ∧ e.msg.slot = s ∧ VoteExtends U e.msg C :=
  result_extendedU (hS := hS.toU) (s := s) (hs := hs) (x := x) (hx := hx) (c := c) (ℓ := ℓ)
      (hc := hc) (ht := ht) (C := C) (hC := hC)

/-- `origin_compatible_proposal` with the unlock given. -/
theorem origin_compatible_proposalU
    {u : Nat → Set Lock} (hS : StandaloneRunU u tr H U proposer g)
    {p : Nat} {P : Blk sp.n FGP}
    (hp : gbar g + 4 * sp.Δ ≤ sp.ts p)
    (hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P)
    {x : Fin sp.n} (hx : x ∈ H) {j s : Nat} {B : Blk sp.n FGP} (hps : p ≤ s)
    (horig : (∃ CV, FastLockAt tr x j s B CV) ∨ SlowLockAt tr x j s B) : Compatible U B P := by
  have hr := hS.run.localRun
  have hU := hr.coherent
  have hs : gbar g + 4 * sp.Δ ≤ sp.ts s := hp.trans ((ts_le_iff sp).2 (by omega))
  rcases horig with ⟨CV, hfl⟩ | ⟨ℓ', C, hupd, hC, hB⟩
  · obtain ⟨z, hz, j', e, hv, hes, hext⟩ := fastLock_honest_voteU hS.run hS.two_faulty_lt hx hfl
    exact compatible_of_vote hU hvotes hz hv (hes ▸ hps) hext
  · obtain ⟨-, hΦU⟩ := frameIn_of_callAtU hr hx hupd.1
    have hBC : ℓ'.frame.Anc B C := (deepest_mem hB).1.1.2.2
    obtain ⟨z, hz, j', e, hv, hes, Hd, hHd, hHdr, hCHd⟩ :=
      result_extendedU hS.toHealthyBaseU hs hx hupd.1
        (by rw [hupd.2.2.1]; linarith only [sp.toParams.hΔ]) hC
    exact compatible_of_vote hU hvotes hz hv (hes ▸ hps)
      ⟨Hd, hHd, hHdr, (Anc.mono hΦU hBC).trans hCHd⟩

/-- **A lock origin of a slot `≥ p` compares with `P`** (`l ≥ p`): an honest fast lock
through an honest counted vote; an honest slow lock through an honest supporter of its update's
result (not its fast test). -/
theorem origin_compatible_proposal (hS : StandaloneRun tr H U proposer g)
    {p : Nat} {P : Blk sp.n FGP}
    (hp : gbar g + 4 * sp.Δ ≤ sp.ts p)
    (hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P)
    {x : Fin sp.n} (hx : x ∈ H) {j s : Nat} {B : Blk sp.n FGP} (hps : p ≤ s)
    (horig : (∃ CV, FastLockAt tr x j s B CV) ∨ SlowLockAt tr x j s B) : Compatible U B P :=
  origin_compatible_proposalU (hS := hS.toU) (p := p) (P := P) (hp := hp) (hvotes := hvotes)
      (x := x) (hx := hx) (j := j) (s := s) (B := B) (hps := hps) (horig := horig)

private theorem compatible_down {B L P : Blk sp.n FGP} (hU : Coherent U) (hLB : Anc U L B)
    (h : Compatible U B P) : Compatible U L P := by
  rcases h with h | h
  · exact Or.inl (hLB.trans h)
  · exact anc_total hU hLB h

/-- `lock_compatible_core` with the unlock given. -/
theorem lock_compatible_coreU
    {u : Nat → Set Lock} (hS : StandaloneRunU u tr H U proposer g) {p : Nat}
    {P : Blk sp.n FGP}
    (hp4 : gbar g + 4 * sp.Δ ≤ sp.ts p)
    (hset : LocksSettledU u tr H U (sp.ts p - 4 * sp.Δ))
    (hexact : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root)
    (hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P)
    (hPU : P ∈ U) {y : Fin sp.n} (hy : y ∈ H) {j : Nat} (htj : sp.ts p + 6 * sp.Δ ≤ tr.time j)
    {c : Nat} (hcj : c = j ∨ c = j + 1) {l : Lock} (hl : l ∈ (tr.state y c).locks)
    (hlive : sp.slot (tr.time j) ≤ l.slot + sp.k) {L : Blk sp.n FGP} (hL : L ∈ U)
    (hLr : L.root = l.block) : Compatible U L P := by
  have hr := hS.run.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  have hΘ := Θ_nonneg sp
  -- labels `≥ p`: by the origin, at any cut
  have hge : ∀ c' (l' : Lock), l' ∈ (tr.state y c').locks → p ≤ l'.slot → ∀ L' ∈ U,
      L'.root = l'.block → Compatible U L' P := by
    intro c' l' hl' hpl L' hL' hL'r
    cases hf : l'.fast
    · obtain ⟨j', -, B, hsl, L₁, hL₁, hL₁r, hL₁B⟩ := slow_lock_provenanceU hr hy c' l' hl' hf
      obtain rfl : L₁ = L' := hU.1 hL₁ hL' (hL₁r.trans hL'r.symm)
      exact compatible_down hU hL₁B
        (origin_compatible_proposalU hS hp4 hvotes hy hpl (Or.inr hsl))
    · obtain ⟨j', -, B, CV, hfl, L₁, hL₁, hL₁r, hL₁B⟩ := fast_lock_provenanceU hr hy c' l' hl' hf
      obtain rfl : L₁ = L' := hU.1 hL₁ hL' (hL₁r.trans hL'r.symm)
      exact compatible_down hU hL₁B
        (origin_compatible_proposalU hS hp4 hvotes hy hpl (Or.inl ⟨CV, hfl⟩))
  -- labels `< p` before the call: `hset` and an honest slot-`p` vote, which is `P`
  have hlt : ∀ l' ∈ (tr.state y j).locks, l'.slot < p → sp.slot (tr.time j) ≤ l'.slot + sp.k →
      ∀ L' ∈ U, L'.root = l'.block → Compatible U L' P := by
    intro l' hl' hpl hlive' L' hL' hL'r
    obtain ⟨hve, -⟩ := locksSettledU_iff.1 hset y hy j (by
        linarith only [htj, hΔ]) l' hl' hlive' L' hL' hL'r
    obtain ⟨x, hx⟩ : H.Nonempty :=
      Set.nonempty_of_ncard_ne_zero (by have := two_faulty_lt_honestU hS.toHealthyBaseU; omega)
    obtain ⟨i, e, hv, hes⟩ := honest_votes_in_slotU hS.toHealthyBaseU hp4 x hx
    obtain ⟨Hd, hHd, hHdr, hLHd⟩ := votesExtendAfter_iff.1 hve x hx i e hv (by omega)
    obtain rfl : Hd = P := hU.1 hHd hPU (hHdr.trans (hexact x hx i e hv hes))
    exact Or.inl hLHd
  by_cases hpl : p ≤ l.slot
  · exact hge c l hl hpl L hL hLr
  rw [not_le] at hpl
  rcases hcj with rfl | rfl
  · exact hlt l hl hpl hlive L hL hLr
  -- after the call: a lock of a label `< p` sits below one held before (no write of it)
  have hsl : p + 1 ≤ sp.slot (tr.time j) := by
    have := (ts_le_iff_le_slot sp (hr.time_nonneg j) (p + 1 : Nat)).1
      (by simp only [SAParams.ts] at htj ⊢; push_cast; linarith only [htj, hΔ])
    exact_mod_cast this
  rcases lock_provenance_fromU hr hy (Nat.le_succ j) l hl with
    ⟨l', hl', hs', hb⟩ | ⟨j', hj1, hj2, B, hw, -⟩
  · rcases hb with rfl | ⟨L₁, hL₁, hL₁r, L', hL', hL'r, hL₁L'⟩
    · exact hlt l' hl' hpl hlive L hL hLr
    · obtain rfl : L₁ = L := hU.1 hL₁ hL (hL₁r.trans hLr.symm)
      exact compatible_down hU hL₁L' (hlt l' hl' (hs' ▸ hpl) (hs' ▸ hlive) L' hL' hL'r)
  · obtain rfl : j' = j := by omega
    exfalso
    rcases hw with ⟨CV, ℓ', A, -, hsl', -⟩ | ⟨ℓ', -, -, hu, -⟩
    · omega
    · have h1 : sp.ts l.slot + 6 * sp.Δ < sp.ts p + 6 * sp.Δ := by
        have := (ts_lt_iff sp).2 (show (l.slot : Int) < p by exact_mod_cast hpl)
        linarith only [this]
      linarith only [htj, hu, h1]

/-- **Every stored lock compares with `P`**, at the state before an honest call at a
time `t ≥ t_{p−1}` (`hset`) and, for a call at `t ≥ t_p + 6Δ`, also after it, for the locks live
at `t`: of a label `< p` by `hset` and the exact slot-`p` votes (a lock written by the call has a
label `≥ p`); of a label `≥ p` by its origin. -/
theorem lock_compatible_core (hS : StandaloneRun tr H U proposer g) {p : Nat}
    {P : Blk sp.n FGP}
    (hp4 : gbar g + 4 * sp.Δ ≤ sp.ts p)
    (hset : LocksSettled tr H U (sp.ts p - 4 * sp.Δ))
    (hexact : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root)
    (hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P)
    (hPU : P ∈ U) {y : Fin sp.n} (hy : y ∈ H) {j : Nat} (htj : sp.ts p + 6 * sp.Δ ≤ tr.time j)
    {c : Nat} (hcj : c = j ∨ c = j + 1) {l : Lock} (hl : l ∈ (tr.state y c).locks)
    (hlive : sp.slot (tr.time j) ≤ l.slot + sp.k) {L : Blk sp.n FGP} (hL : L ∈ U)
    (hLr : L.root = l.block) : Compatible U L P :=
  lock_compatible_coreU (hS := hS.toU) (p := p) (P := P) (hp4 := hp4) (hset := hset.toU)
      (hexact := hexact) (hvotes := hvotes) (hPU := hPU) (y := y) (hy := hy) (j := j) (htj := htj)
          (c := c) (hcj := hcj) (l := l) (hl := hl) (hlive := hlive) (L := L) (hL := hL)
              (hLr := hLr)

/-- `lock_compatible_core` from `t_p ≥ ḡ + 2Θ + 8Δ`. -/
theorem lock_compatible (hS : StandaloneRun tr H U proposer g) {p : Nat} {P : Blk sp.n FGP}
    (hp : gbar g + 2 * Θ sp + 8 * sp.Δ ≤ sp.ts p)
    (hset : LocksSettled tr H U (sp.ts p - 4 * sp.Δ))
    (hexact : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root)
    (hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P)
    (hPU : P ∈ U) {y : Fin sp.n} (hy : y ∈ H) {j : Nat} (htj : sp.ts p + 6 * sp.Δ ≤ tr.time j)
    {c : Nat} (hcj : c = j ∨ c = j + 1) {l : Lock} (hl : l ∈ (tr.state y c).locks)
    (hlive : sp.slot (tr.time j) ≤ l.slot + sp.k) {L : Blk sp.n FGP} (hL : L ∈ U)
    (hLr : L.root = l.block) : Compatible U L P :=
  lock_compatible_core hS (by linarith only [hp, sp.toParams.hΔ, Θ_nonneg sp])
    hset hexact hvotes hPU hy htj hcj hl hlive hL hLr

/-- `liveLock_compatible_core` with the unlock given. -/
theorem liveLock_compatible_coreU
    {u : Nat → Set Lock} (hS : StandaloneRunU u tr H U proposer g) {p : Nat}
    {P : Blk sp.n FGP}
    (hp4 : gbar g + 4 * sp.Δ ≤ sp.ts p)
    (hset : LocksSettledU u tr H U (sp.ts p - 4 * sp.Δ))
    (hexact : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root)
    (hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P)
    (hPU : P ∈ U) {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt y j ℓ) (htj : sp.ts p + 6 * sp.Δ ≤ tr.time j) {c : Nat}
    (hcj : c = j ∨ c = j + 1) :
    ∀ L ∈ liveLockBlocks sp (tr.state y c).locks ℓ.frame (tr.time j), Compatible U L P := by
  have hr := hS.run.localRun
  have hU := hr.coherent
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hy hc
  rintro L ⟨hLt, l', ⟨l, hl, B, hB, hBr, hlive, rfl⟩, hLr⟩
  have hva : ℓ.frame.Anc (ℓ.frame.viableAncestor B) B := anc_viableAncestor ℓ.frame B
  obtain rfl : L = ℓ.frame.viableAncestor B :=
    hΦ.coherent.1 hLt (mem_of_anc hva hB) hLr.symm
  exact compatible_down hU (hva.mono hΦU)
    (lock_compatible_coreU hS hp4 hset hexact hvotes hPU hy htj hcj hl
      (le_trans hlive ((locksWF_stateU hr hy c).cap hl)) (L := B) (hΦU hB) hBr)

/-- **Every live lock block compares with `P`** at the state before (for a call at `t ≥ t_{p−1}`)
or after (for a call at `t ≥ t_p + 6Δ`) an honest call, read at that call's frame and time. -/
theorem liveLock_compatible_core (hS : StandaloneRun tr H U proposer g) {p : Nat}
    {P : Blk sp.n FGP}
    (hp4 : gbar g + 4 * sp.Δ ≤ sp.ts p)
    (hset : LocksSettled tr H U (sp.ts p - 4 * sp.Δ))
    (hexact : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root)
    (hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P)
    (hPU : P ∈ U) {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt y j ℓ) (htj : sp.ts p + 6 * sp.Δ ≤ tr.time j) {c : Nat}
    (hcj : c = j ∨ c = j + 1) :
    ∀ L ∈ liveLockBlocks sp (tr.state y c).locks ℓ.frame (tr.time j), Compatible U L P :=
  liveLock_compatible_coreU (hS := hS.toU) (p := p) (P := P) (hp4 := hp4) (hset := hset.toU)
      (hexact := hexact) (hvotes := hvotes) (hPU := hPU) (y := y) (hy := hy) (j := j) (ℓ := ℓ)
          (hc := hc) (htj := htj) (c := c) (hcj := hcj)

/-- `liveLock_compatible_core` from `t_p ≥ ḡ + 2Θ + 8Δ`. -/
theorem liveLock_compatible (hS : StandaloneRun tr H U proposer g) {p : Nat} {P : Blk sp.n FGP}
    (hp : gbar g + 2 * Θ sp + 8 * sp.Δ ≤ sp.ts p)
    (hset : LocksSettled tr H U (sp.ts p - 4 * sp.Δ))
    (hexact : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root)
    (hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P)
    (hPU : P ∈ U) {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt y j ℓ) (htj : sp.ts p + 6 * sp.Δ ≤ tr.time j) {c : Nat}
    (hcj : c = j ∨ c = j + 1) :
    ∀ L ∈ liveLockBlocks sp (tr.state y c).locks ℓ.frame (tr.time j), Compatible U L P :=
  liveLock_compatible_core hS (by linarith only [hp, sp.toParams.hΔ, Θ_nonneg sp])
    hset hexact hvotes hPU hy hc htj hcj

/-! ## The first update at `t_p + 6Δ` -/

/-- `first_update_post` with the unlock given. -/
theorem first_update_postU
    {uL : Nat → Set Lock} (hS : HealthyBaseU uL tr H U proposer g) {p : Nat} {P : Blk sp.n FGP}
    (hp4 : gbar g + 4 * sp.Δ ≤ sp.ts p)
    (hexact : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt y k ℓ) (hcall : ℓ.call = .tick) (htk : tr.time k = sp.ts p + 6 * sp.Δ)
    (hPt : P ∈ ℓ.frame.tree)
    (hlocks : ∀ L ∈ liveLockBlocks sp (tr.state y k).locks ℓ.frame (tr.time k),
      Compatible U L P) :
    getConfirmation sp (tr.state y k) ℓ.frame p = some P ∧
      ¬ conflictsWithLock sp (tr.state y k).locks ℓ.frame (tr.time k) P ∧
      FastTest sp (tr.state y k) ℓ.frame p P ∧
      tr.post k = updateConfirmation sp (tr.state y k) ℓ.frame (tr.time k) p := by
  have hr := hS.run.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  have hg0 := gbar_nonneg g
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hy hc
  have hts1 := SA.ts_succ (sp := sp) p
  have hslot : sp.slot (tr.time k) = p + 1 :=
    slot_of_mem sp (p + 1) (by rw [htk, hts1]; linarith only [hΔ]) (by
        rw [htk, SA.ts_succ, hts1]; linarith only [hΔ])
  have hj := hS.joined_state hy k (by
    rw [hslot, show (((p + 1 : Nat) : Int) - 1) = p by push_cast; ring]; linarith only [hp4, hΔ])
  have hT2 : tr.time k = sp.ts ((p + 1 : Nat) : Int) + 2 * sp.Δ := by rw [htk, hts1]; ring
  -- the tick is the slot-`p` update
  have he := hr.exec k ℓ hc.2 (hc.1 ▸ hy)
  rw [hc.1, hcall] at he
  have hpost : tr.post k = updateConfirmation sp (tr.state y k) ℓ.frame (tr.time k) p := by
    have h1 : tr.post k = (acOnTickWith sp y (uL k) (tr.state y k) ℓ.frame (tr.time k)).1 :=
      (congrArg Prod.fst he).symm
    rw [h1]
    unfold acOnTickWith
    dsimp only
    rw [hslot]
    have hc1 : ¬ tr.time k = sp.ts ((p + 1 : Nat) : Int) + sp.Δ := by
      intro h; linarith only [htk, hΔ, hts1, h]
    have hc2 : (tr.time k = sp.ts ((p + 1 : Nat) : Int) + 2 * sp.Δ ∧ 0 < p + 1) = True :=
      eq_true ⟨hT2, Nat.succ_pos p⟩
    simp only [hj, not_true_eq_false, hc1, hc2, ↓reduceIte, Nat.add_sub_cancel]
  set A := tr.state y k with hA
  -- the honest slot-`p` votes: held, resolved before `t_p + 2Δ`, on `P`, one per validator
  have hhon : ∀ u ∈ H, ∃ v ∈ A.pool p, v.val = u ∧ v.head = P.root ∧
      resolutionTime A ℓ.frame v < ETime.of (sp.ts p + 2 * sp.Δ) ∧
      ∀ v' ∈ A.pool p, v'.val = u → v' = v := by
    intro u hu
    obtain ⟨i, e, hv, hes⟩ := honest_votes_in_slotU hS hp4 u hu
    obtain ⟨Hd, hHdt, hHdr, hHds, hh⟩ := late_vote_held_of_frameU hS hy hc hp4
      (by rw [htk]; linarith only [hΔ]) hu hv hes fun Hd hHd hHdr => by
        rw [hU.1 hHd (hΦU hPt) (hHdr.trans (hexact u hu i e hv hes))]
        exact (hΦ.rooted.2 P hPt).mono hΦU
    obtain ⟨hmem, hvst, hbst⟩ := hh k (Or.inl rfl)
    obtain ⟨hval, -⟩ := castAt_specU hr hu ⟨hv.choose_spec.1, hv.choose_spec.2⟩
    refine ⟨e.msg, hmem, hval, hexact u hu i e hv hes,
      resolutionTime_lt_of hΦ hHdt hHdr (hes ▸ hHds) hvst hbst, fun v' hv' hv'u => ?_⟩
    obtain ⟨j', -, e', hve', rfl⟩ := hS.run.honest.pool_vote y hy k p v' hv' (hv'u ▸ hu)
    rw [hv'u] at hve'
    obtain ⟨-, rfl⟩ := (one_vote_per_slotU sp) FGP ro H U tr hr _ hu j' i e' e hve' hv
      ((state_pool_slotU sp hr hy k p _ hv').trans hes.symm)
    rfl
  have hHvot : H ⊆ voters {v | v ∈ A.pool p} := fun u hu => by
    obtain ⟨v, hv, hvu, -⟩ := hhon u hu
    exact ⟨v, hv, hvu⟩
  have hvle : (voters {v | v ∈ A.pool p}).ncard ≤ sp.n := by
    have := Set.ncard_le_ncard (Set.subset_univ (voters {v | v ∈ A.pool p}))
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  have hHn : H.ncard + Hᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h2f := two_faulty_lt_honestU hS
  have hHle := Set.ncard_le_ncard hHvot
  -- the honest validators support `P`
  have hscore : H.ncard ≤ confirmationScore sp A ℓ.frame p P := by
    unfold confirmationScore
    dsimp only
    have hsub : H ⊆ supporters ℓ.frame ⟨{v | v ∈ A.pool p}, {v | v ∈ A.pool p ∧
        resolutionTime A ℓ.frame v < ETime.of (sp.ts p + 2 * sp.Δ)}⟩ p P := by
      intro u hu
      obtain ⟨v, hv, hvu, hvh, hres, -⟩ := hhon u hu
      refine ⟨honest_not_equivocator_poolU hS hy k p hu, v, ⟨hv, hres⟩, hvu, ?_,
        P, hPt, hvh.symm, Relation.ReflTransGen.refl⟩
      exact_mod_cast state_pool_slotU sp hr hy k p v hv
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
      refine absurd hmaj (not_lt.2 (le_trans (Nat.mul_le_mul_left 2
        (Set.ncard_le_ncard (t := Hᶜ) ?_)) (by omega)))
      rintro u ⟨-, x, ⟨hx, -⟩, rfl, -, R, hR, hRr, hBR⟩ hu
      obtain ⟨v, -, -, hvh, -, huniq⟩ := hhon _ hu
      obtain rfl := huniq x hx rfl
      obtain rfl : R = P := hΦ.coherent.1 hR hPt (hRr.trans hvh)
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

/-- **The first update**: at an honest node's tick at `t_p + 6Δ`, with every honest
slot-`p` vote exactly `P` and every live lock comparing with `P`, the tick is the slot-`p` update,
whose result is `P` (its honest batch is a strict majority, and every other passing block has only
faulty supporters unless it is an ancestor of `P`), not vetoed, and `P` passes the fast test
(the honest batch is half of the committee or more). -/
theorem first_update_post (hS : HealthyBase tr H U proposer g) {p : Nat} {P : Blk sp.n FGP}
    (hp4 : gbar g + 4 * sp.Δ ≤ sp.ts p)
    (hexact : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
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

/-- **A result passing the fast test is its own fast selection**: the path of `P` holds only
non-genesis ancestors of `P` (no strict descendant), `P` is in the selection set (not genesis,
passing the fast test), and every other member is a strict ancestor, so shallower. -/
theorem fastSelect_eq_result {A : SAState sp.n} {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {p : Nat}
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

/-- `first_update_record` with the unlock given. -/
theorem first_update_recordU
    {u : Nat → Set Lock} (hS : HealthyBaseU u tr H U proposer g) {p : Nat} {P : Blk sp.n FGP}
    (hp4 : gbar g + 4 * sp.Δ ≤ sp.ts p)
    (hexact : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt y k ℓ) (hcall : ℓ.call = .tick) (htk : tr.time k = sp.ts p + 6 * sp.Δ)
    (hPt : P ∈ ℓ.frame.tree)
    (hlocks : ∀ L ∈ liveLockBlocks sp (tr.state y k).locks ℓ.frame (tr.time k),
      Compatible U L P) :
    ∃ R ∈ ℓ.frame.tree, R.root = (tr.post k).latestConfirmed ∧ ℓ.frame.Anc P R := by
  obtain ⟨hconf, hnv, -, hpost⟩ :=
    first_update_postU hS hp4 hexact hy hc hcall htk hPt hlocks
  rw [hpost]
  unfold updateConfirmation
  dsimp only
  rw [hconf]
  dsimp only
  simp only [hnv, ↓reduceIte]
  unfold updateLatestConfirmed
  split_ifs with hanc
  · exact hanc
  · exact ⟨P, hPt, rfl, Relation.ReflTransGen.refl⟩

/-- **The first update repairs the record**: at an honest node's tick at `t_p + 6Δ`, with
every honest slot-`p` vote exactly `P` and every live lock comparing with `P`, the slot-`p`
result is `P` and is not vetoed (`first_update_post`), so the record after the tick extends
`P`. -/
theorem first_update_record (hS : HealthyBase tr H U proposer g) {p : Nat} {P : Blk sp.n FGP}
    (hp4 : gbar g + 4 * sp.Δ ≤ sp.ts p)
    (hexact : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt y k ℓ) (hcall : ℓ.call = .tick) (htk : tr.time k = sp.ts p + 6 * sp.Δ)
    (hPt : P ∈ ℓ.frame.tree)
    (hlocks : ∀ L ∈ liveLockBlocks sp (tr.state y k).locks ℓ.frame (tr.time k),
      Compatible U L P) :
    ∃ R ∈ ℓ.frame.tree, R.root = (tr.post k).latestConfirmed ∧ ℓ.frame.Anc P R :=
  first_update_recordU (hS := hS.toU) (p := p) (P := P) (hp4 := hp4) (hexact := hexact) (y := y)
      (hy := hy) (k := k) (ℓ := ℓ) (hc := hc) (hcall := hcall) (htk := htk) (hPt := hPt)
          (hlocks := hlocks)

end Consensus.Goldilocks.SA

end

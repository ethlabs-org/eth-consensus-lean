module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLock
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor

public section

/-! # Goldilocks Healing: the confirmed tip after an honest proposal (T1 §6, H.1 (ii))

The helpers of `proposal_confirmed` (healing-simple `h1-proposal-confirmed.md` §6), over a
`StandaloneRun` (H.1's premises) and an honest proposal `P` of slot `p`:

* `late_vote_held` (§2): at an honest call from `t_s + 2Δ` on (`s ≥ r`), every honest slot-`s`
  vote is held, with its head in the call's frame, both resolved before `t_s + 2Δ`, before and
  after the call;
* `proposal_mem_tree`: `P` is in every honest frame from `t_p + Δ` on;
* `lock_compatible`, `liveLock_compatible` (§3): every lock live at an honest call from
  `t_p + 6Δ` on, before or after it, compares with `P` (labels `< p` by `LocksSettled` and the
  exact slot-`p` votes, labels `≥ p` by their origin's honest supporter,
  `origin_compatible_proposal`);
* `first_update_post`, `first_update_record` (§4): the slot-`p` update at `t_p + 6Δ` has result
  `P`, not vetoed, with `P` passing the fast test, so its own fast selection
  (`fastSelect_eq_result`);
* `record_step`, `record_extends` (§4): from that update on the record extends `P` (a candidate
  compares with `P`, and an ancestor candidate is refused);
* `head_extends` (§5): the head extends `P` (the latest view is of a slot `≥ p + 1` whose honest
  batch is held and resolved);
* `anc_acConfirmed_of_frame` (§5; frame-only, shared with H.2): then the confirmed tip extends
  `P`. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g : Time} {proposer : Nat → Fin sp.n}

private theorem ts_succ' (s : Nat) : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
  simp only [SAParams.ts]; push_cast; ring

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
  have hgi : gbar g ≤ tr.time i := by linarith
  have hdl := hdeadline j le_rfl (tr.time i) hgi
  rw [max_eq_left hti0] at hdl
  obtain ⟨q, hqj, hiq, hproc, hqt⟩ := hS.sync.message x hx i e.msg
    ⟨ellx, hcx, Or.inl ⟨e, hex, rfl⟩⟩ hgi y hy j ell hc
    (by linarith) (by linarith)
  have hqT : tr.time q < sp.ts s + 2 * sp.Δ := by
    have hqdl := hdeadline q hqj (tr.time i) hgi
    rw [max_eq_left hti0] at hqdl
    linarith
  have hqj' : q < j := lt_of_le_of_ne hqj (by rintro rfl; linarith)
  have hqs : sp.slot (tr.time q) = s :=
    slot_of_mem sp s (by linarith) (by rw [ts_succ']; linarith)
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
    (by rw [hes]; linarith)
    (fun k hk hrs => lt_trans (hrestart k (by omega) hrs) (by linarith))
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
    ⟨_, getHead_mem' hPhix (fun _ h => (voteDomain_subset_tree h.1)) e.readPoint (tr.time i)
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
    have hmax : max (tr.time q) (sp.ts s) ≤ sp.ts s + sp.Δ := max_le hqtime (by linarith)
    obtain ⟨r, hrj, har, hrt⟩ : ∃ r ≤ j, tr.AcceptAt y r B ∧ tr.time r < sp.ts s + 2 * sp.Δ := by
      by_cases hgq : gbar g ≤ tr.time q
      · have hdl := hdeadline j le_rfl (tr.time q) hgq
        obtain ⟨r, hrj, har, hrt⟩ := hS.sync.relay x hx q B hacc hgq y hy j ell hc
          (by linarith) (by linarith) hFB
        exact ⟨r, hrj, har, by have := hdeadline r hrj (tr.time q) hgq; linarith⟩
      · obtain ⟨r, hrj, har, hrt⟩ := hS.catchUp.relay x hx q B hacc (lt_of_not_ge hgq)
          y hy j ell hc (by linarith) hjb hFB
        exact ⟨r, hrj, har, by linarith⟩
    exact ⟨mem_tree_of_acceptAt sp hr hy har hrj hc hFB, Or.inr ⟨r, har, hrt⟩⟩
  have hstamp := blockStamp_lt_of_acceptedBefore sp hr hy hc hBy hAB
    (fun k hk hrs => lt_trans (hrestart k (by omega) hrs) (by linarith)) (Or.inl ht)
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
    · exact Or.inr ⟨k, hk, by linarith⟩
  · rintro v ⟨x, hx, i, e, hv, rfl, hes⟩
    obtain ⟨hp, hst⟩ := late_vote_readPoint_before hS hy hc hs' hs ht hjb hdeadline hrestart
      hx hv hes
    exact Or.inl ⟨hp, lt_trans hst
      (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (by linarith)))⟩

/-- **A late honest vote is held** (h1 §2): for a slot `s ≥ r` and an honest call at a time
`≥ t_s + 2Δ`, every honest slot-`s` vote is held, with a stamp before `t_s + 2Δ`, before and after
the call. -/
theorem late_vote_pool (hS : HealthyBase tr H U proposer g) {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y j ℓ) {s : Nat}
    (hs : gbar g + 4 * sp.Δ ≤ sp.ts s) (ht : sp.ts s + 2 * sp.Δ ≤ tr.time j) {x : Fin sp.n}
    (hx : x ∈ H) {i : Nat} {e : Em sp FGP} (hv : VoteAt tr x i e) (hes : e.msg.slot = s) :
    ∀ c, (c = j ∨ c = j + 1) → e.msg ∈ (tr.state y c).pool s ∧
      (tr.state y c).voteStamp e.msg < ETime.of (sp.ts s + 2 * sp.Δ) := by
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  have hg0 := gbar_nonneg g
  obtain ⟨ℓx, hcx, hex⟩ := hv
  obtain ⟨hval, hslx, -, -⟩ := castAt_spec hr hx ⟨hcx, hex⟩
  have hti : tr.time i ≤ sp.ts s + sp.Δ := by
    have := vote_time_le hr hx ⟨ℓx, hcx, hex⟩
    rwa [← hslx, hes] at this
  have hti' : sp.ts s ≤ tr.time i :=
    (ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by rw [← hslx, hes])
  -- the vote reaches `y` before `t_s + 2Δ`
  have hgi : g ≤ tr.time i := (le_gbar g).trans (by linarith)
  have hmax : max (tr.time i) g = tr.time i := max_eq_left hgi
  have hdl : ∀ c, tr.deadline y c (tr.time i) ≤ tr.time i + sp.Δ := fun c =>
    (hS.deadline_le hy c _).trans (by rw [max_eq_left (by linarith : gbar g ≤ tr.time i)])
  obtain ⟨k', hk'j, hik', hproc, hk'dl⟩ := hS.healthy.1 x hx i e.msg
    ⟨ℓx, hcx, Or.inl ⟨e, hex, rfl⟩⟩ y hy j ℓ hc (by rw [hmax]; linarith [hdl j])
  rw [hmax] at hk'dl
  have hk'T : tr.time k' < sp.ts s + 2 * sp.Δ := by linarith [hdl k']
  have hk'j' : k' < j := lt_of_le_of_ne hk'j (by rintro rfl; linarith)
  have hsl' : sp.slot (tr.time k') = s :=
    slot_of_mem sp s (by linarith) (by rw [ts_succ']; linarith)
  have hxH : e.msg.val ∈ H := hval ▸ hx
  have hheld : e.msg ∈ (tr.state y (k' + 1)).pool s := by
    rcases held_of_processAt hr hy hproc (by rw [hsl', hes]; omega) (by rw [hsl', hes]) with
      h | ⟨a, ha, b, hb, hab, hav, hbv⟩
    · rwa [hes] at h
    · exfalso
      rw [hes] at ha hb
      obtain ⟨ja, -, ea, hva, rfl⟩ := hS.run.honest.pool_vote y hy (k' + 1) s _ ha (hav ▸ hxH)
      obtain ⟨jb, -, eb, hvb, rfl⟩ := hS.run.honest.pool_vote y hy (k' + 1) s _ hb (hbv ▸ hxH)
      have hsa := state_pool_slot sp hr hy (k' + 1) s _ ha
      have hsb := state_pool_slot sp hr hy (k' + 1) s _ hb
      rw [hav] at hva
      rw [hbv] at hvb
      obtain ⟨-, rfl⟩ := (one_vote_per_slot sp) FGP ro H U tr hr _ hxH ja jb ea eb hva hvb
        (hsa.trans hsb.symm)
      exact hab rfl
  intro c hcj
  have hst := stamp_lt_of_held hS hy (a := k' + 1) (b := c) (by omega) (w := e.msg)
    (by rw [hes]; exact hheld) (T := sp.ts s + 2 * sp.Δ)
    (fun k hk => lt_of_le_of_lt (hr.time_mono (Nat.lt_succ_iff.1 hk)) hk'T)
    (by rw [hes]; linarith) (by linarith) fun k h1 _ hrk => by
      have := hS.restart_le hy hrk
      have := hr.time_mono (show k' ≤ k by omega)
      linarith
  rwa [hes] at hst

/-- **A late honest batch** (h1 §2, H.2 §7.5): for a slot `s ≥ r` and an honest call at a time
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
        (tr.state y c).blockStamp e.msg.head < ETime.of (sp.ts s + 2 * sp.Δ) := by
  have hpool := late_vote_pool hS hy hc hs ht hx hv hes
  have hr := hS.run.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  have hg0 := gbar_nonneg g
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hy hc
  obtain ⟨ℓx, hcx, hex⟩ := hv
  obtain ⟨-, hslx, -, hhead⟩ := castAt_spec hr hx ⟨hcx, hex⟩
  have hti : tr.time i ≤ sp.ts s + sp.Δ := by
    have := vote_time_le hr hx ⟨ℓx, hcx, hex⟩
    rwa [← hslx, hes] at this
  -- the head: in `x`'s frame, accepted by `y` before `t_s + 2Δ`
  obtain ⟨hΦx, hΦxU⟩ := frameIn_of_callAt hr hx hcx
  obtain ⟨Hx, hHx, hHxr⟩ : ∃ Hx ∈ ℓx.frame.tree, Hx.root = e.msg.head :=
    ⟨_, getHead_mem' hΦx (fun _ hX => (voteDomain_subset_tree hX.1)) e.readPoint (tr.time i)
      (mergedVoteView sp e.readPoint ℓx.frame e.msg.slot) ((e.msg.slot : Int) - 1)
      (T := ℓx.frame.viableTree (voteDomain sp e.readPoint ℓx.frame e.msg.slot)),
      hhead.symm⟩
  have hHxs : Hx.slot ≤ s := by
    have := frame_slot_le sp hr hx hcx Hx hHx
    rwa [← hslx, hes] at this
  have hF : Anc U ℓ.frame.F Hx := hF Hx (hΦxU hHx) hHxr
  obtain ⟨hHt, hAB⟩ : Hx ∈ ℓ.frame.tree ∧
      AcceptedBefore tr y Hx (sp.ts s + 2 * sp.Δ) := by
    rcases Compose.frame_anc_accepted hr hx i ℓx hcx Hx hHx Hx Relation.ReflTransGen.refl with
      hg | ⟨kh, hkh, hacc⟩
    · refine ⟨?_, Or.inl hg⟩
      obtain ⟨G, hGU, hGr, hGp⟩ := genesis_mem_of_call sp hr hy j ℓ hc
      obtain rfl : Hx = G := hU.1 (hΦxU hHx) hGU (hg.trans hGr.symm)
      obtain h | ⟨c, -, hcp⟩ := (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hF
      · exact h ▸ hΦ.rooted.1
      · exact absurd (hcp.2.2.symm.trans hGp) (Option.some_ne_none _)
    have htkh : tr.time kh ≤ sp.ts s + sp.Δ := (hr.time_mono hkh).trans hti
    obtain ⟨ka, hkaj, hacc', hlt⟩ : ∃ ka ≤ j, tr.AcceptAt y ka Hx ∧
        tr.time ka < sp.ts s + 2 * sp.Δ := by
      by_cases hgk : g ≤ tr.time kh
      · have hmx : max (tr.time kh) (gbar g) ≤ sp.ts s + sp.Δ := max_le htkh (by linarith)
        obtain ⟨ka, hkaj, hacc', hlt⟩ := hS.healthy.2.1 x hx kh Hx hacc hgk y hy j ℓ hc
          (by linarith [hS.deadline_le hy j (tr.time kh)]) hF
        exact ⟨ka, hkaj, hacc', by linarith [hS.deadline_le hy ka (tr.time kh)]⟩
      · obtain ⟨ka, hkaj, hacc', hlt⟩ := hS.catchUp x hx kh Hx hacc
          (lt_of_lt_of_le (not_le.1 hgk) (le_gbar g)) y hy j ℓ hc (by linarith) hF
        exact ⟨ka, hkaj, hacc', by linarith⟩
    exact ⟨mem_tree_of_acceptAt sp hr hy hacc' hkaj hc hF, Or.inr ⟨ka, hacc', hlt⟩⟩
  have hbs := blockStamp_lt_of_acceptedBefore sp hr hy hc hHt hAB
    (fun k _ hrk => lt_of_le_of_lt (hS.restart_le hy hrk) (by linarith)) (Or.inl ht)
  have hpost : (tr.state y (j + 1)).blockStamp Hx.root = (tr.state y j).blockStamp Hx.root := by
    have hst : tr.state y (j + 1) = tr.post j := by simp [Trace.state, hc.1, hc.2]
    have he := hr.exec j ℓ hc.2 (hc.1 ▸ hy)
    rw [hc.1] at he
    have hp' : tr.post j =
        ((goldilocksSA sp FGP ro).step y (tr.state y j) ℓ.frame (tr.time j) ℓ.call).1 := by
      rw [he]
    obtain ⟨hblk, -, hoth⟩ := step_blockStamp_eq ro y (tr.state y j) hΦ (hr.time_nonneg j)
      ℓ.call
    rw [hst, hp']
    by_cases hb : ∃ B, ℓ.call = .block B
    · obtain ⟨B, hB⟩ := hb
      rw [hblk B hB, Function.update_apply]
      split_ifs with hr'
      swap
      · rfl
      exfalso
      have hBU : B ∈ U := hΦU ((accept_new sp hr hy ⟨ℓ, hc, hB⟩).1 ℓ hc)
      obtain rfl : Hx = B := hU.1 (hΦU hHt) hBU hr'
      rcases hAB with hg | ⟨ka, hka, hlt⟩
      · exact accept_ne_genesis sp hr hy ⟨ℓ, hc, hB⟩ hg
      · obtain rfl := accept_unique sp hr hy hka ⟨ℓ, hc, hB⟩
        linarith
    · simp only [not_exists] at hb
      rw [hoth hb fun hrs => by
        have := hS.restart_le hy ⟨ℓ, hc, hrs⟩
        linarith]
  refine ⟨Hx, hHt, hHxr, hHxs, fun c hcj => ⟨(hpool c hcj).1, (hpool c hcj).2, ?_⟩⟩
  rw [← hHxr]
  rcases hcj with rfl | rfl
  · exact hbs
  · rw [hpost]; exact hbs

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

/-- **The proposal is relayed**: an honest proposal `P` of slot `p` (with `ḡ ≤ t_p`) is in the
frame of every honest call from `t_p + Δ` on, accepted before `t_p + Δ`. -/
theorem proposal_mem_tree (hS : StandaloneRun tr H U proposer g) {p : Nat} {P : Blk sp.n FGP}
    (hpH : proposer p ∈ H) (hP : HonestProposal tr (proposer p) p P)
    (hpg : gbar g ≤ sp.ts p) {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y j ℓ)
    (ht : sp.ts p + sp.Δ ≤ tr.time j) :
    P ∈ ℓ.frame.tree ∧ ∃ ka ≤ j, tr.AcceptAt y ka P ∧ tr.time ka < sp.ts p + sp.Δ := by
  have hr := hS.run.localRun
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, j₀, -, ⟨ℓ₀, hc₀, hcall₀⟩, htj₀⟩ := hP
  obtain ⟨hΦ₀, hΦ₀U⟩ := frameIn_of_callAt hr hpH hc₀
  have hP₀ := (accept_new sp hr hpH ⟨ℓ₀, hc₀, hcall₀⟩).1 ℓ₀ hc₀
  have hF : Anc U ℓ.frame.F P := by
    rw [trivial_F_eq hS hy hpH hc hc₀]; exact (hΦ₀.rooted.2 P hP₀).mono hΦ₀U
  have hmax : max (sp.ts p) (gbar g) = sp.ts p := max_eq_left hpg
  obtain ⟨ka, hkaj, hacc, hlt⟩ := hS.healthy.2.1 _ hpH j₀ P ⟨ℓ₀, hc₀, hcall₀⟩
    (by rw [htj₀]; exact (le_gbar g).trans hpg) y hy j ℓ hc
    (by rw [htj₀]; have := hS.deadline_le hy j (sp.ts p); rw [hmax] at this; linarith) hF
  have hdl := hS.deadline_le hy ka (tr.time j₀)
  rw [htj₀, hmax] at hdl
  rw [htj₀] at hlt
  refine ⟨?_, ka, hkaj, hacc, by linarith⟩
  rw [(hS.trivial y hy j ℓ hc).2.2.2]
  exact Set.mem_insert_of_mem _ ⟨ka, hkaj, hacc⟩

/-! ## Honest votes and comparison with `P` -/

/-- An honest validator is not an equivocator in an honest node's pool of a slot. -/
theorem honest_not_equivocator_pool (hS : HealthyBase tr H U proposer g)
    {y : Fin sp.n} (hy : y ∈ H)
    (c s : Nat) {u : Fin sp.n} (hu : u ∈ H) :
    u ∉ equivocators {v | v ∈ (tr.state y c).pool s} := by
  have hr := hS.run.localRun
  rintro ⟨a, ha, b, hb, hab, rfl, hbv⟩
  obtain ⟨ja, -, ea, hva, rfl⟩ := hS.run.honest.pool_vote y hy c s _ ha hu
  obtain ⟨jb, -, eb, hvb, rfl⟩ := hS.run.honest.pool_vote y hy c s _ hb (hbv ▸ hu)
  rw [hbv] at hvb
  obtain ⟨-, rfl⟩ := (one_vote_per_slot sp) FGP ro H U tr hr _ hu ja jb ea eb hva hvb
    ((state_pool_slot sp hr hy c s _ ha).trans (state_pool_slot sp hr hy c s _ hb).symm)
  exact hab rfl

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

/-- The honest validators are more than twice the faulty ones. -/
theorem two_faulty_lt_honest (hS : HealthyBase tr H U proposer g) : 2 * Hᶜ.ncard < H.ncard := by
  have := hS.healthy.2.2.2
  have hn : H.ncard + Hᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have := sp.toParams.hn
  change 1 ≤ sp.n at this
  omega

/-- **A late result has an honest supporter**: the result `C` of an honest update of a slot
`s ≥ r` (read at a time `≥ t_s + 2Δ`) is extended by an honest vote of slot `s`: its supporters
are a strict majority of the voters, which include all honest validators (h1 §3). -/
theorem result_extended (hS : HealthyBase tr H U proposer g) {s : Nat}
    (hs : gbar g + 4 * sp.Δ ≤ sp.ts s) {x : Fin sp.n} (hx : x ∈ H) {c : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x c ℓ)
    (ht : sp.ts s + 2 * sp.Δ ≤ tr.time c) {C : Blk sp.n FGP}
    (hC : getConfirmation sp (tr.state x c) ℓ.frame s = some C) :
    ∃ z ∈ H, ∃ j e, VoteAt tr z j e ∧ e.msg.slot = s ∧ VoteExtends U e.msg C := by
  have hr := hS.run.localRun
  obtain ⟨-, hΦU⟩ := frameIn_of_callAt hr hx hc
  have hmaj := (deepest_mem hC).1.2.2
  unfold confirmationScore at hmaj
  dsimp only at hmaj
  have hHv : H ⊆ voters {v | v ∈ (tr.state x c).pool s} := by
    intro u hu
    obtain ⟨j, e, hv, hes⟩ := honest_votes_in_slot hS hs u hu
    obtain ⟨hval, -⟩ := castAt_spec hr hu ⟨hv.choose_spec.1, hv.choose_spec.2⟩
    exact ⟨e.msg, (late_vote_pool hS hx hc hs ht hu hv hes c (Or.inl rfl)).1, hval⟩
  have h1 := Set.ncard_le_ncard hHv
  have h2 := two_faulty_lt_honest hS
  obtain ⟨u, ⟨-, v, ⟨hvp, -⟩, rfl, -, R, hR, hRr, hCR⟩, hu⟩ :=
    Set.exists_mem_notMem_of_ncard_lt_ncard (s := Hᶜ)
      (t := supporters ℓ.frame ⟨{v | v ∈ (tr.state x c).pool s}, {v | v ∈ (tr.state x c).pool s ∧
        resolutionTime (tr.state x c) ℓ.frame v < ETime.of (sp.ts s + 2 * sp.Δ)}⟩ s C)
      (by omega)
  have huH : v.val ∈ H := not_not.1 hu
  obtain ⟨j', -, e', hve, rfl⟩ := hS.run.honest.pool_vote x hx c s _ hvp huH
  exact ⟨_, huH, j', e', hve, state_pool_slot sp hr hx c s _ hvp, R, hΦU hR, hRr,
    Anc.mono hΦU hCR⟩

/-- **A lock origin of a slot `≥ p` compares with `P`** (h1 §3, `l ≥ p`): an honest fast lock
through an honest counted vote; an honest slow lock through an honest supporter of its update's
result (not its fast test). -/
theorem origin_compatible_proposal (hS : StandaloneRun tr H U proposer g)
    {p : Nat} {P : Blk sp.n FGP}
    (hp : gbar g + 4 * sp.Δ ≤ sp.ts p)
    (hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P)
    {x : Fin sp.n} (hx : x ∈ H) {j s : Nat} {B : Blk sp.n FGP} (hps : p ≤ s)
    (horig : (∃ CV, FastLockAt tr x j s B CV) ∨ SlowLockAt tr x j s B) : Compatible U B P := by
  have hr := hS.run.localRun
  have hU := hr.coherent
  have hs : gbar g + 4 * sp.Δ ≤ sp.ts s := hp.trans ((ts_le_iff sp).2 (by omega))
  rcases horig with ⟨CV, hfl⟩ | ⟨ℓ', C, hupd, hC, hB⟩
  · obtain ⟨z, hz, j', e, hv, hes, hext⟩ := fastLock_honest_vote hS.run hS.two_faulty_lt hx hfl
    exact compatible_of_vote hU hvotes hz hv (hes ▸ hps) hext
  · obtain ⟨-, hΦU⟩ := frameIn_of_callAt hr hx hupd.1
    have hBC : ℓ'.frame.Anc B C := (deepest_mem hB).1.1.2.2
    obtain ⟨z, hz, j', e, hv, hes, Hd, hHd, hHdr, hCHd⟩ :=
      result_extended hS.toHealthyBase hs hx hupd.1
        (by rw [hupd.2.2.1]; linarith [sp.toParams.hΔ]) hC
    exact compatible_of_vote hU hvotes hz hv (hes ▸ hps)
      ⟨Hd, hHd, hHdr, (Anc.mono hΦU hBC).trans hCHd⟩

private theorem compatible_down {B L P : Blk sp.n FGP} (hU : Coherent U) (hLB : Anc U L B)
    (h : Compatible U B P) : Compatible U L P := by
  rcases h with h | h
  · exact Or.inl (hLB.trans h)
  · exact anc_total hU hLB h

/-- **Every stored lock compares with `P`** (h1 §3), at the state before an honest call at a
time `t ≥ t_{p−1}` (`hset`) and, for a call at `t ≥ t_p + 6Δ`, also after it, for the locks live
at `t`: of a label `< p` by `hset` and the exact slot-`p` votes (a lock written by the call has a
label `≥ p`); of a label `≥ p` by its origin. -/
theorem lock_compatible (hS : StandaloneRun tr H U proposer g) {p : Nat} {P : Blk sp.n FGP}
    (hp : gbar g + 2 * Θ sp + 8 * sp.Δ ≤ sp.ts p)
    (hset : LocksSettled tr H U (sp.ts p - 4 * sp.Δ))
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
  have hp4 : gbar g + 4 * sp.Δ ≤ sp.ts p := by linarith
  -- labels `≥ p`: by the origin, at any cut
  have hge : ∀ c' (l' : Lock), l' ∈ (tr.state y c').locks → p ≤ l'.slot → ∀ L' ∈ U,
      L'.root = l'.block → Compatible U L' P := by
    intro c' l' hl' hpl L' hL' hL'r
    cases hf : l'.fast
    · obtain ⟨j', -, B, hsl, L₁, hL₁, hL₁r, hL₁B⟩ := slow_lock_provenance hr hy c' l' hl' hf
      obtain rfl : L₁ = L' := hU.1 hL₁ hL' (hL₁r.trans hL'r.symm)
      exact compatible_down hU hL₁B
        (origin_compatible_proposal hS hp4 hvotes hy hpl (Or.inr hsl))
    · obtain ⟨j', -, B, CV, hfl, L₁, hL₁, hL₁r, hL₁B⟩ := fast_lock_provenance hr hy c' l' hl' hf
      obtain rfl : L₁ = L' := hU.1 hL₁ hL' (hL₁r.trans hL'r.symm)
      exact compatible_down hU hL₁B
        (origin_compatible_proposal hS hp4 hvotes hy hpl (Or.inl ⟨CV, hfl⟩))
  -- labels `< p` before the call: `hset` and an honest slot-`p` vote, which is `P`
  have hlt : ∀ l' ∈ (tr.state y j).locks, l'.slot < p → sp.slot (tr.time j) ≤ l'.slot + sp.k →
      ∀ L' ∈ U, L'.root = l'.block → Compatible U L' P := by
    intro l' hl' hpl hlive' L' hL' hL'r
    obtain ⟨hve, -⟩ := locksSettled_iff.1 hset y hy j (by linarith) l' hl' hlive' L' hL' hL'r
    obtain ⟨x, hx⟩ : H.Nonempty :=
      Set.nonempty_of_ncard_ne_zero (by have := two_faulty_lt_honest hS.toHealthyBase; omega)
    obtain ⟨i, e, hv, hes⟩ := honest_votes_in_slot hS.toHealthyBase hp4 x hx
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
      (by simp only [SAParams.ts] at htj ⊢; push_cast; linarith)
    exact_mod_cast this
  rcases lock_provenance_from hr hy (Nat.le_succ j) l hl with
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
        linarith
      linarith

/-- **Every live lock block compares with `P`** at the state before (for a call at `t ≥ t_{p−1}`)
or after (for a call at `t ≥ t_p + 6Δ`) an honest call, read at that call's frame and time. -/
theorem liveLock_compatible (hS : StandaloneRun tr H U proposer g) {p : Nat} {P : Blk sp.n FGP}
    (hp : gbar g + 2 * Θ sp + 8 * sp.Δ ≤ sp.ts p)
    (hset : LocksSettled tr H U (sp.ts p - 4 * sp.Δ))
    (hexact : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root)
    (hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P)
    (hPU : P ∈ U) {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt y j ℓ) (htj : sp.ts p + 6 * sp.Δ ≤ tr.time j) {c : Nat}
    (hcj : c = j ∨ c = j + 1) :
    ∀ L ∈ liveLockBlocks sp (tr.state y c).locks ℓ.frame (tr.time j), Compatible U L P := by
  have hr := hS.run.localRun
  have hU := hr.coherent
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hy hc
  rintro L ⟨hLt, l', ⟨l, hl, B, hB, hBr, hlive, rfl⟩, hLr⟩
  have hva : ℓ.frame.Anc (ℓ.frame.viableAncestor B) B := anc_viableAncestor ℓ.frame B
  obtain rfl : L = ℓ.frame.viableAncestor B :=
    hΦ.coherent.1 hLt (mem_of_anc hva hB) hLr.symm
  exact compatible_down hU (hva.mono hΦU)
    (lock_compatible hS hp hset hexact hvotes hPU hy htj hcj hl
      (le_trans hlive ((locksWF_state hr hy c).cap hl)) (L := B) (hΦU hB) hBr)

/-! ## The first update at `t_p + 6Δ` -/

private theorem etime_lt_top (t : Time) : ETime.of t < ⊤ :=
  WithBot.coe_lt_coe.2 (WithTop.coe_lt_top t)

/-- **The first update** (h1 §4): at an honest node's tick at `t_p + 6Δ`, with every honest
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
      tr.post k = updateConfirmation sp (tr.state y k) ℓ.frame (tr.time k) p := by
  have hr := hS.run.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  have hg0 := gbar_nonneg g
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hy hc
  have hts1 := ts_succ' (sp := sp) p
  have hslot : sp.slot (tr.time k) = p + 1 :=
    slot_of_mem sp (p + 1) (by rw [htk, hts1]; linarith) (by rw [htk, ts_succ', hts1]; linarith)
  have hj := hS.joined_state hy k (by
    rw [hslot, show (((p + 1 : Nat) : Int) - 1) = p by push_cast; ring]; linarith)
  have hT2 : tr.time k = sp.ts ((p + 1 : Nat) : Int) + 2 * sp.Δ := by rw [htk, hts1]; ring
  -- the tick is the slot-`p` update
  have he := hr.exec k ℓ hc.2 (hc.1 ▸ hy)
  rw [hc.1, hcall] at he
  have hpost : tr.post k = updateConfirmation sp (tr.state y k) ℓ.frame (tr.time k) p := by
    have h1 : tr.post k = (acOnTick sp y (tr.state y k) ℓ.frame (tr.time k)).1 :=
      (congrArg Prod.fst he).symm
    rw [h1]
    unfold acOnTick
    dsimp only
    rw [hslot]
    have hc1 : ¬ tr.time k = sp.ts ((p + 1 : Nat) : Int) + sp.Δ := by intro h; linarith
    have hc2 : (tr.time k = sp.ts ((p + 1 : Nat) : Int) + 2 * sp.Δ ∧ 0 < p + 1) = True :=
      eq_true ⟨hT2, Nat.succ_pos p⟩
    simp only [hj, not_true_eq_false, hc1, hc2, ↓reduceIte, Nat.add_sub_cancel]
  set A := tr.state y k with hA
  -- the honest slot-`p` votes: held, resolved before `t_p + 2Δ`, on `P`, one per validator
  have hhon : ∀ u ∈ H, ∃ v ∈ A.pool p, v.val = u ∧ v.head = P.root ∧
      resolutionTime A ℓ.frame v < ETime.of (sp.ts p + 2 * sp.Δ) ∧
      ∀ v' ∈ A.pool p, v'.val = u → v' = v := by
    intro u hu
    obtain ⟨i, e, hv, hes⟩ := honest_votes_in_slot hS hp4 u hu
    obtain ⟨Hd, hHdt, hHdr, hHds, hh⟩ := late_vote_held_of_frame hS hy hc hp4
      (by rw [htk]; linarith) hu hv hes fun Hd hHd hHdr => by
        rw [hU.1 hHd (hΦU hPt) (hHdr.trans (hexact u hu i e hv hes))]
        exact (hΦ.rooted.2 P hPt).mono hΦU
    obtain ⟨hmem, hvst, hbst⟩ := hh k (Or.inl rfl)
    obtain ⟨hval, -⟩ := castAt_spec hr hu ⟨hv.choose_spec.1, hv.choose_spec.2⟩
    refine ⟨e.msg, hmem, hval, hexact u hu i e hv hes,
      resolutionTime_lt_of hΦ hHdt hHdr (hes ▸ hHds) hvst hbst, fun v' hv' hv'u => ?_⟩
    obtain ⟨j', -, e', hve', rfl⟩ := hS.run.honest.pool_vote y hy k p v' hv' (hv'u ▸ hu)
    rw [hv'u] at hve'
    obtain ⟨-, rfl⟩ := (one_vote_per_slot sp) FGP ro H U tr hr _ hu j' i e' e hve' hv
      ((state_pool_slot sp hr hy k p _ hv').trans hes.symm)
    rfl
  have hHvot : H ⊆ voters {v | v ∈ A.pool p} := fun u hu => by
    obtain ⟨v, hv, hvu, -⟩ := hhon u hu
    exact ⟨v, hv, hvu⟩
  have hvle : (voters {v | v ∈ A.pool p}).ncard ≤ sp.n := by
    have := Set.ncard_le_ncard (Set.subset_univ (voters {v | v ∈ A.pool p}))
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  have hHn : H.ncard + Hᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h2f := two_faulty_lt_honest hS
  have hHle := Set.ncard_le_ncard hHvot
  -- the honest validators support `P`
  have hscore : H.ncard ≤ confirmationScore sp A ℓ.frame p P := by
    unfold confirmationScore
    dsimp only
    have hsub : H ⊆ supporters ℓ.frame ⟨{v | v ∈ A.pool p}, {v | v ∈ A.pool p ∧
        resolutionTime A ℓ.frame v < ETime.of (sp.ts p + 2 * sp.Δ)}⟩ p P := by
      intro u hu
      obtain ⟨v, hv, hvu, hvh, hres, -⟩ := hhon u hu
      refine ⟨honest_not_equivocator_pool hS hy k p hu, v, ⟨hv, hres⟩, hvu, ?_,
        P, hPt, hvh.symm, Relation.ReflTransGen.refl⟩
      exact_mod_cast state_pool_slot sp hr hy k p v hv
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

/-- **The first update repairs the record** (h1 §4): at an honest node's tick at `t_p + 6Δ`, with
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
    ∃ R ∈ ℓ.frame.tree, R.root = (tr.post k).latestConfirmed ∧ ℓ.frame.Anc P R := by
  obtain ⟨hconf, hnv, -, hpost⟩ :=
    first_update_post hS hp4 hexact hy hc hcall htk hPt hlocks
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

/-! ## The record after the first update -/

/-- The record names a block of the frame that extends `P`. -/
private def RecP (Φ : Frm sp.n FGP) (P : Blk sp.n FGP) (A : SAState sp.n) : Prop :=
  ∃ R ∈ Φ.tree, R.root = A.latestConfirmed ∧ Φ.Anc P R

private theorem RecP.of_eq {Φ : Frm sp.n FGP} {P : Blk sp.n FGP} {A A' : SAState sp.n}
    (h : A'.latestConfirmed = A.latestConfirmed) (hR : RecP Φ P A) : RecP Φ P A' := by
  obtain ⟨R, hR, hRr, hPR⟩ := hR
  exact ⟨R, hR, hRr.trans h.symm, hPR⟩

private theorem RecP.mono {Φ Φ' : Frm sp.n FGP} {P : Blk sp.n FGP} {A : SAState sp.n}
    (hsub : Φ.tree ⊆ Φ'.tree) (hR : RecP Φ P A) : RecP Φ' P A := by
  obtain ⟨R, hR, hRr, hPR⟩ := hR
  exact ⟨R, hsub hR, hRr, hPR.mono hsub⟩

/-- A record write of a candidate comparing with `P` keeps the record extending `P`: an ancestor
candidate is refused, a descendant replaces it. -/
private theorem RecP.ulc {Φ : Frm sp.n FGP} {P : Blk sp.n FGP} {A : SAState sp.n}
    (hR : RecP Φ P A) {C : Blk sp.n FGP} (hC : C ∈ Φ.tree) (hcomp : Compatible Φ.tree C P) :
    RecP Φ P (updateLatestConfirmed sp A Φ C) := by
  unfold updateLatestConfirmed
  split_ifs with h
  · exact hR
  · refine ⟨C, hC, rfl, ?_⟩
    rcases hcomp with hCP | hPC
    · exfalso
      obtain ⟨R, hR, hRr, hPR⟩ := hR
      exact h ⟨R, hR, hRr, hCP.trans hPR⟩
    · exact hPC

private theorem lc_admitVote (A : SAState sp.n) (t : Time) (v : Vote sp.n) :
    (admitVote sp A t v).latestConfirmed = A.latestConfirmed := by
  unfold admitVote; split_ifs <;> rfl

private theorem lc_blockReceipt (A : SAState sp.n) (t : Time) (B : Blk sp.n FGP) :
    (blockReceipt sp A t B).latestConfirmed = A.latestConfirmed := by
  unfold blockReceipt
  generalize blockVotes B = l
  suffices h : ∀ A' : SAState sp.n,
      (l.foldl (fun A v => admitVote sp A t v) A').latestConfirmed = A'.latestConfirmed from h _
  induction l with
  | nil => exact fun _ => rfl
  | cons v l ih => intro A'; simp only [List.foldl_cons]; rw [ih, lc_admitVote]

private theorem pool_optimistic (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (optimisticConfirmation sp A Φ t).pool = A.pool := by
  unfold optimisticConfirmation updateLatestConfirmed; split
  · rfl
  · split_ifs <;> rfl

private theorem pool_sub_tryVote (x : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) : ∀ σ, ∀ v ∈ A.pool σ, v ∈ (tryVote sp x A Φ t).1.pool σ := by
  intro σ v hv
  unfold tryVote
  dsimp only
  split_ifs
  · exact hv
  · exact hv
  all_goals
    rw [pool_optimistic]
    unfold admitVote
    split_ifs
    · exact hv
    · exact hv
    · simp only [Function.update_apply]
      split_ifs with hσ
      · subst hσ; exact List.mem_append_left _ hv
      · exact hv

private theorem RecP.ofOptimistic {Φ : Frm sp.n FGP} {P : Blk sp.n FGP} {A : SAState sp.n}
    {t : Time} (hR : RecP Φ P A)
    (hsel : ∀ B, optimisticSelect sp A Φ t = some B → Compatible Φ.tree B P) :
    RecP Φ P (optimisticConfirmation sp A Φ t) := by
  unfold optimisticConfirmation
  rcases h : optimisticSelect sp A Φ t with _ | B
  · exact hR
  · have hB := h
    unfold optimisticSelect at hB
    dsimp only at hB
    split_ifs at hB
    let N : Set (Nat × Bool × Nat) := {(B.root, true, fastExpiry sp A.locks Φ t (sp.slot t))}
    exact RecP.ulc (A := { A with locks := addLocks sp A.locks Φ t (sp.slot t) N })
      hR (deepest_mem hB).1.1 (hsel B h)

private theorem RecP.ofTryVote {Φ : Frm sp.n FGP} {P : Blk sp.n FGP} {x : Fin sp.n}
    {A : SAState sp.n} {t : Time} (hR : RecP Φ P A)
    (hsel : ∀ A' B, A'.pool = (tryVote sp x A Φ t).1.pool →
      optimisticSelect sp A' Φ t = some B → Compatible Φ.tree B P) :
    RecP Φ P (tryVote sp x A Φ t).1 := by
  unfold tryVote at hsel ⊢
  dsimp only at hsel ⊢
  split_ifs at hsel ⊢
  · exact hR
  · exact hR
  all_goals
    exact RecP.ofOptimistic (RecP.of_eq (lc_admitVote _ _ _) hR) fun B hB =>
      hsel _ B (pool_optimistic _ _ _).symm hB

private theorem RecP.ofUpdate {Φ : Frm sp.n FGP} {P : Blk sp.n FGP} {A : SAState sp.n}
    {t : Time} {s : Nat} (hR : RecP Φ P A)
    (hres : ∀ C, getConfirmation sp A Φ s = some C → Compatible Φ.tree C P) :
    RecP Φ P (updateConfirmation sp A Φ t s) := by
  unfold updateConfirmation
  dsimp only
  rcases hC : getConfirmation sp A Φ s with _ | C
  · exact hR
  · dsimp only
    split_ifs
    · exact hR
    all_goals
      exact RecP.ulc (A := { A with saved := Function.update A.saved s (some C.root) }) hR
        (deepest_mem hC).1.1 (hres C hC)

/-- **An optimistic selection compares with `P`** (h1 §4): at an honest call at `t ≥ t_p + 6Δ`,
from a state whose pools the call keeps, the block an optimistic check selects has three
quarters of the committee as voters, one of them honest, whose vote (of a slot `> p`) extends
`P`. -/
theorem optimisticSelect_compatible (hS : HealthyBase tr H U proposer g)
    {p : Nat} {P : Blk sp.n FGP}
    (hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P)
    {y : Fin sp.n} (hy : y ∈ H) {c : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt y c ℓ) (htc : sp.ts p + 6 * sp.Δ ≤ tr.time c) (hPt : P ∈ ℓ.frame.tree)
    {A : SAState sp.n} (hA : ∀ σ, ∀ v ∈ A.pool σ, v ∈ (tr.state y (c + 1)).pool σ)
    {B : Blk sp.n FGP} (hsel : optimisticSelect sp A ℓ.frame (tr.time c) = some B) :
    Compatible ℓ.frame.tree B P := by
  have hr := hS.run.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hy hc
  have hsl : p + 1 ≤ sp.slot (tr.time c) := by
    have := (ts_le_iff_le_slot sp (hr.time_nonneg c) (p + 1 : Nat)).1
      (by simp only [SAParams.ts] at htc ⊢; push_cast; linarith)
    exact_mod_cast this
  unfold optimisticSelect at hsel
  dsimp only at hsel
  split_ifs at hsel
  have hBt := (deepest_mem hsel).1.1
  have h34 := (deepest_mem hsel).1.2.1
  have hf := hS.two_faulty_lt
  have hlt : Hᶜ.ncard <
      (optimisticVoters sp A ℓ.frame (sp.slot (tr.time c)) B).ncard := by omega
  obtain ⟨u, ⟨x, hx, rfl, R, hR, hRr, hBR⟩, hu⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt
  have hx' := hA _ x hx
  obtain ⟨j', -, e', hve, rfl⟩ := hS.run.honest.pool_vote y hy (c + 1) _ _ hx' (not_not.1 hu)
  have hes := state_pool_slot sp hr hy (c + 1) _ _ hx'
  have hcomp := compatible_of_vote hU hvotes (not_not.1 hu) hve (by omega)
    ⟨R, hΦU hR, hRr, hBR.mono hΦU⟩
  rcases hcomp with h | h
  · exact Or.inl (anc_tree_of_anc_U hU hΦ hΦU hBt h hPt)
  · exact Or.inr (anc_tree_of_anc_U hU hΦ hΦU hPt h hBt)

/-- **The record step** (h1 §4): an honest call at `t ≥ t_p + 6Δ` keeps the record extending `P`:
every candidate it writes (an optimistic selection, or the result of an update of a slot `≥ p`)
compares with `P`, and a restart keeps the record. -/
theorem record_step (hS : HealthyBase tr H U proposer g) {p : Nat} {P : Blk sp.n FGP}
    (hp : gbar g + 4 * sp.Δ ≤ sp.ts p)
    (hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P)
    {y : Fin sp.n} (hy : y ∈ H) {c : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt y c ℓ) (htc : sp.ts p + 6 * sp.Δ ≤ tr.time c) (hPt : P ∈ ℓ.frame.tree)
    (hR : ∃ R ∈ ℓ.frame.tree, R.root = (tr.state y c).latestConfirmed ∧ ℓ.frame.Anc P R) :
    ∃ R ∈ ℓ.frame.tree, R.root = (tr.post c).latestConfirmed ∧ ℓ.frame.Anc P R := by
  have hr := hS.run.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hy hc
  change RecP ℓ.frame P (tr.state y c) at hR
  change RecP ℓ.frame P (tr.post c)
  have hst : tr.state y (c + 1) = tr.post c := by simp [Trace.state, hc.1, hc.2]
  have hopt : ∀ A' : SAState sp.n, (∀ σ, ∀ v ∈ A'.pool σ, v ∈ (tr.post c).pool σ) →
      ∀ B, optimisticSelect sp A' ℓ.frame (tr.time c) = some B →
        Compatible ℓ.frame.tree B P := fun A' hA' B hB =>
    optimisticSelect_compatible hS hvotes hy hc htc hPt (fun σ v hv => hst ▸ hA' σ v hv) hB
  have he := hr.exec c ℓ hc.2 (hc.1 ▸ hy)
  rw [hc.1] at he
  have hpost : tr.post c =
      ((goldilocksSA sp FGP ro).step y (tr.state y c) ℓ.frame (tr.time c) ℓ.call).1 := by
    rw [he]
  generalize hA : tr.state y c = A at hR hpost
  generalize ht : tr.time c = t at hopt hpost htc
  cases hcall : ℓ.call with
  | tick =>
    rw [hcall] at hpost
    change tr.post c = (acOnTick sp y A ℓ.frame t).1 at hpost
    rw [hpost] at hopt ⊢
    unfold acOnTick at hopt ⊢
    dsimp only at hopt ⊢
    by_cases hj : joined sp A t
    swap
    · simp only [eq_true hj, ↓reduceIte] at hopt ⊢
      exact hR
    simp only [eq_false (not_not.2 hj), ↓reduceIte] at hopt ⊢
    by_cases hu : t = sp.ts (sp.slot t) + 2 * sp.Δ ∧ 0 < sp.slot t
    · have hv : ¬ t = sp.ts (sp.slot t) + sp.Δ := fun h => by linarith [hu.1]
      simp only [eq_true hu, eq_false hv, ↓reduceIte] at hopt ⊢
      -- the update of slot `slot(t) − 1 ≥ p`
      refine RecP.ofUpdate (A := A) hR fun C hC => ?_
      have hs0 := hu.2
      have hsl : p + 1 ≤ sp.slot t := by
        have := (ts_le_iff_le_slot sp (ht ▸ hr.time_nonneg c) (p + 1 : Nat)).1
          (by simp only [SAParams.ts] at htc ⊢; push_cast; linarith)
        exact_mod_cast this
      have hts : sp.ts ((sp.slot t - 1 : Nat) : Int) + 4 * sp.Δ = sp.ts (sp.slot t) := by
        simp only [SAParams.ts]; push_cast [Nat.cast_sub (by omega : 1 ≤ sp.slot t)]; ring
      have hps : sp.ts p ≤ sp.ts ((sp.slot t - 1 : Nat) : Int) := (ts_le_iff sp).2 (by omega)
      rw [← hA] at hC
      obtain ⟨z, hz, j', e, hv, hes, hext⟩ := result_extended hS (hp.trans hps) hy hc
        (by rw [ht]; linarith [hu.1]) hC
      have hcomp := compatible_of_vote hU hvotes hz hv (by omega) hext
      have hCt := (deepest_mem hC).1.1
      rcases hcomp with h | h
      · exact Or.inl (anc_tree_of_anc_U hU hΦ hΦU hCt h hPt)
      · exact Or.inr (anc_tree_of_anc_U hU hΦ hΦU hPt h hCt)
    simp only [eq_false hu, ↓reduceIte] at hopt ⊢
    by_cases hv : t = sp.ts (sp.slot t) + sp.Δ
    · simp only [eq_true hv, ↓reduceIte] at hopt ⊢
      exact RecP.ofTryVote hR fun A' B hA' hB =>
        hopt A' (fun σ v hv => by rw [← hA']; exact hv) B hB
    · simp only [eq_false hv, ↓reduceIte] at hopt ⊢
      exact hR
  | proposal =>
    rw [hcall] at hpost
    change tr.post c = (acProposal sp A ℓ.frame t).1 at hpost
    rw [hpost]
    refine RecP.of_eq ?_ hR
    unfold acProposal; split_ifs <;> rfl
  | toFG =>
    rw [hcall] at hpost
    change tr.post c = (acToFG sp A ℓ.frame t).1 at hpost
    rw [hpost]
    refine RecP.of_eq ?_ hR
    unfold acToFG
    split_ifs
    all_goals first | rfl | (split <;> (try split_ifs) <;> rfl)
  | message m =>
    rw [hcall] at hpost
    change tr.post c = (tryVote sp y (optimisticConfirmation sp (admitVote sp A t m)
      ℓ.frame t) ℓ.frame t).1 at hpost
    rw [hpost] at hopt ⊢
    refine RecP.ofTryVote (RecP.ofOptimistic (RecP.of_eq (lc_admitVote _ _ _) hR)
      fun B hB => hopt _ (fun σ v hv => ?_) B hB) fun A' B hA' hB =>
        hopt A' (fun σ v hv => by rw [← hA']; exact hv) B hB
    exact pool_sub_tryVote _ _ _ _ σ v (by rw [pool_optimistic]; exact hv)
  | block B =>
    rw [hcall] at hpost
    change tr.post c = (tryVote sp y (optimisticConfirmation sp (blockReceipt sp A t B)
      ℓ.frame t) ℓ.frame t).1 at hpost
    rw [hpost] at hopt ⊢
    refine RecP.ofTryVote (RecP.ofOptimistic (RecP.of_eq (lc_blockReceipt _ _ _) hR)
      fun B' hB' => hopt _ (fun σ v hv => ?_) B' hB') fun A' B' hA' hB' =>
        hopt A' (fun σ v hv => by rw [← hA']; exact hv) B' hB'
    exact pool_sub_tryVote _ _ _ _ σ v (by rw [pool_optimistic]; exact hv)
  | restart =>
    rw [hcall] at hpost
    change tr.post c = (acRestart sp ro y A ℓ.frame t).1 at hpost
    rw [hpost]
    exact RecP.of_eq ((restart_state sp) FGP ro y A ℓ.frame t hΦ
      (ht ▸ hr.time_nonneg c)).2.2.1 hR

/-- Under trivial frames the tree of an honest node only grows. -/
theorem trivial_tree_mono (hS : StandaloneRun tr H U proposer g) {y : Fin sp.n} (hy : y ∈ H)
    {c c' : Nat} {ℓ ℓ' : ACLabel (goldilocksSA sp FGP ro)} (hc' : tr.CallAt y c' ℓ')
    (hc : tr.CallAt y c ℓ) (hcc : c' ≤ c) : ℓ'.frame.tree ⊆ ℓ.frame.tree := by
  intro X hX
  rw [(hS.trivial y hy c' ℓ' hc').2.2.2] at hX
  rw [(hS.trivial y hy c ℓ hc).2.2.2]
  rcases Set.mem_insert_iff.1 hX with rfl | ⟨k, hk, hacc⟩
  · rw [← trivial_F_eq hS hy hy hc hc']
    exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ ⟨k, hk.trans hcc, hacc⟩

/-- **The record after the first update** (h1 §4): from an honest node's tick at `t_p + 6Δ` on,
at every later call of the node, the record after the call names a block of the call's frame
that extends `P`. -/
theorem record_extends (hS : StandaloneRun tr H U proposer g) {p : Nat} {P : Blk sp.n FGP}
    (hpH : proposer p ∈ H) (hP : HonestProposal tr (proposer p) p P)
    (hp : gbar g + 2 * Θ sp + 8 * sp.Δ ≤ sp.ts p)
    (hset : LocksSettled tr H U (sp.ts p - 4 * sp.Δ))
    (hexact : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root)
    (hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓk : ACLabel (goldilocksSA sp FGP ro)}
    (hck : tr.CallAt y k ℓk) (hcallk : ℓk.call = .tick) (htk : tr.time k = sp.ts p + 6 * sp.Δ) :
    ∀ c (ℓ : ACLabel (goldilocksSA sp FGP ro)), tr.CallAt y c ℓ → k ≤ c →
      ∃ R ∈ ℓ.frame.tree, R.root = (tr.post c).latestConfirmed ∧ ℓ.frame.Anc P R := by
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  have hΘ := Θ_nonneg sp
  have hg0 := gbar_nonneg g
  have hPU : P ∈ U := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, j, -, ⟨ℓ, hc, hcall⟩, -⟩ := hP
    exact (frameIn_of_callAt hr hpH hc).2 ((accept_new sp hr hpH ⟨ℓ, hc, hcall⟩).1 ℓ hc)
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro ℓ hc hkc
    have htc : sp.ts p + 6 * sp.Δ ≤ tr.time c := htk ▸ hr.time_mono hkc
    rcases Nat.eq_or_lt_of_le hkc with rfl | hkc
    · obtain rfl : ℓ = ℓk := Option.some.inj (hc.2.symm.trans hck.2)
      exact first_update_record hS.toHealthyBase (by linarith) hexact hy hc hcallk htk
        (proposal_mem_tree hS hpH hP (by linarith) hy hc (by linarith)).1
        (liveLock_compatible hS hp hset hexact hvotes hPU hy hc htc (Or.inl rfl))
    have hPt := (proposal_mem_tree hS hpH hP (by linarith) hy hc (by linarith)).1
    rcases tr.noCall_or_lastCall y c with hn | ⟨c', hc'c, ℓ', hc', hnb⟩
    · exact absurd hck (hn k (Nat.zero_le _) hkc ℓk)
    have hkc' : k ≤ c' := by
      by_contra h
      exact hnb k (by omega) hkc ℓk hck
    have hR := ih c' hc'c ℓ' hc' hkc'
    rw [← tr.state_of_lastCall hc' hc'c hnb] at hR
    exact record_step hS.toHealthyBase (by linarith) hvotes hy hc htc hPt
      (RecP.mono (trivial_tree_mono hS hy hc' hc hc'c.le) hR)

/-! ## The head and the confirmed tip -/

/-- **The head extends `P`** (h1 §5, H.2 §7.5): at an honest call at `t ≥ t_p + 6Δ` whose frame has
`P` in its viable tree, the head after the call extends `P`: the latest view is of a slot
`m ≥ p + 1` whose honest votes are all held and resolved and extend `P` (`n − f > n/2` supporters
along `P`), and every live lock compares with `P`. -/
theorem head_extends_of_frame (hS : HealthyBase tr H U proposer g) {p : Nat} {P : Blk sp.n FGP}
    (hp : gbar g + 4 * sp.Δ ≤ sp.ts p)
    (hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt y j ℓ) (htj : sp.ts p + 6 * sp.Δ ≤ tr.time j)
    (hPv : P ∈ ℓ.frame.viableTree ℓ.frame.tree)
    (hlocks : ∀ L ∈ liveLockBlocks sp (tr.post j).locks ℓ.frame (tr.time j),
      Compatible U L P) :
    ℓ.frame.Anc P (acHead sp (tr.post j) ℓ.frame (tr.time j)) := by
  have hr := hS.run.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hy hc
  have hPt := hPv.1
  have hst : tr.state y (j + 1) = tr.post j := by simp [Trace.state, hc.1, hc.2]
  have ht0 := hr.time_nonneg j
  -- the latest view's slot `m ≥ p + 1`, due
  obtain ⟨m, hm, hpm, htm⟩ : ∃ m : Nat, (latestView sp (tr.post j) ℓ.frame (tr.time j)).2 = m ∧
      p + 1 ≤ m ∧ sp.ts m + 2 * sp.Δ ≤ tr.time j := by
    have h1 : sp.ts (sp.slot (tr.time j)) ≤ tr.time j := (ts_le_iff_le_slot sp ht0 _).2 le_rfl
    have h2 : tr.time j < sp.ts (sp.slot (tr.time j)) + 4 * sp.Δ := by
      have := (ts_le_iff_le_slot sp ht0 ((sp.slot (tr.time j) : Int) + 1)).not.2 (by omega)
      simp only [SAParams.ts] at this ⊢
      linarith
    have hs1 : p + 1 ≤ sp.slot (tr.time j) := by
      have := (ts_le_iff_le_slot sp ht0 (p + 1 : Nat)).1
        (by simp only [SAParams.ts] at htj ⊢; push_cast; linarith)
      exact_mod_cast this
    unfold latestView
    dsimp only
    split_ifs with h
    · exact ⟨_, rfl, hs1, h⟩
    · have hs2 : p + 2 ≤ sp.slot (tr.time j) := by
        by_contra hlt
        have heq : sp.slot (tr.time j) = p + 1 := by omega
        rw [heq] at h
        exact h (by simp only [SAParams.ts] at htj ⊢; push_cast; linarith)
      have h1s : 1 ≤ sp.slot (tr.time j) := by omega
      refine ⟨sp.slot (tr.time j) - 1, by rw [Nat.cast_sub h1s]; push_cast; ring, by omega, ?_⟩
      have : sp.ts ((sp.slot (tr.time j) - 1 : Nat) : Int) + 4 * sp.Δ =
          sp.ts (sp.slot (tr.time j)) := by
        simp only [SAParams.ts]; rw [Nat.cast_sub h1s]; push_cast
        ring
      linarith
  have hm4 : gbar g + 4 * sp.Δ ≤ sp.ts m := hp.trans ((ts_le_iff sp).2 (by omega))
  have hV : (latestView sp (tr.post j) ℓ.frame (tr.time j)).1 =
      voteView (tr.post j) ℓ.frame m ⊤ := by
    rw [← hm]; rfl
  unfold acHead
  rw [hV, hm]
  have hsupp : (voteView (tr.post j) ℓ.frame m ⊤).support ⊆
      (voteView (tr.post j) ℓ.frame m ⊤).votes := fun v hv => List.mem_of_mem_filter hv
  have hvotes_sub : (voteView (tr.post j) ℓ.frame m ⊤).votes ⊆
      {v | v ∈ (tr.post j).pool m} := by
    intro v hv
    have := List.mem_of_mem_filter hv
    simpa [SAState.poolAt] using this
  have h1 : H ⊆ supporters ℓ.frame (voteView (tr.post j) ℓ.frame m ⊤) m P := by
    intro u hu
    obtain ⟨i, e, hv, hes⟩ := honest_votes_in_slot hS hm4 u hu
    obtain ⟨Hd', hHd', hHd'r, hPHd'⟩ := hvotes u hu i e hv (by omega)
    obtain ⟨Hd, hHdt, hHdr, hHds, hh⟩ := late_vote_held_of_frame hS hy hc hm4 htm hu hv hes
      fun Hd hHd hHdr => by
        rw [hU.1 hHd hHd' (hHdr.trans hHd'r.symm)]
        exact ((hΦ.rooted.2 P hPt).mono hΦU).trans hPHd'
    obtain ⟨hmem, hvst, hbst⟩ := hh (j + 1) (Or.inr rfl)
    rw [hst] at hmem hvst hbst
    obtain ⟨hval, -⟩ := castAt_spec hr hu ⟨hv.choose_spec.1, hv.choose_spec.2⟩
    have hres : resolutionTime (tr.post j) ℓ.frame e.msg < ⊤ :=
      resolutionTime_lt_of hΦ hHdt hHdr (hes ▸ hHds) (hvst.trans (etime_lt_top _))
        (hbst.trans (etime_lt_top _))
    have hmemv : e.msg ∈ (voteViewList (tr.post j) ℓ.frame m ⊤).1 := by
      simp only [voteViewList, SAState.poolAt, List.mem_filter, decide_eq_true_eq]
      exact ⟨by simpa using hmem, hvst.trans (etime_lt_top _)⟩
    refine ⟨fun heq => honest_not_equivocator_pool hS hy (j + 1) m hu ?_, e.msg, ?_, hval,
      by rw [hes], ?_⟩
    · rw [hst]; exact equivocators_mono hvotes_sub heq
    · change e.msg ∈ (voteViewList (tr.post j) ℓ.frame m ⊤).2
      simp only [voteViewList, List.mem_filter, decide_eq_true_eq] at hmemv ⊢
      exact ⟨hmemv, hres⟩
    · obtain rfl : Hd = Hd' := hU.1 (hΦU hHdt) hHd' (hHdr.trans hHd'r.symm)
      exact ⟨Hd, hHdt, hHdr, anc_tree_of_anc_U hU hΦ hΦU hPt hPHd' hHdt⟩
  have h3 : (Set.univ : Set (Fin sp.n)).ncard < 2 * H.ncard := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
    have hn : H.ncard + Hᶜ.ncard = sp.n := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    have := hS.two_faulty_lt
    omega
  exact anc_getHead hU hΦ hΦU (tr.post j) (tr.time j) _ (m : Int) (dom := ℓ.frame.tree)
    subset_rfl (fun B hB X hX => mem_of_anc hX hB) (Or.inl hPv) hlocks
    fun X Cx hCx hpx hCxP => isBest_of_majority hΦ hsupp (fun B hB => hB.1) h1
      (Set.subset_univ _) h3 hCx hpx hCxP

/-- `head_extends_of_frame` under trivial frames, where every tree block is viable. -/
theorem head_extends (hS : StandaloneRun tr H U proposer g) {p : Nat} {P : Blk sp.n FGP}
    (hp : gbar g + 4 * sp.Δ ≤ sp.ts p)
    (hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt y j ℓ) (htj : sp.ts p + 6 * sp.Δ ≤ tr.time j) (hPt : P ∈ ℓ.frame.tree)
    (hlocks : ∀ L ∈ liveLockBlocks sp (tr.post j).locks ℓ.frame (tr.time j),
      Compatible U L P) :
    ℓ.frame.Anc P (acHead sp (tr.post j) ℓ.frame (tr.time j)) := by
  obtain ⟨hΦ, -⟩ := frameIn_of_callAt hS.run.localRun hy hc
  obtain ⟨-, hfc, hvh, -⟩ := hS.trivial y hy j ℓ hc
  exact head_extends_of_frame hS.toHealthyBase hp hvotes hy hc htj
    ⟨hPt, by rw [hfc]; exact hΦ.rooted.2 P hPt, P, hPt, by rw [hvh]; exact hPt,
      Relation.ReflTransGen.refl⟩ hlocks

/-- **The confirmed tip from the frame** (h1 §5, H.2 §7): in a well-formed frame inside a coherent
`U`, a block `P` below both the effective record (`latest_confirmed` if in the tree, else `Φ.F`)
and the head is below the confirmed tip, the deepest common ancestor of the two (when `P` is not
in the tree it is below `Φ.F`, which every block of the tree extends). -/
theorem anc_acConfirmed_of_frame (hU : Coherent U) {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    (hΦU : Φ.tree ⊆ U) {A : SAState sp.n} {t : Time} {P : Blk sp.n FGP}
    (hPC : Anc U P ((lookup Φ A.latestConfirmed).getD Φ.F))
    (hPH : Anc U P (acHead sp A Φ t)) : Anc U P (acConfirmed sp A Φ t) := by
  have hCt : (lookup Φ A.latestConfirmed).getD Φ.F ∈ Φ.tree := by
    cases h : lookup Φ A.latestConfirmed with
    | none => exact hΦ.rooted.1
    | some R => exact (lookup_eq_some h).1
  have hHt : acHead sp A Φ t ∈ Φ.tree :=
    getHead_mem' hΦ (T := Φ.viableTree Φ.tree) (fun _ hX => hX.1) _ _ _ _
  unfold acConfirmed
  dsimp only
  have hFS : Φ.F ∈ {X | X ∈ Φ.tree ∧ Φ.Anc X ((lookup Φ A.latestConfirmed).getD Φ.F) ∧
      Φ.Anc X (acHead sp A Φ t)} :=
    ⟨hΦ.rooted.1, hΦ.rooted.2 _ hCt, hΦ.rooted.2 _ hHt⟩
  obtain ⟨D, hD⟩ := exists_deepest hΦ (fun X h => h.1) ⟨Φ.F, hFS⟩
  have hch : ∀ B ∈ {X | X ∈ Φ.tree ∧ Φ.Anc X ((lookup Φ A.latestConfirmed).getD Φ.F) ∧
      Φ.Anc X (acHead sp A Φ t)}, ∀ C ∈ {X | X ∈ Φ.tree ∧
      Φ.Anc X ((lookup Φ A.latestConfirmed).getD Φ.F) ∧ Φ.Anc X (acHead sp A Φ t)},
      Compatible Φ.tree B C := fun B hB C hC => anc_total hΦ.coherent hB.2.1 hC.2.1
  rw [hD, Option.getD_some]
  by_cases hPt : P ∈ Φ.tree
  · exact (anc_deepest hΦ (fun X h => h.1) hch hD P
      ⟨hPt, anc_tree_of_anc_U hU hΦ hΦU hPt hPC hCt,
        anc_tree_of_anc_U hU hΦ hΦU hPt hPH hHt⟩).mono hΦU
  · rcases anc_total hU hPC ((hΦ.rooted.2 _ hCt).mono hΦU) with h | h
    · exact h.trans ((anc_deepest hΦ (fun X h => h.1) hch hD Φ.F hFS).mono hΦU)
    · exact absurd (frame_mem_of_between sp hU hΦ hΦU hCt hPC h) hPt

/-- The confirmed tip when the record names a block of the frame extending `P` and the head
extends `P`. -/
theorem anc_acConfirmed_of_record (hU : Coherent U) {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    (hΦU : Φ.tree ⊆ U) {A : SAState sp.n} {t : Time} {P R : Blk sp.n FGP} (hR : R ∈ Φ.tree)
    (hRr : R.root = A.latestConfirmed) (hPR : Φ.Anc P R) (hPH : Φ.Anc P (acHead sp A Φ t)) :
    Anc U P (acConfirmed sp A Φ t) := by
  have hlk : lookup Φ A.latestConfirmed = some R := by
    cases h : lookup Φ A.latestConfirmed with
    | none => exact absurd ⟨R, hR, hRr⟩ (lookup_eq_none h)
    | some R' =>
      obtain ⟨h1, h2⟩ := lookup_eq_some h
      rw [hΦ.coherent.1 h1 hR (h2.trans hRr.symm)]
  refine anc_acConfirmed_of_frame hU hΦ hΦU ?_ (hPH.mono hΦU)
  rw [hlk, Option.getD_some]
  exact hPR.mono hΦU

/-- Finite stamped honest batch from actual unanimous casts. The actual-vote existence
input is separate from agreement; no ready-proposal support clause is needed. -/
theorem unanimous_pool_before {b : Time} (hS : HealthyBaseUpTo tr H U proposer g b)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ell : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y j ell) {s : Nat}
    (hs : gbar g + 4 * sp.Δ ≤ sp.ts s) (ht : sp.ts s + 2 * sp.Δ ≤ tr.time j)
    (hjb : tr.time j ≤ b)
    (hdeadline : ∀ k ≤ j, ∀ t, gbar g ≤ t → tr.deadline y k t ≤ max t (sp.ts s) + sp.Δ)
    (hrestart : ∀ k ≤ j, tr.RestartAt y k → tr.time k < sp.ts s)
    {P : Blk sp.n FGP} (hPt : P ∈ ell.frame.tree)
    (hvotes : ∀ x ∈ H, ∃ i e, VoteAt tr x i e ∧ e.msg.slot = s ∧ e.msg.head = P.root) :
    ∀ x ∈ H, ∃ v ∈ (tr.state y j).pool s, v.val = x ∧ v.head = P.root ∧
      resolutionTime (tr.state y j) ell.frame v < ETime.of (sp.ts s + 2 * sp.Δ) ∧
      ∀ v' ∈ (tr.state y j).pool s, v'.val = x → v' = v := by
  have hr := hS.run.localRun
  obtain ⟨hPhi, hPhiU⟩ := frameIn_of_callAt hr hy hc
  intro x hx
  obtain ⟨i, e, hv, hes, heP⟩ := hvotes x hx
  obtain ⟨B, hB, hBr, hBs, hmem, hvs, hbs⟩ :=
    late_vote_held_of_frame_before hS hy hc hs ht hjb hdeadline hrestart hx hv hes
      (fun B hBU hBr => by
        rw [hr.coherent.1 hBU (hPhiU hPt) (hBr.trans heP)]
        exact (hPhi.rooted.2 P hPt).mono hPhiU)
  obtain ⟨hval, -⟩ := castAt_spec hr hx ⟨hv.choose_spec.1, hv.choose_spec.2⟩
  refine ⟨e.msg, hmem, hval, heP,
    resolutionTime_lt_of hPhi hB hBr (hes ▸ hBs) hvs hbs, ?_⟩
  intro v' hv' hv'x
  obtain ⟨q, -, e', he', rfl⟩ := hS.run.honest.pool_vote y hy j s v' hv' (hv'x ▸ hx)
  rw [hv'x] at he'
  obtain ⟨-, rfl⟩ := (one_vote_per_slot sp) FGP ro H U tr hr x hx q i e' e he' hv
    ((state_pool_slot sp hr hy j s _ hv').trans hes.symm)
  rfl

end Consensus.Goldilocks.SA

end

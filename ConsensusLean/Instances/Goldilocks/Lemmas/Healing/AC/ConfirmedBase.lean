module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLock
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Opponents
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.HonestPool

public section

/-! # Goldilocks Healing: the confirmed tip after an honest proposal

The late honest votes held at a call, and the fast selection of a result that passes the fast
test, which is the result itself (`fastSelect_eq_result`). -/

namespace Consensus.Goldilocks.AC

variable {wm : AC.WriteMode}

variable {FGP : Type} {sp : ACParams} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : GTrace sp FGP} {g : Time} {proposer : Nat → Fin sp.n}

/-- Finite message service retains an actual honest vote with its strict early stamp.
Only deadlines and restarts through the receiving call are used. -/
theorem late_vote_pool_before {K : AC.CommitteeDict sp.n}
    {b : Time} (hS : HealthyBaseUpTo K tr H U proposer g b)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ell : ACLabel (goldilocksAC sp FGP)} (hc : tr.CallAt y j ell) {s : Nat}
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
  obtain ⟨hval, hslot, -, -⟩ := castAt_specU hr.toU hx ⟨hcx, hex⟩
  have hti : tr.time i ≤ sp.ts s + sp.Δ := by
    have hh := vote_time_leU hr.toU hx ⟨ellx, hcx, hex⟩
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
    rcases held_of_processAtU hr.toU hy hproc (by rw [hqs, hes]; omega) (by rw [hqs, hes]) with
      h | ⟨v, hv, w, hw, hne, hvval, hwval⟩
    · rwa [hes] at h
    · rw [hes] at hv hw
      exact absurd ⟨v, hv, w, hw, hne, hvval, hwval⟩
        (honest_pool_not_equivocator hr.toU hS.run.vstart hS.run.honest hy (q + 1) s hxH)
  intro c hcj
  have hst := stamp_lt_of_held_of_runU hr.toU hS.run.vstart hy (a := q + 1) (b := c) (by omega)
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
    {ell : ACLabel (goldilocksAC sp FGP)} {e' : Em sp FGP}
    (hc : CastAt tr y j ell e') {s : Nat} (hs' : e'.msg.slot = s + 1)
    (hs : gbar g + 4 * sp.Δ ≤ sp.ts s) (ht : sp.ts s + 2 * sp.Δ ≤ tr.time j)
    (hjb : tr.time j ≤ b)
    (hdeadline : ∀ k ≤ j, ∀ t, gbar g ≤ t → tr.deadline y k t ≤ max t (sp.ts s) + sp.Δ)
    (hrestart : ∀ k ≤ j, tr.RestartAt y k → tr.time k < sp.ts s)
    {x : Fin sp.n} (hx : x ∈ H) {i : Nat} {e : Em sp FGP}
    (hv : VoteAt tr x i e) (hes : e.msg.slot = s) :
    HeldBefore e'.readPoint e.msg (sp.ts s + 2 * sp.Δ) := by
  apply heldBefore_readPointU hS.run.localRun.toU hy hc (by omega)
  simpa only [hes] using late_vote_pool_before hS hy hc.1 hs ht hjb hdeadline hrestart
    hx hv hes (j + 1) (Or.inr rfl)

/-- Acceptance before a deadline carries every global ancestor before that deadline too. -/
theorem acceptedBefore_ancestor {ini} (hr : ACLocalRun (goldilocksAC sp FGP) H U tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksAC sp FGP)} (hc : tr.CallAt y i ell)
    {B X : Blk sp.n FGP} (hB : B ∈ U)
    {T : Time} (hacc : AcceptedBefore tr y B T) (hX : Anc U X B) :
    AcceptedBefore tr y X T := by
  rcases hacc with hg | ⟨k, ⟨ell, hc, hcall⟩, ht⟩
  · obtain ⟨G, hGU, hGr, hGp⟩ := genesis_mem_of_callU sp hr.toU hy i ell hc
    obtain rfl : B = G := hr.coherent.1 hB hGU (hg.trans hGr.symm)
    rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hX with rfl | ⟨Q, -, hQ⟩
    · exact Or.inl hGr
    · exact absurd (hQ.2.2.symm.trans hGp) (Option.some_ne_none _)
  · rcases Compose.frame_anc_acceptedU hr.toU hy k ell hc B
      ((accept_new sp hr hy ⟨ell, hc, hcall⟩).1 ell hc) X hX with hg | ⟨j, hj, hjX⟩
    · exact Or.inl hg
    · exact Or.inr ⟨j, hjX, lt_of_le_of_lt (hr.time_mono hj) ht⟩

/-- Guarded finite acceptance service resolves the head of an actual honest vote before
the same strict deadline as its message, retaining the acceptance witness. -/
theorem late_vote_accepted_of_frame_before {K : AC.CommitteeDict sp.n}
    {b : Time} (hS : HealthyBaseUpTo K tr H U proposer g b)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ell : ACLabel (goldilocksAC sp FGP)} (hc : tr.CallAt y j ell) {s : Nat}
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
  obtain ⟨-, hslx, -, hhead⟩ := castAt_specU hr.toU hx ⟨hcx, hex⟩
  have hti : tr.time i ≤ sp.ts s + sp.Δ := by
    have hh := vote_time_leU hr.toU hx ⟨ellx, hcx, hex⟩
    rwa [← hslx, hes] at hh
  obtain ⟨hPhix, hPhixU⟩ := frameIn_of_callAt hr hx hcx
  obtain ⟨B, hB, hBr⟩ : ∃ B ∈ ellx.frame.tree, B.root = e.msg.head :=
    ⟨_, getHead_mem hPhix (fun _ h => (voteDomain_subset_tree h.1)) e.readPoint (tr.time i)
      (mergedVoteView sp e.readPoint ellx.frame e.msg.slot) ((e.msg.slot : Int) - 1)
      (T := ellx.frame.viableTree (voteDomain sp e.readPoint ellx.frame e.msg.slot)),
      hhead.symm⟩
  have hBs : B.slot ≤ s := by
    have hh := frame_slot_leU sp hr.toU hx hcx B hB
    rwa [← hslx, hes] at hh
  have hFB := hF B (hPhixU hB) hBr
  obtain ⟨hBy, hAB⟩ : B ∈ ell.frame.tree ∧ AcceptedBefore tr y B (sp.ts s + 2 * sp.Δ) := by
    rcases Compose.frame_anc_acceptedU hr.toU hx i ellx hcx B hB B .refl with
      hg | ⟨q, hqi, hacc⟩
    · refine ⟨?_, Or.inl hg⟩
      obtain ⟨G, hGU, hGr, hGp⟩ := genesis_mem_of_callU sp hr.toU hy j ell hc
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
    exact ⟨mem_tree_of_acceptAtU sp hr.toU hy har hrj hc hFB, Or.inr ⟨r, har, hrt⟩⟩
  have hstamp := blockStamp_lt_of_acceptedBeforeU sp hr.toU hS.run.vstart hy hc hBy hAB
    (fun k hk hrs => lt_trans (hrestart k (by omega) hrs) (by linarith only [hDelta])) (Or.inl ht)
  exact ⟨B, hBy, hBr, hBs, hpool.1, hpool.2, hBr ▸ hstamp, hAB⟩

/-- Guarded finite acceptance service resolves the head of an actual honest vote before
the same strict deadline as its message. The output is at the observing pre-state. -/
theorem late_vote_held_of_frame_before {K : AC.CommitteeDict sp.n}
    {b : Time} (hS : HealthyBaseUpTo K tr H U proposer g b)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ell : ACLabel (goldilocksAC sp FGP)} (hc : tr.CallAt y j ell) {s : Nat}
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
    {ell : ACLabel (goldilocksAC sp FGP)} {e' : Em sp FGP}
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
  refine ⟨hr.awake_of_call y hy j ell hc.1, (castAt_specU hr.toU hy hc).2.2.1, ?_, ?_⟩
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

/-! ## The slot committees over a finite healthy base -/

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

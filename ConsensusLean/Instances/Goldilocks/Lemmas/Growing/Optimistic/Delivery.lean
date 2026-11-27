module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Optimistic.Locks
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.SuffixBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.ServedSteps
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Timing
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Engine.ArmingSteps
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Optimistic inclusion: the votes reach the optimistic check before `t_p + 2Δ`

A node `y` honest at `t_p + 2Δ` and awake on `[t_p, t_p + 2Δ]` holds, before `t_p + 2Δ`, every
slot-`p` vote of a validator honest at `t_p + 2Δ` (`vote_point_at`): the message service at
`y`'s tick at `t_p + 2Δ` puts the vote in `y`'s pool there; the cut at which `y` first admitted it
(a receipt or `y`'s own emission) is an optimistic check point whose state holds it, at a time
in `[t_p, t_p + 2Δ)` (no non-restart call precedes the tick at its time), and `y`'s pool keeps it
until `t_p + 2Δ` (no restart while `y` is awake).

Likewise for the proposal `P` (`proposal_point_at`): every call of `y` through `t_p + 2Δ` has
`Σ.F ⪯ P` (S1 and the slot bound), so the acceptance relay brings `P`, accepted by its proposer at
`t_p`, to `y` by `t_p + Δ`; that `on_block` call is an optimistic check point holding `P` in its
frame, and so does every later call of `y` before `t_p + 2Δ`.

Every step is proved. -/

namespace Consensus.Goldilocks.Compose.Growing

open AC (ACParams Vote Payload)

variable {sp : ACParams}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- A node awake on `[a, z]` has no restart at a cut after a call of it at a time `≥ a` and at a
time `≤ z`, when it is honest at `z`. -/
private theorem no_restart_after_call {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} {a z : Time} (hy : y ∈ H z) (haw : ∀ u, a ≤ u → u ≤ z → tr.awake y u)
    {c : Nat} (hc : tr.IsCall y c) (hca : a ≤ tr.time c) {r : Nat} (hcr : c < r)
    (hrz : tr.time r ≤ z) : ¬ tr.RestartAt y r := by
  intro hr
  obtain ⟨u, -, hur, hnaw, hcalls⟩ := hrun.sleep_of_restart y r (hrun.antitone hrz hy) hr
  have hcu := hcalls c hcr hc
  exact hnaw (haw u (by linarith) (by linarith))

/-- **An honest validator's vote is the only pool vote of its validator and slot**, in the pool of
a node honest at `d` in the prefix through `d`, when the validator is honest
at `d`. -/
private theorem pool_vote_unique {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {d : Time} (hd : 0 ≤ d) {y : Fin sp.n} (hy : y ∈ H d) {c : Nat}
    {σ : Nat} {w : Vote sp.n}
    (hw : w ∈ ((tr.projAC.upTo d).state y c).pool σ) {x : Fin sp.n} (hxd : x ∈ H d)
    (hwx : w.val = x) {j : Nat} {e : AC.Em sp (List (FG.Att sp.n))} (he : HVoteAt tr H x j e)
    (hes : e.msg.slot = σ) : w = e.msg := by
  have hac := acRun_upTo hrun hnc hd
  obtain ⟨j', -, e', hv', rfl⟩ := hac.honest.pool_vote y hy c σ w hw (hwx ▸ hxd)
  have hs := AC.state_pool_slotU sp hac.localRun.toU hrun.vstart hy c σ _ hw
  obtain ⟨hjd, hv'⟩ := ac_voteAt_upTo.mp hv'
  rw [hwx] at hv'
  obtain ⟨-, rfl⟩ := one_vote_per_slot_at hrun hnc (hVoteAt_iff.2 ⟨hrun.antitone hjd hxd, hv'⟩) he
    (hs.trans hes.symm)
  rfl

/-- A time in `[t_p, t_p + 4Δ)` is of slot `p`. -/
theorem slot_eq_of_window {p : Nat} {t : Time} (h1 : sp.ts p ≤ t)
    (h2 : t < sp.ts p + 4 * sp.Δ) : sp.slot t = p := by
  have hp0 : (0 : Time) ≤ sp.ts p := ts_natCast_nonneg p
  have ht0 : 0 ≤ t := hp0.trans h1
  have hlo := (AC.ts_le_iff_le_slot sp ht0 p).1 h1
  have hhi : ¬ ((p + 1 : Nat) : Int) ≤ sp.slot t := fun h => by
    have := (AC.ts_le_iff_le_slot sp ht0 _).2 h
    have hs : sp.ts ((p + 1 : Nat) : Int) = sp.ts p + 4 * sp.Δ := by
      simp only [ACParams.ts]; push_cast; ring
    linarith
  push_cast at hlo hhi
  omega

/-- **B2v: a vote reaches the optimistic check before `t_p + 2Δ`.** For `y` honest at
`t_p + 2Δ ≤ b` and awake on `[t_p, t_p + 2Δ]`, a slot-`p` vote of a validator honest at
`t_p + 2Δ` is in the slot-`p` pool of an optimistic check point of `y` at a time in
`[t_p, t_p + 2Δ)`, and in `y`'s slot-`p` pool at every later cut before `t_p + 2Δ`. -/
theorem vote_point_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {b : Time} (hsync : SleepyServiceBefore tr H ΔF b) {p : Nat}
    (hpb : sp.ts p + 2 * sp.Δ ≤ b) {y : Fin sp.n} (hy : y ∈ H (sp.ts p + 2 * sp.Δ))
    (hw : ∀ d, sp.ts p ≤ d → d ≤ sp.ts p + 2 * sp.Δ → tr.awake y d ∧ tr.JoinedAt y d)
    {x : Fin sp.n} (hx : x ∈ H (sp.ts p + 2 * sp.Δ)) {j : Nat}
    {e : AC.Em sp (List (FG.Att sp.n))} (he : HVoteAt tr H x j e) (hes : e.msg.slot = p) :
    ∃ k ℓ A, AC.OptimisticPoint tr.projAC y k ℓ A ∧ sp.ts p ≤ tr.time k ∧
      tr.time k < sp.ts p + 2 * sp.Δ ∧ e.msg ∈ A.pool p ∧
      ∀ m, k < m → tr.time m < sp.ts p + 2 * sp.Δ → e.msg ∈ (tr.state y m).ac.pool p := by
  have hΔ := sp.toParams.hΔ
  set d := sp.ts p + 2 * sp.Δ with hd
  have hp0 : (0 : Time) ≤ sp.ts p := ts_natCast_nonneg p
  have hd0 : 0 ≤ d := by linarith
  have hm := hrun.time_mono
  have hac := acRun_upTo hrun hnc hd0
  have hr := hac.localRun
  have haw : ∀ u, sp.ts p ≤ u → u ≤ d → tr.awake y u := fun u h1 h2 => (hw u h1 h2).1
  -- the vote's cast
  obtain ⟨hxj, ℓx, hcx, hex⟩ := hVoteAt_iff.1 he
  obtain ⟨htj0, htj1⟩ := cast_time_at hrun hnc hxj ⟨hcx, hex⟩
  rw [hes] at htj0 htj1
  have hsend : tr.projAC.SendOrAdmit x j e.msg := ⟨ℓx, hcx, Or.inl ⟨e, hex, rfl⟩⟩
  -- `y`'s tick at `d`
  have hpub : sp.toParams.IsPublic d :=
    ⟨4 * (p : Int) + 2, by simp only [hd, ACParams.ts]; ring⟩
  obtain ⟨jc, hT⟩ := hrun.tick_of_awake y d hy hd0 hpub (haw d (by linarith) le_rfl)
  obtain ⟨ℓc, hcc, -, hjc⟩ := tickAt_acCall hT
  have hpubp : sp.toParams.IsPublic (sp.ts p) := ⟨4 * (p : Int), by simp only [ACParams.ts]; ring⟩
  have hdl : ∀ k ≤ jc, tr.projAC.deadline y k (tr.time j) ≤ d := fun k hk => by
    have h := Compose.ac_deadline_le_of_restarts (T := tr.projAC) (c := k) (a := sp.ts p)
      (fun r hr hrr => restart_le_of_awakeOn_at hrun hy haw le_rfl (by linarith) hp0 hpubp
        (projAC_restartAt.1 hrr) (by rw [← hjc]; exact hm (hr.trans hk))) (tr.time j)
    have := max_eq_left htj0
    linarith
  have hyc : y ∈ H (tr.time jc) := hjc ▸ hy
  have hserv := hsync.message x j e.msg (hrun.antitone (by linarith) hx) hsend
    (hrun.time_nonneg j) y jc ℓc hyc hcc ((hdl jc le_rfl).trans hpb) (hjc ▸ hdl jc le_rfl)
  -- the uniqueness of `x`'s slot-`p` pool vote
  have huniq : ∀ c, ∀ w ∈ ((tr.projAC.upTo d).state y c).pool p, w.val = x → w = e.msg :=
    fun c w hw hwx => pool_vote_unique hrun hnc hd0 hy hw hx hwx he hes
  have hx' : e.msg.val = x := (castAt_spec_at hrun hnc hxj ⟨hcx, hex⟩).1
  -- a processing of the vote by `y` in `[t_p, d)`
  obtain ⟨k, hkp, hk0, hk1⟩ : ∃ k, ACTrace.ProcessAt (tr.projAC.upTo d) y k e.msg ∧
      sp.ts p ≤ tr.time k ∧ tr.time k < d := by
    rcases (AC.messageServedBefore_iff _ _ _ _).1 hserv with ⟨k, hkj, hτk, ⟨ℓ, hc, hl⟩, hkd⟩ | hret
    · have hkd' := lt_of_lt_of_le hkd (hdl k hkj)
      exact ⟨k, ⟨ℓ, (Trace.upTo_callAt _).2 ⟨hkd'.le, hc⟩, hl⟩, htj0.trans hτk, hkd'⟩
    obtain ⟨q, hq, hev, -⟩ := (AC.retainedBefore_iff _ _ _ _).1 hret
    have hqd : ∀ k < q, tr.time k ≤ d := fun k hk => by rw [← hjc]; exact hm (hk.le.trans hq)
    have hst := Trace.upTo_state tr.projAC y hqd
    rcases (AC.poolEvidenceBefore_iff _ _ _).1 hev with ⟨hv, hstamp⟩ |
        ⟨a, c, hac', hav, hcv, has, hcs, ⟨ha, -⟩, ⟨hc, -⟩⟩
    · rw [← hst] at hv hstamp
      obtain ⟨k, hkq, hsa, hks, hsl⟩ := AC.pool_origin_sentU hr.toU hrun.vstart hy q e.msg hv
      rw [hks] at hstamp
      have hkd : tr.time k < d :=
        lt_of_lt_of_le (WithTop.coe_lt_coe.1 (WithBot.coe_lt_coe.1 hstamp)) (hdl jc le_rfl)
      rw [← RunTrace.upTo_projAC] at hsa
      have hsrc := Compose.sendOrAdmit_forward_source (hrun.upTo hd0) hy hsa
      refine ⟨k, ?_, ?_, hkd⟩
      · rw [← RunTrace.upTo_projAC]
        rcases hsrc with ⟨ℓ, hc, e', he', hm'⟩ | ⟨⟨ℓ, hc, hl⟩, -⟩
        · exact ⟨ℓ, projAC_callAt.2 hc, Or.inr ⟨e', he', hm'⟩⟩
        · exact ⟨ℓ, projAC_callAt.2 hc, Or.inl hl⟩
      · rw [hes] at hsl
        exact (AC.ts_le_iff_le_slot sp (hrun.time_nonneg k) p).2 (by exact_mod_cast hsl)
    · rw [← hst] at ha hc
      rw [has, hes] at ha; rw [hcs, hes] at hc
      exact absurd ((huniq q a ha (hav.trans hx')).trans
        (huniq q c hc (hcv.trans hx')).symm) hac'
  -- its optimistic check point holds the vote
  have hks : sp.slot ((tr.projAC.upTo d).time k) = p :=
    slot_eq_of_window (t := tr.time k) hk0 (by linarith)
  have h1 : ((sp.slot ((tr.projAC.upTo d).time k) : Nat) : Int) - 1 ≤ e.msg.slot := by
    rw [hks, hes]; omega
  have h2 : e.msg.slot ≤ sp.slot ((tr.projAC.upTo d).time k) := by rw [hks, hes]
  obtain ⟨ℓ, hcT, hl⟩ := hkp
  obtain ⟨A, hpt, hA⟩ : ∃ A, AC.OptimisticPoint (tr.projAC.upTo d) y k ℓ A ∧
      (e.msg ∈ A.pool e.msg.slot ∨
        e.msg.val ∈ AC.equivocators {w | w ∈ A.pool e.msg.slot}) := by
    rcases hl with hm' | ⟨e', he', hem⟩
    · exact ⟨_, ⟨hcT, Or.inl ⟨e.msg, hm', rfl⟩⟩, AC.admitVote_held _ _ _ h1 h2⟩
    · rw [← hem] at h1 h2 ⊢
      exact ⟨_, ⟨hcT, Or.inr (Or.inr ⟨e', he', rfl⟩)⟩, AC.admitVote_held _ _ _ h1 h2⟩
  have hpost := AC.optimisticPoint_pool_postU hr.toU hy hpt p
  have hvA : e.msg ∈ A.pool p := by
    rw [hes] at hA
    rcases hA with h | ⟨a, ha, c, hc, hac', hav, hcv⟩
    · exact h
    · exact absurd ((huniq _ a (hpost ha) (hav.trans hx')).trans
        (huniq _ c (hpost hc) (hcv.trans hx')).symm) hac'
  obtain ⟨-, hpt'⟩ := (AC.upTo_optimisticPoint (tr := tr.projAC) (d := d) hm).1 hpt
  refine ⟨k, ℓ, A, hpt', hk0, hk1, hvA, fun m hkm hmd => ?_⟩
  -- no restart of `y` before `d`, so its pool keeps the vote
  have hcall : tr.IsCall y k := ⟨_, projAC_callAt.1 ((Trace.upTo_callAt _).1 hcT).2⟩
  have hnr : ∀ r, k + 1 ≤ r → r < m → ¬ ACTrace.RestartAt (tr.projAC.upTo d) y r := by
    intro r hr1 hr2 hrr
    obtain ⟨hrd, hrr⟩ := (ac_restartAt_upTo tr.projAC).1 hrr
    exact no_restart_after_call hrun hy haw hcall hk0 (by omega) hrd (projAC_restartAt.1 hrr)
  have hv := AC.pool_mono hr hy (Nat.succ_le_of_lt hkm) hnr p (hpost hvA)
  have hmt : ∀ k' < m, tr.time k' ≤ d := fun k' hk' => (hm hk'.le).trans hmd.le
  rwa [Trace.upTo_state tr.projAC y hmt, projAC_state_at hrun (hrun.antitone hmd.le hy)] at hv

/-- **`Σ.F` of a call is at or below the proposal**: at a call of a node honest then, at a cut
through the horizon `b ≥ t_s + 6Δ` of the proposal's origin, at a slot at most `s`, `Σ.F` is on
the origin chain (S1), so compatible with the proposal `P` (an origin within `b`); it is genesis
or strictly below a block of the frame, so of a slot below `s`, hence not strictly above `P`. -/
private theorem frame_F_anc_proposal_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {b : Time} (hb0 : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hB : SleepyBoundsFrom tr H 0 b) (hinv : SleepyInvariantUpTo tr H b) {p : Fin sp.n} {k : Nat}
    {P : AC.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hp : p ∈ H (sp.ts s + sp.Δ))
    (hP : tr.ProposesAt p k P) (hPs : P.slot = s) (hsb : sp.ts s + 6 * sp.Δ ≤ b)
    {K : AC.CommitteeDict sp.n} (hKB : CommitteeFacts tr H K)
    (hBK : CommitteeBoundsFrom tr H K 0 b) {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ℓ : ACLabel (goldilocksNode sp)} (hc : tr.projAC.CallAt y i ℓ) (hb : tr.time i ≤ b)
    (hsl : sp.slot (tr.time i) ≤ s) : Anc (tr.HonestBlocksAt H) ℓ.frame.F P := by
  have hU := honestBlocksAt_coherent hrun hnc
  obtain ⟨hPo, hPU⟩ := proposal_originWithin_at hrun hnc hb0 hsync hB hinv hp hP hPs hsb hKB hBK
  have hr := hrun.upTo (hrun.time_nonneg i)
  have hst : (tr.upTo (tr.time i)).state y i = tr.state y i :=
    Trace.upTo_state tr y fun k hk => hrun.time_mono hk.le
  have hR := Compose.fg_reachable hr.toLocalRun hy i
  rw [hst] at hR
  obtain ⟨hFt, -, -, -⟩ := Store.cache_invariants _ _ _ _ hR
  have hcoh := (Store.accepted_tree _ _ _ _ hR).2.1
  have hfr : ℓ.frame = Node.frame (tr.state y i) := frame_of_projAC_at hrun hy hc
  have hFU := mem_honestBlocksAt hrun hy hFt
  have hFR : Compatible (tr.HonestBlocksAt H) (tr.state y i).fg.F P :=
    OnOriginChainWithin.compatible hrun hnc hinv.origins_compatible hFU hPU
      (hinv.caches_at_cut hrun hb0 hy (fun k hk => (hrun.time_mono hk.le).trans hb)).1
      (onOriginChainWithin_iff.2 (Or.inr ⟨P, s, hPo, Relation.ReflTransGen.refl⟩))
  rw [hfr]
  change Anc _ (tr.state y i).fg.F P
  by_cases hg : (tr.state y i).fg.F =
      sp.toParams.genesisBlock (goldilocksNode sp).genesisPayload
  · exact honestAt_genesis_root_anc hrun hU hFU (by rw [hg]; rfl) hPU
  obtain ⟨B, hBt, -, hFB, hne⟩ := Store.F_lt_finalizer hR hg
  have hBf : B ∈ ℓ.frame.tree := by rw [hfr]; exact ⟨hBt, hFB⟩
  have hBs := frame_slot_le_at hrun hnc hy hc B hBf
  have hFs : (tr.state y i).fg.F.slot < B.slot := (Anc.slot_le hcoh hFB).2 hne
  rcases hFR with h | hPF
  · exact h
  by_cases hPFe : P = (tr.state y i).fg.F
  · exact hPFe ▸ .refl
  have := (Anc.slot_le hU hPF).2 hPFe
  omega

/-- **B2P: the proposal reaches the optimistic check before `t_s + 2Δ`.** For the proposal `P` of
slot `s` by a proposer honest at `t_s + Δ` and `y` honest at `t_s + 2Δ`
and awake on `[t_s, t_s + 2Δ]`: `y` receives `P` (an `on_block` optimistic check point) at a time
in `[t_s, t_s + 2Δ)`, and `P` is in the frame of every later call of `y` before `t_s + 2Δ`. -/
theorem proposal_point_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {b : Time} (hb0 : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hB : SleepyBoundsFrom tr H 0 b) (hinv : SleepyInvariantUpTo tr H b) {p : Fin sp.n} {k : Nat}
    {P : AC.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hp : p ∈ H (sp.ts s + sp.Δ))
    (hP : tr.ProposesAt p k P) (hPs : P.slot = s) (hsb : sp.ts s + 6 * sp.Δ ≤ b)
    {K : AC.CommitteeDict sp.n} (hKB : CommitteeFacts tr H K)
    (hBK : CommitteeBoundsFrom tr H K 0 b) {y : Fin sp.n} (hy : y ∈ H (sp.ts s + 2 * sp.Δ))
    (hw : ∀ d, sp.ts s ≤ d → d ≤ sp.ts s + 2 * sp.Δ → tr.awake y d ∧ tr.JoinedAt y d) :
    ∃ k ℓ A, AC.OptimisticPoint tr.projAC y k ℓ A ∧ sp.ts s ≤ tr.time k ∧
      tr.time k < sp.ts s + 2 * sp.Δ ∧ P ∈ ℓ.frame.tree ∧
      ∀ m ℓ', k < m → tr.time m < sp.ts s + 2 * sp.Δ → tr.projAC.CallAt y m ℓ' →
        P ∈ ℓ'.frame.tree := by
  have hΔ := sp.toParams.hΔ
  set d := sp.ts s + 2 * sp.Δ with hd
  have hp0 : (0 : Time) ≤ sp.ts s := ts_natCast_nonneg s
  have hd0 : 0 ≤ d := by linarith
  have hm := hrun.time_mono
  have haw : ∀ u, sp.ts s ≤ u → u ≤ d → tr.awake y u := fun u h1 h2 => (hw u h1 h2).1
  -- every call of `y` through `d` has `Σ.F ⪯ P`
  have hF : ∀ i ℓ, tr.time i ≤ d → tr.projAC.CallAt y i ℓ →
      Anc (tr.HonestBlocksAt H) ℓ.frame.F P := by
    intro i ℓ hi hc
    have hsl : sp.slot (tr.time i) ≤ s := by
      by_contra h
      have h' := (AC.ts_le_iff_le_slot sp (hrun.time_nonneg i) ((s + 1 : Nat) : Int)).2
        (by push_cast; omega)
      have hs1 : sp.ts ((s + 1 : Nat) : Int) = sp.ts s + 4 * sp.Δ := by
        simp only [ACParams.ts]; push_cast; ring
      linarith
    exact frame_F_anc_proposal_at hrun hnc hb0 hsync hB hinv hp hP hPs hsb hKB hBK
      (hrun.antitone hi hy) hc (by linarith) hsl
  -- `y`'s tick at `d`
  have hpub : sp.toParams.IsPublic d :=
    ⟨4 * (s : Int) + 2, by simp only [hd, ACParams.ts]; ring⟩
  obtain ⟨jc, hT⟩ := hrun.tick_of_awake y d hy hd0 hpub (haw d (by linarith) le_rfl)
  obtain ⟨ℓc, hcc, -, hjc⟩ := tickAt_acCall hT
  have hyc : y ∈ H (tr.time jc) := hjc ▸ hy
  -- `P` is accepted by its proposer at `t_s`, at the AC cut after the block
  have htk : tr.time k = sp.ts s := by rw [hP.2.2, sp.slotTime_eq, hPs]; rfl
  have hpk : p ∈ H (tr.time k) := hrun.antitone (by rw [htk]; linarith) hp
  have hr := hrun.upTo (hrun.time_nonneg k)
  have hP' : (tr.upTo (tr.time k)).ProposesAt p k P :=
    ⟨(RunTrace.upTo_ownBlockAt tr).2 ⟨le_rfl, hP.1⟩, hP.2.1, hP.2.2⟩
  have hacc := Compose.proposal_accepted hr (hnc.upTo _) hpk hP'
  obtain ⟨ℓ', hc', hcall', ht'⟩ := Compose.accept_next hr.toLocalRun hpk hacc
  have hc'' : tr.CallAt p (k + 1) (.ac ℓ') := ((Trace.upTo_callAt _).1 hc').2
  have hk1 : tr.time (k + 1) = sp.ts s := ht'.trans htk
  have hpk1 : p ∈ H (tr.time (k + 1)) := hk1 ▸ (htk ▸ hpk)
  -- `y`'s restarts through `d` are at or before `t_s`
  have hpubs : sp.toParams.IsPublic (sp.ts s) :=
    ⟨4 * (s : Int), by simp only [ACParams.ts]; ring⟩
  have hdl : ∀ c ≤ jc, tr.projAC.deadline y c (tr.time (k + 1)) ≤ sp.ts s + sp.Δ := by
    intro c hc
    have h := Compose.ac_deadline_le_of_restarts (T := tr.projAC) (c := c) (a := sp.ts s)
      (fun r hr hrr => restart_le_of_awakeOn_at hrun hy haw le_rfl (by linarith) hp0 hpubs
        (projAC_restartAt.1 hrr) (by rw [← hjc]; exact hm (hr.trans hc))) (tr.time (k + 1))
    rw [hk1, max_self] at h
    rwa [hk1]
  obtain ⟨k', hk', hAz, hlt⟩ := hsync.acRelay p (k + 1) P hpk1
    ⟨ℓ', projAC_callAt.2 hc'', hcall'⟩ (hrun.time_nonneg _) y jc ℓc hyc hcc
    (by have := hdl jc le_rfl; linarith) (by have := hdl jc le_rfl; linarith)
    (hF jc ℓc hjc.le hcc)
  have hk'd : tr.time k' < d := by have := hdl k' hk'; linarith
  obtain ⟨ℓk, hck, hcallk⟩ := id hAz
  have hPk : P ∈ ℓk.frame.tree := mem_tree_of_acceptAt_at hrun hnc (hrun.antitone hk'd.le hy)
    hAz le_rfl hck (hF k' ℓk hk'd.le hck)
  have hk0 : sp.ts s ≤ tr.time k' := by
    have h := frame_slot_le_at hrun hnc (hrun.antitone hk'd.le hy) hck P hPk
    rw [hPs] at h
    exact (AC.ts_le_iff_le_slot sp (hrun.time_nonneg k') s).2 (by exact_mod_cast h)
  refine ⟨k', ℓk, _, ⟨hck, Or.inr (Or.inl ⟨P, hcallk, rfl⟩)⟩, hk0, hk'd, hPk,
    fun m ℓm hkm hmd hcm => ?_⟩
  exact mem_tree_of_acceptAt_at hrun hnc (hrun.antitone hmd.le hy) hAz hkm.le hcm
    (hF m ℓm hmd.le hcm)

end Consensus.Goldilocks.Compose.Growing

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FastLockRenewal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.SignGap
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.SignedTick
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.SignTick
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The warm report of a node that signs on a calendar

A node signs (runs `ac_to_fg`) only at the times its calendar allows. With a signing gap `G` from
before the warm update `t_{u+1} + 2Δ`, the node signs at a public time
`t' ∈ [t_{u+1} + 2Δ, t_{u+1} + 2Δ + G·Δ]`. At `t'` its toFG candidates hold a block above the warm
proposal (the update's own fast lock at `t_{u+1} + 2Δ`, a renewed one later), so it reports above
the proposal by `t'`, and the honest proposals of the slots from `u + 3 + ⌈G/4⌉` on extend the
report. -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
  {ini : Fin sp.n → (goldilocksNode sp).State}
variable {hold : Time}

/-- At a public signing time after a warm update deadline, a node honest then executes a joined
`ac_to_fg` call (its tick runs the FG update; proposal cuts may come first in the tick). -/
theorem toFG_call_of_sign_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g : Time} (hnr : NoRestartAfter tr H (gbar g))
    {sign : Fin sp.n → Time → Bool} (hcal : tr.SignCalendarAt proposer dg H sign)
    {y : Fin sp.n} {t : Time} {u : Nat} (hy : y ∈ H t) (hgu : gbar g ≤ sp.ts u)
    (ht : sp.ts u + 6 * sp.Δ ≤ t) (hpub : sp.toParams.IsPublic t) (hawake : tr.awake y t)
    (hsign : sign y t = true) :
    ∃ i ell, tr.projAC.CallAt y i ell ∧ ell.call = .toFG ∧ tr.time i = t ∧
      AC.joined sp (tr.projAC.state y i) (tr.time i) := by
  have hΔ := sp.toParams.hΔ
  have ht0 : 0 ≤ t := by
    have hu0 : 0 ≤ sp.ts u := by simp only [ACParams.ts]; positivity
    linarith
  obtain ⟨j, x, hg⟩ := signTickAt_of_calendar_at hrun hcal hy ht0 hpub hawake hsign
  obtain ⟨k, ell, hc, hcall, htime⟩ := Healing.toFG_call_of_signing_tick hg
  exact ⟨j + k, ell, hc, hcall, htime, joined_of_restart_le_at hrun hnc hy (by linarith)
    (fun r _ hyr hrs => (hnr y r hyr hrs).trans hgu) htime⟩

/-- A block of an honest frame above a non-genesis block is not genesis. -/
private theorem root_ne_genesis_of_anc
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp)} (hc : tr.projAC.CallAt y i ell)
    {P B : AC.Blk sp.n (List (FG.Att sp.n))} (hPg : P.root ≠ sp.genesisRoot)
    (hPB : Anc (tr.HonestBlocksAt H) P B) (hB : B ∈ ell.frame.tree) :
    B.root ≠ sp.genesisRoot := by
  intro hg
  have hr := (Compose.goldilocks_ac_projection_from (hrun.upTo (hrun.time_nonneg i))
    (hnc.upTo (tr.time i))).localRun
  rw [RunTrace.upTo_projAC] at hr
  have hc' : (tr.projAC.upTo (tr.time i)).CallAt y i ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hc⟩
  obtain ⟨G, hGU, hGr, hGp⟩ := AC.genesis_mem_of_callU sp hr.toU hy _ _ hc'
  have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hrun.time_mono (hrun.time_nonneg i)
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have hBU : B ∈ tr.HonestBlocksAt H := hsub ((AC.frameIn_of_callAt hr hy hc').2 hB)
  obtain rfl : B = G := hU.1 hBU (hsub hGU) (hg.trans hGr.symm)
  rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hPB with h | ⟨c, -, hcG⟩
  · exact hPg (by rw [← h]; exact hg)
  · simp [hcG.2.2] at hGp

/-- **The warm report of a node on a signing calendar.** For a warm honest proposal `P` of
slot `u` in a frame window, a node honest at `t_{u+1} + 2Δ + G·Δ` whose calendar
has signing gap `G` from before `t_{u+1} + 2Δ` reports a block extending `P` at a time in
`[t_u, t_{u+1} + 2Δ + G·Δ]`, and every honest proposal of a slot `x ∈ [u + 3 + ⌈G/4⌉, N]` has a
head extending that report. The frame window reaches the later of `t_N + 2Δ` and the delayed
deadline `t_{u+1} + 2Δ + G·Δ`, which at `G = 0` is `t_N + 2Δ`; at `G = 0` the report is
`KernelProof.proposal_report_follow_at`'s. At the slot committees `K` of a run from `K`'s
committee start. -/
theorem proposal_report_follow_delayed_at
    {g ΔF b t₀ : Time} {s₀ u N floor G : Nat} {kindJ : Prop}
    {J P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀)
      (max (sp.ts N + 2 * sp.Δ) (sp.ts (u + 1 : Nat) + 2 * sp.Δ + (G : Time) * sp.Δ))
      floor kindJ J)
    {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hwarm : s₀ + 2 * sp.k ≤ u)
    (hN : u + 1 ≤ N)
    (hmb : max (sp.ts N + 2 * sp.Δ) (sp.ts (u + 1 : Nat) + 2 * sp.Δ + (G : Time) * sp.Δ) ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    {sign : Fin sp.n → Time → Bool} (hcal : tr.SignCalendarAt proposer dg H sign)
    (hgap : SignGapAt sp.toParams sign G t₀) (ht₀ : t₀ ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ)
    {y : Fin sp.n} (hy : y ∈ H (sp.ts (u + 1 : Nat) + 2 * sp.Δ + (G : Time) * sp.Δ))
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∃ i ell R, y ∈ H (tr.time i) ∧ AC.ToFGAt tr.projAC y i ell R ∧
      sp.ts u ≤ tr.time i ∧ tr.time i ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ + (G : Time) * sp.Δ ∧
      Anc (tr.HonestBlocksAt H) P R ∧
      ∀ x, u + 3 + (G + 3) / 4 ≤ x → x ≤ N → ∀ w c ellp, w ∈ H (tr.time c) →
        tr.projAC.CallAt w c ellp → ellp.call = .proposal → tr.time c = sp.ts x →
        ∀ d pay, (AC.acProposal sp (tr.projAC.state w c) ellp.frame (tr.time c)).2 =
          some (d, pay) → Anc (tr.HonestBlocksAt H) R d.head := by
  have hΔ := sp.toParams.hΔ
  have hts {p q : Nat} (hpq : p ≤ q) : sp.ts p ≤ sp.ts q :=
    (AC.ts_le_iff sp).2 (by exact_mod_cast hpq)
  have hstep (a : Nat) : sp.ts (a + 1 : Nat) = sp.ts a + 4 * sp.Δ := AC.ts_succ a
  set T := sp.ts (u + 1 : Nat) + 2 * sp.Δ with hTdef
  have hT : T = sp.ts u + 6 * sp.Δ := by rw [hTdef, hstep]; ring
  have hG0 : (0 : Time) ≤ (G : Time) * sp.Δ := by positivity
  have hu0 : 0 ≤ sp.ts u := by simp only [ACParams.ts]; positivity
  have hpub : sp.toParams.IsPublic T := ⟨4 * (u : Int) + 6, by
    rw [hT]; simp only [ACParams.ts]; ring⟩
  obtain ⟨t', htl, htr, hpub', hs'⟩ := hgap.of_public (y := y) ht₀ hpub
  have hyt' : y ∈ H t' := hrun.antitone htr hy
  have hsu := hts (show s₀ ≤ u by omega)
  have hgu : gbar g ≤ sp.ts u := by linarith
  have hm1 := le_max_left (sp.ts N + 2 * sp.Δ) (T + (G : Time) * sp.Δ)
  have hm2 := le_max_right (sp.ts N + 2 * sp.Δ) (T + (G : Time) * sp.Δ)
  have hsub {hi : Time} (hh : hi ≤ max (sp.ts N + 2 * sp.Δ) (T + (G : Time) * sp.Δ)) :
      FrameWindow tr H (sp.ts s₀) hi floor kindJ J :=
    ⟨fun w i hw hlo hhi => hframe.floor_eq w i hw hlo (hhi.trans hh),
     fun w i hw hlo hhi => hframe.kind_iff w i hw hlo (hhi.trans hh),
     fun w i hw hlo hhi => hframe.root_eq w i hw hlo (hhi.trans hh)⟩
  rcases htl.eq_or_lt with heq | hlt
  · -- the calendar lets the node sign at the warm update itself
    rw [← heq] at hs'
    obtain ⟨i, ell, R, hyi, hR, hlo, hhi, hPR, hheads⟩ :=
      KernelProof.proposal_report_follow_at (hsub hm1) hrun hnc hsvc hawake hf hcatch hnr hm
        hwarm hN (hm1.trans hmb) hz hdes hP hPs hcal (hrun.antitone (by linarith) hy) hs' hK
    exact ⟨i, ell, R, hyi, hR, hlo, hhi.trans (by linarith), hPR,
      fun x hx => hheads x (by omega)⟩
  -- a later signing time: a renewed fast lock above `P` is a candidate there
  have ht'b : t' ≤ b := htr.trans (hm2.trans hmb)
  obtain ⟨i, ell, hc, hcall, hti, hjoin⟩ := toFG_call_of_sign_at hrun hnc hnr hcal hyt' hgu
    (by rw [← hT]; exact htl) hpub' (hawake y t' hyt' (by linarith) ht'b) hs'
  have hyi : y ∈ H (tr.time i) := by rw [hti]; exact hyt'
  obtain ⟨B, hB, hPB⟩ := toFG_candidate_pre_within_at hframe hrun hnc hsvc hawake hf hcatch hnr
    hm hwarm hmb hz hdes hP hPs hK hyi hc (by rw [hti]; exact hlt)
    (by rw [hti]; exact htr.trans hm2)
  -- `P` is not genesis: it was accepted by its honest proposer
  have hptime : tr.time kP = sp.ts u := by
    simpa only [sp.slotTime_eq, hPs, ACParams.ts] using hP.2.2
  have hzk : z ∈ H (tr.time kP) := hrun.antitone (by rw [hptime]; linarith only [hΔ]) hz
  have hP' : (tr.upTo (tr.time kP)).ProposesAt z kP P :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hP.1⟩, hP.2⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hacc, _⟩ :=
    Healing.honestProposalRun_of_proposesAt (hrun.upTo (hrun.time_nonneg kP))
      (hnc.upTo _) hzk hdes hP' hPs
  rw [← hdes] at hacc
  have hPg := AC.accept_ne_genesisU sp
    (Compose.goldilocks_ac_projection_from (hrun.upTo (hrun.time_nonneg kP))
      (hnc.upTo _)).localRun.toU hzk hacc
  have hBg := root_ne_genesis_of_anc hrun hnc hyi hc hPg hPB hB.1.1
  obtain ⟨r, ellr, R, hR, hrt, hBR⟩ := report_of_compatible_candidate_of_run_at hrun hnc hyi hc
    hcall hjoin hBg hB (toFG_candidates_compatible_at_call_at hrun hnc hyi hc hB)
  have hPR := hPB.trans hBR
  have hrlo := toFG_time_ge_of_ancestor_slot_at hrun hnc (hrun.antitone hrt hyi) hR hPs hPR
  have hrhi : tr.time r ≤ T + (G : Time) * sp.Δ := hrt.trans (by rw [hti]; exact htr)
  refine ⟨r, ellr, R, hrun.antitone hrt hyi, hR, hrlo, hrhi, hPR, ?_⟩
  intro x hx hxN w c ellp hw hcp hcallp htc d pay hd
  -- a head witness puts `t_N` after the delayed report
  have he : (G : Time) * sp.Δ ≤ sp.ts (u + 1 + (G + 3) / 4 : Nat) - sp.ts (u + 1 : Nat) := by
    have h4 : (G : Time) ≤ 4 * (((G + 3) / 4 : Nat) : Time) := by
      have : G ≤ 4 * ((G + 3) / 4) := by omega
      exact_mod_cast this
    have hte : sp.ts (u + 1 + (G + 3) / 4 : Nat) =
        sp.ts (u + 1 : Nat) + 4 * sp.Δ * (((G + 3) / 4 : Nat) : Time) := by
      simp only [ACParams.ts]; push_cast; ring
    have hm4 : (G : Time) * sp.Δ ≤ 4 * sp.Δ * (((G + 3) / 4 : Nat) : Time) := by
      nlinarith
    linarith
  have hxN' := hts (show u + 1 + (G + 3) / 4 + 1 ≤ N by omega)
  have hxs := hstep (u + 1 + (G + 3) / 4)
  have hNΔ : sp.ts N + sp.Δ ≤ max (sp.ts N + 2 * sp.Δ) (T + (G : Time) * sp.Δ) := by
    linarith
  exact (hsub hNΔ).toFG_later_proposal_head_within_at (e := (G + 3) / 4) hrun hnc hsvc
    hawake hf hcatch hnr hm hwarm (hNΔ.trans hmb) (hrun.antitone hrt hyi) hR hPs hPR
    (by linarith) (by linarith) (by omega) hxN hw hcp hcallp htc hd hK

end Consensus.Goldilocks.Healing.Growing

end

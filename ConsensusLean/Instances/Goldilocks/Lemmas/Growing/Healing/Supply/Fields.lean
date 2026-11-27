module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.GoldilocksBridge
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.GoldilocksHealing
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Supply.CappedOrigins
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Components
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.CommitteeFaults
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowReportOrigin
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowSigned
import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingRounds
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetRounds
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Rows
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks healing field bodies

Proofs of `ACHealing` fields at the committee-start Goldilocks run interface
`goldilocksRunInterface`, each with exactly the field's statement:

* `reportAt_iff_toFGAt`: an actual report of a node honest at it is an AC `ac_to_fg` call of the
  AC projection;
* `goldilocks_proposal_floor`: the `proposal_floor` field;
* `goldilocks_report_origin`: the `report_origin` field, with `Origin` the joined stored fast
  lock of the Goldilocks data;
* `committeeHalf_of_committeeFaults`: the committee half bound at the run's slot committees, from
  the committee fault bound with `βK ≤ 1/2` and collision freedom;
* `goldilocks_report_follow`: the `report_follow` field with report delay `G` and
  `follow = 3 + (G + 3) / 4`;
* `goldilocks_ac_healing`: the assembled canonical committee-start healing witness,
  assuming `follow ≤ sp.toParams.δt`; this supplies healing, not `ACCorrectLocal` or the endpoint.
-/

namespace Consensus.Goldilocks.Generic

open AC (ACParams ReplayOrder Payload gbar)
open Healing.Growing (HZ IsReset)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
  {sign : Fin sp.n → Time → Bool} {G : Nat}

/-- An actual report of a node honest at it is an `ac_to_fg` call of the AC projection. -/
theorem reportAt_iff_toFGAt {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini) {y : Fin sp.n}
    {i : Nat} (hy : y ∈ H (tr.time i)) {R : AC.Blk sp.n (List (FG.Att sp.n))} :
    ReportAt tr y i R ↔ ∃ ℓ, AC.ToFGAt tr.projAC y i ℓ R := by
  unfold ReportAt AC.ToFGAt
  rw [Compose.Growing.projAC_state_at hrun hy]
  refine exists_congr fun ℓ => ?_
  rw [Compose.projAC_callAt]
  rfl

/-- **The `proposal_floor` field** at the Goldilocks run interface: an honest designated proposal
inside a frame window, under the FG fault bound at its slot, has height at least the window's
floor at its proposer right after the proposal. -/
theorem goldilocks_proposal_floor {cm : Time → Finset (Fin sp.n)} {lo hi : Time}
    {floor u : Nat} {kindJ : Prop} {J B : AC.Blk sp.n (List (FG.Att sp.n))} {z : Fin sp.n}
    {kB : Nat} (hrun : (goldilocksRunInterface sp ro sign G).Run cm proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hframe : FrameWindow tr H lo hi floor kindJ J)
    (hz : z ∈ H (sp.toParams.slotTime u)) (hdes : z = proposer u) (hP : tr.ProposesAt z kB B)
    (hBs : B.slot = u) (hlo : lo ≤ sp.toParams.slotTime u) (hhi : sp.toParams.slotTime u ≤ hi)
    (hf : (H (sp.toParams.slotTime u))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n) :
    floor ≤ ((tr.state z (kB + 1)).fg.σ B.root).h := by
  have hts : sp.toParams.slotTime u = sp.ts u := by
    rw [sp.slotTime_eq]
    rfl
  rw [hts] at hz hlo hhi hf
  exact Healing.Growing.KernelProof.floor_le_warm_proposal_at
    ((goldilocksRunInterface_run_iff cm).mp hrun).1 hnc
    ⟨hframe.floor_eq, hframe.kind_iff, hframe.root_eq⟩ hz hdes hP hBs hlo hhi hf

/-- **The `report_origin` field** at the Goldilocks run interface: a high report of a node honest
at it extends the stored block of an earlier joined fast-lock write of the same node, held by it
at the write. Only collision freedom is read from the premises. -/
theorem goldilocks_report_origin {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    {hold : Time} {g ΔF a b : Time}
    {y : Fin sp.n} {i : Nat} {R : AC.Blk sp.n (List (FG.Att sp.n))}
    (_hβ : βK ≤ 1 / 2)
    (hrun : (goldilocksRunInterface sp ro sign G).Run cm proposer dg H tr)
    (hp : Premises tr H cm βK proposer dg (fun v => v.val) g ΔF b hold)
    (_hr : IsReset tr H g a) (_hab : a ≤ b) (hy : y ∈ H (tr.time i)) (_hib : tr.time i ≤ b)
    (hcap : OriginInCap sp.toParams sp.deepDepth g (tr.time i))
    (hR : ReportAt tr y i R) (hh : HZ tr H g + 1 ≤ ((tr.state y i).fg.σ R.root).h) :
    ∃ r ≤ i, ∃ j B, y ∈ H (tr.time r) ∧
      (tr.JoinedAt y (tr.time r) ∧ ∃ CV, Compose.StoredFastLockAt tr y r j B CV) ∧
      B ∈ (tr.state y r).fg.tree ∧ Anc (tr.HonestBlocksAt H) R B := by
  have hr := ((goldilocksRunInterface_run_iff cm).mp hrun).1
  have hnc := hp.noColl
  obtain ⟨ℓ, hto⟩ := (reportAt_iff_toFGAt hr hy).mp hR
  obtain ⟨r, hri, j, ellw, D, CV, hyr, hcw, hD, hfl, hRB⟩ | hdeep
    := Healing.Growing.toFG_fast_candidate_origin_at hr hnc hy hto
  swap
  · have hfast := high_report_fast_of_cap hr hp hy hto hh (goldilocks_origin_cap_bound hcap)
    rw [← Compose.Growing.projAC_state_at hr hy] at hfast
    obtain ⟨hΦ, -⟩ := Healing.Growing.frame_tree_subset_at hr hnc hy hto.1
    obtain ⟨B, hB⟩ := AC.exists_deepest hΦ (fun C hC => hC.1.1) ⟨R, hfast⟩
    obtain ⟨_, _, _, hn, -⟩ := hdeep
    rw [hn] at hB
    cases hB
  have hj : tr.JoinedAt y (tr.time r) :=
    (Healing.Growing.joinedAt_upTo_iff le_rfl).mp
      (Healing.joinedAt_of_fastLockAt (hr.upTo (hr.time_nonneg r)) (hnc.upTo _) hyr
        ((Healing.Growing.fastLockAt_upTo_iff hr.time_mono le_rfl).mpr hfl))
  obtain ⟨hok, hsub⟩ := Healing.Growing.frame_tree_subset_at hr hnc hyr hcw
  exact ⟨r, hri.le, j, ellw.frame.viableAncestor D, hyr, ⟨hj, CV, ellw, D, hcw, hfl, rfl⟩,
    hsub (AC.viableAncestor_anc hok hD).1, hRB⟩

/-- `committeeHalf_of_committeeFaults` from the committee size, positivity and facts alone, without
the rest of the run interface (its calendar and release laws). -/
theorem committeeHalf_of_facts {cm : Time → Finset (Fin sp.n)} {βK : ℚ} {g b : Time}
    (hβ : βK ≤ 1 / 2) (hpos : 0 < sp.committeeSize)
    (hsize : ∀ s, ((dictOfTime sp cm).committee s).ncard = sp.committeeSize)
    (hfacts : Compose.Growing.CommitteeFacts tr H (dictOfTime sp cm))
    (hcf : CommitteeFaultsUpTo (P := sp.toParams) βK cm H g b) :
    Healing.Growing.CommitteeHalfUpTo tr H (dictOfTime sp cm) g b :=
  ⟨hfacts, fun s hgs hsb _ hd0 hdb => hcf.committee_cs2_at hβ hpos (hsize s) hgs hsb hd0 hdb⟩

/-- **The committee half bound from the committee fault bound** at the run's slot committees:
with `βK ≤ 1/2`, the committee fault bound leaves fewer than half of each slot committee from `ḡ`
by `b` faulty at every read time in `[0, b]` (`CommitteeFaultsUpTo.committee_cs2_at`). The
committee facts, sizes and positivity are the run's, under collision freedom. No reset and no
other premise is read. -/
theorem committeeHalf_of_committeeFaults {cm : Time → Finset (Fin sp.n)} {βK : ℚ} {g b : Time}
    (hβ : βK ≤ 1 / 2)
    (hrun : (goldilocksRunInterface sp ro sign G).Run cm proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hcf : CommitteeFaultsUpTo (P := sp.toParams) βK cm H g b) :
    Healing.Growing.CommitteeHalfUpTo tr H (dictOfTime sp cm) g b := by
  obtain ⟨-, hpos, hsize, hfacts, -, -⟩ := (goldilocksRunInterface_run_iff cm).mp hrun
  exact committeeHalf_of_facts hβ hpos hsize (hfacts hnc) hcf

/-- **The `report_follow` field** at the Goldilocks run interface: after warmup the proposal is
reported by nodes honest at the delayed report deadline, and the same report is an ancestor of
later honest proposal heads. -/
theorem goldilocks_report_follow {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    {hold : Time} {g ΔF b : Time}
    {s₀ N u floor : Nat} {kindJ : Prop} {J B : AC.Blk sp.n (List (FG.Att sp.n))} {z : Fin sp.n}
    {kB : Nat} (hβ : βK ≤ 1 / 2)
    (hrun : (goldilocksRunInterface sp ro sign G).Run cm proposer dg H tr)
    (hp : Premises tr H cm βK proposer dg (fun v => v.val) g ΔF b hold)
    (hframe : FrameWindow tr H (sp.toParams.slotTime s₀)
      (shiftDelay sp.toParams G (sp.toParams.slotTime N + 2 * sp.toParams.Δ)) floor kindJ J)
    (hm : gbar g + 4 * sp.toParams.Δ ≤ sp.toParams.slotTime s₀) (hwarm : s₀ + 2 * sp.k ≤ u)
    (hN : u + 1 ≤ N)
    (hmb : shiftDelay sp.toParams G (sp.toParams.slotTime N + 2 * sp.toParams.Δ) ≤ b)
    (hB : HonestProposal tr H proposer u z kB B) :
    ∀ y, y ∈ H (shiftDelay sp.toParams G (sp.toParams.slotTime (u + 1) + 2 * sp.toParams.Δ)) →
      ∃ i R, y ∈ H (tr.time i) ∧ ReportAt tr y i R ∧ sp.toParams.slotTime u ≤ tr.time i ∧
        tr.time i ≤ shiftDelay sp.toParams G (sp.toParams.slotTime (u + 1) + 2 * sp.toParams.Δ) ∧
        Anc (tr.HonestBlocksAt H) B R ∧
        ∀ x, u + (3 + (G + 3) / 4) ≤ x → x ≤ N → ∀ w c d, w ∈ H (tr.time c) →
          ProposalHeadAt tr w c d → tr.time c = sp.toParams.slotTime x →
          Anc (tr.HonestBlocksAt H) R d.head := by
  intro y hy
  obtain ⟨hr, -, -, -, hcal, hgap⟩ := (goldilocksRunInterface_run_iff cm).mp hrun
  have hts (s : Nat) : sp.toParams.slotTime s = sp.ts s := by
    rw [sp.slotTime_eq]
    rfl
  obtain ⟨hz, hdes, hP, hPs⟩ := hB
  rw [hts] at hz hm
  rw [shiftDelay_eq_add, hts] at hy
  rw [hts, hts] at hframe
  rw [hts] at hmb
  have hmax : max (sp.ts N + 2 * sp.Δ)
      (sp.ts (u + 1 : Nat) + 2 * sp.Δ + (G : Time) * sp.Δ) ≤
      shiftDelay sp.toParams G (sp.ts N + 2 * sp.Δ) := by
    rw [shiftDelay_eq_add]
    have hG : 0 ≤ (G : Time) * sp.Δ := mul_nonneg (by positivity) sp.toParams.hΔ.le
    have hmono := sp.toParams.slotTime_strictMono.monotone hN
    rw [hts, hts] at hmono
    exact max_le (by linarith) (by linarith)
  have ht₀ : 0 ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ := by
    have hΔ := sp.toParams.hΔ
    simp only [ACParams.ts]
    positivity
  obtain ⟨i, ell, R, hyi, hto, hlo, hhi, hPR, hheads⟩ :=
    Healing.Growing.proposal_report_follow_delayed_at
      ⟨fun w j hw hl hh => hframe.floor_eq w j hw hl (hh.trans hmax),
        fun w j hw hl hh => hframe.kind_iff w j hw hl (hh.trans hmax),
        fun w j hw hl hh => hframe.root_eq w j hw hl (hh.trans hmax)⟩ hr hp.noColl
      ⟨hp.sync.deltaF, hp.sync.message, hp.sync.block, hp.sync.relay, hp.sync.signedRow,
      hp.sync.hold_le⟩
      hp.awake hp.faults hp.catchUp hp.noRestart hm hwarm hN (hmax.trans hmb) hz hdes hP hPs
      hcal hgap ht₀ hy
      (committeeHalf_of_committeeFaults hβ hrun hp.noColl hp.committee)
  refine ⟨i, R, hyi, (reportAt_iff_toFGAt hr hyi).mpr ⟨ell, hto⟩, (hts u).symm ▸ hlo,
    by rw [shiftDelay_eq_add, hts]; exact hhi, hPR, ?_⟩
  intro x hx hxN w c d hw ⟨ℓ, pay, hc, hcall, hd⟩ htc
  exact hheads x (by omega) hxN w c ℓ hw (Compose.projAC_callAt.mpr hc) hcall
    (htc.trans (hts x)) d pay (by rw [Compose.Growing.projAC_state_at hr hw]; exact hd)

/-- The Goldilocks healing witness, with the committee-start run interface and the exact
warmup, follow, drain and joined stored-fast-lock origin equations. -/
theorem goldilocks_ac_healing {Rg : Nat} (hδ : 3 + (G + 3) / 4 ≤ sp.toParams.δt) :
    goldilocksACHealing sp ro sign G Rg := by
  let O : ACHealing (goldilocksNode sp ro) (fun v => v.val)
      (goldilocksRunInterface sp ro sign G) ((Rg : Time) * sp.Δ) :=
    { warmup := 2 * sp.k
      follow := 3 + (G + 3) / 4
      reportDelay := G
      drain := 2 * sp.k + 5
      deepBudget := sp.deepDepth
      Origin := fun tr x i j B => tr.JoinedAt x (tr.time i) ∧
        ∃ CV, Compose.StoredFastLockAt tr x i j B CV
      follow_le := fun _ _ => hδ
      report_in_frame := goldilocks_report_in_frame
      proposal_floor := goldilocks_proposal_floor
      report_follow := goldilocks_report_follow
      report_origin := goldilocks_report_origin
      origins_comparable := goldilocks_origins_comparable
      heal_after_reset := fun hβ hr hp hres hab hbudget _ =>
        goldilocks_heal_after_reset hβ hr hp hres hab hbudget }
  exact ⟨goldilocksRunInterface sp ro sign G, O, goldilocksRunInterface_data,
    rfl, rfl, rfl, rfl, rfl, rfl⟩

end Consensus.Goldilocks.Generic

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.ReportFollow
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.GoldilocksBridge
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Deep
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.WitnessFloor
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Service
import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingRounds
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # `ACHealing` fields over the shadow run (draft for the adoption landing)

The Option A fields of the Goldilocks supplier, over `Growing.GoldilocksRun` and the window
`Generic.FrameWindow … M isTop J` (the restated milestone `FrameWindow`, field for field). They
are stated unpacked: the run, its committee-indexed start, signing calendar, signing gap and
committee half bound are separate premises, so the run-interface wrapper of the adopted instance
only splits its `Run` conjunction into them.

* `reportAt_iff_toFGAt`: an actual report of a node honest at it is an `ac_to_fg` call of the AC
  projection;
* `goldilocks_report_follow`: the `report_follow` field, from `proposal_report_follow_delayed_at`
  (`ReportFollow`, standard axioms);
* `goldilocks_proposal_floor`: the floor-free `proposal_floor` field, from the window-free
  `Witness.warm_proposal_store_bounds_at` (proved here with `WitnessFloor`'s store lemmas). -/

namespace Consensus.Goldilocks.Shadow.PU.Witness

open FG
open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- **The warm proposal bounds at one store** (`warm_proposal_bounds_at'` without a window): a
designated honest proposal, under the FG fault bound at its slot, reaches the predecessor of the
pre-proposal maximum height and exceeds the pre-proposal justification height. -/
theorem warm_proposal_store_bounds_at {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    {z : Fin sp.n} {kP : Nat} (hz : z ∈ H (sp.ts u)) (_hdes : z = proposer u)
    (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hf : (H (sp.ts u))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n) :
    (tr.state z kP).fg.hmax - 1 ≤ ((tr.state z (kP + 1)).fg.σ P.root).h ∧
      (tr.state z kP).fg.hj < ((tr.state z (kP + 1)).fg.σ P.root).h := by
  have htime : tr.time kP = sp.ts u := by
    simpa only [sp.slotTime_eq, hPs, ACParams.ts] using hP.2.2
  have hzk : z ∈ H (tr.time kP) := htime ▸ hz
  have ht := hrun.time_nonneg kP
  have hr := hrun.upTo ht
  have h := hr.toLocalRun
  have hP' : (tr.upTo (tr.time kP)).ProposesAt z kP P :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hP.1⟩, hP.2.1, hP.2.2⟩
  have hleB : ∀ q < kP + 1, tr.time q ≤ tr.time kP :=
    fun q hq => hrun.time_mono (by omega)
  obtain ⟨hacc, -, -⟩ := Coherence.accept_of_proposesAt hr (hnc.upTo _) hzk hP'
  obtain ⟨⟨⟨-, -⟩, hpos⟩, -, -⟩ := hP'
  rcases Coherence.blockCall_cases h hzk hacc with hg |
    ⟨j, x, fgDue, rfl, hg, hpr, d, pay, hdp, hB, hacc', ⟨ℓ₀, h₀⟩, -, hst2⟩
  · rw [RunTrace.groupAt_iff] at hg
    exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
  obtain ⟨hc1, ht1, hst1⟩ := Coherence.tick_proposal_call h hzk hg hpr
  simp only [Node.acProposal_eq] at hc1
  set tu := tr.upTo (tr.time (j + 2)) with htu
  have hc := Compose.projAC_callAt.2 hc1
  have hj1 : tu.time (j + 1) = sp.ts u := by
    rw [ht1]
    exact htime
  have hzi : z ∈ H (tr.time (j + 1)) := by
    have : tu.time (j + 1) = tr.time (j + 1) := rfl
    rw [← this, hj1]
    exact hz
  have hle1 : ∀ q < j + 1, tr.time q ≤ tr.time (j + 2) :=
    fun q hq => hrun.time_mono (by omega)
  have hfr := Node.frame_of_projAC_at h hzk hc
  rw [Trace.upTo_state tr z hle1] at hfr
  have hac := (Compose.goldilocks_ac_projection_from' hr (hnc.upTo _)).localRun
  obtain ⟨Q, hQ, hv, hroot⟩ :=
    Healing.Growing.Shadow.full_frame_viable_witness_at hrun hnc hzi (by
      have : tr.time (j + 1) = sp.ts u := hj1
      rw [this]
      exact hf)
  rw [← hfr] at hQ hv hroot
  have hd : (AC.acProposal sp (tu.projAC.state z (j + 1))
      (Node.frame (Node.tickStep proposer dg z (tu.state z j) (tu.time (j + 2)) x
        .acTick).1) (tu.projAC.time (j + 1))).2 = some (d, pay) := by
    have ht1' : tu.projAC.time (j + 1) = tu.time (j + 2) := ht1
    rw [Compose.projAC_state' h hzk, hst1, ht1']
    simpa only [Node.acProposal_eq] using hdp
  have hvd := Healing.proposal_head_viable hac hr.vstart hzk hc rfl
    (by rw [sp.slotTime_eq]; exact hj1) hd
    ⟨(AC.frameIn_of_callAt hac hzk hc).1.fcRoot_mem, .refl, Q, hQ, hv, hroot⟩
  rw [hfr, Node.frame_eq, Store.toFrame_viableHeads] at hvd
  obtain ⟨hDm, -, hDv⟩ := hvd
  -- the proposal's store, block and state
  have hfgj : (tr.state z (j + 1)).fg = (tu.state z j).fg := by
    rw [← Trace.upTo_state tr z hle1, tu.state_succ_of_call h₀,
      ((Node.cutStep_ac _ _ _ _ _).1 (h.cutLaw z hzk _ _ h₀)).2.2.1]
  obtain ⟨fg', hfg'⟩ := hacc'.1 rfl
  have hpost : (tu.state z (j + 2 + 1)).fg = fg' := by
    have hcl := ((Node.cutStep_block_true _ _ _ _ _).1 (h.cutLaw z hzk _ _ hacc)).2.1
    rw [tu.state_succ_of_call hacc]
    rw [hst2, hfg'] at hcl
    exact (Option.some.inj hcl).symm
  obtain ⟨pr, hpar, hσ'⟩ := onBlock_σ hfg'
  rw [← hpost, Trace.upTo_state tr z hleB] at hσ'
  rw [hfgj] at hDm hDv
  have hpr' : pr = d.head.root := by
    rw [hB] at hpar
    simp only [Node.mkBlock] at hpar
    exact (Option.some.inj hpar).symm
  subst hpr'
  have hatts : P.fgView.atts = (tu.state z j).fg.proposalAttestations d.head := by
    rw [hB]
    rfl
  have hreach := Node.fg_reachable_at h hzk j
  have hkP : (tr.state z (j + 2)).fg = (tu.state z j).fg := by
    have hle2 : ∀ q < j + 2, tr.time q ≤ tr.time (j + 2) :=
      fun q hq => hrun.time_mono (by omega)
    rw [← Trace.upTo_state tr z hle2, hst2]
  rw [hkP]
  exact ⟨(Store.headHeightFloor_bounds _).1.trans
      (floor_le_of_isViable hreach hDm hDv hatts hσ'),
    hj_lt_of_isViable hreach hDm hDv hatts hσ'⟩

end Consensus.Goldilocks.Shadow.PU.Witness

namespace Consensus.Goldilocks.Shadow.PU.Growing

open AC (ACParams ReplayOrder Payload gbar)
open Consensus.Goldilocks.Generic
open Consensus.Goldilocks.Healing.Growing (CommitteeHalfUpTo)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- An actual report of a node honest at it is an `ac_to_fg` call of the AC projection
(`reportAt_iff_toFGAt` over the shadow run). -/
theorem reportAt_iff_toFGAt {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini) {y : Fin sp.n}
    {i : Nat} (hy : y ∈ H (tr.time i)) {R : AC.Blk sp.n (List (FG.Att sp.n))} :
    ReportAt tr y i R ↔ ∃ ℓ, AC.ToFGAt tr.projAC y i ℓ R := by
  unfold ReportAt AC.ToFGAt
  rw [projAC_state_at hrun hy]
  refine exists_congr fun ℓ => ?_
  rw [Compose.projAC_callAt]
  rfl

/-- **The `report_follow` field** over the shadow run and the restated window: after warmup the
proposal is reported by nodes honest at the delayed report deadline, and the same report is an
ancestor of later honest proposal heads. -/
theorem goldilocks_report_follow {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    {hold : Time} {g ΔF b : Time} {G : Nat} {sign : Fin sp.n → Time → Bool}
    {s₀ N u M : Nat} {isTop : Prop} {J B : AC.Blk sp.n (List (FG.Att sp.n))} {z : Fin sp.n}
    {kB : Nat}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot (dictOfTime sp cm)))
    (hcal : tr.SignCalendarAt proposer dg H sign) (hgap : SignGapAt sp.toParams sign G 0)
    (hK : CommitteeHalfUpTo tr H (dictOfTime sp cm) g b)
    (hp : Premises tr H cm βK proposer dg (fun v => v.val) g ΔF b hold)
    (hframe : Generic.FrameWindow tr H (sp.toParams.slotTime s₀)
      (shiftDelay sp.toParams G (sp.toParams.slotTime N + 2 * sp.toParams.Δ)) M isTop J)
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
    proposal_report_follow_delayed_at (hframe.mono le_rfl hmax) hrun hp.noColl
      ⟨hp.sync.deltaF, hp.sync.message, hp.sync.block, hp.sync.relay, hp.sync.signedRow,
      hp.sync.hold_le⟩
      hp.awake hp.faults hp.catchUp hp.noRestart hm hwarm hN (hmax.trans hmb) hz hdes hP hPs
      hcal hgap ht₀ hy hK
  refine ⟨i, R, hyi, (reportAt_iff_toFGAt hrun hyi).mpr ⟨ell, hto⟩, (hts u).symm ▸ hlo,
    by rw [shiftDelay_eq_add, hts]; exact hhi, hPR, ?_⟩
  intro x hx hxN w c d hw ⟨ℓ, pay, hc, hcall, hd⟩ htc
  exact hheads x (by omega) hxN w c ℓ hw (Compose.projAC_callAt.mpr hc) hcall
    (htc.trans (hts x)) d pay
    (by rw [projAC_state_at hrun hw]; exact hd)

/-- **The `proposal_floor` field** over the shadow run and the restated window: an honest
designated proposal under the FG fault bound at its slot reaches the predecessor of its
proposer's pre-proposal maximum height and exceeds its pre-proposal justification height. The
window is not read. -/
theorem goldilocks_proposal_floor {cm : Time → Finset (Fin sp.n)} {lo hi : Time}
    {M u : Nat} {isTop : Prop} {J B : AC.Blk sp.n (List (FG.Att sp.n))} {z : Fin sp.n}
    {kB : Nat}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot (dictOfTime sp cm)))
    (hnc : Compose.NoCollRun dg tr) (_hframe : Generic.FrameWindow tr H lo hi M isTop J)
    (hz : z ∈ H (sp.toParams.slotTime u)) (hdes : z = proposer u) (hP : tr.ProposesAt z kB B)
    (hBs : B.slot = u) (_hlo : lo ≤ sp.toParams.slotTime u) (_hhi : sp.toParams.slotTime u ≤ hi)
    (hf : (H (sp.toParams.slotTime u))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n) :
    (tr.state z kB).fg.hmax - 1 ≤ ((tr.state z (kB + 1)).fg.σ B.root).h ∧
      (tr.state z kB).fg.hj < ((tr.state z (kB + 1)).fg.σ B.root).h := by
  have hts : sp.toParams.slotTime u = sp.ts u := by
    rw [sp.slotTime_eq]
    rfl
  rw [hts] at hz hf
  exact Witness.warm_proposal_store_bounds_at hrun hnc hz hdes hP hBs hf

end Consensus.Goldilocks.Shadow.PU.Growing

end

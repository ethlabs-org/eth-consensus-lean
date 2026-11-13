module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.DrainWarm
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.FrameWindow
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.NoAdvance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowEndpoint
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.Row
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.RiseRounds
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Reset rounds with honesty at each observation

Relay calls are obtained from the receiving node's local prefix. Historical row and
source witnesses are kept in the growing trace, independently of that prefix.

The reset bound reads restarts only up to its service bound `b` (`NoRestartUpTo`): the rounds run
on the honest sets truncated after `b`, on which no restart after `b` is honest.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- No restart in `(t, b]` of a node honest at its restart: `NoRestartAfter` for the restarts up
to `b`. -/
def NoRestartUpTo (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n)) (t b : Time) : Prop :=
  ∀ y k, y ∈ H (tr.time k) → tr.RestartAt y k → tr.time k ≤ b → tr.time k ≤ t

/-- The bounded no-restart premise, without exposing the definition's body. -/
theorem noRestartUpTo_iff {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)} {t b : Time} :
    NoRestartUpTo tr H t b ↔
      ∀ y k, y ∈ H (tr.time k) → tr.RestartAt y k → tr.time k ≤ b → tr.time k ≤ t :=
  Iff.rfl

end Consensus.Goldilocks.Healing.Growing

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

private theorem faults_lt_quorums {f n : Nat} (hn : 0 < n) (hf : 3 * f ≤ n - 1) :
    f < (2 * n + 2) / 3 ∧ f < 2 * ((2 * n + 2) / 3) - n := by
  omega

/-- Wakefulness supplies a relay call before an independently honest receiver cut. -/
theorem callLag_of_awake_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) {g b lo : Time}
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hlo : cutZ sp.toParams g ≤ lo) {z : Fin sp.n} {i m : Nat}
    (hz : z ∈ H (tr.time m)) (hi : lo ≤ tr.time i)
    (him : tr.time i + 2 * sp.Δ ≤ tr.time m) (hmb : tr.time m ≤ b) :
    ∃ j < m, tr.IsCall z j ∧
      tr.deadline z j (max (tr.time i) g) sp.Δ ≤ tr.time j := by
  have hr := hrun.upTo (hrun.time_nonneg m)
  have ha : ∀ y ∈ H (tr.time m), ∀ t, gbar g ≤ t → t ≤ tr.time m →
      (tr.upTo (tr.time m)).awake y t := fun y hy t ht htm =>
    ⟨hawake y t (hrun.antitone htm hy) ht (htm.trans hmb), htm⟩
  obtain ⟨j, hjm, hc, hd⟩ := Healing.callLag_of_awake hr ha hlo
    (T := tr.time m + 1) le_rfl z hz i m hi him
      (show tr.time m < tr.time m + 1 by linarith)
  have hjt := ((RunTrace.upTo_isCall tr).mp hc).1
  refine ⟨j, hjm, ((RunTrace.upTo_isCall tr).mp hc).2, ?_⟩
  rwa [RunTrace.upTo_deadline hrun.time_mono hjt] at hd

/-- The proposal's own full frame already bounds its parent by the common floor. -/
theorem floor_le_warm_proposal_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {lo hi : Time} {floor u : Nat} {kindJ : Prop}
    {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H lo hi floor kindJ J)
    {z : Fin sp.n} {kP : Nat} (hz : z ∈ H (sp.ts u)) (hdes : z = proposer u)
    (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hlo : lo ≤ sp.ts u) (hhi : sp.ts u ≤ hi)
    (hf : (H (sp.ts u))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n) :
    floor ≤ ((tr.state z (kP + 1)).fg.σ P.root).h := by
  have htime : tr.time kP = sp.ts u := by
    simpa only [sp.slotTime_eq, hPs, SAParams.ts] using hP.2.2
  have hzk : z ∈ H (tr.time kP) := htime ▸ hz
  have hr := hrun.upTo (hrun.time_nonneg kP)
  have hP' : (tr.upTo (tr.time kP)).ProposesAt z kP P :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hP.1⟩, hP.2.1, hP.2.2⟩
  obtain ⟨_, ip, ell, d, pay, hc, hcall, hd, hti, hpar, _⟩ :=
    Healing.honestProposalRun_of_proposesAt hr (hnc.upTo _) hzk hdes hP' hPs
  rw [← hdes] at hc hd
  have hip : tr.time ip = sp.ts u := hti
  have hipk : tr.time ip ≤ tr.time kP := by rw [hip, htime]
  have hzi := hrun.antitone hipk hzk
  have hc' : tr.projAC.CallAt z ip ell := by
    rw [RunTrace.upTo_projAC] at hc
    exact ((Trace.upTo_callAt tr.projAC).mp hc).2
  have hfr : ell.frame = Node.frame (tr.state z ip) :=
    (hrun.cutLaw z ip (.ac ell) (Compose.projAC_callAt.mp hc') hzi).1
  obtain ⟨Q, hQ, hv, hroot⟩ := full_frame_viable_witness_at hrun hnc hzi (hip ▸ hf)
  rw [← hfr] at hQ hv hroot
  have hac := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time kP)) _ proposer
    hr (hnc.upTo _)).localRun
  have hvd := Healing.proposal_head_viable hac hzk hc hcall
    (by rw [sp.slotTime_eq]; exact hti) hd
    ⟨(SA.frameIn_of_callAt hac hzk hc).1.fcRoot_mem, .refl, Q, hQ, hv, hroot⟩
  rw [hfr] at hvd
  have hheight : (tr.state z ip).fg.headHeightFloor ≤
      ((tr.state z ip).fg.σ d.head.root).h := hvd.2.2.2
  rw [hframe.floor_eq z ip hzi (hip ▸ hlo) (hip ▸ hhi)] at hheight
  have hle : ∀ q < kP + 1, tr.time q ≤ tr.time kP := fun q hq => hrun.time_mono (by omega)
  obtain ⟨_, hPm, _⟩ := Healing.accept_of_proposesAt hr (hnc.upTo _) hzk hP'
  rw [Trace.upTo_state tr z hle] at hPm
  have hDhist : d.head ∈ tr.HonestBlocksAt H :=
    ⟨z, ip, _, hrun.time_nonneg ip, fun q hq => hrun.time_mono hq.le, hzi, hvd.1⟩
  have hPhist : P ∈ tr.HonestBlocksAt H :=
    ⟨z, kP + 1, _, hrun.time_nonneg kP, hle, hzk, hPm⟩
  have hDP : Anc (tr.HonestBlocksAt H) d.head P := .single ⟨hDhist, hPhist, hpar⟩
  have hDpost := mem_of_honest_anc_at hrun hnc (hrun.time_nonneg kP) hle hzk hDP hPm
  have hσ := σ_eq_honest_at hrun hnc (hrun.time_nonneg ip)
    (fun q hq => hrun.time_mono hq.le) hzi (hrun.time_nonneg kP) hle hzk hvd.1 hDpost
  rw [hσ] at hheight
  exact hheight.trans (h_le_of_store_anc (fg_reachable_at hrun (hrun.time_nonneg kP) hle hzk)
    (.single ⟨hDpost, hPm, hpar⟩))

/-- The report's viable floor and fork-choice root determine its client-lock kind. -/
theorem report_kind_of_floor_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hh : (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ R.root).h)
    (hroot : (tr.state y i).fg.Anc (tr.state y i).fg.fcRoot R) :
    (tr.state y i).fg.hj < ((tr.state y i).fg.σ R.root).h ∨
      ((tr.state y i).fg.hj = ((tr.state y i).fg.σ R.root).h ∧
        (tr.state y i).fg.Anc (tr.state y i).fg.J R) := by
  have hr := hrun.upTo (hrun.time_nonneg i)
  have hs := Trace.upTo_state tr y (i := i) (fun q hq => hrun.time_mono hq.le)
  have h := Healing.report_kind_of_floor hr hy (by rwa [hs]) (by rwa [hs])
  rwa [hs] at h

/-- A high source forces a historical reset even when the client suppresses signing. -/
theorem reset_of_high_source_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) {g : Time}
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    (hq : (H (tr.time k))ᶜ.ncard < sp.toParams.fg.q)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Option (FG.Att sp.n)}
    (hc : tr.CallAt y k (.fg (.attest C s)))
    (hh : HZ tr H g + 1 ≤ ((tr.state y k).fg.σ C.root).h) :
    ∃ a, IsReset tr H g a ∧ a ≤ tr.time k := by
  classical
  have hl := hrun.upTo (hrun.time_nonneg k)
  have hst := Trace.upTo_state tr y (i := k) (fun q hq => hrun.time_mono hq.le)
  have hr := fg_reachable_at hrun (hrun.time_nonneg k) (fun q hq => hrun.time_mono hq.le) hy
  have he : ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th).h =
      ((tr.state y k).fg.σ C.root).h := by
    rcases hC : (tr.state y k).fg.blocks C.root with _ | X
    · rw [Store.σ_of_blocks_none hr hC]
      exact congrArg FG.ChainState.h (Store.σ_genesis hr)
    · have hXr := Store.Reachable.blocks_root hr hC
      have hX : X ∈ (tr.state y k).fg.tree := by
        change (tr.state y k).fg.blocks X.root = some X
        rw [hXr]; exact hC
      obtain ⟨⟨E, _, hEr, _, hEh, _⟩, _⟩ := Store.entry_state_of_source _ _ _ _ hr X hX
      rw [← hXr, ← hEr]
      exact hEh
  by_cases hprev : ∃ j < k, ∃ att, tr.SignAt y j att ∧ HZ tr H g + 1 ≤ att.h
  · obtain ⟨j, hj, att, hs, hh⟩ := hprev
    have hjt := hrun.time_mono hj.le
    have hqj : (H (tr.time j))ᶜ.ncard < sp.toParams.fg.q := by
      exact lt_of_le_of_lt (Set.ncard_le_ncard (Set.compl_subset_compl.mpr
        (hrun.antitone hjt)) (Set.toFinite _)) hq
    obtain ⟨a, ha, haj⟩ := reset_of_height_advance_at hrun hqj (hrun.antitone hjt hy) hs hh
    exact ⟨a, ha, haj.trans hjt⟩
  have hlock : (tr.state y k).record.lock ((tr.state y k).fg.σ C.root).h = none := by
    by_contra hn
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 hn
    obtain ⟨j, hj, att, hs, hfin⟩ :=
      (Healing.client_record_origin_of_run hl hy _ r k).2 (by rwa [hst])
    have hw := (Healing.signAt_wellFormed hl hy hs).2
      (((tr.state y k).fg.σ C.root).h, r) (by simp [hfin])
    exact hprev ⟨j, hj, att, ((RunTrace.upTo_signAt tr).mp hs).2, by omega⟩
  have hsent : ∀ b ∈ (tr.state y k).record.sent,
      b.1 ≠ ((tr.state y k).fg.σ C.root).h := by
    intro b hb hbh
    obtain ⟨j, hj, att, hs, heq⟩ := Healing.sent_origin hl hy k (by rwa [hst])
    have hah : att.h = b.1 := congrArg Prod.fst heq
    exact hprev ⟨j, hj, att, ((RunTrace.upTo_signAt tr).mp hs).2, by omega⟩
  have hany (τ : Bool) : (tr.state y k).record.sent.any (fun b =>
      b.1 = ((tr.state y k).fg.σ C.root).h ∧ (!τ ∨ b.2.1 =
        ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th).Th)) = false := by
    apply List.any_eq_false.2
    intro b hb
    simp [hsent b hb]
  cases s with
  | some att =>
    have hcl := (hrun.cutLaw y k _ hc hy).1
    apply reset_of_height_advance_at hrun hq hy ⟨C, hc⟩
    rw [(Store.createAtt_eq hcl).1, he]
    exact hh
  | none =>
    have hcl := (hrun.cutLaw y k _ hc hy).1
    exfalso
    change (tr.state y k).record.createAtt y ((tr.state y k).fg.σ
      ((tr.state y k).fg.σ C.root).Th) = none at hcl
    have hτ : ∃ τ, (tr.state y k).record.heightPair ((tr.state y k).fg.σ C.root).h
        ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th).Th =
        some (((tr.state y k).fg.σ C.root).h,
          ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th).Th, τ) := by
      unfold FG.Record.heightPair
      simp only [hlock, ne_eq, not_true_eq_false, false_and, ↓reduceIte]
      split_ifs <;> exact ⟨_, rfl⟩
    obtain ⟨τ, hτ⟩ := hτ
    unfold FG.Record.createAtt at hcl
    rw [he, hτ] at hcl
    dsimp only at hcl
    rw [hany τ] at hcl
    simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hcl

/-- The adjacent client call of a high report supplies the reset, including suppression. -/
theorem reset_of_high_report_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) {g : Time}
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    (hq : (H (tr.time i))ᶜ.ncard < sp.toParams.fg.q)
    {ell : ACLabel (goldilocksNode sp ro)} {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hR : SA.ToFGAt tr.projAC y i ell R)
    (hh : HZ tr H g + 1 ≤ ((tr.state y i).fg.σ R.root).h) :
    ∃ a, IsReset tr H g a ∧ a ≤ tr.time i := by
  have hr := hrun.upTo (hrun.time_nonneg i)
  have hst := Trace.upTo_state tr y (i := i) (fun q hq => hrun.time_mono hq.le)
  obtain ⟨hc, hto, hres⟩ := hR
  have hc' : (tr.upTo (tr.time i)).CallAt y i (.ac ell) :=
    (Trace.upTo_callAt tr).mpr ⟨le_rfl, Compose.projAC_callAt.mp hc⟩
  have hres' : ((goldilocksNode sp ro).toFG
      ((tr.upTo (tr.time i)).state y i).ac ell.frame (tr.time i)).2 = some R := by
    rw [hst]
    have hstate := Compose.projAC_state hr.toLocalRun hy i
    rw [RunTrace.upTo_projAC, Trace.upTo_state tr.projAC y
      (fun q hq => hrun.time_mono hq.le), hst] at hstate
    rwa [hstate] at hres
  obtain ⟨sg, hatt, ht, hfg⟩ := Healing.toFG_attest hr.toLocalRun hy hc' hto hres'
  have ht' : tr.time (i + 1) = tr.time i := ht
  have hs1 := Trace.upTo_state tr (d := tr.time i) y (i := i + 1)
    (fun q hq => hrun.time_mono (by omega))
  have hatt' := ((Trace.upTo_callAt tr).mp hatt).2
  rw [hs1, hst] at hfg
  have hh' : HZ tr H g + 1 ≤ ((tr.state y (i + 1)).fg.σ R.root).h := by
    rwa [hfg]
  obtain ⟨a, ha, hat⟩ := reset_of_high_source_at hrun (ht' ▸ hy) (ht' ▸ hq) hatt' hh'
  exact ⟨a, ha, by rwa [ht'] at hat⟩

/-- A proposal's immediate acceptance is held while its proposer is honest. -/
theorem proposal_mem_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {p : Fin sp.n} {k : Nat}
    (hp : p ∈ H (tr.time k)) {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : tr.ProposesAt p k P) : P ∈ (tr.state p (k + 1)).fg.tree := by
  have hr := hrun.upTo (hrun.time_nonneg k)
  have hP' : (tr.upTo (tr.time k)).ProposesAt p k P :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hP.1⟩, hP.2.1, hP.2.2⟩
  have hm := (Healing.accept_of_proposesAt hr (hnc.upTo _) hp hP').2.1
  rwa [Trace.upTo_state tr p (fun q hq => hrun.time_mono (by omega))] at hm

/-- The report's actual frame supplies its fork-choice-root ancestry. -/
theorem report_root_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hR : SA.ToFGAt tr.projAC y i ell R) :
    R ∈ (tr.state y i).fg.tree ∧ (tr.state y i).fg.Anc (tr.state y i).fg.fcRoot R := by
  have hret := hR.2.2
  change (SA.acToFG sp _ _ _).2 = some R at hret
  have hroot : R ∈ ell.frame.tree ∧ ell.frame.Anc ell.frame.fcRoot R := by
    unfold SA.acToFG at hret
    split_ifs at hret
    split at hret
    · cases hret
    · rename_i C hC
      split_ifs at hret
      cases hret
      exact ⟨(SA.deepest_mem hC).1.1.1, (SA.deepest_mem hC).1.1.2.1⟩
  have hfr := (hrun.cutLaw y i (.ac ell) (Compose.projAC_callAt.mp hR.1) hy).1
  rw [hfr] at hroot
  exact ⟨hroot.1.1, hroot.2.mono (fun _ h => h.1)⟩

/-- Equal-height reports above a warm proposal have the frame's client-lock kind. -/
theorem report_kind_of_warm_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {lo hi : Time} {floor u : Nat} {kindJ : Prop}
    {J P R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H lo hi floor kindJ J)
    {z : Fin sp.n} {kP : Nat} (hz : z ∈ H (sp.ts u)) (hdes : z = proposer u)
    (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hlo : lo ≤ sp.ts u) (hhi : sp.ts u ≤ hi)
    (hf : (H (sp.ts u))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} (hR : SA.ToFGAt tr.projAC y i ell R)
    (hPR : Anc (tr.HonestBlocksAt H) P R) (hil : lo ≤ tr.time i) (hih : tr.time i ≤ hi)
    (heq : ((tr.state y i).fg.σ R.root).h = ((tr.state y i).fg.σ P.root).h) :
    (tr.state y i).fg.hj < ((tr.state y i).fg.σ P.root).h ∨
      ((tr.state y i).fg.hj = ((tr.state y i).fg.σ P.root).h ∧
        (tr.state y i).fg.Anc (tr.state y i).fg.J R) := by
  have htime : tr.time kP = sp.ts u := by
    simpa only [sp.slotTime_eq, hPs, SAParams.ts] using hP.2.2
  have hzk : z ∈ H (tr.time kP) := htime ▸ hz
  have hm := proposal_mem_at hrun hnc hzk hP
  obtain ⟨hRm, hroot⟩ := report_root_at hrun hy hR
  have hPy := mem_of_honest_anc_at hrun hnc (hrun.time_nonneg i)
    (fun q hq => hrun.time_mono hq.le) hy hPR hRm
  have hh := floor_le_warm_proposal_at hrun hnc hframe hz hdes hP hPs hlo hhi hf
  have hσ := σ_eq_honest_at hrun hnc (hrun.time_nonneg kP)
    (fun q hq => hrun.time_mono (by omega)) hzk (hrun.time_nonneg i)
    (fun q hq => hrun.time_mono hq.le) hy hm hPy
  rw [hσ] at hh
  have hfloor : (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ R.root).h := by
    rw [hframe.floor_eq y i hy hil hih, heq]
    exact hh
  have h := report_kind_of_floor_at hrun hy hfloor hroot
  rwa [heq] at h

/-- A warm proposal crosses one height at the next sufficiently old honest proposal. -/
theorem round_of_warm_at
    {g ΔF b T : Time} {s₀ u x N floor : Nat} {kindJ : Prop}
    {J P X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts N + 2 * sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hwarm : s₀ + 2 * sp.k ≤ u)
    (hδ : 3 ≤ sp.toParams.fg.δt)
    (hΔF : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time))
    (hux : u + sp.toParams.fg.δt ≤ x) (hxN : x ≤ N) (hmb : sp.ts N + 2 * sp.Δ ≤ b)
    (hTb : T ≤ b)
    (hna : ∀ v k att, v ∈ H (tr.time k) → tr.SignAt v k att →
      tr.time k < T → att.h ≤ HZ tr H g)
    (hT : sp.ts (u + 1 : Nat) + 2 * sp.Δ < T)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    {p : Fin sp.n} {kX : Nat} (hp : p ∈ H (tr.time kX)) (hdx : p = proposer x)
    (hX : tr.ProposesAt p kX X) (hXs : X.slot = x) (hstock : sp.committeeSize = sp.n) :
    P ∈ (tr.state p (kX + 1)).fg.tree ∧ X ∈ (tr.state p (kX + 1)).fg.tree ∧
      ((tr.state p (kX + 1)).fg.σ P.root).h + 1 ≤
        ((tr.state p (kX + 1)).fg.σ X.root).h := by
  have hΔ : 1 ≤ sp.Δ := sp.toParams.hΔ
  have hts {a c : Nat} (h : a ≤ c) : sp.ts a ≤ sp.ts c :=
    (SA.ts_le_iff sp).2 (by exact_mod_cast h)
  have htX : tr.time kX = sp.ts x := by
    simpa only [sp.slotTime_eq, hXs, SAParams.ts] using hX.2.2
  have huN : u + 1 ≤ N := by omega
  have hu0 := hts (show s₀ ≤ u by omega)
  have hv : gbar g ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ := by
    have := hts (show s₀ ≤ u + 1 by omega)
    linarith
  have hvx : sp.ts (u + 1 : Nat) + 2 * sp.Δ + ΔF ≤ tr.time kX := by
    have h1 := hts hux
    have h2 : sp.ts (u + sp.toParams.fg.δt : Nat) =
        sp.ts (u + 1 : Nat) + 4 * sp.Δ * (sp.toParams.fg.δt : Time) - 4 * sp.Δ := by
      simp only [SAParams.ts]; push_cast; ring
    rw [htX]
    linarith
  have hvb : sp.ts (u + 1 : Nat) + 2 * sp.Δ ≤ b := by linarith
  have hus : sp.ts (u + 1 : Nat) = sp.ts u + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hvc : sp.ts (u + 1 : Nat) + 2 * sp.Δ ≤ tr.time kX := by
    linarith [hsvc.deltaF]
  have hfi : (H (sp.ts u))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    have hf' := hf (sp.ts u) (by simp only [SAParams.ts]; positivity) (by linarith)
    have hn := sp.toParams.hn
    change (H (sp.ts u))ᶜ.ncard < 2 * ((2 * sp.n + 2) / 3) - sp.n
    omega
  have hz0 : z ∈ H (sp.ts u) := hrun.antitone (by linarith) hz
  have htimeP : tr.time kP = sp.ts u := by
    simpa only [sp.slotTime_eq, hPs, SAParams.ts] using hP.2.2
  have hPm := proposal_mem_at hrun hnc (htimeP ▸ hz0) hP
  have hPH : P ∈ tr.HonestBlocksAt H :=
    ⟨z, kP + 1, tr.time kP, hrun.time_nonneg kP,
      fun q hq => hrun.time_mono (by omega), htimeP ▸ hz0, hPm⟩
  have hr := hrun.upTo (hrun.time_nonneg kX)
  have hX' : (tr.upTo (tr.time kX)).ProposesAt p kX X :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hX.1⟩, hX.2.1, hX.2.2⟩
  obtain ⟨_, c, ellp, d, pay, hc, hcall, hd, htc, hpar, _⟩ :=
    Healing.honestProposalRun_of_proposesAt hr (hnc.upTo _) hp hdx hX' hXs
  rw [← hdx] at hc hd
  have hct : tr.time c = sp.ts x := htc
  have hpc := hrun.antitone (show tr.time c ≤ tr.time kX by rw [hct, htX]) hp
  have hc' : tr.projAC.CallAt p c ellp := by
    rw [RunTrace.upTo_projAC] at hc
    exact ((Trace.upTo_callAt tr.projAC).mp hc).2
  have hd' : (SA.acProposal sp (tr.projAC.state p c) ellp.frame (tr.time c)).2 =
      some (d, pay) := by
    rw [RunTrace.upTo_projAC, Trace.upTo_state tr.projAC p
      (fun q hq => (hrun.time_mono hq.le).trans (by rw [hct, htX]))] at hd
    exact hd
  have hfol := fun y (hy : y ∈ H (tr.time kX)) =>
    proposal_report_follow_at hframe hrun hnc hsvc hawake hf hcatch hnr hm hwarm huN hmb
      hz hdes hP hPs (hrun.antitone (by linarith) hy) hstock
  obtain ⟨i₀, ell₀, R₀, _, _, _, _, hPR₀, hR₀d⟩ := hfol p hp
  refine round_cross_at hrun hnc hsvc hnr hPH
    (hPR₀.trans (hR₀d x (by omega) hxN p c ellp hpc hc' hcall hct d pay hd')) hpar hp hX
    (hf _ (hrun.time_nonneg kX) (by rw [htX]; linarith [hts hxN])) hv hvx
    (by rw [htX]; linarith [hts hxN]) (by omega) ?_
  intro y hy
  obtain ⟨i, ell, R, hyi, hR, htil, hti, hPR, hRd⟩ := hfol y hy
  have hRyD := hRd x (by omega) hxN p c ellp hpc hc' hcall hct d pay hd'
  obtain ⟨hPy, hRy, hor⟩ := row_or_high_of_report_at hrun hnc
    (fun t ht htT => hf t ht (htT.le.trans hTb)) hna hyi hR (by linarith) hPR
    (fun heq => Or.inr (report_kind_of_warm_at hrun hnc hframe hz0 hdes hP hPs hu0
      (by linarith [hts huN]) hfi hyi hR hPR (hu0.trans htil)
      (by linarith [hts huN]) heq))
  rcases hor with ⟨k, att, hyk, hs, hk, hah, haT⟩ | hh
  · exact Or.inl ⟨y, i, hyi, hPy, k, att, hyk, hs, hk.trans hti, hah, haT⟩
  · exact Or.inr ⟨R, hRyD, y, i, hyi, hPy, hRy, hh⟩

/-- A high warm proposal yields a reset via a reader honest at the report deadline. -/
theorem reset_of_high_proposal_at
    {g ΔF b : Time} {s₀ u N floor : Nat} {kindJ : Prop}
    {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts N + 2 * sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hwarm : s₀ + 2 * sp.k ≤ u)
    (hN : u + 1 ≤ N) (hmb : sp.ts N + 2 * sp.Δ ≤ b) (hH : (H b).Nonempty)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hh : HZ tr H g + 1 ≤ ((tr.state z (kP + 1)).fg.σ P.root).h)
    (hstock : sp.committeeSize = sp.n) :
    ∃ a, IsReset tr H g a ∧ a ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ := by
  have hΔ : 1 ≤ sp.Δ := sp.toParams.hΔ
  have hts : sp.ts (u + 1 : Nat) ≤ sp.ts N := (SA.ts_le_iff sp).2 (by exact_mod_cast hN)
  obtain ⟨y, hy⟩ := hH
  obtain ⟨i, ell, R, hyi, hR, _, hti, hPR, _⟩ :=
    proposal_report_follow_at hframe hrun hnc hsvc hawake hf hcatch hnr hm hwarm hN hmb
      hz hdes hP hPs (hrun.antitone (by linarith) hy) hstock
  have htime : tr.time kP = sp.ts u := by
    simpa only [sp.slotTime_eq, hPs, SAParams.ts] using hP.2.2
  have hzk : z ∈ H (tr.time kP) := hrun.antitone (by rw [htime]; linarith) hz
  have hPm := proposal_mem_at hrun hnc hzk hP
  obtain ⟨hRm, _⟩ := report_root_at hrun hyi hR
  have hle : ∀ q < i, tr.time q ≤ tr.time i := fun q hq => hrun.time_mono hq.le
  have hPy := mem_of_honest_anc_at hrun hnc (hrun.time_nonneg i) hle hyi hPR hRm
  have hσ := σ_eq_honest_at hrun hnc (hrun.time_nonneg kP)
    (fun q hq => hrun.time_mono (by omega)) hzk (hrun.time_nonneg i) hle hyi hPm hPy
  rw [hσ] at hh
  have hhR := hh.trans (h_le_of_store_anc (fg_reachable_at hrun (hrun.time_nonneg i) hle hyi)
    (store_anc_of_honest_anc_at hrun hnc (hrun.time_nonneg i) hle hyi hPR hRm))
  have hq : (H (tr.time i))ᶜ.ncard < sp.toParams.fg.q := by
    have hf' := hf _ (hrun.time_nonneg i) (by linarith)
    have hn := sp.toParams.hn
    change (H (tr.time i))ᶜ.ncard < (2 * sp.n + 2) / 3
    omega
  obtain ⟨a, ha, hat⟩ := reset_of_high_report_at hrun hyi hq hR hhR
  exact ⟨a, ha, hat.trans hti⟩

/-- Each round consumes one unit of height deficit; honesty is re-read at the next proposal. -/
theorem rise_reset_rounds_at
    {g ΔF b T : Time} {s₀ N G floor : Nat} {kindJ : Prop}
    {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts N + 2 * sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀)
    (hδ : 3 ≤ sp.toParams.fg.δt) (hG : 1 ≤ G)
    (hΔF : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time))
    (hgp : ProposalGap tr H proposer G s₀ N)
    (hmb : sp.ts N + 2 * sp.Δ ≤ b) (hH : (H b).Nonempty) (hTb : T ≤ b)
    (hna : ∀ v k att, v ∈ H (tr.time k) → tr.SignAt v k att →
      tr.time k < T → att.h ≤ HZ tr H g)
    (r : Nat) {u : Nat} (hwarm : s₀ + 2 * sp.k ≤ u)
    (hN : u + r * (sp.toParams.fg.δt + G - 1) + 1 ≤ N)
    (hT : sp.ts (u + r * (sp.toParams.fg.δt + G - 1) + 1 : Nat) + 2 * sp.Δ ≤ T)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hrise : HZ tr H g + 1 ≤ ((tr.state z (kP + 1)).fg.σ P.root).h + r)
    (hstock : sp.committeeSize = sp.n) :
    ∃ a, IsReset tr H g a ∧
      a ≤ sp.ts (u + r * (sp.toParams.fg.δt + G - 1) + 1 : Nat) + 2 * sp.Δ := by
  induction r generalizing u z kP P with
  | zero =>
    simpa only [Nat.zero_mul, Nat.add_zero] using
      reset_of_high_proposal_at hframe hrun hnc hsvc hawake hf hcatch hnr hm hwarm
        (by simpa using hN) hmb hH hz hdes hP hPs (by simpa using hrise) hstock
  | succ r ih =>
    let ρ := sp.toParams.fg.δt + G - 1
    have hρ : 3 ≤ ρ := by dsimp [ρ]; omega
    have hmul : (r + 1) * ρ = r * ρ + ρ := Nat.succ_mul r ρ
    change u + (r + 1) * ρ + 1 ≤ N at hN
    change sp.ts (u + (r + 1) * ρ + 1 : Nat) + 2 * sp.Δ ≤ T at hT
    have hΔ : 1 ≤ sp.Δ := sp.toParams.hΔ
    have hts {a c : Nat} (h : a ≤ c) : sp.ts a ≤ sp.ts c :=
      (SA.ts_le_iff sp).2 (by exact_mod_cast h)
    by_cases hh : HZ tr H g + 1 ≤ ((tr.state z (kP + 1)).fg.σ P.root).h
    · obtain ⟨a, ha, hat⟩ := reset_of_high_proposal_at hframe hrun hnc hsvc hawake hf
        hcatch hnr hm hwarm (by omega) hmb hH hz hdes hP hPs hh hstock
      exact ⟨a, ha, hat.trans (by linarith [hts (show u + 1 ≤ u + (r + 1) * ρ + 1 by omega)])⟩
    obtain ⟨x, hxl, hxr, hpx, kX, X, hX, hXs⟩ := proposalGap_iff.mp hgp
      (u + sp.toParams.fg.δt) (by omega) (by
        have hδρ : sp.toParams.fg.δt + G ≤ ρ + 1 := by dsimp [ρ]; omega
        omega)
    have htime : tr.time kX = sp.ts x := by
      simpa only [sp.slotTime_eq, hXs, SAParams.ts] using hX.2.2
    have hpx0 : proposer x ∈ H (tr.time kX) := hrun.antitone (by rw [htime]; linarith) hpx
    have hnext : x + r * ρ + 1 ≤ u + (r + 1) * ρ + 1 := by
      have hδρ : sp.toParams.fg.δt + G ≤ ρ + 1 := by dsimp [ρ]; omega
      omega
    have hstrict : sp.ts (u + 1 : Nat) + 2 * sp.Δ < T := by
      have hlt : sp.ts (u + 1 : Nat) < sp.ts (u + (r + 1) * ρ + 1 : Nat) :=
        (SA.ts_lt_iff sp).2 (by exact_mod_cast (show u + 1 < u + (r + 1) * ρ + 1 by omega))
      linarith
    obtain ⟨hPX, _, hcross⟩ := round_of_warm_at hframe hrun hnc hsvc hawake hf hcatch hnr
      hm hwarm hδ hΔF hxl (by omega) hmb hTb hna hstrict hz hdes hP hPs hpx0 rfl hX hXs hstock
    have htP : tr.time kP = sp.ts u := by
      simpa only [sp.slotTime_eq, hPs, SAParams.ts] using hP.2.2
    have hz0 : z ∈ H (tr.time kP) := hrun.antitone (by rw [htP]; linarith) hz
    have hPm := proposal_mem_at hrun hnc hz0 hP
    have hσ := σ_eq_honest_at hrun hnc (hrun.time_nonneg kP)
      (fun q hq => hrun.time_mono (by omega)) hz0 (hrun.time_nonneg kX)
      (fun q hq => hrun.time_mono (by omega)) hpx0 hPm hPX
    rw [← hσ] at hcross
    have hxN : x + r * ρ + 1 ≤ N := hnext.trans hN
    obtain ⟨a, ha, hat⟩ := ih (u := x) (by omega) hxN
      (by linarith [hts hnext]) hpx rfl hX hXs (by omega)
    exact ⟨a, ha, hat.trans (by linarith [hts hnext])⟩

/-- The merged key bounds the deficit at the proposal cut itself. -/
theorem rounds_le_warm_proposal_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g af len : Time} {u floor v : Nat} {kindJ : Prop}
    {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hwin : FrameWindow tr H af (af + len) floor kindJ J)
    (hK : ∀ y i, y ∈ H (tr.time i) → af ≤ tr.time i → tr.time i ≤ af + len →
      frameKey' (tr.state y i).fg = v)
    (hv : 2 * HZ tr H g ≤ v) (hlo : af ≤ sp.ts u) (hhi : sp.ts u ≤ af + len)
    {z : Fin sp.n} {kP : Nat} (hz : z ∈ H (sp.ts u)) (hdes : z = proposer u)
    (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hf : (H (sp.ts u))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n) :
    HZ tr H g + 1 ≤ ((tr.state z (kP + 1)).fg.σ P.root).h + riseRounds (HZ tr H g) v := by
  have ht : tr.time kP = sp.ts u := by
    simpa only [sp.slotTime_eq, hPs, SAParams.ts] using hP.2.2
  have hzk : z ∈ H (tr.time kP) := ht ▸ hz
  have hkey := hK z kP hzk (ht ▸ hlo) (ht ▸ hhi)
  have hr := hrun.upTo (hrun.time_nonneg kP)
  have hpos := Healing.hj_lt_hmax hr hzk kP
  rw [Trace.upTo_state tr z (fun k hk => hrun.time_mono hk.le)] at hpos
  have hfloor := le_floor_add_riseRounds (tr.state z kP).fg (by omega)
    (HZ := HZ tr H g) (by rw [hkey]; exact hv)
  rw [hkey, hwin.floor_eq z kP hzk (ht ▸ hlo) (ht ▸ hhi)] at hfloor
  exact hfloor.trans (Nat.add_le_add_right
    (floor_le_warm_proposal_at hrun hnc hwin hz hdes hP hPs hlo hhi hf) _)

/-- Five integer-aligned attempts fit before the frozen bound, without extending service, with no
restart after GST at all. -/
private theorem exists_reset_of_drain_rounds_noRestartAfter_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b r : Time} {G Ld : Nat}
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hH : (H b).Nonempty) (hδ : 3 ≤ sp.toParams.fg.δt)
    (hΔF : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time))
    (hr : 0 ≤ r) (hgr : gbar g ≤ r) (hG : 1 ≤ G)
    (hcz : cutZ sp.toParams g + sp.Δ + 1 ≤ r + 4 * sp.Δ)
    (hb : Obligations.resetBoundRounds r sp.Δ (2 * sp.Δ) sp.toParams.fg.δt G Ld ≤ b)
    (hgp : ∀ s₀ N : Nat, r + 4 * sp.Δ ≤ sp.ts s₀ →
      sp.ts N + 2 * sp.Δ <
        Obligations.resetBoundRounds r sp.Δ (2 * sp.Δ) sp.toParams.fg.δt G Ld →
      ProposalGap tr H proposer G s₀ N)
    (hdrain : DrainOutputs tr proposer H g G Ld b) (hstock : sp.committeeSize = sp.n) :
    ∃ a, IsReset tr H g a ∧
      a ≤ Obligations.resetBoundRounds r sp.Δ (2 * sp.Δ) sp.toParams.fg.δt G Ld := by
  classical
  let D := sp.Δ
  let ρ : Nat := sp.toParams.fg.δt + G - 1
  let lo := r + 4 * D
  let d := 4 * D * ((Ld : Time) + 2)
  let rt := 4 * D * (ρ : Time)
  let B := Obligations.resetBoundRounds r D (2 * D) sp.toParams.fg.δt G Ld
  have hD : 1 ≤ D := sp.toParams.hΔ
  have hρ : (ρ : Time) = (sp.toParams.fg.δt : Time) + G - 1 := by
    dsimp [ρ]
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
  have hfq {t : Time} (ht : 0 ≤ t) (htb : t ≤ b) :
      (H t)ᶜ.ncard < sp.toParams.fg.q ∧
        (H t)ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    exact faults_lt_quorums sp.toParams.hn (hf t ht htb)
  by_cases hadv : ∃ y k att, y ∈ H (tr.time k) ∧ tr.SignAt y k att ∧
      tr.time k ≤ B ∧ HZ tr H g + 1 ≤ att.h
  · obtain ⟨y, k, att, hy, hs, hk, hh⟩ := hadv
    obtain ⟨a, ha, hat⟩ := reset_of_height_advance_at hrun
      (hfq (hrun.time_nonneg k) (hk.trans hb)).1 hy hs hh
    exact ⟨a, ha, hat.trans hk⟩
  have hna : ∀ y k att, y ∈ H (tr.time k) → tr.SignAt y k att →
      tr.time k < B → att.h ≤ HZ tr H g := by
    intro y k att hy hs hk
    by_contra hh
    exact hadv ⟨y, k, att, hy, hs, hk.le, by omega⟩
  have hlo : gbar g + 2 * D ≤ lo := by dsimp [lo]; linarith
  have hrange : ∀ y i, y ∈ H (tr.time i) → lo ≤ tr.time i → tr.time i < B →
      HZ tr H g ≤ (tr.state y i).fg.hmax ∧
        (tr.state y i).fg.hmax ≤ HZ tr H g + 1 := by
    intro y i hy hi hiB
    have hib : tr.time i ≤ b := hiB.le.trans hb
    obtain ⟨hsnap, hcall⟩ := snapshotCall_of_awake_at hrun hawake hy
      (hcz.trans hi) hib
    have hczle : cutZ sp.toParams g ≤ tr.time i := by
      have hDpos : 0 < D := lt_of_lt_of_le (by decide) hD
      dsimp [lo, D] at hi
      linarith
    have hmax : max (cutZ sp.toParams g) (tr.time i) = tr.time i := max_eq_right hczle
    refine ⟨HZ_le_hmax_at hrun hnc hsvc hcatch
      (hH.mono (hrun.antitone (hczle.trans hib))) hsnap hy ?_ hcall (hlo.trans hi),
      hmax_le_of_noAdvance_at hrun hna hy (hfq (hrun.time_nonneg i) hib).1 hiB⟩
    rw [hmax]
    exact (hfq (hrun.time_nonneg i) hib).2
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hrt : 0 ≤ rt := by dsimp [rt]; positivity
  have hlen := riseLen_nonneg hd hrt (show 0 ≤ 2 * D - 1 by linarith only [hD]) (HZ tr H g)
  have hsum : lo + ∑ j ∈ Finset.range 5,
      (riseLen d rt (2 * D - 1) (HZ tr H g) (2 * HZ tr H g + j) + 2 * D) = B - 5 := by
    rw [sum_riseLen]
    dsimp [lo, d, rt, B]
    rw [Obligations.resetBoundRounds_eq, hρ]
    ring
  obtain ⟨v, hv, hvhi, af, haf, hend, hK, floor, kindJ, J, hwin⟩ :=
    exists_frameWindow_seq_of_service_proof_at hrun hnc
      (fun t ht htb => (hfq ht htb).2) hsvc hcatch
      (riseLen d rt (2 * D - 1) (HZ tr H g)) hlen (by linarith only [hD]) hlo hb hrange
      (fun z i m hz hi him hm => callLag_of_awake_at hrun hawake
        (by dsimp [lo, D]; linarith) hz hi him (hm.le.trans hb))
      (by rw [hsum]; exact sub_lt_self B (by decide))
  let len := riseLen d rt (2 * D - 1) (HZ tr H g) v
  have hsub : ∑ j ∈ Finset.range (v - 2 * HZ tr H g + 1),
      (riseLen d rt (2 * D - 1) (HZ tr H g) (2 * HZ tr H g + j) + 2 * D) ≤
      ∑ j ∈ Finset.range 5,
      (riseLen d rt (2 * D - 1) (HZ tr H g) (2 * HZ tr H g + j) + 2 * D) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun j _ _ => add_nonneg (hlen _) (by linarith only [hD]))
  have hwinB : af + len ≤ B - 5 := by linarith [hsum]
  obtain ⟨s₀, hslo, hshi⟩ := Obligations.exists_slot_align sp (af := af)
    (by dsimp [lo] at haf; linarith only [haf, hr, hD])
  let rr := riseRounds (HZ tr H g) v
  let N := s₀ + Ld + rr * ρ + 1
  have hNtime : sp.ts N = 4 * D * ((s₀ : Time) + Ld + (rr : Time) * (ρ : Time) + 1) := by
    change 4 * D * (N : Time) = _
    dsimp [N]
  have hlenEq : len = 4 * D * ((Ld : Time) + (rr : Time) * (ρ : Time) + 2) + 2 * D - 1 := by
    dsimp [len, rr]
    rw [riseLen_eq]
    dsimp [d, rt]
    ring
  have hfit : sp.ts N + 2 * D ≤ af + len := by
    rw [hNtime, hlenEq]
    change 4 * D * (s₀ : Time) < af + 4 * D at hshi
    have halign := Int.le_sub_one_of_lt hshi
    linarith only [halign]
  have hts {x y : Nat} (h : x ≤ y) : sp.ts x ≤ sp.ts y :=
    (SA.ts_le_iff sp).2 (by exact_mod_cast h)
  have hframe : FrameWindow tr H (sp.ts s₀) (sp.ts N + 2 * D) floor kindJ J :=
    ⟨fun y i hy hi hj => hwin.floor_eq y i hy (hslo.trans hi) (hj.trans hfit),
      fun y i hy hi hj => hwin.kind_iff y i hy (hslo.trans hi) (hj.trans hfit),
      fun y i hy hi hj => hwin.root_eq y i hy (hslo.trans hi) (hj.trans hfit)⟩
  have hsready : r + 4 * D ≤ sp.ts s₀ := by dsimp [lo] at haf; linarith
  have hm : gbar g + 4 * D ≤ sp.ts s₀ := by linarith
  have hmb : sp.ts N + 2 * D ≤ b := by linarith
  have hgpN := hgp s₀ N hsready (by linarith)
  have hLdN : s₀ + Ld ≤ N := by dsimp [N]; omega
  obtain ⟨u, hwarm, huLd, z, kP, P, hz, hdes, hP, hPs, _⟩ := hdrain.warm hframe hm hLdN hmb
    (fun y k att hy hs hk => hna y k att hy hs (by linarith)) hgpN
  have huN : u + rr * ρ + 1 ≤ N := by dsimp [N]; omega
  have hu0 : s₀ ≤ u := by omega
  have huN' : u ≤ N := by omega
  have hz0 : z ∈ H (sp.ts u) := hrun.antitone (by dsimp [D] at hD; linarith) hz
  have hulo : af ≤ sp.ts u := hslo.trans (hts hu0)
  have huhi : sp.ts u ≤ af + len := by linarith [hts huN']
  have hrise := rounds_le_warm_proposal_at hrun hnc hwin hK hv hulo huhi hz0 hdes hP hPs
    (hfq (by change 0 ≤ 4 * sp.Δ * (u : Time); positivity) (by linarith)).2
  obtain ⟨a, ha, hat⟩ := rise_reset_rounds_at hframe hrun hnc hsvc hawake hf hcatch hnr hm
    hδ hG hΔF hgpN hmb hH hb hna rr hwarm huN
    (by linarith [hts huN]) hz hdes hP hPs hrise hstock
  exact ⟨a, ha, hat.trans (by linarith [hts huN])⟩

/-! ### Truncation after `b`

The honest sets truncated after `b` keep every honesty read up to `b` and drop every later one, so
a restart honest on them is at a time `≤ b`, where `NoRestartUpTo` bounds it. -/

/-- The honest sets truncated after `b`: `y` is honest at `t ≤ b` as in `H`, and at no `t > b`. -/
private def truncH (K : Time → Set (Fin sp.n)) (b : Time) : Time → Set (Fin sp.n) :=
  fun t => {y | y ∈ K t ∧ t ≤ b}

private theorem truncH_eq_of_le {b t : Time} (ht : t ≤ b) : truncH H b t = H t :=
  Set.ext fun _ => and_iff_left ht

/-- **The truncation is antitone.** Membership at `t'` gives `t' ≤ b`, hence `t ≤ b` for every
`t ≤ t'`, and honesty at `t` is the antitonicity of `H`. -/
private theorem truncH_antitone (hH : Antitone H) (b : Time) : Antitone (truncH H b) := by
  intro t t' htt' y hy
  exact ⟨hH htt' hy.1, htt'.trans hy.2⟩

/-- **The run laws transfer to the truncation.** Antitonicity is `truncH_antitone`. Every other
law of `GoldilocksRun` reads honesty only in its hypotheses, and `truncH H b t ⊆ H t`, so each law
for `H` is the law for `truncH H b` (with the honesty premises projected by `.1`). -/
private theorem goldilocksRun_truncH
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) (b : Time) :
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg (truncH H b) tr where
  vstart := hrun.vstart
  antitone := truncH_antitone hrun.antitone b
  init y hy := hrun.init y hy.1
  grouped y i c hc hy := hrun.grouped y i c hc hy.1
  cutLaw y i c hc hy := hrun.cutLaw y i c hc hy.1
  wire y j t e hy := hrun.wire y j t e hy.1
  proposerCredential y j t B hy := hrun.proposerCredential y j t B hy.1
  time_nonneg := hrun.time_nonneg
  time_mono := hrun.time_mono
  finite := hrun.finite
  phase_order y y' j j' t e e' hy hy' := hrun.phase_order y y' j j' t e e' hy.1 hy'.1
  tick_public y j t hy := hrun.tick_public y j t hy.1
  tick_unique y j j' t hy := hrun.tick_unique y j j' t hy.1
  tick_of_awake y t hy := hrun.tick_of_awake y t hy.1
  awake_in_horizon y t hy := hrun.awake_in_horizon y t hy.1
  awake_of_call y i hy := hrun.awake_of_call y i hy.1
  restart_of_sleep y i u hy := hrun.restart_of_sleep y i u hy.1
  restart_at_wake y u v hy := hrun.restart_at_wake y u v hy.1
  sleep_of_restart y i hy := hrun.sleep_of_restart y i hy.1
  block_unforgeable y i B hy hB hp := hrun.block_unforgeable y i B hy.1 hB hp.1
  att_unforgeable y i a hy ha hs := hrun.att_unforgeable y i a hy.1 ha hs.1
  msg_unforgeable y i m hy hm hs := hrun.msg_unforgeable y i m hy.1 hm hs.1
  genesis_root_ok := hrun.genesis_root_ok
  carried_vote_unforgeable y i B hy hB v hv hs :=
    hrun.carried_vote_unforgeable y i B hy.1 hB v hv hs.1

private theorem honestBlocksAt_truncH_subset (b : Time) :
    tr.HonestBlocksAt (truncH H b) ⊆ tr.HonestBlocksAt H :=
  fun _ ⟨y, i, t, ht, hle, hy, hB⟩ => ⟨y, i, t, ht, hle, hy.1, hB⟩

private theorem resetService_truncH {g ΔF b' : Time} (hs : ResetService tr H g ΔF b')
    (b : Time) : ResetService tr (truncH H b) g ΔF b' where
  deltaF := hs.deltaF
  message x i m hx hm y j hy := hs.message x i m hx.1 hm y j hy.1
  block x i B hx hB y j hy := hs.block x i B hx.1 hB y j hy.1
  relay x i B hx hB hg y j hy hj hd hF :=
    hs.relay x i B hx.1 hB hg y j hy.1 hj hd (Anc.mono (honestBlocksAt_truncH_subset b) hF)
  signedRow x i att hx hsg y j hy := hs.signedRow x i att hx.1 hsg y j hy.1

private theorem catchRun_truncH {g κ : Time} (hc : CatchRun tr H g κ) (b : Time) :
    CatchRun tr (truncH H b) g κ :=
  fun x i B hx hA hlt y j hy hfirst hF =>
    hc x i B hx.1 hA hlt y j hy.1 hfirst (Anc.mono (honestBlocksAt_truncH_subset b) hF)

/-- `H_z` is read at `c_z`, where the truncation is `H` itself. -/
private theorem HZ_truncH {g b : Time} (hcz : cutZ sp.toParams g ≤ b) :
    HZ tr (truncH H b) g = HZ tr H g := by
  simp only [HZ, truncH_eq_of_le hcz]

private theorem proposalGap_truncH {G s₀ N : Nat} {b : Time}
    (hgp : ProposalGap tr H proposer G s₀ N) (hN : sp.ts N + sp.Δ ≤ b) :
    ProposalGap tr (truncH H b) proposer G s₀ N := by
  rw [proposalGap_iff] at hgp ⊢
  intro a ha haN
  obtain ⟨x, hax, hxa, hx, hP⟩ := hgp a ha haN
  have hts : sp.ts x ≤ sp.ts N := (SA.ts_le_iff sp).2 (by exact_mod_cast (show x ≤ N by omega))
  exact ⟨x, hax, hxa, ⟨hx, by linarith⟩, hP⟩

private theorem proposalGap_of_truncH {G s₀ N : Nat} {b : Time}
    (hgp : ProposalGap tr (truncH H b) proposer G s₀ N) : ProposalGap tr H proposer G s₀ N := by
  rw [proposalGap_iff] at hgp ⊢
  intro a ha haN
  obtain ⟨x, hax, hxa, hx, hP⟩ := hgp a ha haN
  exact ⟨x, hax, hxa, hx.1, hP⟩

private theorem frameWindow_of_truncH {lo hi b : Time} {floor : Nat} {kindJ : Prop}
    {J : SA.Blk sp.n (List (FG.Att sp.n))} (hw : FrameWindow tr (truncH H b) lo hi floor kindJ J)
    (hhi : hi ≤ b) : FrameWindow tr H lo hi floor kindJ J :=
  ⟨fun y i hy hl hh => hw.floor_eq y i ⟨hy, hh.trans hhi⟩ hl hh,
    fun y i hy hl hh => hw.kind_iff y i ⟨hy, hh.trans hhi⟩ hl hh,
    fun y i hy hl hh => hw.root_eq y i ⟨hy, hh.trans hhi⟩ hl hh⟩

private theorem drainOutputs_truncH {g b : Time} {G Ld : Nat}
    (hd : DrainOutputs tr proposer H g G Ld b) (hcz : cutZ sp.toParams g ≤ b) :
    DrainOutputs tr proposer (truncH H b) g G Ld b where
  warm := by
    intro s₀ N floor kindJ J hw hm hN hmb hsig hgp
    obtain ⟨u, hu, huL, z, kP, P, hz, hdes, hP, hPs, hh⟩ :=
      hd.warm (frameWindow_of_truncH hw hmb) hm hN hmb
        (fun v k att hv hs hk => by
          have h := hsig v k att ⟨hv, hk.trans hmb⟩ hs hk
          rwa [HZ_truncH hcz] at h)
        (proposalGap_of_truncH hgp)
    have hts : sp.ts u ≤ sp.ts N := (SA.ts_le_iff sp).2 (by exact_mod_cast (show u ≤ N by omega))
    have hΔ : 1 ≤ sp.Δ := sp.toParams.hΔ
    refine ⟨u, hu, huL, z, kP, P, ⟨hz, by linarith⟩, hdes, hP, hPs, ?_⟩
    rwa [HZ_truncH hcz]

private theorem isReset_of_truncH {g a b : Time} (hcz : cutZ sp.toParams g ≤ b)
    (h : IsReset tr (truncH H b) g a) (hab : a ≤ b) : IsReset tr H g a := by
  unfold IsReset at h ⊢
  rw [HZ_truncH hcz] at h
  obtain ⟨⟨y, k, att, hy, hs, hh, hk⟩, hmin⟩ := h
  refine ⟨⟨y, k, att, hy.1, hs, hh, hk⟩, fun y' k' att' hy' hs' hh' => ?_⟩
  by_cases hk' : tr.time k' ≤ b
  · exact hmin y' k' att' ⟨hy', hk'⟩ hs' hh'
  · exact hab.trans (lt_of_not_ge hk').le

/-- **The reset bound from finite service**, reading restarts only up to `b`: the rounds of
`exists_reset_of_drain_rounds_noRestartAfter_at` run on the honest sets truncated after `b`, where
the premises up to `b` are those for `H`, no restart is honest after `b`, and `H_z` and the reset
are those for `H` (`c_z` and the reset bound are `≤ b`). -/
theorem exists_reset_of_drain_rounds_awake_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b r : Time} {G Ld : Nat}
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartUpTo tr H (gbar g) b)
    (hH : (H b).Nonempty) (hδ : 3 ≤ sp.toParams.fg.δt)
    (hΔF : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time))
    (hr : 0 ≤ r) (hgr : gbar g ≤ r) (hG : 1 ≤ G)
    (hcz : cutZ sp.toParams g + sp.Δ + 1 ≤ r + 4 * sp.Δ)
    (hb : Obligations.resetBoundRounds r sp.Δ (2 * sp.Δ) sp.toParams.fg.δt G Ld ≤ b)
    (hgp : ∀ s₀ N : Nat, r + 4 * sp.Δ ≤ sp.ts s₀ →
      sp.ts N + 2 * sp.Δ <
        Obligations.resetBoundRounds r sp.Δ (2 * sp.Δ) sp.toParams.fg.δt G Ld →
      ProposalGap tr H proposer G s₀ N)
    (hdrain : DrainOutputs tr proposer H g G Ld b) (hstock : sp.committeeSize = sp.n) :
    ∃ a, IsReset tr H g a ∧
      a ≤ Obligations.resetBoundRounds r sp.Δ (2 * sp.Δ) sp.toParams.fg.δt G Ld := by
  have hΔ : 1 ≤ sp.Δ := sp.toParams.hΔ
  have hlo : r + 4 * sp.Δ ≤ Obligations.resetBoundRounds r sp.Δ (2 * sp.Δ)
      sp.toParams.fg.δt G Ld := by
    rw [Obligations.resetBoundRounds_eq]
    have hc : (0 : Time) ≤ 20 * (Ld : Time) + 24 * ((sp.toParams.fg.δt : Time) + G - 1) := by
      have h1 : (0 : Time) ≤ Ld := Nat.cast_nonneg _
      have h2 : (0 : Time) ≤ sp.toParams.fg.δt := Nat.cast_nonneg _
      have h3 : (1 : Time) ≤ G := by exact_mod_cast hG
      linarith
    linarith [mul_nonneg hc (show (0 : Time) ≤ sp.Δ by linarith)]
  have hczb : cutZ sp.toParams g ≤ b := by linarith
  obtain ⟨a, ha, hab⟩ := exists_reset_of_drain_rounds_noRestartAfter_at
    (goldilocksRun_truncH hrun b) hnc
    (fun t ht htb => by rw [truncH_eq_of_le htb]; exact hf t ht htb)
    (resetService_truncH hsvc b) (fun y t hy => hawake y t hy.1) (catchRun_truncH hcatch b)
    (fun y k hy hk => noRestartUpTo_iff.mp hnr y k hy.1 hk hy.2)
    (hH.mono fun _ hy => ⟨hy, le_rfl⟩) hδ hΔF hr hgr hG hcz hb
    (fun s₀ N hs₀ hN => proposalGap_truncH (hgp s₀ N hs₀ hN) (by linarith))
    (drainOutputs_truncH hdrain hczb) hstock
  exact ⟨a, isReset_of_truncH hczb ha (hab.trans hb), hab⟩

end Consensus.Goldilocks.Healing.Growing.KernelProof

end

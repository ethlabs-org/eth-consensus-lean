module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.DrainWarm
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.FrameWindow
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowEndpoint
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.Row
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingLeaves
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Local
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.StoreCache
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

/-- The proposal's own full frame already bounds its parent by the common floor. -/
theorem floor_le_warm_proposal_at {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
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
  have hac := (Compose.goldilocks_ac_projection_from hr (hnc.upTo _)).localRun
  have hvd := Healing.proposal_head_viable hac hr.vstart hzk hc hcall
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

/-- The client call of a high report under vote latency `D`, by a reporter honest `D` after it
and at `c_z`, supplies the reset no later than `D` after the report, including suppression. -/
theorem reset_of_high_report_within_at
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini) {g D : Time}
    (hlat : Generic.VoteLatencyAt tr H D) (hD : 0 ≤ D)
    {y : Fin sp.n} {i : Nat} (hyz : y ∈ H (max (cutZ sp.toParams g) (tr.time i + D)))
    (hq : (H (max (cutZ sp.toParams g) (tr.time i + D)))ᶜ.ncard < sp.toParams.fg.q)
    {ell : ACLabel (goldilocksNode sp ro)} {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hR : SA.ToFGAt tr.projAC y i ell R)
    (hh : HZ tr H g + 1 ≤ ((tr.state y i).fg.σ R.root).h) :
    ∃ a, IsReset tr H g a ∧ a ≤ tr.time i + D := by
  have hy := hrun.antitone ((le_add_of_nonneg_right hD).trans (le_max_right _ _)) hyz
  have hr := hrun.upTo (hrun.time_nonneg i)
  have hst := Trace.upTo_state tr y (i := i) (fun q hq => hrun.time_mono hq.le)
  obtain ⟨hc, hto, hres⟩ := hR
  apply Generic.reset_of_high_report_within_from hrun.toLocalRun hlat hyz hq ?_ hh
  refine ⟨ell, Compose.projAC_callAt.mp hc, hto, ?_⟩
  have hstate := Compose.projAC_state hr.toLocalRun hy i
  rw [RunTrace.upTo_projAC, Trace.upTo_state tr.projAC y
    (fun q hq => hrun.time_mono hq.le), hst] at hstate
  rwa [hstate] at hres

/-- The adjacent client call of a high report, by a reporter honest at it and at `c_z`, supplies
the reset, including suppression (`reset_of_high_report_within_at` at latency `0`). -/
theorem reset_of_high_report_at
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini) {g : Time}
    {y : Fin sp.n} {i : Nat} (hyz : y ∈ H (max (cutZ sp.toParams g) (tr.time i)))
    (hq : (H (max (cutZ sp.toParams g) (tr.time i)))ᶜ.ncard < sp.toParams.fg.q)
    {ell : ACLabel (goldilocksNode sp ro)} {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hR : SA.ToFGAt tr.projAC y i ell R)
    (hh : HZ tr H g + 1 ≤ ((tr.state y i).fg.σ R.root).h) :
    ∃ a, IsReset tr H g a ∧ a ≤ tr.time i := by
  simpa using reset_of_high_report_within_at hrun
    (Generic.voteLatency_zero_from hrun.toLocalRun) le_rfl (by simpa using hyz)
    (by simpa using hq) hR hh

/-- A proposal's immediate acceptance is held while its proposer is honest
(`Generic.proposal_mem_at_from` at the Goldilocks requirements from the run's starts). -/
theorem proposal_mem_at
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {p : Fin sp.n} {k : Nat}
    (hp : p ∈ H (tr.time k)) {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : tr.ProposesAt p k P) : P ∈ (tr.state p (k + 1)).fg.tree :=
  Generic.proposal_mem_at_from hrun.toLocalRun
    (fun y => Compose.requirements_from sp ro (hrun.vstart y)) hrun.genesis_root_ok hnc hp hP

/-- The report's actual frame supplies its fork-choice-root ancestry. -/
theorem report_root_at {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
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

/-- A warm proposal crosses one height when delayed signing and delivery fit before the next
sufficiently old honest proposal. -/
theorem round_of_warm_within_at
    {g ΔF b T D : Time} {s₀ u x N floor : Nat} {kindJ : Prop}
    {J P X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts N + 2 * sp.Δ) floor kindJ J)
    {K : SA.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (SA.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hwarm : s₀ + 2 * sp.k ≤ u)
    (hδ : 3 ≤ sp.toParams.fg.δt)
    (hlat : Generic.VoteLatencyAt tr H D) (hD : 0 ≤ D)
    (hΔF : 6 * sp.Δ + D + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time))
    (hux : u + sp.toParams.fg.δt ≤ x) (hxN : x ≤ N) (hmb : sp.ts N + 2 * sp.Δ ≤ b)
    (hTb : T ≤ b)
    (hna : ∀ v k att, v ∈ H (max (cutZ sp.toParams g) (tr.time k)) → tr.SignAt v k att →
      tr.time k < T → att.h ≤ HZ tr H g)
    (hT : sp.ts (u + 1 : Nat) + 2 * sp.Δ + D < T)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    {p : Fin sp.n} {kX : Nat} (hp : p ∈ H (tr.time kX)) (hdx : p = proposer x)
    (hX : tr.ProposesAt p kX X) (hXs : X.slot = x) (hK : CommitteeHalfUpTo tr H K g b) :
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
  have hcu : cutZ sp.toParams g ≤ sp.ts u := by
    have h4 := hts (show s₀ + 4 ≤ u by have := sp.two_le_k; omega)
    have he : sp.ts (s₀ + 4 : Nat) = sp.ts s₀ + 16 * sp.Δ := by
      simp only [SAParams.ts]; push_cast; ring
    linarith [cutZ_le sp g]
  have hv : gbar g ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ + D := by
    have := hts (show s₀ ≤ u + 1 by omega)
    linarith
  have hvx : sp.ts (u + 1 : Nat) + 2 * sp.Δ + D + ΔF ≤ tr.time kX := by
    have h1 := hts hux
    have h2 : sp.ts (u + sp.toParams.fg.δt : Nat) =
        sp.ts (u + 1 : Nat) + 4 * sp.Δ * (sp.toParams.fg.δt : Time) - 4 * sp.Δ := by
      simp only [SAParams.ts]; push_cast; ring
    rw [htX]
    linarith
  have hvc : sp.ts (u + 1 : Nat) + 2 * sp.Δ + D < tr.time kX := by
    linarith [hsvc.deltaF]
  have hfi : (H (sp.ts u))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    have hf' := hf (sp.ts u) (by simp only [SAParams.ts]; positivity)
      (by linarith [hts (show u ≤ N by omega)])
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
      hz hdes hP hPs (hrun.antitone (by linarith) hy) hK
  obtain ⟨i₀, ell₀, R₀, _, _, _, _, hPR₀, hR₀d⟩ := hfol p hp
  refine round_cross_at hrun hnc hsvc hnr hPH
    (hPR₀.trans (hR₀d x (by omega) hxN p c ellp hpc hc' hcall hct d pay hd')) hpar hp hX
    (hf _ (hrun.time_nonneg kX) (by rw [htX]; linarith [hts hxN])) hv hvx
    (by rw [htX]; linarith [hts hxN]) (by omega) ?_
  intro y hy
  obtain ⟨i, ell, R, hyi, hR, htil, hti, hPR, _⟩ := hfol y hy
  have hreport : Generic.ReportAt tr y i R :=
    ⟨ell, Compose.projAC_callAt.mp hR.1, hR.2.1,
      by change (SA.acToFG sp (tr.state y i).ac ell.frame (tr.time i)).2 = some R
         rw [← Compose.Growing.projAC_state_at hrun hyi]
         exact hR.2.2⟩
  obtain ⟨k, hik, hk, C, s, hatt, _, hRC, j, hij, hjk, ellC, hcC, htoC, hretC⟩ :=
    hlat.attests y i R hreport (hrun.antitone (by linarith) hy)
  have hPC := hPR.trans hRC
  have htk := hrun.time_mono hik
  have htkx : tr.time k < sp.ts x := by rw [← htX]; linarith
  have hyk := hrun.antitone (htX ▸ htkx.le) hy
  have htjk := hrun.time_mono hjk
  have hyj := hrun.antitone htjk hyk
  have hC : SA.ToFGAt tr.projAC y j ellC C :=
    ⟨Compose.projAC_callAt.mpr hcC, htoC,
      by change (SA.acToFG sp (tr.projAC.state y j) ellC.frame (tr.time j)).2 = some C
         rw [Compose.Growing.projAC_state_at hrun hyj]
         exact hretC⟩
  obtain ⟨hCj, hroot⟩ := report_root_at hrun hyj hC
  have hkle : ∀ q < k, tr.time q ≤ tr.time k := fun q hq => hrun.time_mono hq.le
  have hk0 := hrun.time_nonneg k
  have hCk := Compose.Growing.tree_mono_at hrun hk0 hyk hkle hjk hCj
  have hPk := mem_of_honest_anc_at hrun hnc hk0 hkle hyk hPC hCk
  have hσ := σ_eq_honest_at hrun hnc (hrun.time_nonneg kP)
    (fun q hq => hrun.time_mono (by omega)) (htimeP ▸ hz0) hk0 hkle hyk hPm hPk
  have hfloor := floor_le_warm_proposal_at hrun hnc hframe hz0 hdes hP hPs hu0
    (by linarith [hts huN]) hfi
  rw [hσ] at hfloor
  have hjlo := hu0.trans (htil.trans (hrun.time_mono hij))
  have hklo := hjlo.trans htjk
  have hkhi : tr.time k ≤ sp.ts N + 2 * sp.Δ := by linarith [hts hxN]
  have hkind := hframe.kind_iff y k hyk hklo hkhi
  have hfh := hframe.floor_eq y k hyk hklo hkhi
  obtain ⟨hPy, hCy, hor⟩ := Generic.row_or_high_of_attest_at_from hrun.toLocalRun hnc
    (fun t ht htT => hf t ht (htT.le.trans hTb)) hna
    (by rwa [max_eq_right (hcu.trans (htil.trans htk))]) hatt (by linarith) hCk hPC (fun _ => by
      right
      have hjmax := Healing.Store.hj_lt_hmax_of_reachable (fg_reachable_at hrun hk0 hkle hyk)
      by_cases hkj : kindJ
      · have ⟨hmax, hncst⟩ := hkind.mpr hkj
        have hjf : (tr.state y k).fg.hj = floor := by
          rw [Store.headHeightFloor, ite_eq_right hncst, hmax] at hfh
          omega
        rcases hfloor.lt_or_eq with hlt | heq
        · exact Or.inl (hjf ▸ hlt)
        right
        have hjkind := (hframe.kind_iff y j hyj hjlo (htjk.trans hkhi)).mpr hkj
        rw [Store.fcRoot, ite_eq_left hjkind,
          hframe.root_eq y j hyj hjlo (htjk.trans hkhi) hkj] at hroot
        refine ⟨hjf.trans heq, ?_⟩
        rw [hframe.root_eq y k hyk hklo hkhi hkj]
        exact store_anc_of_honest_anc_at hrun hnc hk0 hkle hyk
          (honest_anc_of_store_anc_at (hrun.time_nonneg j)
            (fun q hq => hrun.time_mono hq.le) hyj hroot) hCk
      · left
        have hlt : (tr.state y k).fg.hj < floor := by
          rw [Store.headHeightFloor] at hfh
          split_ifs at hfh with hcontest
          · omega
          · have hne : (tr.state y k).fg.hmax ≠ (tr.state y k).fg.hj + 1 :=
              fun he => hkj (hkind.mp ⟨he, hcontest⟩)
            omega
        exact hlt.trans_le hfloor)
  rcases hor with ⟨l, att, hyl, hs, hlk, hah, haT⟩ | hh
  · exact Or.inl ⟨y, k, hyk, hPy, l, att, hyl, hs, by linarith, hah, haT⟩
  · have hshort : FrameWindow tr H (sp.ts s₀) (sp.ts N + sp.Δ) floor kindJ J :=
      ⟨fun w l hw hlo hhi => hframe.floor_eq w l hw hlo (by linarith),
       fun w l hw hlo hhi => hframe.kind_iff w l hw hlo (by linarith),
       fun w l hw hlo hhi => hframe.root_eq w l hw hlo (by linarith)⟩
    have hChead := hshort.toFG_later_proposal_head_after_at hrun hnc hsvc hawake hf hcatch hnr
      hm hwarm (by linarith) hyj hC hPs hPC (by linarith [hts hxN])
      (htjk.trans_lt htkx) hxN hpc hc' hcall hct hd' hK
    exact Or.inr ⟨C, hChead, y, k, hyk, hPy, hCy, hh⟩

/-- The same-tick warm round is the delayed round with latency `0`. -/
theorem round_of_warm_at
    {g ΔF b T : Time} {s₀ u x N floor : Nat} {kindJ : Prop}
    {J P X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts N + 2 * sp.Δ) floor kindJ J)
    {K : SA.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (SA.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hwarm : s₀ + 2 * sp.k ≤ u)
    (hδ : 3 ≤ sp.toParams.fg.δt)
    (hΔF : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time))
    (hux : u + sp.toParams.fg.δt ≤ x) (hxN : x ≤ N) (hmb : sp.ts N + 2 * sp.Δ ≤ b)
    (hTb : T ≤ b)
    (hna : ∀ v k att, v ∈ H (max (cutZ sp.toParams g) (tr.time k)) → tr.SignAt v k att →
      tr.time k < T → att.h ≤ HZ tr H g)
    (hT : sp.ts (u + 1 : Nat) + 2 * sp.Δ < T)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    {p : Fin sp.n} {kX : Nat} (hp : p ∈ H (tr.time kX)) (hdx : p = proposer x)
    (hX : tr.ProposesAt p kX X) (hXs : X.slot = x) (hK : CommitteeHalfUpTo tr H K g b) :
    P ∈ (tr.state p (kX + 1)).fg.tree ∧ X ∈ (tr.state p (kX + 1)).fg.tree ∧
      ((tr.state p (kX + 1)).fg.σ P.root).h + 1 ≤
        ((tr.state p (kX + 1)).fg.σ X.root).h :=
  round_of_warm_within_at hframe hrun hnc hsvc hawake hf hcatch hnr hm hwarm hδ
    (Generic.voteLatency_zero_from hrun.toLocalRun) le_rfl (by simpa using hΔF)
    hux hxN hmb hTb hna (by simpa using hT) hz hdes hP hPs hp hdx hX hXs hK

/-- **The zero-rise reset under vote latency `D`**: with the premises of
`reset_of_high_proposal_at`, the latency `D` and a service horizon covering `t_{u+1} + 2Δ + D`,
a high warm proposal yields a reset by `t_{u+1} + 2Δ + D`. The frame window and the report are
those of the same-tick case; only the signing moves. -/
theorem reset_of_high_proposal_within_at
    {g ΔF b D : Time} {s₀ u N floor : Nat} {kindJ : Prop}
    {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts N + 2 * sp.Δ) floor kindJ J)
    {K : SA.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (SA.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hwarm : s₀ + 2 * sp.k ≤ u)
    (hN : u + 1 ≤ N) (hmb : sp.ts N + 2 * sp.Δ ≤ b) (hH : (H b).Nonempty)
    (hlat : Generic.VoteLatencyAt tr H D) (hD : 0 ≤ D)
    (hDb : sp.ts (u + 1 : Nat) + 2 * sp.Δ + D ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hh : HZ tr H g + 1 ≤ ((tr.state z (kP + 1)).fg.σ P.root).h)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∃ a, IsReset tr H g a ∧ a ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ + D := by
  have hΔ : 1 ≤ sp.Δ := sp.toParams.hΔ
  have hts : sp.ts (u + 1 : Nat) ≤ sp.ts N := (SA.ts_le_iff sp).2 (by exact_mod_cast hN)
  obtain ⟨y, hy⟩ := hH
  obtain ⟨i, ell, R, hyi, hR, htil, hti, hPR, _⟩ :=
    proposal_report_follow_at hframe hrun hnc hsvc hawake hf hcatch hnr hm hwarm hN hmb
      hz hdes hP hPs (hrun.antitone (by linarith) hy) hK
  have hcz : cutZ sp.toParams g ≤ tr.time i := by
    have h4 : sp.ts (s₀ + 4 : Nat) ≤ sp.ts u :=
      (SA.ts_le_iff sp).2 (by exact_mod_cast (show s₀ + 4 ≤ u by have := sp.two_le_k; omega))
    have he : sp.ts (s₀ + 4 : Nat) = sp.ts s₀ + 16 * sp.Δ := by
      simp only [SAParams.ts]; push_cast; ring
    linarith [cutZ_le sp g]
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
  -- The signing may come `D` after the report: read honesty and faults there, inside `b`.
  have hiD : tr.time i + D ≤ b := by linarith
  have hcD : max (cutZ sp.toParams g) (tr.time i + D) = tr.time i + D :=
    max_eq_right (by linarith)
  have hyD : y ∈ H (max (cutZ sp.toParams g) (tr.time i + D)) := by
    rw [hcD]; exact hrun.antitone hiD hy
  have hq : (H (max (cutZ sp.toParams g) (tr.time i + D)))ᶜ.ncard < sp.toParams.fg.q := by
    have hf' := hf _ (by linarith [hrun.time_nonneg i]) hiD
    have hn := sp.toParams.hn
    rw [hcD]
    change (H (tr.time i + D))ᶜ.ncard < (2 * sp.n + 2) / 3
    omega
  obtain ⟨a, ha, hat⟩ := reset_of_high_report_within_at hrun hlat hD hyD hq hR hhR
  exact ⟨a, ha, by linarith⟩

/-- A high warm proposal yields a reset via a reader honest at the report deadline
(`reset_of_high_proposal_within_at` at latency `0`). -/
theorem reset_of_high_proposal_at
    {g ΔF b : Time} {s₀ u N floor : Nat} {kindJ : Prop}
    {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts N + 2 * sp.Δ) floor kindJ J)
    {K : SA.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (SA.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hwarm : s₀ + 2 * sp.k ≤ u)
    (hN : u + 1 ≤ N) (hmb : sp.ts N + 2 * sp.Δ ≤ b) (hH : (H b).Nonempty)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hh : HZ tr H g + 1 ≤ ((tr.state z (kP + 1)).fg.σ P.root).h)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∃ a, IsReset tr H g a ∧ a ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ := by
  have hts : sp.ts (u + 1 : Nat) ≤ sp.ts N := (SA.ts_le_iff sp).2 (by exact_mod_cast hN)
  simpa using reset_of_high_proposal_within_at hframe hrun hnc hsvc hawake hf hcatch hnr hm
    hwarm hN hmb hH (Generic.voteLatency_zero_from hrun.toLocalRun) le_rfl (by linarith) hz hdes
    hP hPs hh hK

/-- Each round consumes one unit of height deficit. The latency `D` is covered by the timeout
between consecutive proposals and added once to the terminal deadline. -/
theorem rise_reset_rounds_within_at
    {g ΔF b T D : Time} {s₀ N G floor : Nat} {kindJ : Prop}
    {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts N + 2 * sp.Δ) floor kindJ J)
    {K : SA.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (SA.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀)
    (hδ : 3 ≤ sp.toParams.fg.δt) (hG : 1 ≤ G)
    (hlat : Generic.VoteLatencyAt tr H D) (hD : 0 ≤ D)
    (hΔF : 6 * sp.Δ + D + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time))
    (hgp : ProposalGap tr H proposer G s₀ N)
    (hmb : sp.ts N + 2 * sp.Δ ≤ b) (hH : (H b).Nonempty) (hTb : T ≤ b)
    (hna : ∀ v k att, v ∈ H (max (cutZ sp.toParams g) (tr.time k)) → tr.SignAt v k att →
      tr.time k < T → att.h ≤ HZ tr H g)
    (r : Nat) {u : Nat} (hwarm : s₀ + 2 * sp.k ≤ u)
    (hN : u + r * (sp.toParams.fg.δt + G - 1) + 1 ≤ N)
    (hT : sp.ts (u + r * (sp.toParams.fg.δt + G - 1) + 1 : Nat) + 2 * sp.Δ + D ≤ T)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hrise : HZ tr H g + 1 ≤ ((tr.state z (kP + 1)).fg.σ P.root).h + r)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∃ a, IsReset tr H g a ∧
      a ≤ sp.ts (u + r * (sp.toParams.fg.δt + G - 1) + 1 : Nat) + 2 * sp.Δ + D := by
  induction r generalizing u z kP P with
  | zero =>
    simpa only [Nat.zero_mul, Nat.add_zero] using
      reset_of_high_proposal_within_at hframe hrun hnc hsvc hawake hf hcatch hnr hm hwarm
        (by simpa using hN) hmb hH hlat hD (by simpa using hT.trans hTb)
        hz hdes hP hPs (by simpa using hrise) hK
  | succ r ih =>
    let ρ := sp.toParams.fg.δt + G - 1
    have hρ : 3 ≤ ρ := by dsimp [ρ]; omega
    have hmul : (r + 1) * ρ = r * ρ + ρ := Nat.succ_mul r ρ
    change u + (r + 1) * ρ + 1 ≤ N at hN
    change sp.ts (u + (r + 1) * ρ + 1 : Nat) + 2 * sp.Δ + D ≤ T at hT
    have hΔ : 1 ≤ sp.Δ := sp.toParams.hΔ
    have hts {a c : Nat} (h : a ≤ c) : sp.ts a ≤ sp.ts c :=
      (SA.ts_le_iff sp).2 (by exact_mod_cast h)
    by_cases hh : HZ tr H g + 1 ≤ ((tr.state z (kP + 1)).fg.σ P.root).h
    · have hle := hts (show u + 1 ≤ u + (r + 1) * ρ + 1 by omega)
      obtain ⟨a, ha, hat⟩ := reset_of_high_proposal_within_at hframe hrun hnc hsvc hawake hf
        hcatch hnr hm hwarm (by omega) hmb hH hlat hD (by linarith) hz hdes hP hPs hh hK
      exact ⟨a, ha, hat.trans (by linarith)⟩
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
    have hstrict : sp.ts (u + 1 : Nat) + 2 * sp.Δ + D < T := by
      have hlt : sp.ts (u + 1 : Nat) < sp.ts (u + (r + 1) * ρ + 1 : Nat) :=
        (SA.ts_lt_iff sp).2 (by exact_mod_cast (show u + 1 < u + (r + 1) * ρ + 1 by omega))
      linarith
    obtain ⟨hPX, _, hcross⟩ := round_of_warm_within_at hframe hrun hnc hsvc hawake hf hcatch hnr
      hm hwarm hδ hlat hD hΔF hxl (by omega) hmb hTb hna hstrict hz hdes hP hPs hpx0 rfl hX hXs hK
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

/-- The same-tick reset rounds are the delayed reset rounds with latency `0`. -/
theorem rise_reset_rounds_at
    {g ΔF b T : Time} {s₀ N G floor : Nat} {kindJ : Prop}
    {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts N + 2 * sp.Δ) floor kindJ J)
    {K : SA.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (SA.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀)
    (hδ : 3 ≤ sp.toParams.fg.δt) (hG : 1 ≤ G)
    (hΔF : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time))
    (hgp : ProposalGap tr H proposer G s₀ N)
    (hmb : sp.ts N + 2 * sp.Δ ≤ b) (hH : (H b).Nonempty) (hTb : T ≤ b)
    (hna : ∀ v k att, v ∈ H (max (cutZ sp.toParams g) (tr.time k)) → tr.SignAt v k att →
      tr.time k < T → att.h ≤ HZ tr H g)
    (r : Nat) {u : Nat} (hwarm : s₀ + 2 * sp.k ≤ u)
    (hN : u + r * (sp.toParams.fg.δt + G - 1) + 1 ≤ N)
    (hT : sp.ts (u + r * (sp.toParams.fg.δt + G - 1) + 1 : Nat) + 2 * sp.Δ ≤ T)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hrise : HZ tr H g + 1 ≤ ((tr.state z (kP + 1)).fg.σ P.root).h + r)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∃ a, IsReset tr H g a ∧
      a ≤ sp.ts (u + r * (sp.toParams.fg.δt + G - 1) + 1 : Nat) + 2 * sp.Δ := by
  simpa only [add_zero] using rise_reset_rounds_within_at hframe hrun hnc hsvc hawake hf hcatch
    hnr hm hδ hG (Generic.voteLatency_zero_from hrun.toLocalRun) le_rfl (by simpa using hΔF)
    hgp hmb hH hTb hna r hwarm hN (by simpa using hT) hz hdes hP hPs hrise hK

/-- The merged key bounds the deficit at the proposal cut itself. -/
theorem rounds_le_warm_proposal_at
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
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
    {K : SA.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (SA.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b r latency : Time} {G Ld : Nat}
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hH : (H b).Nonempty) (hδ : 3 ≤ sp.toParams.fg.δt)
    (hlat : Generic.VoteLatencyAt tr H latency) (hlat0 : 0 ≤ latency)
    (hΔF : 6 * sp.Δ + latency + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time))
    (hr : 0 ≤ r) (hgr : gbar g ≤ r) (hG : 1 ≤ G)
    (hcz : cutZ sp.toParams g + sp.Δ + 1 ≤ r + 4 * sp.Δ)
    (hb : Obligations.resetBoundRounds r sp.Δ (2 * sp.Δ) sp.toParams.fg.δt G Ld + 5 * latency ≤ b)
    (hgp : ∀ s₀ N : Nat, r + 4 * sp.Δ ≤ sp.ts s₀ →
      sp.ts N + 2 * sp.Δ <
        Obligations.resetBoundRounds r sp.Δ (2 * sp.Δ) sp.toParams.fg.δt G Ld + 5 * latency →
      ProposalGap tr H proposer G s₀ N)
    (hdrain : DrainOutputs tr proposer H g G Ld b) (hK : CommitteeHalfUpTo tr H K g b) :
    ∃ a, IsReset tr H g a ∧
      a ≤ Obligations.resetBoundRounds r sp.Δ (2 * sp.Δ) sp.toParams.fg.δt G Ld + 5 * latency := by
  classical
  let D := sp.Δ
  let ρ : Nat := sp.toParams.fg.δt + G - 1
  let lo := r + 4 * D
  let d := 4 * D * ((Ld : Time) + 2)
  let rt := 4 * D * (ρ : Time)
  let B := Obligations.resetBoundRounds r D (2 * D) sp.toParams.fg.δt G Ld + 5 * latency
  have hD : 1 ≤ D := sp.toParams.hΔ
  have hρ : (ρ : Time) = (sp.toParams.fg.δt : Time) + G - 1 := by
    dsimp [ρ]
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
  have hfq {t : Time} (ht : 0 ≤ t) (htb : t ≤ b) :
      (H t)ᶜ.ncard < sp.toParams.fg.q ∧
        (H t)ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    exact faults_lt_quorums sp.toParams.hn (hf t ht htb)
  have hczb : cutZ sp.toParams g ≤ b := by
    have hδ' : (3 : Time) ≤ sp.toParams.fg.δt := by exact_mod_cast hδ
    have hG' : (1 : Time) ≤ G := by exact_mod_cast hG
    have hLd' : (0 : Time) ≤ Ld := Nat.cast_nonneg _
    have hprod := mul_nonneg (show (0 : Time) ≤ 20 * Ld + 24 * (sp.toParams.fg.δt + G - 1) by
      linarith) (show (0 : Time) ≤ D by linarith)
    have hB : B = r + (20 * Ld + 24 * (sp.toParams.fg.δt + G - 1) + 54) * D + 5 * (2 * D)
        + 5 * latency := by dsimp [B]; rw [Obligations.resetBoundRounds_eq]
    linarith
  by_cases hadv : ∃ y k att, y ∈ H (max (cutZ sp.toParams g) (tr.time k)) ∧
      tr.SignAt y k att ∧ tr.time k ≤ B ∧ HZ tr H g + 1 ≤ att.h
  · obtain ⟨y, k, att, hy, hs, hk, hh⟩ := hadv
    obtain ⟨a, ha, hat⟩ := Generic.reset_of_height_advance_at_from hrun.toLocalRun
      (hfq ((hrun.time_nonneg k).trans (le_max_right _ _)) (max_le hczb (hk.trans hb))).1 hy hs hh
    exact ⟨a, ha, hat.trans hk⟩
  have hna : ∀ y k att, y ∈ H (max (cutZ sp.toParams g) (tr.time k)) → tr.SignAt y k att →
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
    obtain ⟨hsnap, hcall⟩ := Generic.snapshotCall_of_awake_at_from hrun.toLocalRun hawake hy
      (hcz.trans hi) hib
    have hczle : cutZ sp.toParams g ≤ tr.time i := by
      have hDpos : 0 < D := lt_of_lt_of_le (by decide) hD
      dsimp [lo, D] at hi
      linarith
    have hmax : max (cutZ sp.toParams g) (tr.time i) = tr.time i := max_eq_right hczle
    refine ⟨Generic.HZ_le_hmax_at_from hrun.toLocalRun hnc hsvc.toService hcatch
      (hH.mono (hrun.antitone (hczle.trans hib))) hsnap hy ?_ hcall (hlo.trans hi),
      Generic.hmax_le_of_noAdvance_at_from hrun.toLocalRun hna hy
        (by rw [hmax]; exact (hfq (hrun.time_nonneg i) hib).1) hiB⟩
    rw [hmax]
    exact (hfq (hrun.time_nonneg i) hib).2
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hrt : 0 ≤ rt := by dsimp [rt]; positivity
  let slack := 2 * D - 1 + latency
  have hlen := riseLen_nonneg hd hrt (show 0 ≤ slack by dsimp [slack]; linarith) (HZ tr H g)
  have hsum : lo + ∑ j ∈ Finset.range 5,
      (riseLen d rt slack (HZ tr H g) (2 * HZ tr H g + j) + 2 * D) = B - 5 := by
    rw [sum_riseLen]
    dsimp [lo, d, rt, slack, B]
    rw [Obligations.resetBoundRounds_eq, hρ]
    ring
  obtain ⟨v, hv, hvhi, af, haf, hend, hkey, floor, kindJ, J, hwin⟩ :=
    exists_frameWindow_seq_of_service_proof_at hrun hnc
      (fun t ht htb => (hfq ht htb).2) hsvc hcatch
      (riseLen d rt slack (HZ tr H g)) hlen (by linarith only [hD]) hlo hb hrange
      (fun z i m hz hi him hm => Generic.callLag_of_awake_at_from hrun.toLocalRun hawake
        (by dsimp [lo, D]; linarith) hz hi him (hm.le.trans hb))
      (by rw [hsum]; exact sub_lt_self B (by decide))
  let len := riseLen d rt slack (HZ tr H g) v
  have hsub : ∑ j ∈ Finset.range (v - 2 * HZ tr H g + 1),
      (riseLen d rt slack (HZ tr H g) (2 * HZ tr H g + j) + 2 * D) ≤
      ∑ j ∈ Finset.range 5,
      (riseLen d rt slack (HZ tr H g) (2 * HZ tr H g + j) + 2 * D) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun j _ _ => add_nonneg (hlen _) (by linarith only [hD]))
  have hwinB : af + len ≤ B - 5 := by linarith [hsum]
  obtain ⟨s₀, hslo, hshi⟩ := Generic.exists_slot_align_of_grid (P := sp.toParams)
    (fun s => by rw [sp.slotTime_eq]; ring) af
    (by dsimp [lo] at haf; linarith only [haf, hr, hD])
  replace hslo : af ≤ sp.ts s₀ := by rw [sp.slotTime_eq] at hslo; exact hslo
  let rr := riseRounds (HZ tr H g) v
  let N := s₀ + Ld + rr * ρ + 1
  have hNtime : sp.ts N = 4 * D * ((s₀ : Time) + Ld + (rr : Time) * (ρ : Time) + 1) := by
    change 4 * D * (N : Time) = _
    dsimp [N]
  have hlenEq : len = 4 * D * ((Ld : Time) + (rr : Time) * (ρ : Time) + 2) + slack := by
    dsimp [len, rr]
    rw [riseLen_eq]
    dsimp [d, rt]
    ring
  have hfit : sp.ts N + 2 * D + latency ≤ af + len := by
    rw [hNtime, hlenEq]
    change 4 * D * (s₀ : Time) < af + 4 * D at hshi
    have halign := Int.le_sub_one_of_lt hshi
    dsimp [slack]
    linarith only [halign]
  have hts {x y : Nat} (h : x ≤ y) : sp.ts x ≤ sp.ts y :=
    (SA.ts_le_iff sp).2 (by exact_mod_cast h)
  have hframe : FrameWindow tr H (sp.ts s₀) (sp.ts N + 2 * D) floor kindJ J :=
    ⟨fun y i hy hi hj => hwin.floor_eq y i hy (hslo.trans hi) (by linarith),
      fun y i hy hi hj => hwin.kind_iff y i hy (hslo.trans hi) (by linarith),
      fun y i hy hi hj => hwin.root_eq y i hy (hslo.trans hi) (by linarith)⟩
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
  have hrise := rounds_le_warm_proposal_at hrun hnc hwin hkey hv hulo huhi hz0 hdes hP hPs
    (hfq (by change 0 ≤ 4 * sp.Δ * (u : Time); positivity) (by linarith)).2
  obtain ⟨a, ha, hat⟩ := rise_reset_rounds_within_at hframe hrun hnc hsvc hawake hf hcatch hnr hm
    hδ hG hlat hlat0 hΔF hgpN hmb hH hb hna rr hwarm huN
    (by linarith [hts huN]) hz hdes hP hPs hrise hK
  exact ⟨a, ha, hat.trans (by linarith [hts huN])⟩

/-! ### Truncation after `b`

The honest sets truncated after `b` (`Generic.truncH`) keep every honesty read up to `b` and drop
every later one, so a restart honest on them is at a time `≤ b`, where `NoRestartUpTo` bounds it.
The run-independent facts are the generic ones (`Lemmas/Generic/HealingLeaves`). -/

open Generic (truncH truncH_eq_of_le honestBlocksAt_truncH_subset catchRun_truncH
  HZ_truncH isReset_truncH_iff)

/-- The local run laws transfer by `LocalRun.truncH`; the Goldilocks-specific laws preserve the
same starts and the genesis root. -/
theorem goldilocksRun_truncH {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini) (b : Time) :
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg (truncH H b) tr ini where
  toLocalRun := hrun.toLocalRun.truncH b
  vstart := hrun.vstart
  genesis_root_ok := hrun.genesis_root_ok

/-- Committee facts survive truncating honesty after `b`: the sizes do not read honesty, and P
and the gate read it only in hypotheses, where the truncation is a subset of `H`. -/
theorem _root_.Consensus.Goldilocks.Compose.Growing.CommitteeFacts.truncH
    {K : SA.CommitteeDict sp.n} (hK : Compose.Growing.CommitteeFacts tr H K) (b : Time) :
    Compose.Growing.CommitteeFacts tr (truncH H b) K where
  hsize := hK.hsize
  hP := ⟨fun t y hy i hi s v hv => hK.hP.1 t y hy.1 i hi s v hv,
    fun y i ℓ A hy hO s v hv => hK.hP.2 y i ℓ A hy.1 hO s v hv⟩
  hGate t ht x hx := hK.hGate t ht x hx.1

/-- The committee half bound through `b` survives truncating honesty after `b`: CS2 reads honesty
only at times `≤ b`, where the truncation is `H` itself. -/
theorem _root_.Consensus.Goldilocks.Healing.Growing.CommitteeHalfUpTo.truncH
    {K : SA.CommitteeDict sp.n} {g b : Time} (hK : CommitteeHalfUpTo tr H K g b) :
    CommitteeHalfUpTo tr (truncH H b) K g b :=
  ⟨hK.facts.truncH b, fun s hgs hsb d hd0 hdb => by
    rw [truncH_eq_of_le hdb]
    exact hK.cs2 s hgs hsb d hd0 hdb⟩

private theorem resetService_truncH {g ΔF b' : Time} (hs : ResetService tr H g ΔF b')
    (b : Time) : ResetService tr (truncH H b) g ΔF b' where
  deltaF := hs.deltaF
  message x i m hx hm y j hy := hs.message x i m hx.1 hm y j hy.1
  block x i B hx hB y j hy := hs.block x i B hx.1 hB y j hy.1
  relay x i B hx hB hg y j hy hj hd hF :=
    hs.relay x i B hx.1 hB hg y j hy.1 hj hd (Anc.mono (honestBlocksAt_truncH_subset b) hF)
  signedRow x i att hx hsg y j hy := hs.signedRow x i att hx.1 hsg y j hy.1

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
          have h := hsig v k att ⟨hv, max_le hcz (hk.trans hmb)⟩ hs hk
          rwa [HZ_truncH hcz] at h)
        (proposalGap_of_truncH hgp)
    have hts : sp.ts u ≤ sp.ts N := (SA.ts_le_iff sp).2 (by exact_mod_cast (show u ≤ N by omega))
    have hΔ : 1 ≤ sp.Δ := sp.toParams.hΔ
    refine ⟨u, hu, huL, z, kP, P, ⟨hz, by linarith⟩, hdes, hP, hPs, ?_⟩
    rwa [HZ_truncH hcz]

/-- **The delayed reset bound from finite service**, reading restarts only up to `b`: the rounds of
`exists_reset_of_drain_rounds_noRestartAfter_at` run on the honest sets truncated after `b`, where
the premises up to `b` are those for `H`, no restart is honest after `b`, and `H_z` and the reset
are those for `H` (`c_z` and the reset bound are `≤ b`). -/
theorem _root_.Consensus.Goldilocks.Healing.Growing.exists_reset_of_drain_rounds_awake_within_at
    {K : SA.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (SA.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b r latency : Time} {G Ld : Nat}
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartUpTo tr H (gbar g) b)
    (hH : (H b).Nonempty) (hδ : 3 ≤ sp.toParams.fg.δt)
    (hlat : Generic.VoteLatencyAt tr H latency) (hlat0 : 0 ≤ latency)
    (hΔF : 6 * sp.Δ + latency + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time))
    (hr : 0 ≤ r) (hgr : gbar g ≤ r) (hG : 1 ≤ G)
    (hcz : cutZ sp.toParams g + sp.Δ + 1 ≤ r + 4 * sp.Δ)
    (hb : Obligations.resetBoundRounds r sp.Δ (2 * sp.Δ) sp.toParams.fg.δt G Ld + 5 * latency ≤ b)
    (hgp : ∀ s₀ N : Nat, r + 4 * sp.Δ ≤ sp.ts s₀ →
      sp.ts N + 2 * sp.Δ <
        Obligations.resetBoundRounds r sp.Δ (2 * sp.Δ) sp.toParams.fg.δt G Ld + 5 * latency →
      ProposalGap tr H proposer G s₀ N)
    (hdrain : DrainOutputs tr proposer H g G Ld b) (hK : CommitteeHalfUpTo tr H K g b) :
    ∃ a, IsReset tr H g a ∧
      a ≤ Obligations.resetBoundRounds r sp.Δ (2 * sp.Δ) sp.toParams.fg.δt G Ld + 5 * latency := by
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
  have hlat' : Generic.VoteLatencyAt tr (truncH H b) latency := by
    refine ⟨fun y i R hR hy => ?_⟩
    obtain ⟨k, hik, hk, C, s, hc, hh, hRC, j, hij, hjk, ell, hcall, hto, hret⟩ :=
      hlat.attests y i R hR hy.1
    have hjb := (hrun.time_mono hjk).trans (hk.trans hy.2)
    have hyj := hrun.antitone (hrun.time_mono hjk |>.trans hk) hy.1
    have hC : SA.ToFGAt tr.projAC y j ell C :=
      ⟨Compose.projAC_callAt.mpr hcall, hto, by
        change (SA.acToFG sp (tr.projAC.state y j) ell.frame (tr.time j)).2 = some C
        rw [Compose.Growing.projAC_state_at hrun hyj]
        exact hret⟩
    have hle : ∀ q < j, tr.time q ≤ tr.time j := fun q hq => hrun.time_mono hq.le
    have hj0 := hrun.time_nonneg j
    have hlocal := store_anc_of_honest_anc_at hrun hnc hj0 hle hyj hRC
      (report_root_at hrun hyj hC).1
    exact ⟨k, hik, hk, C, s, hc, hh,
      honest_anc_of_store_anc_at (H := truncH H b) hj0 hle ⟨hyj, hjb⟩ hlocal,
      j, hij, hjk, ell, hcall, hto, hret⟩
  obtain ⟨a, ha, hab⟩ := exists_reset_of_drain_rounds_noRestartAfter_at
    (goldilocksRun_truncH hrun b) hnc
    (fun t ht htb => by rw [truncH_eq_of_le htb]; exact hf t ht htb)
    (resetService_truncH hsvc b) (fun y t hy => hawake y t hy.1) (catchRun_truncH hcatch b)
    (fun y k hy hk => noRestartUpTo_iff.mp hnr y k hy.1 hk hy.2)
    (hH.mono fun _ hy => ⟨hy, le_rfl⟩) hδ hlat' hlat0 hΔF hr hgr hG hcz hb
    (fun s₀ N hs₀ hN => proposalGap_truncH (hgp s₀ N hs₀ hN) (by linarith))
    (drainOutputs_truncH hdrain hczb) hK.truncH
  exact ⟨a, (isReset_truncH_iff hczb (hab.trans hb)).mp ha, hab⟩

/-- Finite-service reset with same-tick signing. -/
theorem _root_.Consensus.Goldilocks.Healing.Growing.exists_reset_of_drain_rounds_awake_at
    {K : SA.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (SA.committeeStart sp.genesisRoot K))
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
    (hdrain : DrainOutputs tr proposer H g G Ld b) (hK : CommitteeHalfUpTo tr H K g b) :
    ∃ a, IsReset tr H g a ∧
      a ≤ Obligations.resetBoundRounds r sp.Δ (2 * sp.Δ) sp.toParams.fg.δt G Ld := by
  simpa only [mul_zero, add_zero] using exists_reset_of_drain_rounds_awake_within_at hrun hnc
    hf hsvc hawake hcatch hnr hH hδ (Generic.voteLatency_zero_from hrun.toLocalRun) le_rfl
    (by simpa only [add_zero] using hΔF) hr hgr hG hcz
    (by simpa only [mul_zero, add_zero] using hb)
    (by simpa only [mul_zero, add_zero] using hgp) hdrain hK

end Consensus.Goldilocks.Healing.Growing.KernelProof

end

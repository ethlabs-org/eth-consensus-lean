module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.OldSources
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.Relay
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.OriginLabel
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.PivotBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameLabels
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Timing
import ConsensusLean.Lemmas.Tactic.Linarith

import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HalfCommittee
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.HighOriginSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Arith
public section

/-! # Receipt of historical high origins at proposals

The counted voter is honest through the origin write, hence through the snapshot.
Only that witness, not an arbitrary historical holder, is used to bound the relay's start.
-/

namespace Consensus.Goldilocks.Healing.Growing.ProposalImpl

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}
variable {hold : Time}

/-- Earlier high origins are held at an actual proposal, or below its finalized cache. -/
theorem proposal_holds_old_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {p : Fin sp.n} {i u : Nat} (hpH : p ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (AC.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b)
    {x : Fin sp.n} {r l : Nat} {O : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r l O) (hrt : tr.time r < sp.ts u) :
    O ∈ ell.frame.tree ∨ Anc (tr.HonestBlocksAt H) O ell.frame.F := by
  have hm := hp.run.time_mono
  have ht := hp.run.time_nonneg i
  have hrb : tr.time r ≤ b := hrt.le.trans (hti ▸ hib)
  have hac := Compose.Growing.goldilocks_ac_projection_from hp.run hp.noColl
  have hr := hac.localRun.upTo ht
  have hci' := (Trace.upTo_callAt tr.projAC).mpr (And.intro le_rfl hci)
  obtain ⟨hPhi, hPhiU⟩ := AC.frameIn_of_callAt hr hpH hci'
  have hcmp := finalized_compatible_high_origin_at hp hpH hib ho hrb
  have hruni := hp.run.upTo ht
  have hcin : (tr.upTo (tr.time i)).projAC.CallAt p i ell := by
    rwa [RunTrace.upTo_projAC]
  have hfr := Compose.frame_of_projAC hruni hpH hcin
  rw [RunTrace.upTo_state_of_le hm le_rfl] at hfr
  have hF : ell.frame.F = (tr.state p i).fg.F := by rw [hfr]; rfl
  rw [← hF] at hcmp
  rcases hcmp with hFO | hOF
  · left
    obtain ⟨ellX, D, CV, hcx, hfl, hOD⟩ := highOrigin_raw_head_at hp.run hp.noColl ho
    have hr' := hac.upTo (hp.run.time_nonneg r)
    have hlab := hp.cutZ_le_ts_of_highOrigin_at ho
    have hf := hp.committee_cs2_at (s := l) (Healing.gbar_le_of_cutZ_le sp hlab)
      ((ProposalImpl.ts_le_of_fastLock_at hp.run hfl).trans hrb) (hp.run.time_nonneg r) hrb
    obtain ⟨z, hz, j, e, hv, hes, B, hB, hBr, hDB⟩ :=
      AC.fastLock_honest_vote hr' _
        (AC.CommitteePAt.upTo hm hp.run.antitone hp.committeeFacts.hP _)
        (hp.run.antitone (le_max_right _ _) ho.1)
        ((AC.upTo_fastLockAt hm).mpr ⟨le_rfl, hfl⟩) hf
    obtain ⟨hjr, hv₀⟩ := (AC.upTo_voteAt).mp hv
    have hzj := hp.run.antitone hjr hz
    obtain ⟨ellZ, hcz, he⟩ := hv₀
    have hrj := hac.localRun.upTo (hp.run.time_nonneg j)
    have hcz' := (Trace.upTo_callAt tr.projAC).mpr (And.intro le_rfl hcz)
    obtain ⟨⟨B', hB't, hB'r, _⟩, hjt⟩ := Compose.cast_head_fcRoot hrj hp.run.vstart hzj
      ⟨hcz', he⟩
    have hBB : B' = B := hac.localRun.coherent.1
      ((AC.frameIn_of_callAt hrj hzj hcz').2 hB't) hB (hB'r.trans hBr.symm)
    subst B'
    have hOB := hOD.trans hDB
    have hzZ : z ∈ H (max (tr.time j) (cutZ sp.toParams g)) :=
      hp.run.antitone (max_le hjr (hlab.trans (ts_le_of_fastLock_at hp.run hfl))) hz
    have hBz : B ∈ (tr.state z j).fg.tree :=
      (frame_tree_subset_at hp.run hp.noColl hzj hcz).2 hB't
    have hZj := cutZ_lt_of_anc_at hp ho hzZ hBz hOB
    have hlu := label_lt_of_old_at hp.run ho hrt
    have hts : sp.ts l ≤ sp.ts ((u : Int) - 1) := (AC.ts_le_iff sp).mpr (by omega)
    have hjt' : tr.time j ≤ sp.ts ((u : Int) - 1) + sp.Δ := by
      rw [hes] at hjt
      change tr.time j ≤ sp.ts l + sp.Δ at hjt
      linarith
    rcases Compose.frame_anc_acceptedU hrj.toU hzj j ellZ hcz' B hB't B .refl with hg |
        ⟨c, hcj, hacc⟩
    · exact (hp.not_genesis_above_at ho
        ⟨z, j, tr.time j, hp.run.time_nonneg j, fun _ hq => hm hq.le, hzj, hBz⟩ hOB hg).elim
    have hctj : tr.time c ≤ tr.time j := hm hcj
    have hacc₀ := (ACTrace.upTo_acceptAt).mp hacc |>.2
    have hzc : z ∈ H (max (tr.time c) (cutZ sp.toParams g)) :=
      hp.run.antitone (max_le hctj (le_of_lt hZj))
        (hp.run.antitone hjr hz)
    have hzc₀ := hp.run.antitone hctj hzj
    have hBc : B ∈ (tr.state z c).fg.tree := by
      have hrunC := hp.run.upTo (hp.run.time_nonneg c)
      have haC : (tr.upTo (tr.time c)).projAC.AcceptAt z c B := by
        rw [RunTrace.upTo_projAC]
        exact (ACTrace.upTo_acceptAt).mpr ⟨le_rfl, hacc₀⟩
      obtain ⟨ellC, hcC, heC⟩ := hacc₀
      have hrC := hac.localRun.upTo (hp.run.time_nonneg c)
      have hcC' := (Trace.upTo_callAt tr.projAC).mpr (And.intro le_rfl hcC)
      exact (frame_tree_subset_at hp.run hp.noColl hzc₀ hcC).2
        ((AC.accept_new sp hrC hzc₀ ⟨ellC, hcC', heC⟩).1 ellC hcC')
    have hgc : g ≤ tr.time c := by
      have hcZ := cutZ_lt_of_anc_at hp ho hzc hBc hOB
      have := lt_cutZ sp g
      have := le_gbar g
      have := sp.toParams.hΔ
      linarith
    have hct : tr.time c < sp.ts ((u : Int) - 1) + 2 * sp.Δ := by
      have := sp.toParams.hΔ
      linarith
    have hd' : (AC.acProposal sp ((tr.upTo (tr.time i)).projAC.state p i)
        ell.frame (tr.time i)).2 = some (d, pay) := by
      rwa [RunTrace.upTo_projAC, Trace.upTo_state tr.projAC p (fun _ hq => hm hq.le)]
    have hrs := Compose.proposal_call_restarts hruni (hp.noColl.upTo _) hpH hcin hcall hd'
    have hslot : sp.slot (tr.time i) = u := by
      rw [hti]; simpa using (AC.slot_arithmetic sp u).1 0 (by omega)
    change ∀ c ≤ i, (tr.upTo (tr.time i)).projAC.RestartAt p c →
      tr.time c ≤ sp.ts ((sp.slot (tr.time i) : Int) - 1) at hrs
    rw [hslot] at hrs
    have hdl : ∀ k ≤ i, tr.projAC.deadline p k (tr.time c) ≤
        sp.ts ((u : Int) - 1) + 3 * sp.Δ := by
      intro k hk
      have hh := Compose.ac_deadline_le_of_restarts (T := tr.projAC)
        (fun c' hc' hr' => hrs c' (hc'.trans hk)
          (by rw [RunTrace.upTo_projAC]; exact
            (ACTrace.upTo_restartAt).mpr ⟨hm (hc'.trans hk), hr'⟩)) (tr.time c)
      have := sp.toParams.hΔ
      change _ ≤ max (tr.time c) (sp.ts ((u : Int) - 1)) + sp.Δ at hh
      have := max_le hct.le (show sp.ts ((u : Int) - 1) ≤
          sp.ts ((u : Int) - 1) + 2 * sp.Δ by linarith)
      linarith
    have htsu : sp.ts u = sp.ts ((u : Int) - 1) + 4 * sp.Δ := by
      simp only [ACParams.ts]; ring
    obtain ⟨k, hki, hak, _⟩ := hp.frame_relay_at hzc₀ hacc₀ hgc hpH hci
      (by rw [hti, htsu]; have := hdl i le_rfl; have := sp.toParams.hΔ; linarith)
      (hFO.trans hOB)
    have hak' := (ACTrace.upTo_acceptAt).mpr (And.intro (hm hki) hak)
    have hBt := AC.mem_tree_of_acceptAtU sp hr.toU hpH hak' hki hci' (hFO.trans hOB)
    exact Compose.mem_between hac.localRun.coherent hPhi hPhiU hPhi.rooted.1 hBt hFO hOB
  · exact Or.inr hOF

end Consensus.Goldilocks.Healing.Growing.ProposalImpl

end

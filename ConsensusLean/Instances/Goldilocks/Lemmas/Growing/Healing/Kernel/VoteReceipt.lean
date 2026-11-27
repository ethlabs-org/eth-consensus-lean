module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.VoteRelay
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.HighOriginSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.OriginLabel
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Timing
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Lemmas.Tactic.Linarith

import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HalfCommittee
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Arith
public section

/-! # A counted high-origin head reaches the vote freeze

The counted supporter is honest at the origin write, and therefore also at the
snapshot. This is stronger than honesty of an arbitrary historical holder.
-/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open AC (ACParams ReplayOrder Payload)
open ProposalImpl

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}
variable {hold : Time}

/-- A high origin's counted head is held at the later vote's freeze. -/
theorem high_origin_frozen_head_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x y : Fin sp.n} {r l k : Nat} {O : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r l O) (hrb : tr.time r ≤ b)
    (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y k ell e) (hl : l < e.msg.slot)
    (hFO : Anc (tr.HonestBlocksAt H) ell.frame.F O) :
    ∃ D ∈ AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot,
      Anc (tr.HonestBlocksAt H) O D := by
  have hm := hp.run.time_mono
  have hac := Compose.Growing.goldilocks_ac_projection_from hp.run hp.noColl
  obtain ⟨ellX, D, CV, hcx, hfl, hOD⟩ := highOrigin_raw_head_at hp.run hp.noColl ho
  have hr := hac.upTo (hp.run.time_nonneg r)
  have hlab := hp.cutZ_le_ts_of_highOrigin_at ho
  have hf := hp.committee_cs2_at (s := l) (Healing.gbar_le_of_cutZ_le sp hlab)
    ((ProposalImpl.ts_le_of_fastLock_at hp.run hfl).trans hrb) (hp.run.time_nonneg r) hrb
  obtain ⟨z, hz, j, ev, hv, hes, W, hW, hWr, hDW⟩ :=
    AC.fastLock_honest_vote hr _
      (AC.CommitteePAt.upTo hm hp.run.antitone hp.committeeFacts.hP _)
      (hp.run.antitone (le_max_right _ _) ho.1)
      ((AC.upTo_fastLockAt hm).mpr ⟨le_rfl, hfl⟩) hf
  obtain ⟨hjr, hv₀⟩ := AC.upTo_voteAt.mp hv
  have hzj := hp.run.antitone hjr hz
  obtain ⟨ellZ, hcz, he⟩ := hv₀
  have hrj := (hac.upTo (hp.run.time_nonneg j)).localRun
  have hcz' := Trace.upTo_callAt tr.projAC |>.mpr (And.intro le_rfl hcz)
  obtain ⟨⟨W', hW't, hW'r, _⟩, hjt⟩ :=
    Compose.cast_head_fcRoot hrj hp.run.vstart hzj ⟨hcz', he⟩
  have heq : W' = W := hac.localRun.coherent.1
    ((AC.frameIn_of_callAt hrj hzj hcz').2 hW't) hW (hW'r.trans hWr.symm)
  subst W'
  have hOW := hOD.trans hDW
  have hzZ : z ∈ H (max (tr.time j) (cutZ sp.toParams g)) :=
    hp.run.antitone (max_le hjr (hlab.trans (ts_le_of_fastLock_at hp.run hfl))) hz
  have hWz : W ∈ (tr.state z j).fg.tree :=
    (frame_tree_subset_at hp.run hp.noColl hzj hcz).2 hW't
  have hZj := cutZ_lt_of_anc_at hp ho hzZ hWz hOW
  have hjt' : tr.time j ≤ sp.ts l + sp.Δ := by
    rw [hes] at hjt
    exact hjt
  rcases Compose.frame_anc_acceptedU hrj.toU hzj j ellZ hcz' W hW't W .refl with hg |
      ⟨c, hcj, hacc⟩
  · exact (hp.not_genesis_above_at ho
      ⟨z, j, tr.time j, hp.run.time_nonneg j, fun _ hq => hm hq.le, hzj, hWz⟩ hOW hg).elim
  have hctj : tr.time c ≤ tr.time j := hm hcj
  have hacc₀ := ACTrace.upTo_acceptAt.mp hacc |>.2
  have hzc : z ∈ H (max (tr.time c) (cutZ sp.toParams g)) :=
    hp.run.antitone (max_le hctj hZj.le) hzj
  have hzc₀ := hp.run.antitone hctj hzj
  have hWc : W ∈ (tr.state z c).fg.tree := by
    obtain ⟨ellC, hcC, heC⟩ := hacc₀
    have hrC := (hac.upTo (hp.run.time_nonneg c)).localRun
    have hcC' := Trace.upTo_callAt tr.projAC |>.mpr (And.intro le_rfl hcC)
    exact (frame_tree_subset_at hp.run hp.noColl hzc₀ hcC).2
      ((AC.accept_new sp hrC hzc₀ ⟨ellC, hcC', heC⟩).1 ellC hcC')
  have hgc : g ≤ tr.time c := by
    have hcZ := cutZ_lt_of_anc_at hp ho hzc hWc hOW
    have := lt_cutZ sp g
    have := le_gbar g
    have := sp.toParams.hΔ
    linarith
  have hWT := relay_mem_voterBlockTree_at (s := l) hp hzc₀ hacc₀ hgc
    (by have := sp.toParams.hΔ; linarith) hy hc (by omega)
    (hFO.trans hOW)
  exact ⟨W, hWT, hOW⟩

end Consensus.Goldilocks.Healing.Growing.KernelProof

end

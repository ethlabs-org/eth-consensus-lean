module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.HighOriginSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.Relay
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Frames
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.OriginLabel
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Timing
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameFrozen
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
import ConsensusLean.Lemmas.Tactic.Linarith

import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HalfCommittee
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Arith
public section

/-! # A counted high-origin supporter reaches a later voter without catch-up

The supporter is honest through the origin write, hence through the snapshot.
Its own acceptance is after the snapshot; only post-GST relay is needed.
-/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open AC (ACParams ReplayOrder Payload)
open ProposalImpl

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}
variable {hold : Time}

set_option linter.unusedVariables false in
/-- A high origin is in a later honest cast's voter tree whenever its finalized cache
is below that origin. There is no catch-up premise or retained-vote induction dependency. -/
theorem high_origin_held_at_vote_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x y : Fin sp.n} {i j k : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hib : tr.time i ≤ b)
    (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y k ell e) (hkb : tr.time k ≤ b)
    (hj : j < e.msg.slot) (hF : Anc (tr.HonestBlocksAt H) ell.frame.F B) :
    B ∈ AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot := by
  have hm := hp.run.time_mono
  have hac := Compose.Growing.goldilocks_ac_projection_from hp.run hp.noColl
  have hr := hac.localRun.upTo (hp.run.time_nonneg k)
  have hc' : AC.CastAt (tr.projAC.upTo (tr.time k)) y k ell e :=
    ⟨(Trace.upTo_callAt _).mpr ⟨le_rfl, hc.1⟩, hc.2⟩
  obtain ⟨hPhi, hPhiU⟩ := AC.frameIn_of_callAt hr hy hc'.1
  obtain ⟨ellX, D, CV, hcx, hfl, hBD⟩ := highOrigin_raw_head_at hp.run hp.noColl ho
  have hr' := hac.upTo (hp.run.time_nonneg i)
  have hlab := hp.cutZ_le_ts_of_highOrigin_at ho
  have hf := hp.committee_cs2_at (s := j) (Healing.gbar_le_of_cutZ_le sp hlab)
    ((ProposalImpl.ts_le_of_fastLock_at hp.run hfl).trans hib) (hp.run.time_nonneg i) hib
  obtain ⟨z, hz, q, ez, hv, hes, W, hW, hWr, hDW⟩ :=
    AC.fastLock_honest_vote hr' _
      (AC.CommitteePAt.upTo hm hp.run.antitone hp.committeeFacts.hP _)
      (hp.run.antitone (le_max_right _ _) ho.1)
      ((AC.upTo_fastLockAt hm).mpr ⟨le_rfl, hfl⟩) hf
  obtain ⟨hqi, hv₀⟩ := (AC.upTo_voteAt).mp hv
  have hzq := hp.run.antitone hqi hz
  obtain ⟨ellZ, hcz, he⟩ := hv₀
  have hrq := hac.localRun.upTo (hp.run.time_nonneg q)
  have hcz' := (Trace.upTo_callAt tr.projAC).mpr (And.intro le_rfl hcz)
  obtain ⟨⟨W', hW't, hW'r, _⟩, hqt⟩ :=
    Compose.cast_head_fcRoot hrq hp.run.vstart hzq ⟨hcz', he⟩
  have hWW : W' = W := hac.localRun.coherent.1
    ((AC.frameIn_of_callAt hrq hzq hcz').2 hW't) hW (hW'r.trans hWr.symm)
  subst W'
  change tr.time q ≤ sp.ts ez.msg.slot + sp.Δ at hqt
  have hBW := hBD.trans hDW
  have hzZ : z ∈ H (max (tr.time q) (cutZ sp.toParams g)) :=
    hp.run.antitone (max_le hqi (hlab.trans (ts_le_of_fastLock_at hp.run hfl))) hz
  have hWz : W ∈ (tr.state z q).fg.tree :=
    (frame_tree_subset_at hp.run hp.noColl hzq hcz).2 hW't
  have hZq := cutZ_lt_of_anc_at hp ho hzZ hWz hBW
  rcases Compose.frame_anc_accepted hrq hzq q ellZ hcz' W hW't W .refl with hg |
      ⟨c, hcq, hacc⟩
  · exact (hp.not_genesis_above_at ho
      ⟨z, q, tr.time q, hp.run.time_nonneg q, fun _ hq => hm hq.le, hzq, hWz⟩ hBW hg).elim
  have hctq : tr.time c ≤ tr.time q := hm hcq
  have hacc₀ := (ACTrace.upTo_acceptAt).mp hacc |>.2
  have hzc : z ∈ H (max (tr.time c) (cutZ sp.toParams g)) :=
    hp.run.antitone (max_le hctq (le_of_lt hZq)) hzq
  have hzc₀ := hp.run.antitone hctq hzq
  have hWc : W ∈ (tr.state z c).fg.tree := by
    obtain ⟨ellC, hcC, heC⟩ := hacc₀
    have hrC := hac.localRun.upTo (hp.run.time_nonneg c)
    have hcC' := (Trace.upTo_callAt tr.projAC).mpr (And.intro le_rfl hcC)
    exact (frame_tree_subset_at hp.run hp.noColl hzc₀ hcC).2
      ((AC.accept_new sp hrC hzc₀ ⟨ellC, hcC', heC⟩).1 ellC hcC')
  have hgc : g ≤ tr.time c := by
    have := cutZ_lt_of_anc_at hp ho hzc hWc hBW
    linarith [lt_cutZ sp g, le_gbar g, sp.toParams.hΔ]
  have hΔ := sp.toParams.hΔ
  have hys := (AC.castAt_spec hr hy hc').2.1
  change e.msg.slot = sp.slot (tr.time k) at hys
  have hyj := (AC.castAt_spec hr hy hc').2.2.1
  have hm' : sp.ts ((e.msg.slot : Int) - 1) + 4 * sp.Δ = sp.ts e.msg.slot := by
    simp only [ACParams.ts]; ring
  have hkt : sp.ts e.msg.slot ≤ tr.time k :=
    (AC.ts_le_iff_le_slot sp (hp.run.time_nonneg k) _).mpr (by rw [hys])
  have hct : tr.time c < sp.ts ((e.msg.slot : Int) - 1) + 2 * sp.Δ := by
    rw [hes] at hqt
    have hts := (AC.ts_le_iff sp).mpr (show (j : Int) ≤ (e.msg.slot : Int) - 1 by omega)
    linarith
  have hrsy : ∀ r ≤ k, tr.projAC.RestartAt y r →
      tr.time r ≤ sp.ts ((e.msg.slot : Int) - 1) := by
    have hj' : AC.joined sp ((tr.projAC.upTo (tr.time k)).post k) (tr.time k) := by
      unfold AC.joined
      rw [AC.restartTime_of_castAt hr hy hc']
      exact hyj
    intro r hrk hrr
    have hrr' := (ACTrace.upTo_restartAt).mpr ⟨hm hrk, hrr⟩
    have hh := (AC.joined_awakeU sp (List (FG.Att sp.n)) ro (H (tr.time k))
      (tr.HonestBlocksAt H) _ hr.toU y hy k ell hc'.1 hj').2 r hrk hrr'
    change tr.time r ≤ sp.ts ((sp.slot (tr.time k) : Int) - 1) at hh
    rwa [← hys] at hh
  have hdl : ∀ r ≤ k, tr.projAC.deadline y r (tr.time c) <
      sp.ts ((e.msg.slot : Int) - 1) + 3 * sp.Δ := by
    intro r hrk
    have hd := Compose.ac_deadline_le_of_restarts
      (fun r' hrr hrs => hrsy r' (hrr.trans hrk) hrs) (tr.time c)
    change tr.projAC.deadline y r (tr.time c) ≤
      max (tr.time c) (sp.ts ((e.msg.slot : Int) - 1)) + sp.Δ at hd
    have hmax := max_lt hct (show sp.ts ((e.msg.slot : Int) - 1) <
      sp.ts ((e.msg.slot : Int) - 1) + 2 * sp.Δ by linarith)
    linarith
  obtain ⟨r, hrk, har, hrt⟩ := hp.frame_relay_at hzc₀ hacc₀ hgc hy hc.1
    (by have := hdl k le_rfl; linarith) (hF.trans hBW)
  have har' := (ACTrace.upTo_acceptAt).mpr ⟨hm hrk, har⟩
  have hWt := AC.mem_tree_of_acceptAt sp hr hy har' hrk hc'.1 (hF.trans hBW)
  have hrt' : tr.time r < AC.freeze sp e.msg.slot := by
    have := hdl r hrk
    unfold AC.freeze
    linarith
  have hfz : AC.freeze sp e.msg.slot ≤ tr.time k := by
    unfold AC.freeze
    linarith
  have hbs := AC.blockStamp_lt_of_acceptedBefore sp hr hp.run.vstart hy hc'.1 hWt
    (Or.inr ⟨r, har', hrt'⟩)
    (fun r hrk hrr => lt_of_le_of_lt (hrsy r hrk ((ACTrace.upTo_restartAt).mp hrr).2)
      (by unfold AC.freeze; linarith)) (Or.inl hfz)
  have hne : ∀ X, ell.call = .block X → W.root ≠ X.root := by
    intro X hcall hroot
    have hX := (AC.accept_new sp hr hy ⟨ell, hc'.1, hcall⟩).1 ell hc'.1
    obtain rfl : X = W := hac.localRun.coherent.1 (hPhiU hX) (hPhiU hWt) hroot.symm
    have heq := AC.accept_unique sp hr hy har' ⟨ell, hc'.1, hcall⟩
    rw [heq] at hrt'
    linarith
  rw [← AC.readPoint_blockStamp hr hy hc' hne] at hbs
  have hWtree : W ∈ AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot :=
    ⟨hWt, Or.inl hbs⟩
  have hBt := mem_of_honest_anc_at hp.run hp.noColl
    (hp.run.time_nonneg k) (fun _ hq => hm hq.le) hy hBW
      ((frame_tree_subset_at hp.run hp.noColl hy hc.1).2 hWt)
  have hBf : B ∈ ell.frame.tree := by
    have hF' := hF
    rw [Outcome.frame_of_call hp.run hy hc.1] at hF'
    rw [Outcome.frame_of_call hp.run hy hc.1]
    exact ⟨hBt, store_anc_of_honest_anc_at hp.run hp.noColl
      (hp.run.time_nonneg k) (fun _ hq => hm hq.le) hy hF' hBt⟩
  exact AC.voterBlockTree_anc hr hp.run.vstart hy hc' W hWtree B
    (AC.anc_tree_of_anc_U hac.localRun.coherent hPhi hPhiU hBf hBW hWt)

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end

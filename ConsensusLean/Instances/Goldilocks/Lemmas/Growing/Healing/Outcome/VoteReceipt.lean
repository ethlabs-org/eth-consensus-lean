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

public section

/-! # A counted high-origin supporter reaches a later voter without catch-up

The supporter is honest through the origin write, hence through the snapshot.
Its own acceptance is after the snapshot; only post-GST relay is needed.
-/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)
open ProposalImpl

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

set_option linter.unusedVariables false in
/-- A high origin is in a later honest cast's voter tree whenever its finalized cache
is below that origin. There is no catch-up premise or retained-vote induction dependency. -/
theorem high_origin_held_at_vote_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x y : Fin sp.n} {i j k : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hib : tr.time i ≤ b)
    (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ell e) (hkb : tr.time k ≤ b)
    (hj : j < e.msg.slot) (hF : Anc (tr.HonestBlocksAt H) ell.frame.F B) :
    B ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot := by
  have hm := hp.run.time_mono
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := hac.localRun.upTo (hp.run.time_nonneg k)
  have hc' : SA.CastAt (tr.projAC.upTo (tr.time k)) y k ell e :=
    ⟨(Trace.upTo_callAt _).mpr ⟨le_rfl, hc.1⟩, hc.2⟩
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hc'.1
  obtain ⟨ellX, D, CV, hcx, hfl, hBD⟩ := highOrigin_raw_head_at hp.run hp.noColl ho
  have hr' := hac.upTo (hp.run.time_nonneg i)
  have hf : 2 * (H (tr.time i))ᶜ.ncard < sp.n := by
    have := hp.faults (tr.time i) (hp.run.time_nonneg i) hib
    have hn := sp.toParams.hn
    change 0 < sp.n at hn
    omega
  obtain ⟨z, hz, q, ez, hv, hes, W, hW, hWr, hDW⟩ :=
    SA.fastLock_honest_vote hr' hf ho.1 ((SA.upTo_fastLockAt hm).mpr ⟨le_rfl, hfl⟩)
  obtain ⟨hqi, hv₀⟩ := (SA.upTo_voteAt).mp hv
  have hzq := hp.run.antitone hqi hz
  obtain ⟨ellZ, hcz, he⟩ := hv₀
  have hrq := hac.localRun.upTo (hp.run.time_nonneg q)
  have hcz' := (Trace.upTo_callAt tr.projAC).mpr (And.intro le_rfl hcz)
  obtain ⟨⟨W', hW't, hW'r, _⟩, hqt⟩ := Compose.cast_head_fcRoot hrq hzq ⟨hcz', he⟩
  have hWW : W' = W := hac.localRun.coherent.1
    ((SA.frameIn_of_callAt hrq hzq hcz').2 hW't) hW (hW'r.trans hWr.symm)
  subst W'
  change tr.time q ≤ sp.ts ez.msg.slot + sp.Δ at hqt
  have hBW := hBD.trans hDW
  have hzZ : z ∈ H (max (tr.time q) (cutZ sp.toParams g)) :=
    hp.run.antitone (max_le hqi ((hp.cutZ_le_ts_of_highOrigin_at ho hib).trans
      (ts_le_of_fastLock_at hp.run hfl))) hz
  have hWz : W ∈ (tr.state z q).fg.tree :=
    (frame_tree_subset_at hp.run hp.noColl hzq hcz).2 hW't
  have hZq := cutZ_lt_of_anc_at hp ho hzZ hWz hBW
  rcases Compose.frame_anc_accepted hrq hzq q ellZ hcz' W hW't W .refl with hg |
      ⟨c, hcq, hacc⟩
  · have hreach := fg_reachable_at hp.run (hp.run.time_nonneg q)
      (fun _ hq => hm hq.le) hzq
    have heq : W = sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload :=
      (Compose.Growing.honest_blocks_coherent hp.run hp.noColl).1
        ⟨z, q, tr.time q, hp.run.time_nonneg q, fun _ hq => hm hq.le, hzq, hWz⟩
        ⟨z, q, tr.time q, hp.run.time_nonneg q, fun _ hq => hm hq.le, hzq,
          (Store.accepted_tree _ _ _ _ hreach).2.2.1⟩ hg
    have hh := hp.high_of_anc_at ho (hp.run.time_nonneg q)
      (fun _ hq => hm hq.le) hzq hWz hBW
    rw [heq, show (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload).root =
        sp.toParams.genesisRoot from rfl, Store.σ_genesis hreach] at hh
    change HZ tr H g + 1 ≤ 1 at hh
    obtain ⟨kZ, hkZ, _⟩ := hp.snapshot
    have hzZ' := hp.run.antitone (le_max_right _ _) hzZ
    have hZ0 : 0 ≤ cutZ sp.toParams g := by
      linarith [lt_cutZ sp g, SA.gbar_nonneg g, sp.toParams.hΔ]
    have hreachZ := fg_reachable_at hp.run hZ0 hkZ.1 hzZ'
    have hGZ := (Store.accepted_tree _ _ _ _ hreachZ).2.2.1
    have hbnd := (Store.cache_invariants _ _ _ _ hreachZ).2.2.2.2.1 _ hGZ
    rw [show (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload).root =
        sp.toParams.genesisRoot from rfl, Store.σ_genesis hreachZ] at hbnd
    have hmax : (tr.state z kZ).fg.hmax ≤ HZ tr H g := by
      refine le_csSup (((Set.finite_range fun v => (tr.state v kZ).fg.hmax).subset ?_).bddAbove)
        ⟨z, hzZ', kZ, hkZ, rfl⟩
      rintro _ ⟨v, _, c', hc', rfl⟩
      obtain rfl := hc'.unique hkZ
      exact ⟨v, rfl⟩
    change 1 ≤ (tr.state z kZ).fg.hmax at hbnd
    omega
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
      ((SA.accept_new sp hrC hzc₀ ⟨ellC, hcC', heC⟩).1 ellC hcC')
  have hgc : g ≤ tr.time c := by
    have := cutZ_lt_of_anc_at hp ho hzc hWc hBW
    linarith [lt_cutZ sp g, le_gbar g, sp.toParams.hΔ]
  have hΔ := sp.toParams.hΔ
  have hys := (SA.castAt_spec hr hy hc').2.1
  change e.msg.slot = sp.slot (tr.time k) at hys
  have hyj := (SA.castAt_spec hr hy hc').2.2.1
  have hm' : sp.ts ((e.msg.slot : Int) - 1) + 4 * sp.Δ = sp.ts e.msg.slot := by
    simp only [SAParams.ts]; ring
  have hkt : sp.ts e.msg.slot ≤ tr.time k :=
    (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg k) _).mpr (by rw [hys])
  have hct : tr.time c < sp.ts ((e.msg.slot : Int) - 1) + 2 * sp.Δ := by
    rw [hes] at hqt
    have hts := (SA.ts_le_iff sp).mpr (show (j : Int) ≤ (e.msg.slot : Int) - 1 by omega)
    linarith
  have hrsy : ∀ r ≤ k, tr.projAC.RestartAt y r →
      tr.time r ≤ sp.ts ((e.msg.slot : Int) - 1) := by
    have hj' : SA.joined sp ((tr.projAC.upTo (tr.time k)).post k) (tr.time k) := by
      unfold SA.joined
      rw [SA.restartTime_of_castAt hr hy hc']
      exact hyj
    intro r hrk hrr
    have hrr' := (ACTrace.upTo_restartAt).mpr ⟨hm hrk, hrr⟩
    have hh := ((SA.joined_awake sp) (List (FG.Att sp.n)) ro (H (tr.time k))
      (tr.HonestBlocksAt H) _ hr y hy k ell hc'.1 hj').2 r hrk hrr'
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
  have hWt := SA.mem_tree_of_acceptAt sp hr hy har' hrk hc'.1 (hF.trans hBW)
  have hrt' : tr.time r < SA.freeze sp e.msg.slot := by
    have := hdl r hrk
    unfold SA.freeze
    linarith
  have hfz : SA.freeze sp e.msg.slot ≤ tr.time k := by
    unfold SA.freeze
    linarith
  have hbs := SA.blockStamp_lt_of_acceptedBefore sp hr hy hc'.1 hWt (Or.inr ⟨r, har', hrt'⟩)
    (fun r hrk hrr => lt_of_le_of_lt (hrsy r hrk ((ACTrace.upTo_restartAt).mp hrr).2)
      (by unfold SA.freeze; linarith)) (Or.inl hfz)
  have hne : ∀ X, ell.call = .block X → W.root ≠ X.root := by
    intro X hcall hroot
    have hX := (SA.accept_new sp hr hy ⟨ell, hc'.1, hcall⟩).1 ell hc'.1
    obtain rfl : X = W := hac.localRun.coherent.1 (hPhiU hX) (hPhiU hWt) hroot.symm
    have heq := SA.accept_unique sp hr hy har' ⟨ell, hc'.1, hcall⟩
    rw [heq] at hrt'
    linarith
  rw [← SA.readPoint_blockStamp hr hy hc' hne] at hbs
  have hWtree : W ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot :=
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
  exact SA.voterBlockTree_anc hr hy hc' W hWtree B
    (SA.anc_tree_of_anc_U hac.localRun.coherent hPhi hPhiU hBf hBW hWt)

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end

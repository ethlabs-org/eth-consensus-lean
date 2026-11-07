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

public section

/-! # A counted high-origin head reaches the vote freeze

The counted supporter is honest at the origin write, and therefore also at the
snapshot. This is stronger than honesty of an arbitrary historical holder.
-/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload)
open ProposalImpl

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- A high origin's counted head is held at the later vote's freeze. -/
theorem high_origin_frozen_head_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x y : Fin sp.n} {r l k : Nat} {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r l O) (hrb : tr.time r ≤ b)
    (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ell e) (hl : l < e.msg.slot)
    (hFO : Anc (tr.HonestBlocksAt H) ell.frame.F O) :
    ∃ D ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot,
      Anc (tr.HonestBlocksAt H) O D := by
  have hm := hp.run.time_mono
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  obtain ⟨ellX, D, CV, hcx, hfl, hOD⟩ := highOrigin_raw_head_at hp.run hp.noColl ho
  have hr := hac.upTo (hp.run.time_nonneg r)
  have hf : 2 * (H (tr.time r))ᶜ.ncard < sp.n := by
    have := hp.faults (tr.time r) (hp.run.time_nonneg r) hrb
    have hn := sp.toParams.hn
    change 0 < sp.n at hn
    omega
  obtain ⟨z, hz, j, ev, hv, hes, W, hW, hWr, hDW⟩ :=
    SA.fastLock_honest_vote hr hf ho.1 ((SA.upTo_fastLockAt hm).mpr ⟨le_rfl, hfl⟩)
  obtain ⟨hjr, hv₀⟩ := SA.upTo_voteAt.mp hv
  have hzj := hp.run.antitone hjr hz
  obtain ⟨ellZ, hcz, he⟩ := hv₀
  have hrj := (hac.upTo (hp.run.time_nonneg j)).localRun
  have hcz' := Trace.upTo_callAt tr.projAC |>.mpr (And.intro le_rfl hcz)
  obtain ⟨⟨W', hW't, hW'r, _⟩, hjt⟩ := Compose.cast_head_fcRoot hrj hzj ⟨hcz', he⟩
  have heq : W' = W := hac.localRun.coherent.1
    ((SA.frameIn_of_callAt hrj hzj hcz').2 hW't) hW (hW'r.trans hWr.symm)
  subst W'
  have hOW := hOD.trans hDW
  have hzZ : z ∈ H (max (tr.time j) (cutZ sp.toParams g)) :=
    hp.run.antitone (max_le hjr ((hp.cutZ_le_ts_of_highOrigin_at ho hrb).trans
      (ts_le_of_fastLock_at hp.run hfl))) hz
  have hWz : W ∈ (tr.state z j).fg.tree :=
    (frame_tree_subset_at hp.run hp.noColl hzj hcz).2 hW't
  have hZj := cutZ_lt_of_anc_at hp ho hzZ hWz hOW
  have hjt' : tr.time j ≤ sp.ts l + sp.Δ := by
    rw [hes] at hjt
    exact hjt
  rcases Compose.frame_anc_accepted hrj hzj j ellZ hcz' W hW't W .refl with hg |
      ⟨c, hcj, hacc⟩
  · have hreach := fg_reachable_at hp.run (hp.run.time_nonneg j)
      (fun _ hq => hm hq.le) hzj
    have heq : W = sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload :=
      (Compose.Growing.honest_blocks_coherent hp.run hp.noColl).1
        ⟨z, j, tr.time j, hp.run.time_nonneg j, fun _ hq => hm hq.le, hzj, hWz⟩
        ⟨z, j, tr.time j, hp.run.time_nonneg j, fun _ hq => hm hq.le, hzj,
          (Store.accepted_tree _ _ _ _ hreach).2.2.1⟩ hg
    have hh := hp.high_of_anc_at ho (hp.run.time_nonneg j)
      (fun _ hq => hm hq.le) hzj hWz hOW
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
      ((SA.accept_new sp hrC hzc₀ ⟨ellC, hcC', heC⟩).1 ellC hcC')
  have hgc : g ≤ tr.time c := by
    have hcZ := cutZ_lt_of_anc_at hp ho hzc hWc hOW
    have := lt_cutZ sp g
    have := le_gbar g
    have := sp.toParams.hΔ
    linarith
  have hWT := relay_mem_voterBlockTree_at hp hzc₀ hacc₀ hgc
    (by have := sp.toParams.hΔ; linarith) hy hc (by omega)
    (hFO.trans hOW)
  exact ⟨W, hWT, hOW⟩

/-- A high origin supplies a frozen viable head above a target and a held floor witness. -/
theorem raw_target_frozen_witness_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x y : Fin sp.n} {r l k : Nat} {B O E : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r l O) (hrb : tr.time r ≤ b)
    (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ell e) (hl : l < e.msg.slot)
    (hFB : Anc (tr.HonestBlocksAt H) ell.frame.F B)
    (hBO : Anc (tr.HonestBlocksAt H) B O) (_hE : E ∈ (tr.state y k).fg.tree)
    (hEO : Anc (tr.HonestBlocksAt H) E O)
    (hfloor : (tr.state y k).fg.headHeightFloor ≤ ((tr.state y k).fg.σ E.root).h) :
    ∃ D ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot,
      Anc (tr.HonestBlocksAt H) B D ∧ (tr.state y k).fg.IsViable D := by
  have hm := hp.run.time_mono
  obtain ⟨W, hWT, hOW⟩ := high_origin_frozen_head_at hp ho hrb hy hc hl (hFB.trans hBO)
  have hWy := (frame_tree_subset_at hp.run hp.noColl hy hc.1).2 hWT.1
  have hh := Healing.h_le_of_store_anc
    (fg_reachable_at hp.run (hp.run.time_nonneg k) (fun _ hq => hm hq.le) hy)
    (store_anc_of_honest_anc_at hp.run hp.noColl (hp.run.time_nonneg k)
      (fun _ hq => hm hq.le) hy (hEO.trans hOW) hWy)
  exact ⟨W, hWT, hBO.trans hOW, hfloor.trans hh⟩

end Consensus.Goldilocks.Healing.Growing.KernelProof

end

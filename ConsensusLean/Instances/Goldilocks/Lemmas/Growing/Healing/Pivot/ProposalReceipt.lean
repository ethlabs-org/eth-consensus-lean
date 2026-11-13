module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.OldSources
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.Relay
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.OriginLabel
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Pivot
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Timing
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Receipt of historical high origins at proposals

The counted voter is honest through the origin write, hence through the snapshot.
Only that witness, not an arbitrary historical holder, is used to bound the relay's start.
-/

namespace Consensus.Goldilocks.Healing.Growing.ProposalImpl

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- Earlier high origins are held at an actual proposal, or below its finalized cache. -/
theorem proposal_holds_old_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {p : Fin sp.n} {i u : Nat} (hpH : p ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b)
    {x : Fin sp.n} {r l : Nat} {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r l O) (hrt : tr.time r < sp.ts u) :
    O ∈ ell.frame.tree ∨ Anc (tr.HonestBlocksAt H) O ell.frame.F := by
  have hm := hp.run.time_mono
  have ht := hp.run.time_nonneg i
  have hrb : tr.time r ≤ b := hrt.le.trans (hti ▸ hib)
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := hac.localRun.upTo ht
  have hci' := (Trace.upTo_callAt tr.projAC).mpr (And.intro le_rfl hci)
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hpH hci'
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
    have hf : 2 * (H (tr.time r))ᶜ.ncard < sp.n := by
      have := hp.faults (tr.time r) (hp.run.time_nonneg r) hrb
      have hn := sp.toParams.hn
      change 0 < sp.n at hn
      omega
    obtain ⟨z, hz, j, e, hv, hes, B, hB, hBr, hDB⟩ :=
      SA.fastLock_honest_vote hr' hf ho.1 ((SA.upTo_fastLockAt hm).mpr ⟨le_rfl, hfl⟩)
        hp.stock
    obtain ⟨hjr, hv₀⟩ := (SA.upTo_voteAt).mp hv
    have hzj := hp.run.antitone hjr hz
    obtain ⟨ellZ, hcz, he⟩ := hv₀
    have hrj := hac.localRun.upTo (hp.run.time_nonneg j)
    have hcz' := (Trace.upTo_callAt tr.projAC).mpr (And.intro le_rfl hcz)
    obtain ⟨⟨B', hB't, hB'r, _⟩, hjt⟩ := Compose.cast_head_fcRoot hrj hzj ⟨hcz', he⟩
    have hBB : B' = B := hac.localRun.coherent.1
      ((SA.frameIn_of_callAt hrj hzj hcz').2 hB't) hB (hB'r.trans hBr.symm)
    subst B'
    have hOB := hOD.trans hDB
    have hzZ : z ∈ H (max (tr.time j) (cutZ sp.toParams g)) :=
      hp.run.antitone (max_le hjr ((hp.cutZ_le_ts_of_highOrigin_at ho hrb).trans
        (ts_le_of_fastLock_at hp.run hfl))) hz
    have hBz : B ∈ (tr.state z j).fg.tree :=
      (frame_tree_subset_at hp.run hp.noColl hzj hcz).2 hB't
    have hZj := cutZ_lt_of_anc_at hp ho hzZ hBz hOB
    have hlu := label_lt_of_old_at hp.run ho hrt
    have hts : sp.ts l ≤ sp.ts ((u : Int) - 1) := (SA.ts_le_iff sp).mpr (by omega)
    have hjt' : tr.time j ≤ sp.ts ((u : Int) - 1) + sp.Δ := by
      rw [hes] at hjt
      change tr.time j ≤ sp.ts l + sp.Δ at hjt
      linarith
    rcases Compose.frame_anc_accepted hrj hzj j ellZ hcz' B hB't B .refl with hg |
        ⟨c, hcj, hacc⟩
    · have hreach := fg_reachable_at hp.run (hp.run.time_nonneg j)
        (fun _ hq => hm hq.le) hzj
      have heq : B = sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload :=
        (Compose.Growing.honest_blocks_coherent hp.run hp.noColl).1
          ⟨z, j, tr.time j, hp.run.time_nonneg j, fun _ hq => hm hq.le, hzj, hBz⟩
          ⟨z, j, tr.time j, hp.run.time_nonneg j, fun _ hq => hm hq.le, hzj,
            (Store.accepted_tree _ _ _ _ hreach).2.2.1⟩ hg
      have hh := hp.high_of_anc_at ho (hp.run.time_nonneg j)
        (fun _ hq => hm hq.le) hzj hBz hOB
      have hgen := Store.σ_genesis hreach
      rw [heq, show (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload).root =
          sp.toParams.genesisRoot from rfl,
        hgen] at hh
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
        ((SA.accept_new sp hrC hzc₀ ⟨ellC, hcC', heC⟩).1 ellC hcC')
    have hgc : g ≤ tr.time c := by
      have hcZ := cutZ_lt_of_anc_at hp ho hzc hBc hOB
      have := lt_cutZ sp g
      have := le_gbar g
      have := sp.toParams.hΔ
      linarith
    have hct : tr.time c < sp.ts ((u : Int) - 1) + 2 * sp.Δ := by
      have := sp.toParams.hΔ
      linarith
    have hd' : (SA.acProposal sp ((tr.upTo (tr.time i)).projAC.state p i)
        ell.frame (tr.time i)).2 = some (d, pay) := by
      rwa [RunTrace.upTo_projAC, Trace.upTo_state tr.projAC p (fun _ hq => hm hq.le)]
    have hrs := Compose.proposal_call_restarts hruni (hp.noColl.upTo _) hpH hcin hcall hd'
    have hslot : sp.slot (tr.time i) = u := by
      rw [hti]; simpa using (SA.slot_arithmetic sp u).1 0 (by omega)
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
      simp only [SAParams.ts]; ring
    obtain ⟨k, hki, hak, _⟩ := hp.frame_relay_at hzc₀ hacc₀ hgc hpH hci
      (by rw [hti, htsu]; have := hdl i le_rfl; have := sp.toParams.hΔ; linarith)
      (hFO.trans hOB)
    have hak' := (ACTrace.upTo_acceptAt).mpr (And.intro (hm hki) hak)
    have hBt := SA.mem_tree_of_acceptAt sp hr hpH hak' hki hci' (hFO.trans hOB)
    exact Compose.mem_between hac.localRun.coherent hPhi hPhiU hPhi.rooted.1 hBt hFO hOB
  · exact Or.inr hOF

end Consensus.Goldilocks.Healing.Growing.ProposalImpl

end

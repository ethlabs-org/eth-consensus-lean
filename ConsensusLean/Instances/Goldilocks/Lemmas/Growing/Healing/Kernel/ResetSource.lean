module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Unlocked
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Reset
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Reset sources and the original snapshot frontier

Counted voters are charged at the snapshot, while the reset signer is required honest
only at its signing. No service or awake premise is needed for the lower bound.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

private theorem hmax_le_snapshot {y : Fin sp.n} (hy : y ∈ H (cutZ sp.toParams g))
    {j : Nat} (hj : FirstCutAfter tr j (cutZ sp.toParams g)) :
    (tr.state y j).fg.hmax ≤ HZ tr H g := by
  refine le_csSup (((Set.finite_range fun z => (tr.state z j).fg.hmax).subset ?_).bddAbove)
    ⟨y, hy, j, hj, rfl⟩
  rintro _ ⟨z, -, j', hj', rfl⟩
  obtain rfl := hj'.unique hj
  exact ⟨z, rfl⟩

/-- The reset lies after the snapshot from its fault bound alone. The counted fast-lock votes
are a committee half, read at the stock committee (`hstock`, §S.2 scope-(ii) item). -/
theorem cutZ_lt_reset_of_fault_bound_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr)
    (hsnapshot : ∃ j, FirstCutAfter tr j (cutZ sp.toParams g))
    (hf : 2 * (H (cutZ sp.toParams g))ᶜ.ncard < sp.n)
    (hR : IsReset tr H g a) (hstock : sp.committeeSize = sp.n) : cutZ sp.toParams g < a := by
  classical
  obtain ⟨⟨y, k, att, hy, hs, hh, rfl⟩, -⟩ := hR
  by_contra hlate
  have hka : tr.time k ≤ cutZ sp.toParams g := le_of_not_gt hlate
  have hk0 := hrun.time_nonneg k
  have hr := hrun.upTo hk0
  have hsign := (RunTrace.upTo_signAt tr).mpr ⟨le_rfl, hs⟩
  obtain ⟨r, hkr, hrt, ell, C, E, hto, hC, hE, _, hEC, _, _, hEh, hCa⟩ :=
    Healing.signAt_report_entry hr hy hsign
  have hac := Compose.goldilocks_ac_projection sp ro dg (H (tr.time k))
    (tr.upTo (tr.time k)) proposer hr (hnc.upTo _)
  have hU := hac.localRun.coherent
  have subU := RunTrace.honestBlocks_upTo_subset hrun.time_mono (H := H) hk0
  obtain ⟨hcall, _, hret⟩ := hto
  obtain ⟨hCv, l, hl, hlb, hlf, _⟩ := SA.toFG_candidate hret
  obtain ⟨l₀, hl₀, B₀, hB₀, hB₀r, _, rfl⟩ := hl
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hac.localRun hy hcall
  obtain ⟨c, hcr, D, CV, hfl, L, hL, hLr, hLD⟩ :=
    SA.fast_lock_provenance hac.localRun hy r l₀ hl₀ hlf
  have hB : B₀ = L := hU.1 (hΦU hB₀) hL (hB₀r.trans hLr.symm)
  have hCL : C = ell.frame.viableAncestor B₀ :=
    hU.1 (hΦU hCv.1) (hΦU (SA.viableAncestor_anc hΦ hB₀).1) hlb.symm
  have hCLanc : Anc ((tr.upTo (tr.time k)).HonestBlocks (H (tr.time k))) C D := by
    rw [hCL]
    exact ((SA.anc_viableAncestor ell.frame B₀).mono hΦU).trans (hB ▸ hLD)
  obtain ⟨hcount, hheads⟩ := SA.fastLock_counted hac hy hfl
  rw [hstock] at hcount
  have hless : (H (cutZ sp.toParams g))ᶜ.ncard < {u | ∃ v ∈ CV, v.val = u}.ncard := by omega
  obtain ⟨v, ⟨vote, hvote, rfl⟩, hv⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hless
  have hvZ : vote.val ∈ H (cutZ sp.toParams g) := not_not.mp hv
  have hvk := hrun.antitone hka hvZ
  obtain ⟨hvs, R, hRU, hRroot, _, hDR⟩ := hheads vote hvote
  have hvcast : ∃ q ≤ c, ∃ e, SA.VoteAt (tr.upTo (tr.time k)).projAC vote.val q e ∧
      e.msg = vote := by
    rcases hfl with ⟨ell', _, hu, _, _, hCV⟩ | ⟨ell', A, hpt, _, _, hCV⟩
    · subst CV
      obtain ⟨q, hq, e, he, hev⟩ := hac.honest.pool_vote y hy c _ vote hvote.1 hvk
      exact ⟨q, hq.le, e, he, hev⟩
    · subst CV
      exact (SA.optimisticPoint_pool_vote hac hy hpt hvote.1 hvk).2
  obtain ⟨q, hqc, e, ⟨ellq, hcq, heq⟩, hev⟩ := hvcast
  obtain ⟨⟨R', hR'frame, hR'root, _⟩, _⟩ := Compose.cast_head_fcRoot hac.localRun hvk ⟨hcq, heq⟩
  have hframe := Compose.frame_of_projAC hr hvk hcq
  have hR' : R' ∈ ((tr.upTo (tr.time k)).state vote.val q).fg.tree := by
    rw [hframe] at hR'frame
    exact hR'frame.1
  have hR'U : R' ∈ (tr.upTo (tr.time k)).HonestBlocks (H (tr.time k)) := ⟨_, hvk, q, hR'⟩
  have heR : R = R' := hU.1 hRU hR'U (hRroot.trans (by rw [hev] at hR'root; exact hR'root.symm))
  subst R'
  have hrk : r ≤ k := by omega
  have hqk : q ≤ k := hqc.trans (hcr.le.trans hrk)
  have hrtime : tr.time r ≤ tr.time k := hrun.time_mono hrk
  have hqtime : tr.time q ≤ tr.time k := hrun.time_mono hqk
  have hsR := RunTrace.upTo_state_of_le (y := vote.val) hrun.time_mono hqtime
  have hsE := RunTrace.upTo_state_of_le (y := y) hrun.time_mono hrtime
  rw [hsR] at hR'
  rw [hsE] at hE hEC hEh hCa
  have hEC' : Anc (tr.HonestBlocksAt H) E C := honest_anc_of_store_anc_at hk0
    (fun _ hi => (hrun.time_mono hi.le).trans hrtime) hy hEC
  have hER := hEC'.trans (Anc.mono subU (hCLanc.trans hDR))
  have hqZ : tr.time q ≤ cutZ sp.toParams g := hqtime.trans hka
  have hEq := mem_of_honest_anc_at hrun hnc ((hrun.time_nonneg q).trans hqZ)
    (fun _ hi => (hrun.time_mono hi.le).trans hqZ) hvZ hER hR'
  have hσ := σ_eq_honest_at hrun hnc hk0
    (fun _ hi => (hrun.time_mono hi.le).trans hrtime) hy
    ((hrun.time_nonneg q).trans hqZ) (fun _ hi => (hrun.time_mono hi.le).trans hqZ) hvZ hE hEq
  obtain ⟨j, hj⟩ := hsnapshot
  have hqj : q ≤ j := by
    by_contra h
    exact (not_lt_of_ge hqZ) (hj.2.trans_le (hrun.time_mono (by omega)))
  have hz0 := hk0.trans hka
  have hbefore : ∀ i < j, tr.time i ≤ cutZ sp.toParams g := hj.1
  have hprefix := hrun.upTo hz0
  have hEq' : E ∈ ((tr.upTo (cutZ sp.toParams g)).state vote.val q).fg.tree := by
    rw [Trace.upTo_state tr vote.val (fun _ hi => (hrun.time_mono hi.le).trans hqZ)]
    exact hEq
  have hEj := Compose.tree_mono hprefix.toLocalRun hvZ hqj hEq'
  have hσj := Store.σ_eq_of_mem (Compose.fg_reachable hprefix.toLocalRun hvZ q)
    (Compose.fg_reachable hprefix.toLocalRun hvZ j)
    (Compose.honest_blocks_coherent hprefix.toLocalRun (hnc.upTo _)).1
    (fun _ hX => ⟨vote.val, hvZ, q, hX⟩) (fun _ hX => ⟨vote.val, hvZ, j, hX⟩) hEq' hEj
  rw [Trace.upTo_state tr vote.val hbefore] at hEj hσj
  rw [Trace.upTo_state tr vote.val (fun _ hi => (hrun.time_mono hi.le).trans hqZ)] at hσj
  have hbound :=
    ((Store.cache_invariants _ _ _ _ (fg_reachable_at hrun hz0 hbefore hvZ)).2.2.2.2.1 E hEj).trans
      (hmax_le_snapshot hvZ hj)
  rw [← hσj, ← hσ] at hbound
  omega

/-- Finite reset premises suffice; the snapshot is observed before their horizon. -/
theorem ResetPremisesUpTo.cutZ_lt_reset_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) : cutZ sp.toParams g < a := by
  obtain ⟨j, hj, hjb⟩ := hp.snapshot
  have hz0 : 0 ≤ cutZ sp.toParams g := by
    have := Healing.gbar_nonneg g
    have := Healing.lt_cutZ sp g
    have := sp.toParams.hΔ
    linarith
  have hf := hp.faults _ hz0 (hj.2.le.trans hjb)
  exact cutZ_lt_reset_of_fault_bound_at hp.run hp.noColl ⟨j, hj⟩ (by
    have := sp.toParams.hn
    change 0 < sp.n at this
    omega) hp.reset hp.stock

end Consensus.Goldilocks.Healing.Growing

end

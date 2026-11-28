module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.ServiceCarry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.OptimisticFirstProposal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PrefixBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshVotesRelay
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Relay
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.PivotBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameLabels
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Committee

public section

/-! # Compatibility of optimistic locks under growing faults

Compare the writers' locks using honesty at their respective writes and the fault count at the
later write. This comparison does not require a frame window. -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open AC (ACParams Payload Vote)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}

/-- The static AC run of the prefix through `d` of the nodes honest at `d`. -/
private theorem acRun_prefix {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {d : Time} (hd : 0 ≤ d) :
    AC.ACRun proposer (tr.projAC.upTo d) (H d) ((tr.upTo d).HonestBlocks (H d)) ini := by
  have h := Compose.goldilocks_ac_projection_from (hrun.upTo hd) (hnc.upTo d)
  rwa [RunTrace.upTo_projAC] at h

/-- **Two optimistic locks of one slot are compatible**, their writers honest at their own
writes, with fewer than half of the slot committee faulty at the later write, for a run from
`K`'s committee start. -/
theorem optimisticLock_pair_compatible_at
    {K : AC.CommitteeDict sp.n} {g b : Time}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {x y : Fin sp.n} {i j s : Nat}
    (hx : x ∈ H (tr.time i)) (hy : y ∈ H (tr.time j))
    (hf : 2 * (K.committee s ∩ (H (max (tr.time i) (tr.time j)))ᶜ).ncard < sp.committeeSize)
    {D E : AC.Blk sp.n (List (FG.Att sp.n))} {CV CW : Set (Vote sp.n)}
    (hd : AC.OptimisticLockAt tr.projAC x i s D CV)
    (he : AC.OptimisticLockAt tr.projAC y j s E CW) (hK : CommitteeHalfUpTo tr H K g b) :
    Compatible (tr.HonestBlocksAt H) D E := by
  have hmono := hrun.time_mono
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have hi0 := hrun.time_nonneg i
  have hj0 := hrun.time_nonneg j
  have hrx := acRun_prefix hrun hnc hi0
  have hry := acRun_prefix hrun hnc hj0
  have hd' : AC.OptimisticLockAt (tr.projAC.upTo (tr.time i)) x i s D CV :=
    (AC.upTo_optimisticLockAt hmono).mpr ⟨le_rfl, hd⟩
  have he' : AC.OptimisticLockAt (tr.projAC.upTo (tr.time j)) y j s E CW :=
    (AC.upTo_optimisticLockAt hmono).mpr ⟨le_rfl, he⟩
  obtain ⟨-, hnD, ellD, A, hpD, -, hvD, hhD, hKD⟩ := AC.optimisticLockAt_spec hrx hx hd' K
    (fun σ v hv => (AC.CommitteePAt.upTo hmono hrun.antitone hK.facts.hP _).1 x hx _ σ v hv)
  obtain ⟨-, hnE, ellE, A', hpE, -, hvE, hhE, hKE⟩ := AC.optimisticLockAt_spec hry hy he' K
    (fun σ v hv => (AC.CommitteePAt.upTo hmono hrun.antitone hK.facts.hP _).1 y hy _ σ v hv)
  have hint := Set.ncard_inter_add_ncard_union (AC.voters CV) (AC.voters CW)
  have hu := Set.ncard_le_ncard (Set.union_subset hKD hKE)
  rw [hK.facts.hsize s] at hu
  obtain ⟨w, ⟨⟨v, hv, hvw⟩, v', hv', hv'w⟩, hw⟩ :=
    Set.exists_mem_notMem_of_ncard_lt_ncard
      (s := K.committee s ∩ (H (max (tr.time i) (tr.time j)))ᶜ)
      (t := AC.voters CV ∩ AC.voters CW) (by omega)
  have hw : w ∈ H (max (tr.time i) (tr.time j)) := by
    by_contra hn
    exact hw ⟨hKD ⟨v, hv, hvw⟩, hn⟩
  have hwi : w ∈ H (tr.time i) := hrun.antitone (le_max_left _ _) hw
  have hwj : w ∈ H (tr.time j) := hrun.antitone (le_max_right _ _) hw
  obtain ⟨a, hai, ev, hev, hevv⟩ := hhD v hv (hvw ▸ hwi)
  obtain ⟨c, hcj, ev', hev', hevv'⟩ := hhE v' hv' (hv'w ▸ hwj)
  obtain ⟨hat, hev⟩ := AC.upTo_voteAt.mp hev
  obtain ⟨hct, hev'⟩ := AC.upTo_voteAt.mp hev'
  have heqv : v = v' := by
    have hvval : v.val = v'.val := hvw.trans hv'w.symm
    have heq := Compose.Growing.one_vote_per_slot_at hrun hnc
      (Compose.Growing.hVoteAt_iff.mpr ⟨hrun.antitone hat (hvw ▸ hwi), hev⟩)
      (Compose.Growing.hVoteAt_iff.mpr
        ⟨hrun.antitone hct (hvval ▸ hv'w ▸ hwj), by simpa only [hvval] using hev'⟩)
      (by simp only [hevv, hevv', (hvD v hv).2.1, (hvE v' hv').2.1])
    exact hevv.symm.trans ((congrArg (fun e : AC.Em sp (List (FG.Att sp.n)) => e.msg)
      heq.2).trans hevv')
  obtain ⟨R, hR, hRr, hDR⟩ := (hvD v hv).2.2
  obtain ⟨R', hR', hR'r, hER'⟩ := (hvE v' hv').2.2
  have hDU := (AC.frameIn_of_callAt hrx.localRun hx hpD.1).2.trans
    (RunTrace.honestBlocks_upTo_subset hmono hi0)
  have hEU := (AC.frameIn_of_callAt hry.localRun hy hpE.1).2.trans
    (RunTrace.honestBlocks_upTo_subset hmono hj0)
  obtain rfl : R' = R := hU.1 (hEU hR') (hDU hR)
    (hR'r.trans ((congrArg AC.Vote.head heqv).symm.trans hRr.symm))
  exact AC.anc_total hU (hDR.mono hDU) (hER'.mono hEU)

end Consensus.Goldilocks.Healing.Growing.KernelProof

end

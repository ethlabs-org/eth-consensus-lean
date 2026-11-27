module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.ClientSteps

public section

/-! # Goldilocks Healing, HR.4: honest ancestry, stored fast locks and joined writes

Run facts read by the retention and growing-fault source arguments: honest ancestry in a node's
store (`store_anc_of_honest_anc`, `mem_of_honest_anc`, `σ_eq_honest`), a frame's tree in the
caller's store (`mem_tree_of_frame`), the stored block of a fast lock (`storedFastLock_mem`) and a
joined fast-lock write (`joinedAt_of_fastLockAt`). -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {tr : GoldilocksTrace sp} {K : AC.CommitteeDict sp.n}
  {ini : Fin sp.n → (goldilocksNode sp).State} {H : Set (Fin sp.n)}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}
  {proposer : Nat → Fin sp.n}

/-! ## Store facts at the honest nodes -/

/-- Ancestry inside the honest blocks below a block of an honest tree is ancestry in that tree
(honest trees are parent-closed down to genesis). -/
theorem store_anc_of_honest_anc {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {A C : AC.Blk sp.n (List (FG.Att sp.n))}
    (h : Anc (tr.HonestBlocks H) A C) (hC : C ∈ (tr.state y k).fg.tree) :
    (tr.state y k).fg.Anc A C :=
  store_anc_of_honest_anc_from hrun.toLocalRun hnc hy h hC

/-- A block below (inside the honest blocks) a block of an honest tree is in that tree. -/
theorem mem_of_honest_anc {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {A C : AC.Blk sp.n (List (FG.Att sp.n))}
    (h : Anc (tr.HonestBlocks H) A C) (hC : C ∈ (tr.state y k).fg.tree) :
    A ∈ (tr.state y k).fg.tree := by
  by_cases he : A = C
  · exact he ▸ hC
  · exact (Anc.mem (store_anc_of_honest_anc hrun hnc hy h hC) he).1

/-- One state per block across the honest stores of a run. -/
theorem σ_eq_honest {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {y z : Fin sp.n} (hy : y ∈ H) (hz : z ∈ H) {i j : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hBy : B ∈ (tr.state y i).fg.tree) (hBz : B ∈ (tr.state z j).fg.tree) :
    (tr.state y i).fg.σ B.root = (tr.state z j).fg.σ B.root :=
  Store.σ_eq_of_mem (Compose.fg_reachable hrun.toLocalRun hy i)
    (Compose.fg_reachable hrun.toLocalRun hz j)
    (Compose.honest_blocks_coherent hrun.toLocalRun hnc).1 (fun _ hX => ⟨y, hy, i, hX⟩)
    (fun _ hX => ⟨z, hz, j, hX⟩) hBy hBz

/-- The block of a frame of an honest call is in the node's FG tree. -/
theorem mem_tree_of_frame {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {ℓ : ACLabel (goldilocksNode sp)} (hc : tr.projAC.CallAt y k ℓ)
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ℓ.frame.tree) :
    B ∈ (tr.state y k).fg.tree := by
  rw [Compose.frame_of_projAC hrun hy hc] at hB
  exact hB.1

/-- The stored block of a fast-lock write is in the writer's FG tree, below its selection. -/
theorem storedFastLock_mem (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {x : Fin sp.n} (hx : x ∈ H) {i s : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (AC.Vote sp.n)} (h : Compose.StoredFastLockAt tr x i s B CV) :
    B ∈ (tr.state x i).fg.tree ∧ ∃ D, AC.FastLockAt tr.projAC x i s D CV ∧
      Anc (tr.HonestBlocks H) B D := by
  unfold Compose.StoredFastLockAt at h
  obtain ⟨ℓ, D, hc, hfl, rfl⟩ := h
  have hr := (Compose.goldilocks_ac_projection_from hrun hnc).localRun
  obtain ⟨hΦ, hΦU⟩ := AC.frameIn_of_callAt hr hx hc
  obtain ⟨hvt, hva⟩ := AC.viableAncestor_anc hΦ (fastLockAt_frame_mem hfl hc)
  exact ⟨mem_tree_of_frame hrun hx hc hvt, D, hfl, hva.mono hΦU⟩

/-- **A fast-lock write is joined** (run level): `JoinedAt` at the write's time. -/
theorem joinedAt_of_fastLockAt {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {x : Fin sp.n} (hx : x ∈ H) {i s : Nat} {D : AC.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (AC.Vote sp.n)} (h : AC.FastLockAt tr.projAC x i s D CV) :
    tr.JoinedAt x (tr.time i) := by
  have hr := (Compose.goldilocks_ac_projection_from hrun hnc).localRun
  obtain ⟨hj, ℓ, hc, hnr⟩ := joined_of_fastLockAt hr hx h
  have hnr' : ¬ tr.RestartAt x i := by
    rintro ⟨ℓk, hck, hkr⟩
    obtain rfl : ℓk = ℓ := Option.some.inj ((Compose.projAC_callAt.mpr hck).2.symm.trans hc.2)
    exact hnr hkr
  refine ((Compose.joined_projection_from hrun hx (tr.time i)).2.1 i
    ⟨_, Compose.projAC_callAt.mp hc⟩ hnr' rfl).mpr ?_
  rw [← Compose.projAC_state hrun.toLocalRun hx]
  exact hj

/-! ## The source of an honest attestation -/

end Consensus.Goldilocks.Healing

end

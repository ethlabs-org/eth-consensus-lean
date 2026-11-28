module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ResultAnc
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.PreAdvance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Geo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Carry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Writer
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLock
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalCore
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Confirmed
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ViewAgree
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.SupplierFrames
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.StoreCache
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The full frame's viable witness

`full_frame_viable_witness`: the full current frame has a viable head above its finalized tip,
witnessed by the hmax cache. It assumes no settled phase. -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp} {g ΔF b : Time}
  {ini : Fin sp.n → (goldilocksNode sp).State}

/-- The full current frame has a viable head above its finalized tip, witnessed by the hmax cache.
Unlike a frozen voter domain, the proposal domain cannot lose this witness. -/
theorem full_frame_viable_witness (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) :
    ∃ Q ∈ (Node.frame (tr.state y i)).tree,
      Q ∈ (Node.frame (tr.state y i)).viableHeads ∧
      (Node.frame (tr.state y i)).Anc (Node.frame (tr.state y i)).F Q := by
  have hr := Compose.fg_reachable hrun.toLocalRun hy i
  obtain ⟨_, _, _, _, _, ⟨Q, hQ, hQh⟩, _⟩ :=
    Goldilocks.Store.cache_invariants _ _ _ _ hr
  have hj := Store.hj_lt_hmax_of_reachable hr
  obtain ⟨hFQ, hQt, hv⟩ := viable_head_of_height hrun hnc hf hy hQ
    (by omega) (fun h => by omega)
  have hΦ := Store.frame_realization _ _ _ _ hr
  have hsub : (Node.frame (tr.state y i)).tree ⊆ tr.HonestBlocks H :=
    fun B hB => ⟨y, hy, i, hB.1⟩
  exact ⟨Q, hQt, hv, AC.anc_tree_of_anc_U
    (Compose.honest_blocks_coherent hrun.toLocalRun hnc) hΦ hsub hΦ.rooted.1
    (hFQ.mono (fun B hB => ⟨y, hy, i, hB⟩)) hQt⟩

end Consensus.Goldilocks.Healing

end

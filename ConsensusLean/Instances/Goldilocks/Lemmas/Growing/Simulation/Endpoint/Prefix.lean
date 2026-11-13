module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FGProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameBase

public section

/-! # Prefix runs of a node honest through a cut

Under growing faults a node honest at `d ≥ 0`, read before a cut whose predecessors are all at
times `≤ d`, is read on the prefix through `d`, which is a static run for the keys honest at `d`:

* `reachable_upTo`, `held_upTo`: its store is reachable and its tree is held while honest;
* `fgRun_upTo`, `projFG_store_upTo`: the FG projection of that prefix is a static FG run over the
  blocks held while honest in the whole run, and its store is the node's FG state. Readers on
  different prefixes so share one coherent universe. -/

namespace Consensus.Goldilocks.Simulation

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}
  {ini : Fin sp.n → (goldilocksNode sp ro).State}

/-- The store of a node honest at `d ≥ 0`, before a cut whose predecessors are at times `≤ d`, is
reachable. -/
theorem reachable_upTo (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {w : Fin sp.n} {m : Nat} {d : Time} (hd : 0 ≤ d) (hb : ∀ k < m, tr.time k ≤ d)
    (hw : w ∈ H d) : (tr.state w m).fg.Reachable (goldilocksNode sp ro).genesisPayload := by
  rw [← Trace.upTo_state tr w hb]
  exact Compose.fg_reachable (hrun.upTo hd).toLocalRun hw m

/-- The tree of a node honest at `d ≥ 0`, before a cut whose predecessors are at times `≤ d`, is
held while honest. -/
theorem held_upTo {w : Fin sp.n} {m : Nat} {d : Time} (hd : 0 ≤ d)
    (hb : ∀ k < m, tr.time k ≤ d) (hw : w ∈ H d) :
    (tr.state w m).fg.tree ⊆ tr.HonestBlocksAt H :=
  fun _ hX => ⟨w, m, d, hd, hb, hw, hX⟩

/-- The FG projection of the prefix through `d ≥ 0` is a static FG run for the keys honest at `d`,
over the blocks held while honest in the whole run. -/
theorem fgRun_upTo (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {d : Time} (hd : 0 ≤ d) :
    FGLocalRun (goldilocksNode sp ro).genesisPayload (H d) (tr.HonestBlocksAt H)
      (tr.upTo d).projFG := by
  have h := Compose.projFG_localRun (hrun.upTo hd) (hnc.upTo d)
  exact { h with
    coherent := Compose.Growing.honest_blocks_coherent hrun hnc
    tree_subset := fun y hy i => (h.tree_subset y hy i).trans
      (RunTrace.honestBlocks_upTo_subset hrun.time_mono hd) }

/-- The FG store on the prefix through `d ≥ 0` of a node honest at `d`, before a cut whose
predecessors are at times `≤ d`, is its state's FG part in the run. -/
theorem projFG_store_upTo (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {d : Time} (hd : 0 ≤ d) {y : Fin sp.n} (hy : y ∈ H d) {i : Nat}
    (hi : ∀ k < i, tr.time k ≤ d) : (tr.upTo d).projFG.store y i = (tr.state y i).fg := by
  change ((tr.upTo d).projFG.state y i).1 = _
  rw [Compose.projFG_state (hrun.upTo hd).toLocalRun hy i, Trace.upTo_state _ y hi]

end Consensus.Goldilocks.Simulation

end

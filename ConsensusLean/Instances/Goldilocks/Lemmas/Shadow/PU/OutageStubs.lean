module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Node
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare

public section

/-! # P-U shadow, V-B7: interface stubs of the static run facts of the outage chain

A static run lemma that the shell `outage_lock_inv_at'` reads and that another lane proves
(`Shadow/PU/Provenance` on `work/fg-pu-shadow-trace`): the stock lemma with its exact signature over
the shadow run law `GoldilocksRun'`, under the name that lane gives it, so that removing this file
is the whole swap. Interface only: a named `sorry`. -/

namespace Consensus.Goldilocks.Compose

open AC (ACParams ReplayOrder Payload Vote)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace' sp ro} {proposer : Nat → Fin sp.n}

/-- **Every stored lock sits below an origin of its slot** whose event precedes the cut, and names
a block of the node's tree (stock `lock_origin`). -/
theorem lock_origin' {ini} (hrun : GoldilocksRun' proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) :
    ∀ l ∈ (tr.state y i).ac.locks, ∃ L ∈ (tr.state y i).fg.tree, L.root = l.block ∧
      ∃ C, OriginBefore tr H C l.slot i ∧ Anc (tr.HonestBlocks H) L C := by
  sorry

end Consensus.Goldilocks.Compose

end

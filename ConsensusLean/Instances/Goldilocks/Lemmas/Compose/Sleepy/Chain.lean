module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run

public section

/-! # Goldilocks under `Sleepy`: the origin chain

Blocks on the ancestor closure of the origin chain (`OnOriginChain`) are pairwise compatible once
the origins are (S1): an ancestor of an origin is compatible with every ancestor of a compatible
origin, and genesis is below every honest block. Hence R.1's safety part
(workbench#11 §5): every honest `ac_confirmed` is an ancestor of the effective record (the record,
or `Σ.F` when the record is not in the frame), which is on the chain, so the honest confirmed
outputs are pairwise compatible, served or not. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro}

/-- **Blocks on the origin chain are compatible** when the origins are pairwise compatible. -/
theorem OnOriginChain.compatible (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hcomp : ∀ C s C' s', Origin tr H C s → Origin tr H C' s' →
      Compatible (tr.HonestBlocks H) C C')
    {B B' : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ tr.HonestBlocks H)
    (hB' : B' ∈ tr.HonestBlocks H) (h : OnOriginChain tr H B) (h' : OnOriginChain tr H B') :
    Compatible (tr.HonestBlocks H) B B' := by
  sorry

/-- **An ancestor of a block on the origin chain is on it.** -/
theorem OnOriginChain.of_anc (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    {A B : SA.Blk sp.n (List (FG.Att sp.n))} (hA : A ∈ tr.HonestBlocks H)
    (hAB : Anc (tr.HonestBlocks H) A B) (h : OnOriginChain tr H B) : OnOriginChain tr H A := by
  sorry

/-- **R.1 from the invariant**: the confirmed outputs of honest nodes at any two cuts are
compatible (inside the honest blocks). -/
theorem SleepyInvariant.confirmed_compatible (hinv : SleepyInvariant tr H)
    (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr) :
    ∀ y ∈ H, ∀ y' ∈ H, ∀ i i',
      Compatible (tr.HonestBlocks H) (tr.confirmedAt y i) (tr.confirmedAt y' i') := by
  sorry

end Consensus.Goldilocks.Compose

end

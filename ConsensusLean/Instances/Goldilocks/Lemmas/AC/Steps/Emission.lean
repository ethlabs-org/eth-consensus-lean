module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
public import ConsensusLean.Instances.Goldilocks.Statements.AC.Steps

public section

/-! # Goldilocks SA: an honest vote

Every emission of an honest node's call is the vote of `try_vote` (a restart's replay sends
nothing, A0.7): it is the node's own vote of the slot of the call's time, cast while joined, and
its head is the walk from the anchor over the viable tree of the voter block tree with the
merged view against the previous slot, all read at the emission's read point (the unlocking and
`voted_slot` change nothing the walk reads but the locks). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}

/-- **An honest vote.** -/
theorem castAt_spec (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) :
    e.msg.val = y ∧ e.msg.slot = sp.slot (tr.time i) ∧ joined sp e.readPoint (tr.time i) ∧
      e.msg.head = (getHead sp e.readPoint ℓ.frame (tr.time i)
        (ℓ.frame.viableTree (voterBlockTree sp e.readPoint ℓ.frame e.msg.slot))
        (mergedVoteView sp e.readPoint ℓ.frame e.msg.slot) ((e.msg.slot : Int) - 1)).root := by
  sorry

/-- The voter block tree of an honest vote is closed under ancestors in the frame (block stamps
grow along parent edges, A0.1, at the state the call leaves, whose stamps are the read
point's). -/
theorem voterBlockTree_anc (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) :
    ∀ B ∈ voterBlockTree sp e.readPoint ℓ.frame e.msg.slot, ∀ X, ℓ.frame.Anc X B →
      X ∈ voterBlockTree sp e.readPoint ℓ.frame e.msg.slot := by
  sorry

end Consensus.Goldilocks.SA

end

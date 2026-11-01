module
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.TopFrame
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockKeep

public section

/-! # Goldilocks: a contest keeps the locks below the high heads

The composed form of the benign-contest lemma (workbench `fg-liveness/r14-end-to-end`,
`s4b-contest-benign.md`, Lemma B): the FG store part (`Store.viableHead_of_contest`) and the AC
part (`SA.viableAncestor_of_anc_viableHead`) together. In a contest, a lock whose block is below an
accepted block above `Σ.F` at state height at least `h_max` stays in place. -/

namespace Consensus.Goldilocks.Store

variable {P : Params}

/-- **Benign contest, locks (r14 s4b, Lemma B).** In a contest with a well-formed frame, a block of
the frame that is an ancestor of an accepted block above `Σ.F` at state height at least `h_max` is
its own viable ancestor: `live_locks` keeps a lock on it in place. -/
theorem viableAncestor_of_contest {st : Store P (SA.Payload P.n)} (hΦ : FrameOK st.toFrame)
    (hc : st.Contest) {B Y : NodeBlock P (SA.Payload P.n)} (hB : B ∈ st.toFrame.tree)
    (hY : Y ∈ st.tree) (hFY : st.Anc st.F Y) (hh : st.hmax ≤ (st.σ Y.root).h)
    (hBY : st.toFrame.Anc B Y) : st.toFrame.viableAncestor B = B := by
  refine SA.viableAncestor_of_anc_viableHead hΦ hB ?_ ⟨hY, hFY⟩
    (st.viableHead_of_contest hc hY hFY hh) hBY
  change Goldilocks.Anc {X | X ∈ st.tree ∧ st.Anc st.F X} st.fcRoot B
  rw [st.fcRoot_of_contest hc]
  exact Anc.restrict Relation.ReflTransGen.refl hB.2

end Consensus.Goldilocks.Store

end

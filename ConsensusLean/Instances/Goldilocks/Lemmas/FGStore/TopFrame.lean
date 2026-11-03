module
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Store.View
public import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Tree

public section

/-! # Goldilocks FG store: the frame in a contest

The deterministic core of the benign-contest lemma (workbench `fg-liveness/r14-end-to-end`,
`s4b-contest-benign.md`, Lemma B): in a frontier contest the fork-choice root is `Σ.F`, the
head height floor is `h_max`, and every accepted block above `Σ.F` with state height at least
`h_max` is a viable head. So a contest started by an off-chain justification at `h_max − 1`
keeps as viable heads the blocks of a chain that already reached `h_max`. Without a contest
at `h_max = h_j + 1` the fork-choice root is `Σ.J`. -/

namespace Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type} (st : Store P ACP)

/-- At `h_max = h_j + 1` without a contest the fork-choice root is `Σ.J`. -/
theorem fcRoot_of_not_contest (hm : st.hmax = st.hj + 1) (h : ¬ st.Contest) :
    st.fcRoot = st.J := by
  simp [fcRoot, hm, h]

end Consensus.Goldilocks.Store

end

module
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Store.View

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

/-- In a contest the fork-choice root is `Σ.F`. -/
theorem fcRoot_of_contest (h : st.Contest) : st.fcRoot = st.F := by
  simp [fcRoot, h]

/-- At `h_max = h_j + 1` without a contest the fork-choice root is `Σ.J`. -/
theorem fcRoot_of_not_contest (hm : st.hmax = st.hj + 1) (h : ¬ st.Contest) :
    st.fcRoot = st.J := by
  simp [fcRoot, hm, h]

/-- In a contest the head height floor is `h_max`. -/
theorem headHeightFloor_of_contest (h : st.Contest) : st.headHeightFloor = st.hmax := by
  simp [headHeightFloor, h]

/-- Without a contest the head height floor is `h_max − 1`. -/
theorem headHeightFloor_of_not_contest (h : ¬ st.Contest) :
    st.headHeightFloor = st.hmax - 1 := by
  simp [headHeightFloor, h]

/-- An accepted block above `Σ.F` at state height `h_max` that does not extend `Σ.J` starts a
contest when `h_max = h_j + 1`. -/
theorem contest_of_offJ (hm : st.hmax = st.hj + 1) {B : NodeBlock P ACP} (hB : B ∈ st.tree)
    (hFB : st.Anc st.F B) (hh : (st.σ B.root).h = st.hmax) (hJ : ¬ st.Anc st.J B) :
    st.Contest :=
  ⟨hm, B, hB, hFB, hh, hJ⟩

/-- **Benign contest (r14 s4b, Lemma B, store part).** In a contest, every accepted block above
`Σ.F` with state height at least `h_max` is a viable head of the frame. -/
theorem viableHead_of_contest (h : st.Contest) {B : NodeBlock P ACP} (hB : B ∈ st.tree)
    (hFB : st.Anc st.F B) (hh : st.hmax ≤ (st.σ B.root).h) : B ∈ st.toFrame.viableHeads := by
  refine ⟨hB, hFB, ?_, ?_⟩
  · rw [st.fcRoot_of_contest h]
    exact hFB
  · change st.headHeightFloor ≤ (st.σ B.root).h
    rw [st.headHeightFloor_of_contest h]
    exact hh

end Consensus.Goldilocks.Store

end

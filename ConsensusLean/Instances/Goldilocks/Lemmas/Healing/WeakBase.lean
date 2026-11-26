module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Sleepy
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Reset
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run

public section

/-! # Goldilocks Healing: the cached `h_j` across a finality update

A store's finality update never lowers its cached `h_j` (`updateFinality_hj_le`). -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}

theorem updateFinality_hj_le {P : Params} {ACP : Type}
    (st : Store P ACP) (σ : FG.ChainState P.n) : st.hj ≤ (st.updateFinality σ).hj := by
  rcases (Store.updateFinality_spec st σ).2.2.2.2.1 with h | ⟨_, he, _, hlex⟩
  · exact le_of_eq h.2.symm
  · rw [he]
    rcases hlex with h | h
    · exact h.le
    · exact le_of_eq h.1

end Consensus.Goldilocks.Healing

end

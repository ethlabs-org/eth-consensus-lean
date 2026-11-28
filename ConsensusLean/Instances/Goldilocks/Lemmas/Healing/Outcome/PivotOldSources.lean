module
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.PivotRun
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Induction
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: old sources at proposals

Prerequisites for the post-reset proposal pivot. -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams Payload Vote)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {K : AC.CommitteeDict sp.n} {g ΔF a : Time}

/-! ### Old sources -/

end Consensus.Goldilocks.Healing

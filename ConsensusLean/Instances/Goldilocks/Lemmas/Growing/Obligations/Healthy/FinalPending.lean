module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Growing.Run
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.FinalWindowDefs

public section

/-! # Pending growing Healing interface of the final window

Statements the final-window route consumes whose home modules are not on this branch yet, under
their agreed names:

* `Healing.Growing.honestProposalRun_of_proposesAt_at` (`Healing.honestProposalRun_of_proposesAt`):
  an own proposal of the slot's proposer, honest through `t_s + hold`, is an honest proposal run;
* `Obligations.Growing.anchorStepAt_iff`, the characterising lemma of `AnchorStepAt`, home
  `Lemmas/Growing/Obligations/Healthy/FinalWindowDefs`.

Each theorem here is an open `sorry`; this module is deleted when the home modules land. -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)
open Regimes.Growing (hold)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- An own proposal of slot `s` by its proposer, honest through `t_s + hold`, is the honest
proposal run of `s`. -/
theorem honestProposalRun_of_proposesAt_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr)
    {p : Fin sp.n} {kP s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hp : p ∈ H (sp.ts s + hold sp)) (hpp : p = proposer s) (hP : tr.ProposesAt p kP P)
    (hPs : P.slot = s) : HonestProposalRun tr H proposer s P := by
  sorry

end Consensus.Goldilocks.Healing.Growing

namespace Consensus.Goldilocks.Obligations.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- The characterising lemma of `AnchorStepAt`. -/
theorem anchorStepAt_iff {A X : SA.Blk sp.n (List (FG.Att sp.n))} :
    AnchorStepAt tr H A X ↔
      ∃ z j j', z ∈ H (tr.time j) ∧ z ∈ H (tr.time j') ∧
        A ∈ (tr.state z j).fg.tree ∧ X ∈ (tr.state z j').fg.tree ∧
        ((tr.state z j).fg.σ A.root).h + 1 ≤ ((tr.state z j').fg.σ X.root).h := by
  sorry

end Consensus.Goldilocks.Obligations.Growing

end

module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Growing.Run
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.FinalWindowDefs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeBase

public section

/-! # Pending growing Healing interface of the final window

Statements the final-window route consumes whose home modules are not on this branch yet, under
their agreed names, each the growing form of the static Healing lemma of the same stem:

* `Healing.Growing.honestProposalRun_of_proposesAt_at` (`Healing.honestProposalRun_of_proposesAt`):
  an own proposal of the slot's proposer, honest through `t_s + hold`, is an honest proposal run;
* `Obligations.Growing.anchorStepAt_iff`, the characterising lemma of `AnchorStepAt`, home
  `Lemmas/Growing/Obligations/Healthy/FinalWindowDefs`;
* `Obligations.Growing.accept_of_proposesAt_at` and `Obligations.Growing.honestProposalRun_slot_at`,
  copies of the final-route node lemmas of the same names, home
  `Lemmas/Growing/Obligations/Concrete/Final`.

Each theorem here is an open `sorry` or a copy of the home proof; this module is deleted when the
home modules land. -/

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

/-- The block of an honest proposal run of slot `s` has slot `s`. -/
theorem honestProposalRun_slot_at {s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : Healing.Growing.HonestProposalRun tr H proposer s P) : P.slot = s := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hs, -⟩ := hP
  exact hs

/-- **A proposal of a node honest at its proposal cut is accepted there**, with the block in its
tree after the cut (the static `accept_of_proposesAt` on the prefix through the cut's time). -/
theorem accept_of_proposesAt_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {p : Fin sp.n} {k : Nat}
    {W : SA.Blk sp.n (List (FG.Att sp.n))} (hp : p ∈ H (tr.time k)) (hW : tr.ProposesAt p k W) :
    tr.AcceptAt p k W ∧ W ∈ (tr.state p (k + 1)).fg.tree ∧ tr.post k = tr.state p (k + 1) := by
  have hd := hrun.time_nonneg k
  have hb : ∀ m < k + 1, tr.time m ≤ tr.time k := fun _ hm => hrun.time_mono (by omega)
  have hW' : (tr.upTo (tr.time k)).ProposesAt p k W :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hW.1⟩, hW.2.1, hW.2.2⟩
  obtain ⟨ha, hmem, hpost⟩ := Healing.accept_of_proposesAt (hrun.upTo hd)
    (hnc.upTo (tr.time k)) hp hW'
  rw [Trace.upTo_state _ _ hb] at hmem hpost
  exact ⟨((RunTrace.upTo_acceptAt _).mp ha).2, hmem, hpost⟩

end Consensus.Goldilocks.Obligations.Growing

end

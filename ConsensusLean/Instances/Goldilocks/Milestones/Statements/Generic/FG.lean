module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Model
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.GenericRun
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.PersistKernel
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.BlockFinality

@[expose] public section

/-! # Population finality contracts over growing generic node runs

These propositions supply no proofs. The population is `Fin P.n`; neither `P.q` nor `2*q-n`
is an AC committee threshold. Each reader is honest at its own observation; safety charges
faults at the later observation and non-framing at the later signing.

O-FG-PERSIST: the imported persistence vocabulary has fixed-cohort premises. It is not aliased
as a new growing API: a growing VoteStep/SourceStep induction remains open.
O-FG-ACQUIRE: all-node report/source acquisition needs explicit generic service and report
vocabulary before it can be stated; no arbitrary predicate stands in for it.
O-FG-WINDOW and O-FG-CACHE: final-window extraction and cache coverage are FG-plus-healing
edges, not local AC fields. Generic window data and its healing/engine bridges remain open.
-/

namespace Consensus.Goldilocks.Generic

variable {P : Params} (A : NodeAC P) (sg : A.Msg → Fin P.n)

/-- Conflicting finalized reads expose population evidence, without a fault-bound premise. -/
def FinalAccountable : Prop :=
  ∀ (proposer : Nat → Fin P.n) (dg : Digest (List (FG.Att P.n)) A.Payload)
    (H : Time → Set (Fin P.n)) (tr : RunTrace A),
    A.Requirements → (P.genesisBlock A.genesisPayload).RootOk dg →
    Growing.LocalRun proposer dg H sg tr → Compose.NoCollRun dg tr →
    ∀ y z i j, y ∈ H (tr.time i) → z ∈ H (tr.time j) →
      ¬ Compatible (tr.HonestBlocksAt H) (tr.finalizedAt y i) (tr.finalizedAt z j) →
      ∃ X₁ ∈ (tr.state y i).fg.tree, ∃ X₂ ∈ (tr.state z j).fg.tree,
        ∃ S : Finset (Fin P.n), 2 * P.q - P.n ≤ S.card ∧
          ∀ v ∈ S, ∃ a ∈ BlockFinality.ChainAtts tr y i X₁ ∪
              BlockFinality.ChainAtts tr z j X₂,
            ∃ b ∈ BlockFinality.ChainAtts tr y i X₁ ∪ BlockFinality.ChainAtts tr z j X₂,
              a.val = v ∧ FG.slashable a b

/-- Honest signings cannot frame their signer; honesty is charged at the later signing. -/
def NonFraming : Prop :=
  ∀ (proposer : Nat → Fin P.n) (dg : Digest (List (FG.Att P.n)) A.Payload)
    (H : Time → Set (Fin P.n)) (tr : RunTrace A),
    Growing.LocalRun proposer dg H sg tr →
    ∀ v k k' a b, tr.SignAt v k a → tr.SignAt v k' b →
      v ∈ H (max (tr.time k) (tr.time k')) → ¬ FG.slashable a b

/-- Population faults below `2*q-n` at the later read imply compatible finalized tips. -/
def FinalizedSafe : Prop :=
  ∀ (proposer : Nat → Fin P.n) (dg : Digest (List (FG.Att P.n)) A.Payload)
    (H : Time → Set (Fin P.n)) (tr : RunTrace A),
    A.Requirements → (P.genesisBlock A.genesisPayload).RootOk dg →
    Growing.LocalRun proposer dg H sg tr → Compose.NoCollRun dg tr →
    ∀ y z i j, y ∈ H (tr.time i) → z ∈ H (tr.time j) →
      (H (max (tr.time i) (tr.time j)))ᶜ.ncard < 2 * P.q - P.n →
      Compatible (tr.HonestBlocksAt H) (tr.finalizedAt y i) (tr.finalizedAt z j)

/-- The finalized cache is monotone at ordered cuts of a node still honest at the later cut. -/
def FinalMonotone : Prop :=
  ∀ (proposer : Nat → Fin P.n) (dg : Digest (List (FG.Att P.n)) A.Payload)
    (H : Time → Set (Fin P.n)) (tr : RunTrace A),
    Growing.LocalRun proposer dg H sg tr →
    ∀ y i j, i ≤ j → y ∈ H (tr.time j) →
      (tr.state y j).fg.Anc (tr.finalizedAt y i) (tr.finalizedAt y j)

end Consensus.Goldilocks.Generic

end

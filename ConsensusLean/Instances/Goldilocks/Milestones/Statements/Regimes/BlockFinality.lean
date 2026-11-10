module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.GenericRun
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Common.Params

@[expose] public section

/-! # Finality accountability over an arbitrary node AC

The R.7 conclusions use the generic node observations. Accountability and safety
take exactly the FG projection premises; non-framing needs only local execution.
-/

namespace Consensus.Goldilocks.BlockFinality

/-- Attestations on the chain of `X` in the reader's held tree before cut `i`. -/
def ChainAtts {P : Params} {A : NodeAC P} (tr : RunTrace A)
    (y : Fin P.n) (i : Nat) (X : A.Blk) : Set (FG.Att P.n) :=
  {a | ∃ Y ∈ (tr.state y i).fg.tree, (tr.state y i).fg.Anc Y X ∧ a ∈ Y.fgPayload}

/-- Conflicting honest finalized tips expose at least `2q − n` slashable signers,
with both attestations bound to chains in the two readers' held trees. -/
def FinalAccountable : Prop :=
  ∀ (P : Params) (A : NodeAC P) (dg : Digest (List (FG.Att P.n)) A.Payload)
    (H : Set (Fin P.n)) (sg : A.Msg → Fin P.n) (tr : RunTrace A)
    (proposer : Nat → Fin P.n),
    A.Requirements → (P.genesisBlock A.genesisPayload).RootOk dg →
    Node.LocalRun proposer dg H sg tr → Compose.NoCollRun dg tr →
    ∀ y ∈ H, ∀ z ∈ H, ∀ i j,
      ¬ Compatible (tr.HonestBlocks H) (tr.finalizedAt y i) (tr.finalizedAt z j) →
      ∃ X₁ ∈ (tr.state y i).fg.tree, ∃ X₂ ∈ (tr.state z j).fg.tree,
        ∃ S : Finset (Fin P.n), 2 * P.q - P.n ≤ S.card ∧
          ∀ v ∈ S, ∃ a ∈ ChainAtts tr y i X₁ ∪ ChainAtts tr z j X₂,
            ∃ b ∈ ChainAtts tr y i X₁ ∪ ChainAtts tr z j X₂,
              a.val = v ∧ FG.slashable a b

/-- Local execution alone prevents an honest validator signing a slashable pair. -/
def NonFraming : Prop :=
  ∀ (P : Params) (A : NodeAC P) (dg : Digest (List (FG.Att P.n)) A.Payload)
    (H : Set (Fin P.n)) (sg : A.Msg → Fin P.n) (tr : RunTrace A)
    (proposer : Nat → Fin P.n),
    Node.LocalRun proposer dg H sg tr →
    ∀ v ∈ H, ∀ k k' a b, tr.SignAt v k a → tr.SignAt v k' b → ¬ FG.slashable a b

/-- With fewer than `2q − n` faulty validators, honest finalized tips are compatible. -/
def FinalizedSafe : Prop :=
  ∀ (P : Params) (A : NodeAC P) (dg : Digest (List (FG.Att P.n)) A.Payload)
    (H : Set (Fin P.n)) (sg : A.Msg → Fin P.n) (tr : RunTrace A)
    (proposer : Nat → Fin P.n),
    A.Requirements → (P.genesisBlock A.genesisPayload).RootOk dg →
    Node.LocalRun proposer dg H sg tr → Compose.NoCollRun dg tr →
    Hᶜ.ncard < 2 * P.q - P.n →
    ∀ y ∈ H, ∀ z ∈ H, ∀ i j,
      Compatible (tr.HonestBlocks H) (tr.finalizedAt y i) (tr.finalizedAt z j)

end Consensus.Goldilocks.BlockFinality

end

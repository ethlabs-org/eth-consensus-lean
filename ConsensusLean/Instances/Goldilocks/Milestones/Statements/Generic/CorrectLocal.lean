module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Premises
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.GenericRun

@[expose] public section

/-! # Local available-chain correctness obligations

These are conditional protocol obligations, not evidence and not the nine system claims.
Every field reads the AC's own output in a generic growing node run. No field mentions a
compiled system, ledger output or correctness assembly record.

* O-CORR-L2: engine-held/view provenance, feeding output validity; needs the engine morphism.
* O-CORR-L6: pending the healing skeleton dependency for its exact healed-tip interface.
* O-CORR-L9: L9 pending the U-REG edge ruling; no replacement outage regime is defined here.

Final-window extraction and final-cache coverage are classified as FG-plus-healing edges, not
local fields: their existing adapters combine window/reset premises, FG replay safety and
engine transport. Their generic window and engine vocabulary remains an open edge, not data
supplied by this record. Engine prefix-reader, no-collision transport and service conversion
likewise belong to separate concrete implication contracts, not local protocol fields.
-/

namespace Consensus.Goldilocks.Generic

variable {P : Params}

/-- A ready honest reader at a cut, with an explicit catch-up duration. -/
def ReadyCut {A : NodeAC P} (tr : RunTrace A) (H : Time → Set (Fin P.n))
    (c : Time) (y : Fin P.n) (i : Nat) : Prop :=
  y ∈ H (tr.time i) ∧
    ∀ t, max 0 (tr.time i - c - 1) ≤ t → t ≤ tr.time i → tr.awake y t

/-- A ready proposal whose signer stays honest through the explicit hold interval. -/
def ReadyProposal {A : NodeAC P} (tr : RunTrace A) (H : Time → Set (Fin P.n))
    (c hold : Time) (B : A.Blk) (i : Nat) : Prop :=
  tr.ProposesAt B.proposer i B ∧ ReadyCut tr H c B.proposer i ∧
    B.proposer ∈ H (tr.time i + hold)

/-- The local supplier for a generic AC. Constructing its type supplies no evidence.
The first row states membership and the finalized-to-confirmed-to-head ancestry at honest cuts.
The assembly record lives separately and cannot be used as a premise of this field. -/
structure ACCorrectLocal (A : NodeAC P) (sg : A.Msg → Fin P.n) where
  /-- Protocol-supplied durations, not fixed instance coefficients. -/
  look : Time
  catchUp : Time
  margin : Time
  latency : Time
  hold : Time
  /-- The transaction/input projection of a block, supplied as data. -/
  payload : A.Blk → Set Nat
  /-- Durations cannot make readiness or deadlines negative. -/
  durations : 0 ≤ look ∧ 0 ≤ catchUp ∧ 0 ≤ margin ∧ 0 ≤ latency ∧ 0 ≤ hold
  /-- L1: the confirmed tip is held, extends the finalized root and precedes the head. -/
  tipsValid : ∀ (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (H : Time → Set (Fin P.n))
    (tr : RunTrace A), Growing.LocalRun proposer dg H sg tr →
    ∀ y i, y ∈ H (tr.time i) →
      tr.confirmedAt y i ∈ (Node.frame (tr.state y i)).tree ∧
      (Node.frame (tr.state y i)).Anc (tr.finalizedAt y i) (tr.confirmedAt y i) ∧
      (Node.frame (tr.state y i)).Anc (tr.confirmedAt y i) (tr.headAt y i)
  /-- L3: ready confirmed reads under growing sleepy service are compatible. -/
  sleepyReadySafe : ∀ (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (H : Time → Set (Fin P.n))
    (tr : RunTrace A) (ΔF : Time), Growing.LocalRun proposer dg H sg tr →
    Compose.NoCollRun dg tr → tr.SleepyRunAt H ΔF look →
    ∀ y z i j, ReadyCut tr H catchUp y i → ReadyCut tr H catchUp z j →
      Compatible (tr.HonestBlocksAt H) (tr.confirmedAt y i) (tr.confirmedAt z j)
  /-- L4: a serviced ready proposal is confirmed at every ready read past its deadline. -/
  sleepyProposalSupply : ∀ (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (H : Time → Set (Fin P.n))
    (tr : RunTrace A) (ΔF : Time), Growing.LocalRun proposer dg H sg tr →
    Compose.NoCollRun dg tr → tr.SleepyRunAt H ΔF look →
    ∀ B k y j, ReadyProposal tr H catchUp hold B k →
      tr.time k + margin ≤ tr.time j → ReadyCut tr H catchUp y j →
      Anc (tr.HonestBlocksAt H) B (tr.confirmedAt y j)
  /-- L5: the same serviced proposal's projected payload is covered by that output. -/
  sleepyInclusionCoverage : ∀ (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (H : Time → Set (Fin P.n))
    (tr : RunTrace A) (ΔF : Time), Growing.LocalRun proposer dg H sg tr →
    Compose.NoCollRun dg tr → tr.SleepyRunAt H ΔF look →
    ∀ B k y j, ReadyProposal tr H catchUp hold B k →
      tr.time k + margin ≤ tr.time j → ReadyCut tr H catchUp y j →
      payload B ⊆ payload (tr.confirmedAt y j)
  /-- L7: under healthy service, a fresh ready proposal is confirmed within the latency. -/
  healthyConfirmedSupply : ∀ (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (H : Time → Set (Fin P.n))
    (tr : RunTrace A) (ΔF g healed : Time), Growing.LocalRun proposer dg H sg tr →
    Compose.NoCollRun dg tr → tr.HealthyRunAt H ΔF g → max g 0 + margin ≤ healed →
    ∀ B k y j, ReadyProposal tr H catchUp hold B k → healed ≤ tr.time k →
      tr.time k + latency ≤ tr.time j → ReadyCut tr H catchUp y j →
      Anc (tr.HonestBlocksAt H) B (tr.confirmedAt y j)
  /-- L8: ancestry of a proposal into either output preserves its projected payload. -/
  payloadProjection : ∀ (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (H : Time → Set (Fin P.n))
    (tr : RunTrace A), Growing.LocalRun proposer dg H sg tr →
    ∀ B y j, y ∈ H (tr.time j) →
      (Anc (tr.HonestBlocksAt H) B (tr.confirmedAt y j) →
        payload B ⊆ payload (tr.confirmedAt y j)) ∧
      (Anc (tr.HonestBlocksAt H) B (tr.finalizedAt y j) →
        payload B ⊆ payload (tr.finalizedAt y j))

end Consensus.Goldilocks.Generic

end

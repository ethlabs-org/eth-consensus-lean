module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Premises
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.GenericRun
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.Obligations
public import ConsensusLean.Spec.Problem.Regimes

@[expose] public section

/-! # Local available-chain correctness obligations

These are conditional protocol obligations, not evidence and not the nine system claims.
Every field reads the AC's own output in a generic growing node run. No field mentions a
compiled system, ledger output or correctness assembly record.

* O-CORR-L2: engine-held/view provenance, feeding output validity; needs the engine morphism.
* O-ENG: the supplied payload projection needs its engine/input binding.

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

/-- Concrete environment/run schedule binding on the node's validator indices.
This asserts no engine simulation or payload correspondence. -/
def RunPointBinding {A : NodeAC P} (tr : RunTrace A) (H : Time → Set (Fin P.n))
    (p : EnvPoint (Fin P.n)) : Prop :=
  p.env.ΔAC = P.Δ ∧
    (∀ y t, y ∈ H t ↔ p.HonestAt y t) ∧
    (∀ y t, tr.awake y t ↔ p.env.awake y t = true) ∧
    (∀ t, tr.InHorizon t ↔ t ≤ p.horizon)

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
  /-- Fixed local outage recovery duration, not chosen separately for each reader. -/
  recovery : Time
  /-- Fixed outage participation threshold and durations, matched to the contract separately. -/
  θ : ℚ
  outageEta : Time
  outageLag : Time
  outageBudget : Time
  committeeLook : Time
  /-- The local outage policy cannot start recovery before the outage ends. -/
  recovery_nonneg : 0 ≤ recovery
  /-- One run/start owner for the local and healing obligations. -/
  run : ACRun A sg
  /-- AC-owned message service, allowing fresh delivery or retained protocol evidence. -/
  served : RunTrace A → Fin P.n → Nat → Time → A.Msg → Prop
  served_of_delivered : ∀ {cm proposer dg H tr} {y j τ m}, run.Run cm proposer dg H tr →
    tr.MsgDeliveredBy y j τ τ m → served tr y j τ m
  /-- Healing is a separate protocol obligation, not implied by this record's endpoint claims. -/
  healing : ACHealing A sg run
  /-- The transaction/input projection of a block, supplied as data. -/
  payload : A.Blk → Set Nat
  /-- Durations cannot make readiness or deadlines negative. -/
  durations : 0 ≤ look ∧ 0 ≤ catchUp ∧ 0 ≤ margin ∧ 0 ≤ latency ∧ 0 ≤ hold
  /-- L1: the confirmed tip is held, extends the finalized root and precedes the head. -/
  tipsValid : ∀ (cm : Time → Finset (Fin P.n)) (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (H : Time → Set (Fin P.n))
    (tr : RunTrace A), run.Run cm proposer dg H tr →
    ∀ y i, y ∈ H (tr.time i) →
      tr.confirmedAt y i ∈ (Node.frame (tr.state y i)).tree ∧
      (Node.frame (tr.state y i)).Anc (tr.finalizedAt y i) (tr.confirmedAt y i) ∧
      (Node.frame (tr.state y i)).Anc (tr.confirmedAt y i) (tr.headAt y i)
  /-- L8: ancestry of a proposal into either output preserves its projected payload. -/
  payloadProjection : ∀ (cm : Time → Finset (Fin P.n)) (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (H : Time → Set (Fin P.n))
    (tr : RunTrace A), run.Run cm proposer dg H tr →
    ∀ B y j, y ∈ H (tr.time j) →
      (Anc (tr.HonestBlocksAt H) B (tr.confirmedAt y j) →
        payload B ⊆ payload (tr.confirmedAt y j)) ∧
      (Anc (tr.HonestBlocksAt H) B (tr.finalizedAt y j) →
        payload B ⊆ payload (tr.finalizedAt y j))

/-- A run interface transported along signer equality has the same runs. -/
theorem ACRun.cast_run {A : NodeAC P} {sg sg' : A.Msg → Fin P.n} (h : sg = sg') (R : ACRun A sg) :
    (h ▸ R).Run = R.Run := by
  subst sg'
  rfl

/-- Pre-outage service under growing honesty, cut off at the recipient's deadline.
Message service is AC-owned; node acceptance relay retains its processing bounds.
Certificate: part of the open OC-K obligation. -/
structure ACServiceBefore {A : NodeAC P} {sg : A.Msg → Fin P.n}
    (C : ACCorrectLocal A sg) (tr : RunTrace A) (H : Time → Set (Fin P.n))
    (ΔF b : Time) : Prop where
  deltaF : 0 < ΔF
  message : ∀ x i m, x ∈ H (tr.time i) → tr.SendOrAdmitAt x i m → 0 ≤ tr.time i →
    ∀ y j ℓ, y ∈ H (tr.time j) → tr.CallAt y j (.ac ℓ) →
      tr.deadline y j (tr.time i) P.Δ ≤ b →
      tr.deadline y j (tr.time i) P.Δ ≤ tr.time j → C.served tr y j (tr.time i) m
  relay : ∀ x i B, x ∈ H (tr.time i) → tr.AcceptAt x i B → 0 ≤ tr.time i →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j → tr.deadline y j (tr.time i) P.Δ ≤ b →
      tr.deadline y j (tr.time i) P.Δ ≤ tr.time j →
      Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B → tr.BlockAcceptedBy y j (tr.time i) B

end Consensus.Goldilocks.Generic

end

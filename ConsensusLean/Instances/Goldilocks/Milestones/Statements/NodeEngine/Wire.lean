module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.NodeEngine.Stages
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.Interface
public import ConsensusLean.Spec.Model.Conditions

@[expose] public section

namespace Consensus.Goldilocks.NodeEngine
open Blocks Shape
open Consensus.Model (Public)

/-- Newly emitted restart messages only. It says nothing about an engine queue. -/
def RestartSilent {P : Params} (A : NodeAC P) : Prop :=
  ∀ self s Φ t, 0 ≤ t → (A.step self s Φ t .restart).2 = []

variable {pub : Public} {hn : 1 ≤ pub.n} {S M Q Info Body : Type}
  [DecidableEq Info] [Countable Info] {R : Runtime pub hn S M Q}

/-- Algebraic wire facts only: no queue, schedule, AC requirements or publication premise. -/
structure WireLaws (W : Wire R Info Body) : Prop where
  msg_roundTrip : ∀ m, W.decodeMsg (W.encodeMsg m) = some m
  msg_injective : Function.Injective W.encodeMsg
  info_roundTrip : ∀ atts p, W.decodeInfo (W.encodeInfo atts p) = some (atts, p)
  info_injective : ∀ as₁ as₂ p₁ p₂,
    W.encodeInfo as₁ p₁ = W.encodeInfo as₂ p₂ → as₁ = as₂ ∧ p₁ = p₂
  msg_canonical : ∀ hs m, R.operations.validMsg m →
    W.canonEvent hs (msgObj W m) = some (.message m)
  msg_authentic : ∀ hs o m, W.canonEvent hs o = some (.message m) → o = msgObj W m
  block_authentic : ∀ hs o B, W.canonEvent hs o = some (.block B) →
    o = blockObj W B ∧ (∀ a ∈ B.fgPayload, a.WellFormed) ∧ R.operations.validPayload B
  att_authentic : ∀ hs o a, W.canonEvent hs o = some (.attestation a) →
    o = .mk (.signed a.val .poll) (.data (W.encodeAtt a)) [] ∧ a.WellFormed
  payload_complete : ∀ atts p,
    W.payloadObjs atts p =
      atts.map (fun a => .mk (.signed a.val .poll) (.data (W.encodeAtt a)) []) ++
      (W.payloadMsgs p).map (msgObj W)
  drain_order : ∀ bs, (W.drain bs).1 ++ (W.drain bs).2 = bs
  att_injective : Function.Injective W.encodeAtt
  header_payload : ∀ B, W.decodeInfo (W.headerOf B).info = some (B.fgPayload, B.acPayload)
  block_root : ∀ hs o B, W.canonEvent hs o = some (.block B) →
    ∃ d, W.rootOf hs (W.headerOf B) = some d ∧
      W.blockOf d (W.headerOf B) B.proposer B.fgPayload B.acPayload = B
  nonatt_conflicts : ∀ o o', ¬ W.isFGAtt o → W.conflicts o o' = false ∧ W.conflicts o' o = false

/-- Own-key signing is an operation-level fact on the actual call domain, not a codec retract. -/
def EmissionSigner (W : Wire R Info Body)
    (At : Fin pub.n → S → R.operations.toAC.Frm → Time → R.operations.toAC.Call → Prop) : Prop :=
  ∀ self s Φ t c, At self s Φ t c →
    ∀ e ∈ (R.operations.toAC.step self s Φ t c).2, W.signer e.msg = self

/-- Full AC requirements belong at the projection endpoint that uses them. -/
def ProjectionRequirements {P : Params} (A : NodeAC P) : Prop := A.Requirements

/-- Stored-clock tips on an explicitly provided reachable node/frame domain.
The consumer supplies frame well-formedness, not collision freedom or a regime. -/
def StoredClockTips {P : Params} (A : NodeAC P) (Reach : NodeState A → Time → Prop) : Prop :=
  ∀ st t, Reach st t → FrameOK (Node.frame st) →
    A.confirmed st.ac (Node.frame st) t ∈ (Node.frame st).tree ∧
    (Node.frame st).Anc (A.confirmed st.ac (Node.frame st) t) (A.head st.ac (Node.frame st) t)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
  {I B : Type} {O : OutputSchema} [DecidableEq I] [Countable I]
  (A : Family I B) (fin : O.Id → Bool)
  (rho : Model.Run (compiled (shapeFamily A fin)) E)

/-- Run obligations inspect actual selected candidate prefixes, not arbitrary states.
Restart silence is separate. Queue coverage requires draining at sending-event boundaries,
not at arbitrary states or restarts; this remains a supplier obligation. -/
structure WireRunLaws (rho : Model.Run (compiled (shapeFamily A fin)) E) : Prop where
  policy : ∀ pub hn, skeleton (A.wire pub hn) = A.skeleton pub
  dependencies : ∀ pub hn, (A.wire pub hn).dependencies = A.dependencies pub.n
  conflicts : ∀ pub hn, (A.wire pub hn).conflicts = A.conflicts pub.n
  isFGAtt : ∀ pub hn, (A.wire pub hn).isFGAtt = A.isFGAtt pub.n
  selected : ∀ (i : Nat) (v : V) (t : Time), rho.events[i]? = some (Model.Event.tick v t) ∨
    (∃ o, rho.events[i]? = some (Model.Event.deliver v o t)) →
    rho.ownKey v ∈ rho.sel .poll
  candidate_ready : ∀ i v ev, rho.ExecutionValid → rho.events[i]? = some ev → ev.node = v →
    ∀ j d, (eventDuties A fin rho i)[j]? = some d →
    ∀ k c,
      let P := Model.protoOf (compiled (shapeFamily A fin)) E
      let nd := stageNode A fin rho i v (.duty j)
      (rho.signedCandidate v d (P.act nd.st d).2)[k]? = some c →
      ¬ P.isFGAtt c →
      let pre := stageNode A fin rho i v (.candidate j k)
      Model.releasable pre.seen c = true ∧
      Model.protects P (rho.ownKey v) pre.seen c = true ∧
      P.dependencies.ready (Model.closure pre.seen) c = true
  att_ready : ∀ i v ev, rho.ExecutionValid → rho.events[i]? = some ev → ev.node = v →
    ∀ j d, (eventDuties A fin rho i)[j]? = some d → ∀ k c,
      let P := Model.protoOf (compiled (shapeFamily A fin)) E
      let nd := stageNode A fin rho i v (.duty j)
      (rho.signedCandidate v d (P.act nd.st d).2)[k]? = some c → P.isFGAtt c →
      let pre := stageNode A fin rho i v (.candidate j k)
      Model.releasable pre.seen c = true ∧
      P.dependencies.ready (Model.closure pre.seen) c = true
  queue_coverage : ∀ i v t, rho.ExecutionValid → rho.SendsAt v i t →
    ∀ hn j b, j ≤ (eventDuties A fin rho i).length →
    b ∈ (((stageNode A fin rho i v (.duty j)).st.1 hn).outbox) →
    ∃ k d cs, j ≤ k ∧ (eventDuties A fin rho i)[k]? = some d ∧
      let P := Model.protoOf (compiled (shapeFamily A fin)) E
      let nd := stageNode A fin rho i v (.duty k)
      Model.Obj.mk (.signed (rho.ownKey v) .poll) (.data b) cs ∈
        rho.signedCandidate v d (P.act nd.st d).2

/-- Per-cut admission is not a consequence of a codec retract or a handler-wide pool test.
This supplier is applied only to the actual AC cuts of a reachable handler expansion. -/
structure AdmissionLaws {P : Params} (A : NodeAC P) (payloadMsgs : A.Payload → List A.Msg)
    (At : Fin P.n → A.State → A.Frm → Time → A.Call → Prop) : Prop where
  emitted_valid : ∀ self s Φ t c, At self s Φ t c →
    ∀ e ∈ (A.step self s Φ t c).2, A.validMsg e.msg
  holds_mono : ∀ self s Φ t c m, At self s Φ t c → c ≠ .restart → A.holdsMsg s m →
    A.holdsMsg (A.step self s Φ t c).1 m
  complete : ∀ self s Φ t c m, At self s Φ t c → c ≠ .restart →
    ¬ A.holdsMsg s m → A.holdsMsg (A.step self s Φ t c).1 m →
    m ∈ (match c with | .message x => [x] | .block B => payloadMsgs B.acPayload | _ => []) ++
      ((A.step self s Φ t c).2.map (·.msg))

end Consensus.Goldilocks.NodeEngine

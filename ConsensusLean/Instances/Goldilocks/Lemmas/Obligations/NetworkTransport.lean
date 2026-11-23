module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Forwarding
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.PublicationQueue
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.PublicationProvenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.SentForward
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Run
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Sleepy
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.DeadlineWake
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OwnReleaseProcessing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Defs
public import ConsensusLean.Lemmas.Model.SysLog
import ConsensusLean.Lemmas.Model.Constant

public section

/-! # Network transport for the concrete publisher/simulation adapter

The full transports of the engine network to the node service premises are not stated here and
are not premises of `MeetsObligations`.
The trace parameters remain independent here. `Setup.params` gives protocol delay Δp = Δe: the
engine holds an object strictly before `a + Δe` (by `a + Δe − 1`), which is the node's strict
deadline `a + Δp`. FG attestation service has its own delay `Δ_F`: the engine serves
standalone attestations (`isFGAtt`) strictly before its FG delay `ΔF` (the `fgAtts` clause of
`PSync`), at the protocol FG delay `Δ_F,p = protoFGDelay (pubOf E) = ΔF`.
Every other object (blocks, votes, forwarding and vote-forwarding wrappers) is served strictly
before the bound `Δ`; no statement here claims a block before `ΔF`.
A full transport would include message, block, acceptance-relay and attestation service. Receipt
alone proves none of the acceptance-relay fields. The finite services up to a synchronous horizon
are proved under growing faults (`Growing/Obligations/Network`); full GST remains separate.
-/

namespace Consensus.Goldilocks.RunTrace

variable {P : Params} {A : NodeAC P} (tr : RunTrace A)

/-- The delivery deadline is monotone in its delivery parameter. -/
theorem deadline_mono_delta (y : Fin P.n) (k : Nat) (τ : Time) {Δ₁ Δ₂ : Time}
    (h : Δ₁ ≤ Δ₂) : tr.deadline y k τ Δ₁ ≤ tr.deadline y k τ Δ₂ := by
  unfold deadline
  exact add_le_add le_rfl h

end Consensus.Goldilocks.RunTrace

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation

open Shape Blocks

/-- The protocol FG delay of the public parameters: `ΔF_p = ΔFG`, the engine FG delay, as the
protocol delay `Δ_p = ΔAC` (`Setup.params`): L0 delivers strictly before the bound
(`CommLog.PSync`), which is the node's deadline `[τ, max(τ, w) + Δ_F)`. -/
def protoFGDelay (pub : Model.Public) : Time := pub.ΔFG

theorem protoFGDelay_eq (pub : Model.Public) : protoFGDelay pub = pub.ΔFG := by rfl

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)

/-- The engine log's message class is the Goldilocks attestation class (`isFGAtt`). -/
theorem log_fgAtt_iff {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
    (rho : Model.Run (compiled (goldilocks S)) E) (o : Wire (Fintype.card V) S.vote) :
    rho.log.fgAtt o ↔ isFGAtt o := Iff.rfl

/-- A standalone attestation is an attestation. -/
theorem isFGAtt_attObj {binding : VoteBinding} {n : Nat} (a : FG.Att n) :
    isFGAtt (attObj (binding := binding) a) := by
  simp [isFGAtt, IsAttObj, attObj]

/-- A forwarding wrapper is not an attestation. -/
theorem not_isFGAtt_forwardObj {binding : VoteBinding} {sp : AC.ACParams} (origin : Fin sp.n)
    (t : Time) (parent : Option (Wire sp.n binding)) (B : Blk sp) :
    ¬ isFGAtt (forwardObj sp origin t parent B) := by
  simp [forwardObj, isFGAtt, IsAttObj]

/-- An object that decodes as a forwarding wrapper is not an attestation. -/
theorem not_isFGAtt_of_decodeForward {binding : VoteBinding} {sp : AC.ACParams}
    {hs : List (Header Info × Nat)} {o : Wire sp.n binding}
    {q : Fin sp.n × Time × Option (Wire sp.n binding) × Blk sp}
    (h : decodeForward sp hs o = some q) : ¬ isFGAtt o := by
  obtain ⟨origin, t, parent, B⟩ := q
  rw [forwardObj_of_decodeForward hs o origin t parent B h]
  exact not_isFGAtt_forwardObj origin t parent B

/-- Every well-formed attestation an actual receipt delivers (`delivered`: not the payload of a
refused block) gets a real processing call at receipt time, including duplicate attestations
already present in the pool. -/
theorem received_att_processAt
    (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    {i : Nat} {v : V} {receipt : Wire (Fintype.card V) S.vote} {t : Time}
    (he : rho.events[i]? = some (.deliver v receipt t)) {a : FG.Att (Fintype.card V)}
    (hwf : a.WellFormed)
    (hc : attObj a ∈ delivered (stateAt S rho hn v i).voteIO (Model.digests rho.hash receipt)
      (stateAt S rho hn v i) receipt) :
    ∃ k < cutMap S rho hn (i + 1),
      (simTrace S rho hn).ProcessAttAt (rho.ownKey v) k a ∧
      (simTrace S rho hn).time k = t := by
  obtain ⟨k, _, hk, hp, ht⟩ :=
    NodeAsChainShape.CanonicalTrace.received_att_processAt (traceEncoding S hn) rho he
      (by
        apply traceEncoding_induction S hn (fun e _ _ =>
          ∃ w ∈ NodeAsChainShape.delivered (NodeAsChainShape.CanonicalTrace.receiverCodec e rho v)
              e.adapter (Model.digests rho.hash receipt)
              (NodeAsChainShape.CanonicalTrace.stateAt e rho v i)
              (NodeAsChainShape.CanonicalTrace.wireOf e receipt),
            NodeAsChainShape.canonEvent (NodeAsChainShape.CanonicalTrace.receiverCodec e rho v)
              (Model.digests rho.hash receipt) w = some (.attestation a))
        intro _ _
        rw [NodeAsChainShape.CanonicalTrace.receiverCodec_eq,
          NodeAsChainShape.CanonicalTrace.voteIOAt_eq]
        refine ⟨attObj (binding := S.vote) a, ?_,
          canonEvent_attObj (sp := S.params (Model.pubOf E) hn) (ro := S.ro _) _ _ a hwf⟩
        rw [NodeAsChainShape.CanonicalTrace.stateAt_eq]
        rw (config := { transparency := .default }) [NodeAsChainShape.CanonicalTrace.wireOf_eq]
        rw [stateAt_voteIO S rho hn, stateAt_eq] at hc
        exact hc)
  simpa only [(simTrace_encoding S rho hn).1, (simTrace_encoding S rho hn).2] using ⟨k, hk, hp, ht⟩

end Consensus.Goldilocks.Obligations

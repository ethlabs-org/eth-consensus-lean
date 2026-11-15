module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Interface
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.FGSafety
import ConsensusLean.Lemmas.Model.Objects
import ConsensusLean.Lemmas.Model.Protection
import ConsensusLean.Lemmas.Model.Constant
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Client
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Shape
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.AttGuard

public section

/-! # Engine signings: client safety and the own-object guard

Consequences of the engine signing history (`Provenance`): the actual engine input of a selected
proposal duty (`EngineProposalAt`), the signing record across a restart
(`engine_restart_record`), pairwise non-slashable engine signings by the paper's G0.5
(`engine_signings_nonFraming`), and the own-object guard admitting a freshly generated attestation
(`engine_att_protected`, `engine_poll_att_protected`). The guard has NO PAPER PROOF: it is G0.5
plus implementation provenance. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- A selected proposal duty actually scheduled at a tick, with its actual input node.
The index and duty-list lookup supply the slot/time relation through the schedule; no bare
time equality replaces the execution witness. `rho.dutyStep` must gate both `act` and its
state effects by this selection, as in the engine repair. The clock uses the actual
engine time; slot equalities follow from absolute slot lengths/phase offsets, not network Δ. -/
def EngineProposalAt (v : V) (i p : Nat) (t : Time) (s : Slot)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) : Prop :=
  rho.events[i]? = some (.tick v t) ∧ E.awake v t = true ∧
    ∃ hs : 0 < s,
      ((Model.protoOf (compiled (goldilocks S)) E).duties t)[p]? = some (.propose s hs) ∧
      rho.ownKey v ∈ rho.sel (.proposer s) ∧
      nd = (rho.runDuties v
        ⟨(Model.protoOf (compiled (goldilocks S)) E).clock (rho.stateBefore i v).st t
          (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩
        (((Model.protoOf (compiled (goldilocks S)) E).duties t).take p)).1

/-- Characterization of a selected proposal's actual engine input. -/
theorem engineProposalAt_iff (v : V) (i p : Nat) (t : Time) (s : Slot)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) :
    EngineProposalAt S rho v i p t s nd ↔
      rho.events[i]? = some (.tick v t) ∧ E.awake v t = true ∧
        ∃ hs : 0 < s,
          ((Model.protoOf (compiled (goldilocks S)) E).duties t)[p]? = some (.propose s hs) ∧
          rho.ownKey v ∈ rho.sel (.proposer s) ∧
          nd = (rho.runDuties v
            ⟨(Model.protoOf (compiled (goldilocks S)) E).clock (rho.stateBefore i v).st t
              (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩
            (((Model.protoOf (compiled (goldilocks S)) E).duties t).take p)).1 := by rfl

/-- Restart retains the signing record, including at a wake boundary after a sleeping
interval. This follows directly from the engine's durable/restore operations and the node's
restart, independently of execution validity. -/
theorem engine_restart_record (_hv : rho.ExecutionValid) {v : V} {i : Nat} {t : Time}
    (he : rho.events[i]? = some (.restart v t)) :
    (stateAt S rho hn v (i + 1)).node.record = (stateAt S rho hn v i).node.record := by
  simp only [stateAt_eq, rho.stateBefore_succ he, Model.Run.step, Function.update_self]
  rfl

/-- **Paper G0.5 (`FG.client_safety`) after the implementation history lemma.** Put both
signings in the history before an event after both signings, then apply client safety to its
`EntryInputs`. No node-simulation or network-timing premise is needed. -/
theorem engine_signings_nonFraming (hv : rho.ExecutionValid) {v : V}
    (hv' : v ∉ rho.faultyAt 0) {i p j q : Nat} {a b : FG.Att (Fintype.card V)}
    (ha : EngineSignsAt S rho hn v i p a) (hb : EngineSignsAt S rho hn v j q b) :
    ¬ FG.slashable a b := by
  obtain ⟨inputs, hi, _, hs⟩ := engine_event_signing_history S rho hn hv hv' (max i j + 1)
  exact FG.client_safety _ _ inputs hi a (hs i p a (by omega) ha)
    b (hs j q b (by omega) hb)

/-- **G0.5 plus implementation provenance; NO independent PAPER PROOF of the engine guard.**
A freshly generated attestation passes the candidate/seen protection boundary: self-conflict
is impossible by client safety; any conflicting own-signed object in `seen` is another actual
signing by `engine_seen_att_signed`. Include both conflict orientations. Earlier releases in
the same event are included in this actual duty-prefix `seen`. -/
theorem engine_att_protected (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    {v : V} (hv' : v ∉ rho.faultyAt 0)
    {i p : Nat} {nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)}
    (hc : EngineDutyCut S rho v i p nd) {j q : Nat} {a : FG.Att (Fintype.card V)}
    (ha : EngineSignsAt S rho hn v j q a) :
    Model.protects (Model.protoOf (compiled (goldilocks S)) E) (rho.ownKey v) nd.seen
      (attObj a) = true :=
  att_protected_of_signings S rho hn (engine_signings_nonFraming S rho hn hv hv')
    (fun hval ho => by
      obtain ⟨j', q', _, hs⟩ := engine_seen_att_signed S rho hn hf hv hv' hv' hc hval ho
      exact ⟨j', q', hs⟩) ha

/-- The own-object guard admits the ordinary attestation produced by an actual poll. -/
theorem engine_poll_att_protected (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid) {v : V}
    (hv' : v ∉ rho.faultyAt 0) {i p : Nat} {nd} {k : Nat}
    (hc : EngineDutyCut S rho v i p nd)
    (hd : (∃ t, rho.events[i]? = some (.tick v t) ∧ E.awake v t = true ∧
        ((Model.protoOf (compiled (goldilocks S)) E).duties t)[p]? = some (.poll k)) ∨
      ∃ t o, rho.events[i]? = some (.deliver v o t) ∧
        ((Model.protoOf (compiled (goldilocks S)) E).deliverDuties t)[p]? = some (.poll k))
    (hsel : rho.ownKey v ∈ rho.sel .poll) {w cs}
    (hm : (poll (nd.st.1 hn) k).2 = some (.att w, cs)) :
    Model.protects (Model.protoOf (compiled (goldilocks S)) E) (rho.ownKey v) nd.seen
      (.mk (.signed (rho.ownKey v) .poll) (.data (.att w)) []) = true :=
  poll_att_protected_of S rho hn hc (engine_att_protected S rho hn hf hv hv' hc) hd hsel hm

end Consensus.Goldilocks.Simulation

end

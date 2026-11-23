module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Groups
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Relay

public section

/-! # Wire checks for the growing canonical trace

Wire decoding is independent of signer honesty; the latter is needed separately for
unforgeability. We recover the canonical event at each group and preserve that separation.
-/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

set_option linter.unusedVariables false in
/-- Every canonical handler group passes wire checks, independently of later compromise. -/
theorem simTraceAt_wire (hv : rho.ExecutionValid) :
    ∀ y j t e,
      (simTraceAt S rho hn).GroupAt (runProposer S rho hn) (digestOf S rho) y j t e →
      WireOK (digestOf S rho) e := by
  obtain ⟨hpr, hdg⟩ := runProposer_digestOf S rho hn
  rw [simTraceAt_eq, (simTrace_encoding S rho hn).1, hpr, hdg]
  intro y j t e hg
  apply NodeAsChainShape.CanonicalTrace.wire (traceEncoding S hn) rho _ _ _ hg
  · apply traceEncoding_induction (E := E) S hn (fun enc _ =>
      ∀ {h atts payload}, enc.codec.decode h = some (atts, payload) →
        enc.codec.encode atts payload = h)
    dsimp only
    intro _ _ _ _ h
    exact encodeInfo_of_decodeInfo h
  · intro _ w m _
    trivial
  · apply traceEncoding_induction (E := E) S hn (fun enc _ =>
      ∀ {w a}, enc.codec.attestation w = some a → a.WellFormed)
    dsimp only
    intro _ _ _ h
    exact wellFormed_of_decodeAttObj h

end Consensus.Goldilocks.Simulation

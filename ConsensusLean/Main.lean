module
public import ConsensusLean.Spec.Shape.Obligations
public import ConsensusLean.Proofs.Behaviour.Main
public import ConsensusLean.Proofs.RegimesRealizable.Main

public section

/-! # Shape obligations: the theorems (L2)

`ShapeObligations.behaviour` and `ShapeObligations.correct` for the structure `ShapeObligations` of
`ConsensusLean/Spec/Shape/Obligations.lean` (moved from it). -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (pubOf sysOf)

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]

/-- An instance that meets its obligations has the L0 behaviour for every finite validator
type. -/
theorem ShapeObligations.behaviour {F : ChainShapeFamily O Info} {K : Contract ProgressReq}
    (h : ShapeObligations F K) (V : Type) [Fintype V] [DecidableEq V] :
    Behaviour (sysOf O (compiled F) V) (shapeProgress F V) K :=
  refinement F K V h.claims h.admissible h.serves

/-- An instance that meets its obligations is a correct protocol (L0 `CorrectProtocol`) for every
finite validator type. -/
theorem ShapeObligations.correct {F : ChainShapeFamily O Info} {K : Contract ProgressReq}
    (h : ShapeObligations F K) (V : Type) [Fintype V] [DecidableEq V] :
    CorrectProtocol (sysOf O (compiled F) V) (shapeProgress F V) K :=
  ⟨h.behaviour V, Model.sysOf_adequate _ rfl,
    fun hn =>
      (regimes_realizable F K h.admissible h.progressFits h.progressTolerant V hn).toRealizable⟩

end Consensus.Shape

/-! # Active service (L2, a checked corollary outside the trusted surface)

`ShapeObligations.activeService`: an instance that meets its obligations actively serves
transactions in a final or an available output. A corollary of `ShapeObligations.correct` via L0
`CorrectProtocol.served`; the reader of `ShapeObligations.correct` need not read it. -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (pubOf sysOf)

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]

/-- Output `g`, serving capability `cap`, actively serves transactions: for
every population of at least five, every index, `Δ > 1` and GST `gst ≥ 0`, some
clean witness run (valid, no excuse, a faulty validator) in the healthy regime
from `gst`, with the progress of `cap` at the index, has a transaction
submitted to one honest node in the `g`-read of another honest node that was
never submitted it (it arrived by relay and was ordered by the protocol). -/
def ActiveService (F : ChainShapeFamily O Info) (K : Contract ProgressReq) (cap : Capability)
    (g : O.Id) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V], 5 ≤ Fintype.card V →
    ∀ (i : K.Idx) (Δ gst : Time), 1 < Δ → 0 ≤ gst →
    ∃ r, (Sys F V).Witness r ∧ ((Sys F V).pt r).env.ΔAC = Δ ∧ (Sys F V).Healthy K gst r ∧
      (Sys F V).prog (shapeProgress F V) K cap i ((Sys F V).ready K gst r)
        ((Sys F V).pt r).horizon r ∧
      ∃ x u w t t', u ∈ ((Sys F V).pt r).honest ∧ w ∈ ((Sys F V).pt r).honest ∧ w ≠ u ∧
        x ∈ ((Sys F V).pt r).submit u t ∧ (∀ τ, x ∉ ((Sys F V).pt r).submit w τ) ∧
        t' ≤ ((Sys F V).pt r).horizon ∧ x ∈ ((Sys F V).trace r).readAt g w t'

/-- An instance that meets its obligations actively serves transactions in a final or an
available output: the output is chosen once (final if provided, else
available), then L0 `CorrectProtocol.served` applies at every population. -/
theorem ShapeObligations.activeService {F : ChainShapeFamily O Info} {K : Contract ProgressReq}
    (h : ShapeObligations F K) : ∃ cap g, (cap = .final ∨ cap = .available) ∧ O.output cap =
        some g ∧
      ActiveService F K cap g := by
  obtain ⟨cap, g, hcap, hg⟩ : ∃ cap g, (cap = .final ∨ cap = .available) ∧
      O.output cap = some g := by
    rcases h.serves with hb | ha
    · exact ⟨.final, (Option.isSome_iff_exists.mp hb).choose, Or.inl rfl,
        (Option.isSome_iff_exists.mp hb).choose_spec⟩
    · exact ⟨.available, (Option.isSome_iff_exists.mp ha).choose, Or.inr rfl,
        (Option.isSome_iff_exists.mp ha).choose_spec⟩
  exact ⟨cap, g, hcap, hg, fun V _ _ hn i Δ gst hΔ hgst =>
    (h.correct V).served hn hcap hg i Δ gst hΔ hgst⟩

end Consensus.Shape

end

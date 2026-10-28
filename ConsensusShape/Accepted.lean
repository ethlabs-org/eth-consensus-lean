module
public import ConsensusShape.Realizable

@[expose] public section

/-! # Acceptance (L2): the review endpoint

`Accepted F K` is what an instance must establish: its shape claims
(`ShapeClaims`, proved by the protocol), admissible numbers
(`Params.Admissible`: thresholds no stronger than standard), a served ledger
(`OutputSchema.Serves`: a final output, or an available one), and progress
requirements that fit the skeleton (`Contract.ProgressFits`: a recurrence needs
one proposer per slot), and tolerate arbitrary numbers of validators not ready.

`Accepted.good` gives the full L0 `Good` of the compiled system, for every
finite validator type: `Accepted.behaviour` (the refinement of the shape
claims), `Accepted.adequate` (the model's adequacy, proved once) and the
generic `regimes_realizable` (from admissibility, progress fit and tolerance).
`Accepted.activeService`: a final or available output actively serves
transactions (`ActiveService`). -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (pubOf sysOf)

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Encodable Info]

/-- An accepted instance: shape claims, admissible numbers, a served ledger,
and progress requirements that fit the skeleton and tolerate arbitrary numbers
of validators not ready. -/
structure Accepted (F : ShapeFamily O Info) (K : Contract ProgressReq) : Prop where
  /-- The chain-level claims (proved by the protocol). -/
  claims : ShapeClaims F K
  /-- The numbers are admissible. -/
  admissible : K.params.Admissible
  /-- A final or an available output is provided. -/
  serves : O.Serves
  /-- The progress requirements fit the skeleton. -/
  progressFits : K.ProgressFits F
  /-- Every provided output tolerates arbitrary numbers of validators not ready. -/
  progressTolerant : Contract.ProgressTolerant O K

/-- An accepted instance has the L0 behaviour for every finite validator
type. -/
theorem Accepted.behaviour {F : ShapeFamily O Info} {K : Contract ProgressReq}
    (h : Accepted F K) (V : Type) [Fintype V] [DecidableEq V] :
    Behaviour (sysOf O (compiled F) V) (shapeProgress F V) K :=
  refinement F K V h.claims h.admissible h.serves

/-- The compiled system of every family is adequate for the shape's progress
reader (an L1 theorem; it does not depend on the claims). -/
theorem Accepted.adequate {F : ShapeFamily O Info} {K : Contract ProgressReq}
    (_h : Accepted F K) (V : Type) [Fintype V] [DecidableEq V] :
    (sysOf O (compiled F) V).Adequate (shapeProgress F V) :=
  Model.sysOf_adequate _ rfl

/-- An accepted instance is a good protocol (L0 `Good`) for every finite
validator type. -/
theorem Accepted.good {F : ShapeFamily O Info} {K : Contract ProgressReq}
    (h : Accepted F K) (V : Type) [Fintype V] [DecidableEq V] :
    Good (sysOf O (compiled F) V) (shapeProgress F V) K :=
  ⟨h.behaviour V, h.adequate V,
    fun hn => (regimes_realizable F K h.admissible h.progressFits h.progressTolerant V hn).1⟩

/-- Output `g`, serving capability `cap`, actively serves transactions: for
every population of at least five, every index, `Δ` and GST `gst ≥ 0`, some
clean witness run (valid, no excuse, a faulty validator) in the healthy regime
from `gst`, with the progress of `cap` at the index, has a transaction
submitted to one honest node in the `g`-read of another honest node that was
never submitted it (it arrived by relay and was ordered by the protocol). -/
def ActiveService (F : ShapeFamily O Info) (K : Contract ProgressReq) (cap : Capability)
    (g : O.Id) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V], 5 ≤ Fintype.card V →
    ∀ (i : K.Idx) (Δ gst : Time), 0 < Δ → 0 ≤ gst →
    ∃ r, (sysOf O (compiled F) V).Witness r ∧ ((sysOf O (compiled F) V).pt r).env.Δ = Δ ∧
      (sysOf O (compiled F) V).Healthy K gst r ∧
      (sysOf O (compiled F) V).prog (shapeProgress F V) K cap i
        ((sysOf O (compiled F) V).ready K gst r) ((sysOf O (compiled F) V).pt r).horizon r ∧
      ∃ x u w t t', u ∈ ((sysOf O (compiled F) V).pt r).honest ∧
        w ∈ ((sysOf O (compiled F) V).pt r).honest ∧ w ≠ u ∧
        x ∈ ((sysOf O (compiled F) V).pt r).submit u t ∧
        (∀ τ, x ∉ ((sysOf O (compiled F) V).pt r).submit w τ) ∧
        t' ≤ ((sysOf O (compiled F) V).pt r).horizon ∧
        x ∈ ((sysOf O (compiled F) V).trace r).readAt g w t'

/-- An accepted instance actively serves transactions in a final or an
available output: the output is chosen once (final if provided, else
available), then L0 `Good.served` applies at every population. -/
theorem Accepted.activeService {F : ShapeFamily O Info} {K : Contract ProgressReq}
    (h : Accepted F K) : ∃ cap g, (cap = .final ∨ cap = .available) ∧ O.output cap = some g ∧
      ActiveService F K cap g := by
  obtain ⟨cap, g, hcap, hg⟩ : ∃ cap g, (cap = .final ∨ cap = .available) ∧
      O.output cap = some g := by
    rcases h.serves with hb | ha
    · exact ⟨.final, (Option.isSome_iff_exists.mp hb).choose, Or.inl rfl,
        (Option.isSome_iff_exists.mp hb).choose_spec⟩
    · exact ⟨.available, (Option.isSome_iff_exists.mp ha).choose, Or.inr rfl,
        (Option.isSome_iff_exists.mp ha).choose_spec⟩
  exact ⟨cap, g, hcap, hg, fun V _ _ hn i Δ gst hΔ hgst =>
    (h.good V).served hn hcap hg i Δ gst hΔ hgst⟩

end Consensus.Shape

end

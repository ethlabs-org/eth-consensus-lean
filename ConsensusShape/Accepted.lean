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
structure Accepted (F : ShapeFamily O Info) (K : Contract O ProgressReq) : Prop where
  /-- The chain-level claims (proved by the protocol). -/
  claims : ShapeClaims F K
  /-- The numbers are admissible. -/
  admissible : K.params.Admissible
  /-- A final or an available output is provided. -/
  serves : O.Serves
  /-- The progress requirements fit the skeleton. -/
  progressFits : K.ProgressFits F
  /-- Every provided output tolerates arbitrary numbers of validators not ready. -/
  progressTolerant : K.ProgressTolerant

/-- An accepted instance has the L0 behaviour for every finite validator
type. -/
theorem Accepted.behaviour {F : ShapeFamily O Info} {K : Contract O ProgressReq}
    (h : Accepted F K) (V : Type) [Fintype V] [DecidableEq V] :
    Behaviour (sysOf O (compiled F) V) (shapeProgress F V) K :=
  refinement F K V h.claims h.admissible h.serves

/-- The compiled system of every family is adequate for the shape's progress
reader (an L1 theorem; it does not depend on the claims). -/
theorem Accepted.adequate {F : ShapeFamily O Info} {K : Contract O ProgressReq}
    (_h : Accepted F K) (V : Type) [Fintype V] [DecidableEq V] :
    (sysOf O (compiled F) V).Adequate (shapeProgress F V) :=
  Model.sysOf_adequate _ rfl

/-- An accepted instance is a good protocol (L0 `Good`) for every finite
validator type. -/
theorem Accepted.good {F : ShapeFamily O Info} {K : Contract O ProgressReq}
    (h : Accepted F K) (V : Type) [Fintype V] [DecidableEq V] :
    Good (sysOf O (compiled F) V) (shapeProgress F V) K :=
  ⟨h.behaviour V, h.adequate V,
    fun hn => (regimes_realizable F K h.admissible h.progressFits h.progressTolerant V hn).1⟩

/-- A live claim met on an active witness serves a transaction: one submitted
to an honest node is in the `g`-read of another honest node, which was never
submitted it. -/
theorem _root_.Consensus.Trace.TxLive.served {V Id : Type} {tr : Trace V Tx Id} {c : Time}
    {g : Id} {start D : Time} (hl : tr.TxLive c g start D) (ha : tr.TxLiveActive c start D) :
    ∃ x u w t t', u ∈ tr.point.honest ∧ w ∈ tr.point.honest ∧ w ≠ u ∧
      x ∈ tr.point.submit u t ∧ (∀ τ, x ∉ tr.point.submit w τ) ∧ t' ≤ tr.point.horizon ∧
      x ∈ tr.readAt g w t' := by
  obtain ⟨x, t, t', u, w, ht0, hu, hua, hx, hw, hne, hnw, hdl, hth, hr⟩ := ha
  exact ⟨x, u, w, t, t', hu, hw, hne, hx, hnw, hth,
    hl x t t' ⟨u, hu, t, ht0, le_rfl, hua, hx⟩ hdl hth w hr⟩

/-- Output `g`, serving capability `cap`, actively serves transactions: for
every population of at least five, every index, `Δ` and GST `gst ≥ 0`, some
clean witness run (valid, no excuse, a faulty validator) in the healthy regime
from `gst`, with the progress of `cap` at the index, has a transaction
submitted to one honest node in the `g`-read of another honest node that was
never submitted it (it arrived by relay and was ordered by the protocol).
Renamed from rev-0 `Delivers` (no clash with L0 `CommLog.Delivers`). -/
def ActiveService (F : ShapeFamily O Info) (K : Contract O ProgressReq) (cap : Capability)
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
available output: the healthy witness of `regimes_realizable` meets the
premise of the output's live claim (`FinalClaims.live` or
`DAClaims.healedLive`) with an active antecedent, and has no excuse. -/
theorem Accepted.activeService {F : ShapeFamily O Info} {K : Contract O ProgressReq}
    (h : Accepted F K) : ∃ cap g, (cap = .final ∨ cap = .available) ∧ O.output cap = some g ∧
      ActiveService F K cap g := by
  -- The live claim of `cap` at `g`, at every population, index and GST.
  have key : ∀ cap g, O.output cap = some g →
      (∀ (V : Type) [Fintype V] [DecidableEq V] (i : K.Idx) (gst : Time),
        (sysOf O (compiled F) V).Holds
          (fun r => (sysOf O (compiled F) V).Healthy K gst r ∧
            (sysOf O (compiled F) V).prog (shapeProgress F V) K cap i
              ((sysOf O (compiled F) V).ready K gst r) ((sysOf O (compiled F) V).pt r).horizon r)
          (fun r => ((sysOf O (compiled F) V).trace r).TxLive
            ((sysOf O (compiled F) V).cDur K r) g ((sysOf O (compiled F) V).heal K cap i gst r)
            ((sysOf O (compiled F) V).lat K cap i r))) →
      ActiveService F K cap g := by
    intro cap g _ hl V _ _ hn i Δ gst hΔ hg
    obtain ⟨r, hw, hd, -, hH, hp, ha, -⟩ :=
      (regimes_realizable F K h.admissible h.progressFits h.progressTolerant V hn).1.healthy cap i
        Δ gst hΔ hg
    refine ⟨r, hw, hd, hH, hp, ?_⟩
    rcases hl V i gst r hw.1 ⟨hH, hp⟩ with hlive | he
    · exact hlive.served ha
    · exact absurd he hw.2.1
  rcases h.serves with hb | ⟨ha, -⟩
  · obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp hb
    exact ⟨.final, g, Or.inl rfl, hg, key .final g hg fun V _ _ i gst =>
      ((h.behaviour V).final g hg).live i gst⟩
  · obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp ha
    exact ⟨.available, g, Or.inr rfl, hg, key .available g hg fun V _ _ i gst =>
      ((h.behaviour V).da .available g (Or.inl rfl) hg).healedLive i gst⟩

end Consensus.Shape

end

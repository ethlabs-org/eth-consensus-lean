module
public import ConsensusLean.Spec.Shape.Obligations

@[expose] public section

/-! # The shape obligations on a class of runs (L2)

`ShapeClaimsOnAt F K V Q` is `ShapeClaimsAt F K V` with each field restricted to
the runs whose environment point satisfies `Q`; nothing else differs.
`ShapeObligationsOn F K Q` is `ShapeObligations F K` with those claims. At
`Q = ConstantFaults` (the static adversary) this is the shape obligations of the
static model, which `Review.ObligationsSufficientOn` turns into
`CorrectProtocolOn`: the growing-fault statements are additional to it, and the
static statements keep their strength. -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (pubOf sysOf)

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]

/-- `ShapeClaimsAt`, field by field, on the runs whose point satisfies `Q`. -/
structure ShapeClaimsOnAt (F : ChainShapeFamily O Info) (K : Contract ProgressReq)
    (V : Type) [Fintype V] [DecidableEq V] (Q : EnvPoint V → Prop) : Prop where
  outputValid : (Sys F V).HoldsAlways fun r => Q ((Sys F V).pt r) →
    ∀ c g, O.output c = some g → OutputValid r.2 g
  nested : ∀ c₁ c₂ g₁ g₂, c₁.rank < c₂.rank → O.output c₁ = some g₁ → O.output c₂ = some g₂ →
    (Sys F V).HoldsAlways fun r => Q ((Sys F V).pt r) →
      (chainTrace r.2).Nested g₁ g₂
  finalMonotone : ∀ g, O.output .final = some g →
    (Sys F V).HoldsAlways fun r => Q ((Sys F V).pt r) →
      (chainTrace r.2).Monotone g 0
  finalAccountable : ∀ g, O.output .final = some g →
    (Sys F V).Holds (fun r => Q ((Sys F V).pt r))
    fun r => (chainTrace r.2).AccountablySafe r.2.ViewIdx r.2.Slashable K.params.α g 0
  healthyLive : ∀ cap g, O.output cap = some g → ∀ (i : K.Idx) (gst : Time), (Sys F V).Holds
    (fun r => Q ((Sys F V).pt r) ∧ (Sys F V).Healthy K gst r ∧
      (Sys F V).prog (shapeProgress F V) K cap i ((Sys F V).ready K gst r)
        ((Sys F V).pt r).horizon r)
    fun r => ProposalLiveReady r.2 ((Sys F V).cDur K r) g ((Sys F V).heal K cap i gst r)
      (K.params.latency cap i)
  sleepySafe : ∀ cap g, (cap = .available ∨ cap = .stable) → O.output cap = some g →
    (Sys F V).Holds (fun r => Q ((Sys F V).pt r) ∧ (Sys F V).Sleepy K r) fun r =>
      (chainTrace r.2).ReadySafe ((Sys F V).cDur K r) g 0
  sleepyLive : ∀ cap g, (cap = .available ∨ cap = .stable) → O.output cap = some g →
    ∀ i : K.Idx, (Sys F V).Holds
      (fun r => Q ((Sys F V).pt r) ∧ (Sys F V).Sleepy K r ∧
        (Sys F V).prog (shapeProgress F V) K cap i 0 ((Sys F V).pt r).horizon r)
      fun r => ProposalLiveReady r.2 ((Sys F V).cDur K r) g 0 (K.params.latency cap i)
  healedSafe : ∀ cap g, (cap = .available ∨ cap = .stable) → O.output cap = some g →
    ∀ (i : K.Idx) (gst : Time), (Sys F V).Holds
      (fun r => Q ((Sys F V).pt r) ∧ (Sys F V).Healthy K gst r ∧
        (Sys F V).prog (shapeProgress F V) K cap i ((Sys F V).ready K gst r)
          ((Sys F V).heal K cap i gst r) r)
      fun r => (chainTrace r.2).ReadySafe ((Sys F V).cDur K r) g ((Sys F V).heal K cap i gst r)
  persists : ∀ g, O.output .stable = some g → ∀ T b₀ b₁,
    (Sys F V).Holds (fun r => Q ((Sys F V).pt r) ∧ (Sys F V).Outage K T b₀ b₁ r)
      fun r => (chainTrace r.2).ProtectedReadyFrom ((Sys F V).cDur K r) g (resilienceTarget O g) T
        ((Sys F V).recoveryAt K b₁ r)

/-- `ShapeObligations` with the claims restricted to the runs whose point satisfies
`Q`; admissibility, service, progress fit and tolerance unchanged. -/
structure ShapeObligationsOn (F : ChainShapeFamily O Info) (K : Contract ProgressReq)
    (Q : ∀ V : Type, EnvPoint V → Prop) : Prop where
  claims : ∀ (V : Type) [Fintype V] [DecidableEq V], ShapeClaimsOnAt F K V (Q V)
  admissible : K.params.Admissible
  serves : O.Serves
  progressFits : ProgressFits K F
  progressTolerant : ProgressTolerant O K

/-- `ShapeObligationsOn` under the profile label `p`. -/
def ShapeObligationsOnAs (p : Profile) (F : ChainShapeFamily O Info)
    (K : Contract ProgressReq) (Q : ∀ V : Type, EnvPoint V → Prop) : Prop :=
  p.Matches O ∧ ShapeObligationsOn F K Q

end Consensus.Shape

end

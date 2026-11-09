module
public import ConsensusLean.Spec.Model.System

public section

/-! # Correctness with explicit execution-binding failures

The complete behaviour table transfers to a single valid run, retaining the
original excuse only in Holds rows. Splitting the execution bindings then gives
the disjunctive headline on structural runs.
-/

namespace Consensus

variable {V : Type} [Fintype V] [DecidableEq V] {Prog : Type}
    {S : System V} {X : Progress S Prog} {K : Contract Prog}

private theorem holds_atRun {V : Type} {S : System V}
    {A P : S.Run → Prop} (h : S.Holds A P)
    {r : S.Run} (hv : S.Valid r) :
    (S.atRun r).Holds A P := by
  intro s hs ha
  subst s
  exact (h r hv ha).imp_right fun he => ⟨rfl, he⟩

/-- The full table transfers to a valid run, with the original excuse only in
`Holds` rows. `HoldsAlways` rows have no collision escape; monotonicity laws
for conviction and views remain global over all runs. -/
theorem Behaviour.at_run (h : Behaviour S X K) {r : S.Run}
    (hv : S.Valid r) : Behaviour (S.atRun r) (X.atRun r) K where
  laws := ⟨by intro s hs; subst s; exact h.laws.trace r hv,
    h.laws.convicts_mono, h.laws.view_mono⟩
  admissible := h.admissible
  serves := h.serves
  nonFraming := by intro s hs; subst s; exact h.nonFraming r hv
  nested := by
    intro c₁ c₂ g₁ g₂ hlt hg₁ hg₂ s hs
    subst s
    exact h.nested c₁ c₂ g₁ g₂ hlt hg₁ hg₂ r hv
  finalMonotone := by
    intro g hg s hs
    subst s
    exact h.finalMonotone g hg r hv
  finalAccountable := fun g hg => holds_atRun (h.finalAccountable g hg) hv
  healthyLive := fun cap g hg i gst => holds_atRun (h.healthyLive cap g hg i gst) hv
  sleepySafe := fun cap g hc hg => holds_atRun (h.sleepySafe cap g hc hg) hv
  sleepyLive := fun cap g hc hg i => holds_atRun (h.sleepyLive cap g hc hg i) hv
  healedSafe := fun cap g hc hg i gst => holds_atRun (h.healedSafe cap g hc hg i gst) hv
  persists := fun g hg T b₀ b₁ => holds_atRun (h.persists g hg T b₀ b₁) hv

/-- Moving failed bindings out of validity gives an explicit disjunction,
without weakening adequacy or realizability. -/
theorem CorrectProtocol.with_excuses (h : CorrectProtocol S X K)
    (Structural Failure : S.Run → Prop)
    (valid : ∀ r, Structural r → ¬ Failure r → S.Valid r) :
    CorrectProtocolWithExcuses S X K Structural Failure := by
  classical
  refine ⟨?_, h.adequate, h.realizable⟩
  intro r hs
  by_cases hf : Failure r
  · exact Or.inr hf
  exact Or.inl (h.behaviour.at_run (valid r hs hf))

/-- The model's three failed bindings are exactly the additional excuses. -/
theorem Model.correctProtocol_with_excuses {O : OutputSchema} {F : Model.ProtocolFamily O}
    {X : Progress (Model.sysOf O F V) Prog}
    (h : CorrectProtocol (Model.sysOf O F V) X K) :
    CorrectProtocolWithExcuses (Model.sysOf O F V) X K
      (fun r => r.2.StructuralValid) (fun r => r.2.BindingFailure) := by
  apply h.with_excuses
  intro r hs hf
  have hb : r.2.Unforgeable ∧ r.2.Credentials ∧ r.2.SelValid := by
    simpa only [Model.Run.BindingFailure, not_or, not_not] using hf
  exact r.2.executionValid_iff_structuralValid.mpr ⟨hs, hb⟩

end Consensus

end

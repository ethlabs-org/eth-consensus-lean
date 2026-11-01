module
public import Mathlib.Data.Fintype.Defs
public import AvailableChainModel.Objects.Time

@[expose] public section

namespace AvailableChain.Framework

/-- A finite validator type, bundled so that claims can quantify over it. -/
structure Validators where
  V : Type
  dec : DecidableEq V
  fin : Fintype V

attribute [instance] Validators.dec Validators.fin

/-- What a claim speaks about (design §3; carrier generalization, PHASE0-REPORT
§6 I3 and I5): a type of instances and, for each instance and validator type,
a type of run contexts. The v1 claim domain has an environment and a v1 run. A
facet or a new engine is a new claim domain value, not a change to `ClaimSpec`. -/
structure ClaimDomain where
  /-- A stable name (async m6), for example `v1`, `strong`. -/
  id : Lean.Name
  Inst : Type 1
  Ctx : Inst → Validators → Type
  /-- The contexts that a certificate covers (v1: the environment has the
  instance's Δ). -/
  admissible : (I : Inst) → (W : Validators) → Ctx I W → Prop
  /-- The last time of the run of a context. -/
  horizon : (I : Inst) → (W : Validators) → Ctx I W → Time

end AvailableChain.Framework

end

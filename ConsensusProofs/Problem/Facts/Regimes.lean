module
public import ConsensusProofs.Problem.Derived
public import ConsensusSpec.Problem.Regimes
public import Mathlib.Tactic

@[expose] public section

/-! # Numbers and regimes (L0 facts)

The standard thresholds are admissible; the healthy regime bounds the faults. -/

namespace Consensus

namespace Params

variable {Idx : Type}

/-- The standard thresholds are admissible. -/
theorem standard_admissible {catchUp lag budget : Nat} {heal latency : Capability → Idx → Nat}
    (h : 1 ≤ catchUp) (hb : 1 ≤ budget) :
    (standard catchUp lag budget heal latency).Admissible :=
  ⟨h, by norm_num [standard], by norm_num [standard], by norm_num [standard],
    by norm_num [standard], hb⟩

end Params

namespace EnvPoint

variable {V : Type} [Fintype V] [DecidableEq V] {p : EnvPoint V}

/-- Healthy bounds the faults below `β`. -/
theorem HealthyOn.faultsBelow {β : ℚ} {g b : Time} (h : p.HealthyOn β g b) :
    p.FaultsBelow β :=
  h.1

end EnvPoint

end Consensus

end

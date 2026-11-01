module
public import AvailableChainGeneric.Proofs.V2.DCRegimes -- shake: keep (examples)

public section

namespace AvailableChain.Gen.V2.Tests.DCRegimes

open AvailableChain AvailableChain.V2

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
  {I : Interface P} {E : Generic.Env V} {rho : Run V P}

-- The DC gap-period instance needs no constants, execution, or participation bundle.
example (gap : Nat) (period : Time)
    (h : RecoveryCore P I E rho (gap * period)) :
    PartialSynchrony E rho ∧ SingleProposerRecurrence I rho E.t_GST (gap * period) :=
  h.to_dcRecoveryConditions

-- The target exposes DC's strict lower bound, inclusive upper bound, and membership.
example {G t : Time} (h : RecoveryCore P I E rho G)
    (ht : E.t_GST ≤ t) (hh : t + G ≤ rho.horizon) :
    ∃ s, t < proposalTime I s ∧ proposalTime I s ≤ t + G ∧
      proposerOf rho I s ∈ rho.honest :=
  h.to_dcRecoveryConditions.2 t ht hh

-- A zero-length outage uses only CutCore's own interval bounds.
example {b₀ : Time} (h : CutCore E rho b₀) :
    HealthyPrefixDelivery E rho b₀ ∧ OutageInterval rho b₀ b₀ :=
  h.to_dcOutageFields le_rfl h.cut.2

-- An AC outage supplies the upper bounds. Its extra T bounds remain in the source.
example {T b₀ b₁ : Time} (hc : CutCore E rho b₀) (ho : OutageCore rho T b₀ b₁) :
    HealthyPrefixDelivery E rho b₀ ∧ OutageInterval rho b₀ b₁ :=
  hc.to_dcOutageFields ho.order.2.2.1 ho.order.2.2.2

-- The interval includes both endpoints, without a T or positive-length premise.
example (hh : 3 ≤ rho.horizon) : OutageInterval rho 0 3 :=
  ⟨le_rfl, by decide, hh⟩

end AvailableChain.Gen.V2.Tests.DCRegimes

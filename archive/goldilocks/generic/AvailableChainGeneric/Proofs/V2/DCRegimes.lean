module
public import AvailableChainGeneric.Statements.V2.DCRegimes
public import AvailableChainGeneric.Statements.V2.Regimes

public section

namespace AvailableChain.Gen.V2

open AvailableChain AvailableChain.V2

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}

/-- DC: DecoupledConsensusStatements/Generic/Regimes.lean:59–66;
DecoupledConsensusStatements/Generic/Conditions.lean:110–131,207–211.
INTENTIONAL: Export the two E-12 conditions with `gap * period := G`.
GLY r3.19 S128:1591–1595 says "healing needs only G".
S106:1529–1533 says ".prop 0 returns none"; `HonestSlot` thus adds `0 < s`.
The DC conclusion keeps only proposer membership. The synchrony fields agree. -/
theorem RecoveryCore.to_dcRecoveryConditions {I : Interface P} {E : Generic.Env V}
    {rho : Run V P} {G : Time} (h : RecoveryCore P I E rho G) :
    PartialSynchrony E rho ∧ SingleProposerRecurrence I rho E.t_GST G := by
  refine ⟨h.sync, ?_⟩
  intro t ht hh
  obtain ⟨s, hts, hst, hs⟩ := h.gap t ht hh
  exact ⟨s, hts, hst, hs.2⟩

/-- DC: DecoupledConsensusStatements/Generic/Regimes.lean:148–149;
DecoupledConsensusStatements/Generic/Conditions.lean:134–155.
INTENTIONAL: Export the healthy and interval fields requested by E-12.
GLY r3.19 S127:1587–1590 records "OutageCore adds 0 ≤ T ∧ T ≤ b₀";
the design record is TS/blueprint/00-outline.md:256,261–262.
Those AC bounds stay in `OutageCore`. Only the two upper interval bounds
are needed here; a caller can read them from `OutageCore.order`.
The result is the exact DC field pair, without the rest of its regime bundle. -/
theorem CutCore.to_dcOutageFields {E : Generic.Env V} {rho : Run V P} {b₀ b₁ : Time}
    (h : CutCore E rho b₀) (h₀₁ : b₀ ≤ b₁) (h₁ : b₁ ≤ rho.horizon) :
    HealthyPrefixDelivery E rho b₀ ∧ OutageInterval rho b₀ b₁ :=
  ⟨h.healthy, h.cut.1, h₀₁, h₁⟩

end AvailableChain.Gen.V2

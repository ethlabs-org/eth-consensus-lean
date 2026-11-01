module
public import AvailableChainEngineV2.Conditions.Interface

@[expose] public section

namespace AvailableChain.Gen.V2

open AvailableChain AvailableChain.V2

variable {V : Type} {In : Type} {P : ProtocolSpec In}

/-- DC: DecoupledConsensusStatements/Generic/Conditions.lean:207–211 (b241081, 2026-09-28);
same: verbatim mirror over V2 runs, with `gap * period := G`.
The proposal time and proposer use the V2 interface and run readers.
GLY r3.19 S128:1591–1595 records "healing needs only G" and this instance.
The mirror keeps DC's proposer membership, without the extra `HonestSlot` bound. -/
def SingleProposerRecurrence (I : Interface P) (rho : Run V P) (t₀ G : Time) : Prop :=
  ∀ t : Time, t₀ ≤ t → t + G ≤ rho.horizon →
    ∃ s, t < proposalTime I s ∧ proposalTime I s ≤ t + G ∧
      proposerOf rho I s ∈ rho.honest

/-- Defining equation.
DC: DecoupledConsensusStatements/Generic/Conditions.lean:207–211 (b241081, 2026-09-28);
same: verbatim mirror over V2 runs, with `gap * period := G`. -/
theorem SingleProposerRecurrence_def (I : Interface P) (rho : Run V P) (t₀ G : Time) :
    SingleProposerRecurrence I rho t₀ G =
      (∀ t : Time, t₀ ≤ t → t + G ≤ rho.horizon →
        ∃ s, t < proposalTime I s ∧ proposalTime I s ≤ t + G ∧
          proposerOf rho I s ∈ rho.honest) := by rfl

/-- DC: DecoupledConsensusStatements/Generic/Regimes.lean:149 (b241081, 2026-09-28);
same: verbatim mirror over V2 runs of the `OutageRegime.interval` field type.
GLY r3.19 E-12:2663–2667 requests the healthy and interval fields.
This predicate preserves all three bounds and their order. -/
def OutageInterval (rho : Run V P) (b₀ b₁ : Time) : Prop :=
  0 ≤ b₀ ∧ b₀ ≤ b₁ ∧ b₁ ≤ rho.horizon

/-- Defining equation.
DC: DecoupledConsensusStatements/Generic/Regimes.lean:149 (b241081, 2026-09-28);
same: verbatim mirror over V2 runs of the `OutageRegime.interval` field type. -/
theorem OutageInterval_def (rho : Run V P) (b₀ b₁ : Time) :
    OutageInterval rho b₀ b₁ = (0 ≤ b₀ ∧ b₀ ≤ b₁ ∧ b₁ ≤ rho.horizon) := by rfl

end AvailableChain.Gen.V2

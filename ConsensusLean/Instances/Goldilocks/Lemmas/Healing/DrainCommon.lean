module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Induction
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Relay
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Confirmed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Compat
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Inclusion
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Geo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing, HS.2: the settled setting and the common local facts

The context `Γ` (`GoldilocksRun`, `HSShared`, `Catch(2Δ)`,
`Prop⁺(G_p)`, `SettledIn … w i₀ m c`). What remains of the common local facts of HS.2–HS.4: the
phase holds on every shorter interval (`PhaseOn.mono_right`). The other facts, used only by the
static healing chain, are removed with HS.4 and HR.3 (retired, owner decision). -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {K : AC.CommitteeDict sp.n}
  {ini : Fin sp.n → (goldilocksNode sp).State} {g ΔF Gp w : Time}
  {i₀ m : Nat}
  {c : PhaseCase (AC.Blk sp.n (List (FG.Att sp.n)))}

/-! ### Settled time facts -/

/-- The phase holds on every shorter interval. -/
theorem PhaseOn.mono_right {k k' : Nat} (h : PhaseOn tr.projFG H i₀ k m c) (hk : k' ≤ k) :
    PhaseOn tr.projFG H i₀ k' m c :=
  fun k'' h₁ h₂ => h k'' h₁ (h₂.trans hk)

end Consensus.Goldilocks.Healing

end

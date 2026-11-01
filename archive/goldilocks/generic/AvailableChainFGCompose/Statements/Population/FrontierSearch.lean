module
public import AvailableChainFGCompose.Statements.FrontierSearch
public import AvailableChainFGCompose.Statements.Population.Promotion
public import AvailableChainFGCompose.Statements.Population.Seats

@[expose] public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {Prot : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads Prot n Base Proposal Wire) (S : FGSafetyReads Prot n Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V Prot)
variable (O : FGObservationReads R) (T : FGTiming) (I : V2.D.Interface Prot)
variable (pair : Wire → NamedHeightPair) (Jst : Time) (leaseSlots deltaT : Nat)

/-- Holder coverage at the service boundary; every other receiver/source clause is unchanged. -/
def FrontierLocalServiceFG (q : Slot) (Q : Block) (Qfg : FGBlock (Fin n))
    (m : Nat) (v : Time) : Prop :=
  (∀ x s H, x ∈ rho.honest → q + 1 ≤ s → T.vote s ≤ v →
    headAtLabel R E rho T x s = some H → Block.Preceq Q H) ∧
  (∀ s B, q + 2 ≤ s → T.proposal s ≤ v → HonestProposal E rho I s B →
    Block.Preceq Q B.parent) ∧
  (∀ i x, x ∈ rho.honest → T.gate q + 4 * T.delta ≤ v →
    afterTicksIdx rho (T.gate q + 4 * T.delta) ≤ i → i ≤ timeIdx rho v →
    Block.Preceq Q (I.stable (rho.stateBefore E i x))) ∧
  (∀ s B, T.proposal q < T.proposal s → T.gate s ≤ v →
    HonestProposal E rho I s B → FrontierProposalService R E rho T s B) ∧
  (∀ r, q ≤ r * T.roundSlots → T.action r ≤ v →
    OpeningCoveredFG R S E rho O.height T pair (FGHonestSeats S rho) r Q ∧
    OpeningEntry R E rho O.height T r m ∧
    (∀ x K, x ∈ rho.honest → actionSourceFG R E rho T x r = some (some K) →
      (O.height K).T_h = (O.height Qfg).T_h) ∧
    ((∀ r', q ≤ r' * T.roundSlots → r ≤ r') →
      T.action r - T.gate q ≤ FGCompose.P T - 4 * T.delta))

theorem FrontierLocalServiceFG_def (q : Slot) (Q : Block) (Qfg : FGBlock (Fin n))
    (m : Nat) (v : Time) :
    FrontierLocalServiceFG R S E rho O T I pair q Q Qfg m v ↔
  (∀ x s H, x ∈ rho.honest → q + 1 ≤ s → T.vote s ≤ v →
    headAtLabel R E rho T x s = some H → Block.Preceq Q H) ∧
  (∀ s B, q + 2 ≤ s → T.proposal s ≤ v → HonestProposal E rho I s B →
    Block.Preceq Q B.parent) ∧
  (∀ i x, x ∈ rho.honest → T.gate q + 4 * T.delta ≤ v →
    afterTicksIdx rho (T.gate q + 4 * T.delta) ≤ i → i ≤ timeIdx rho v →
    Block.Preceq Q (I.stable (rho.stateBefore E i x))) ∧
  (∀ s B, T.proposal q < T.proposal s → T.gate s ≤ v →
    HonestProposal E rho I s B → FrontierProposalService R E rho T s B) ∧
  (∀ r, q ≤ r * T.roundSlots → T.action r ≤ v →
    OpeningCoveredFG R S E rho O.height T pair (FGHonestSeats S rho) r Q ∧
    OpeningEntry R E rho O.height T r m ∧
    (∀ x K, x ∈ rho.honest → actionSourceFG R E rho T x r = some (some K) →
      (O.height K).T_h = (O.height Qfg).T_h) ∧
    ((∀ r', q ≤ r' * T.roundSlots → r ≤ r') →
      T.action r - T.gate q ≤ FGCompose.P T - 4 * T.delta)) := Iff.rfl

/-- A saved seed keeps the actual proposal, phase, read cutoff, and local service. -/
def StrongServedFG (m : Nat) (t : Time) : Prop :=
  ∃ u J contested q Q Qfg,
    Jst ≤ u ∧ HonestProposal E rho I q Q ∧ R.erase Qfg = Q ∧
    (O.height Qfg).h = m ∧ FrontierProposalService R E rho T q Q ∧
    FrontierSeedQualification T leaseSlots E.t_GST u q ∧ u ≤ T.proposal q ∧
    PhaseInterval R E rho O u (T.gate q) m J contested ∧ T.gate q ≤ t ∧
    t ≤ rho.horizon ∧
    (∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho t → x ∈ rho.honest →
      (R.core (rho.stateBefore E i x)).fg.h_max ≤ m) ∧
    FrontierLocalServiceFG R S E rho O T I pair q Q Qfg m t

theorem StrongServedFG_def (m : Nat) (t : Time) :
    StrongServedFG R S E rho O T I pair Jst leaseSlots m t ↔
  ∃ u J contested q Q Qfg,
    Jst ≤ u ∧ HonestProposal E rho I q Q ∧ R.erase Qfg = Q ∧
    (O.height Qfg).h = m ∧ FrontierProposalService R E rho T q Q ∧
    FrontierSeedQualification T leaseSlots E.t_GST u q ∧ u ≤ T.proposal q ∧
    PhaseInterval R E rho O u (T.gate q) m J contested ∧ T.gate q ≤ t ∧
    t ≤ rho.horizon ∧
    (∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho t → x ∈ rho.honest →
      (R.core (rho.stateBefore E i x)).fg.h_max ≤ m) ∧
    FrontierLocalServiceFG R S E rho O T I pair q Q Qfg m t := Iff.rfl

/-- Holder-served alternative with the original first-stop and rise alternatives. -/
def FrontierHG3ResultFG (i m : Nat) (start deadline : Time) : Prop :=
  FirstPhaseStopBy R E rho O i m deadline ∨
  FirstRiseStopBy R E rho O i m deadline ∨
  ∃ t, start ≤ t ∧ t ≤ deadline ∧ StrongServedFG R S E rho O T I pair Jst leaseSlots m t

/-- Blueprint 21 HG.3. DC: SAME the public conclusion interface. -/
theorem FrontierHG3ResultFG_def (i m : Nat) (start deadline : Time) :
    FrontierHG3ResultFG R S E rho O T I pair Jst leaseSlots i m start deadline ↔
  FirstPhaseStopBy R E rho O i m deadline ∨
  FirstRiseStopBy R E rho O i m deadline ∨
  ∃ t, start ≤ t ∧ t ≤ deadline ∧ StrongServedFG R S E rho O T I pair Jst leaseSlots m t := Iff.rfl

/-- Interrupted repair with holder-served seeds and the original horizon guard. -/
def InterruptedRepairStatementFG (G ΔF ρbar : Time) : Prop :=
  deltaT = 2 * T.roundSlots → LivenessBoundW T ΔF →
  ∀ i ev m kind, FrontierSearchStart R E rho O T Jst i ev m kind →
    FrontierRepairAllowance R E rho O T I Jst leaseSlots G ρbar (ev.time + 3 * T.delta) →
    ev.time + interruptedRepairBudget T G ΔF ρbar kind ≤ rho.horizon →
    FirstEffectiveBy R E rho O i
      (ev.time + interruptedRepairBudget T G ΔF ρbar kind) ∨
    FrontierRiseBy R E rho i m
      (ev.time + interruptedRepairBudget T G ΔF ρbar kind) ∨
    (∃ t, ev.time ≤ t ∧ t ≤ ev.time + interruptedRepairBudget T G ΔF ρbar kind ∧
      StrongServedFG R S E rho O T I pair Jst leaseSlots m t)

theorem InterruptedRepairStatementFG_def (G ΔF ρbar : Time) :
    InterruptedRepairStatementFG R S E rho O T I pair Jst leaseSlots deltaT G ΔF ρbar ↔
  deltaT = 2 * T.roundSlots → LivenessBoundW T ΔF →
  ∀ i ev m kind, FrontierSearchStart R E rho O T Jst i ev m kind →
    FrontierRepairAllowance R E rho O T I Jst leaseSlots G ρbar (ev.time + 3 * T.delta) →
    ev.time + interruptedRepairBudget T G ΔF ρbar kind ≤ rho.horizon →
    FirstEffectiveBy R E rho O i
      (ev.time + interruptedRepairBudget T G ΔF ρbar kind) ∨
    FrontierRiseBy R E rho i m
      (ev.time + interruptedRepairBudget T G ΔF ρbar kind) ∨
    (∃ t, ev.time ≤ t ∧ t ≤ ev.time + interruptedRepairBudget T G ΔF ρbar kind ∧
      StrongServedFG R S E rho O T I pair Jst leaseSlots m t) := Iff.rfl

/-- The served antecedent uses holder coverage; both task horizons are unchanged. -/
def FrontierTailStatementFG (G ΔF : Time) : Prop :=
  deltaT = 2 * T.roundSlots → LivenessBoundW T ΔF →
  ∀ i ev m kind, FrontierSearchStart R E rho O T Jst i ev m kind →
    StrongServedFG R S E rho O T I pair Jst leaseSlots m ev.time →
    (ev.time + (2 * FGCompose.P T + Γ T G - 9 * T.delta) ≤ rho.horizon →
      FrontierRiseBy R E rho i m (ev.time + (2 * FGCompose.P T + Γ T G - 9 * T.delta))) ∧
    (ev.time + (FGCompose.P T - 4 * T.delta) ≤ rho.horizon →
      FirstHeightRowBy S E rho T pair m (ev.time + (FGCompose.P T - 4 * T.delta)))

theorem FrontierTailStatementFG_def (G ΔF : Time) :
    FrontierTailStatementFG R S E rho O T I pair Jst leaseSlots deltaT G ΔF ↔
  deltaT = 2 * T.roundSlots → LivenessBoundW T ΔF →
  ∀ i ev m kind, FrontierSearchStart R E rho O T Jst i ev m kind →
    StrongServedFG R S E rho O T I pair Jst leaseSlots m ev.time →
    (ev.time + (2 * FGCompose.P T + Γ T G - 9 * T.delta) ≤ rho.horizon →
      FrontierRiseBy R E rho i m (ev.time + (2 * FGCompose.P T + Γ T G - 9 * T.delta))) ∧
    (ev.time + (FGCompose.P T - 4 * T.delta) ≤ rho.horizon →
      FirstHeightRowBy S E rho T pair m (ev.time + (FGCompose.P T - 4 * T.delta))) := Iff.rfl

end AvailableChain.FGCompose
end

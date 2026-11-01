module
public import AvailableChainFGCompose.Statements.ExecutionBridges
public import AvailableChainFGCompose.Statements.SafetyStore -- shake: keep (policy)
public import AvailableChainFGCompose.Statements.FinalityReceipts
public import AvailableChainKitFG.WindowViewsDef

@[expose] public section

/-! X1e: conditional acceptance mechanics at receiver-local cuts. The PC instance supplies
these laws; P10 supplies the carrier, target, receiver guards, service and deadline. -/

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG
variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire Body : Type}
variable (R : FGCoreReads P n Base Proposal Wire) (S : FGSafetyReads P n Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V P)
variable (H : FGHistoricalReads P.State Body) (Wr : FGDependencyWireReads P Body Wire)
variable (O : FGExecutionObs V P)
variable (Ef : Electorate (Fin n)) (cfg : FGConfig) (K : Nat)

/-- One-body effect ONLY at the selected successful leaf, with carrier-finality
membership. Ordinary observations mark refused deliveries too: selecting `A` explicitly
requires its successful effect. F retention still covers every later microstep. -/
structure FGAcceptanceEffectLaws (x : V) (W : FGBlock (Fin n)) (d : Time)
    (A : FGSelectedAcceptance R S E rho H Wr O
      (SimplexFG.Window.update_finality Ef cfg K) x W d) : Prop where
  leaf : (R.core (O.cutState x (A.step + 1))).fg =
      SimplexFG.Window.update_finality Ef cfg K
        { (R.core (O.cutState x A.step)).fg with
          TF := insert W (R.core (O.cutState x A.step)).fg.TF } W ∧
    (SimplexFG.Window.derive Ef cfg K W).F ∈
      insert W (R.core (O.cutState x A.step)).fg.TF
  finality : FGObservedFinalityLaws R rho O

/-- Receiver guards at the accepting leaf, never at the original receipt event. Prior
coverage at this leaf is a separate case and does not require the J or height guards. -/
structure FGAcceptanceGuards (x : V) (k : Nat) (W U : FGBlock (Fin n)) : Prop where
  invariant : FGStoreInvariant (KitFG.Window.certificateHeight Ef cfg K)
    (KitFG.Window.certificateFinality Ef cfg K) (R.core (O.cutState x k)).fg
  finCmp : FGBlock.Preceq (R.core (O.cutState x k)).fg.F U ∨
    FGBlock.Preceq U (R.core (O.cutState x k)).fg.F
  jPath : ¬ FGBlock.Preceq U (R.core (O.cutState x k)).fg.F →
    FGBlock.Preceq (R.core (O.cutState x k)).fg.J W ∨
      (R.core (O.cutState x k)).fg.h_j < (SimplexFG.Window.derive Ef cfg K W).h_j
  cap : ¬ FGBlock.Preceq U (R.core (O.cutState x k)).fg.F →
    max (R.core (O.cutState x k)).fg.h_max (SimplexFG.Window.derive Ef cfg K W).h ≤
      (SimplexFG.Window.derive Ef cfg K W).h + 1

/-- F at the actual strict event-prefix read. This is a coverage conclusion; it does not
assert that a receipt or an accepting operation exists. -/
def AcceptsFinalBefore_obs (x : V) (U : FGBlock (Fin n)) (d : Time) : Prop :=
  FGBlock.Preceq U (R.core (obsStrictState O rho x d)).fg.F

omit [DecidableEq V] in
theorem AcceptsFinalBefore_obs_def (x : V) (U : FGBlock (Fin n)) (d : Time) :
    AcceptsFinalBefore_obs R rho O x U d =
      FGBlock.Preceq U (R.core (obsStrictState O rho x d)).fg.F := rfl

/-- Strict acceptance of the selected carrier at its actual leaf, its consequence at the
deadline read, and retention to any later bounded cut of this same receiver. -/
def AcceptBeforeDriverStatement : Prop :=
  ¬ Ef.IsQuorum ∅ → 2 ≤ K → FGExecutionObsLaws E rho O →
  V2.D.ScheduleWellFormed E rho →
  ∀ x W U d (A : FGSelectedAcceptance R S E rho H Wr O
      (SimplexFG.Window.update_finality Ef cfg K) x W d),
    FGAcceptanceEffectLaws R S E rho H Wr O Ef cfg K x W d A →
    d ≤ rho.horizon → FGBlock.Preceq U (SimplexFG.Window.derive Ef cfg K W).F →
    FGAcceptanceGuards R O Ef cfg K x A.step W U →
    A.token.receiptTime < d ∧
    FGBlock.Preceq U (R.core (O.cutState x (A.step + 1))).fg.F ∧
    AcceptsFinalBefore_obs R rho O x U d ∧
    ∀ k, A.step < k → k ≤ O.cutLength x →
      FGBlock.Preceq U (R.core (O.cutState x k)).fg.F

theorem AcceptBeforeDriverStatement_def :
    AcceptBeforeDriverStatement R S E rho H Wr O Ef cfg K =
      (¬ Ef.IsQuorum ∅ → 2 ≤ K → FGExecutionObsLaws E rho O →
      V2.D.ScheduleWellFormed E rho →
      ∀ x W U d (A : FGSelectedAcceptance R S E rho H Wr O
          (SimplexFG.Window.update_finality Ef cfg K) x W d),
        FGAcceptanceEffectLaws R S E rho H Wr O Ef cfg K x W d A →
        d ≤ rho.horizon → FGBlock.Preceq U (SimplexFG.Window.derive Ef cfg K W).F →
        FGAcceptanceGuards R O Ef cfg K x A.step W U →
        A.token.receiptTime < d ∧
        FGBlock.Preceq U (R.core (O.cutState x (A.step + 1))).fg.F ∧
        AcceptsFinalBefore_obs R rho O x U d ∧
        ∀ k, A.step < k → k ≤ O.cutLength x →
          FGBlock.Preceq U (R.core (O.cutState x k)).fg.F) := rfl

/-- The pending fold and acceptance use the identical carrier, target and selected token.
The fold is the accepted pure window predicate; no search or finality claim is assumed. -/
def FinalizePendingDriverStatement : Prop :=
  ¬ Ef.IsQuorum ∅ → 2 ≤ K → FGExecutionObsLaws E rho O →
  V2.D.ScheduleWellFormed E rho →
  ∀ x y U X d (A : FGSelectedAcceptance R S E rho H Wr O
      (SimplexFG.Window.update_finality Ef cfg K) x X d),
    FGAcceptanceEffectLaws R S E rho H Wr O Ef cfg K x X d A →
    d ≤ rho.horizon → PendingFold_W Ef cfg K y U X →
    FGAcceptanceGuards R O Ef cfg K x A.step X U →
    A.token.receiptTime < d ∧
    FGBlock.Preceq U (R.core (O.cutState x (A.step + 1))).fg.F ∧
    AcceptsFinalBefore_obs R rho O x U d ∧
    ∀ k, A.step < k → k ≤ O.cutLength x →
      FGBlock.Preceq U (R.core (O.cutState x k)).fg.F

theorem FinalizePendingDriverStatement_def :
    FinalizePendingDriverStatement R S E rho H Wr O Ef cfg K =
      (¬ Ef.IsQuorum ∅ → 2 ≤ K → FGExecutionObsLaws E rho O →
      V2.D.ScheduleWellFormed E rho →
      ∀ x y U X d (A : FGSelectedAcceptance R S E rho H Wr O
          (SimplexFG.Window.update_finality Ef cfg K) x X d),
        FGAcceptanceEffectLaws R S E rho H Wr O Ef cfg K x X d A →
        d ≤ rho.horizon → PendingFold_W Ef cfg K y U X →
        FGAcceptanceGuards R O Ef cfg K x A.step X U →
        A.token.receiptTime < d ∧
        FGBlock.Preceq U (R.core (O.cutState x (A.step + 1))).fg.F ∧
        AcceptsFinalBefore_obs R rho O x U d ∧
        ∀ k, A.step < k → k ≤ O.cutLength x →
          FGBlock.Preceq U (R.core (O.cutState x k)).fg.F) := rfl

end AvailableChain.FGCompose
end

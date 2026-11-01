module
public import AvailableChainFGCompose.Statements.Channels -- shake: keep (re-export)
public import AvailableChainFGCompose.Statements.Bounds
public import AvailableChainFGCompose.Statements.FinalityHistory -- shake: keep (re-export)

@[expose] public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads P n Base Proposal Wire) (S : FGSafetyReads P n Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V P)
variable (H : FGHeightView (Fin n)) (T : FGTiming)
variable (pair : Wire → NamedHeightPair)

/-- The target case excludes timeout; progress retains either original bit. -/
inductive RowKind | target | progress

/-- Exact wire pair, before decoding. -/
def NamesEntry (kind : RowKind) (a : Wire) (height : Nat) (U : FGBlock (Fin n)) : Prop :=
  match kind with
  | .target => pair a = .vote height U.root false
  | .progress => ∃ timeout, pair a = .vote height U.root timeout

/-- One entry root for all actual sources at the selected action. -/
def OpeningEntry (r height : Nat) : Prop := ∃ e, ∀ x K, x ∈ rho.honest →
  actionSourceFG R E rho T x r = some (some K) → (H K).h = height ∧ (H K).T_h.root = e

/-- Earlier-or-current signed coverage at the actual source read. -/
def OpeningCovered (r : Nat) (Q : Block) : Prop := ∀ x ∈ rho.honest,
  ∃ K nd j rSent a, postClock E rho x (T.action r) = some nd ∧
    actionSourceFG R E rho T x r = some (some K) ∧ K ∈ (R.core nd).fg.TF ∧
    Block.Preceq Q (R.erase K) ∧ rSent ≤ r ∧ HonestRowAt S E rho T j x rSent a ∧
    namedEntry (pair a) = some ((H K).h, (H K).T_h.root)

/-- A batch fixes the original source, send index, round, and wire for each identity. -/
def FixedRows (r height : Nat) (Q : Block) (U : FGBlock (Fin n)) : Prop :=
  ∀ x ∈ rho.honest, ∃ K nd j rSent a,
    postClock E rho x (T.action r) = some nd ∧
    actionSourceFG R E rho T x r = some (some K) ∧ K ∈ (R.core nd).fg.TF ∧
    Block.Preceq Q (R.erase K) ∧ FGBlock.Preceq U K ∧ K.slot ≤ r * T.roundSlots ∧
    (H K).h = height ∧ (H K).T_h = U ∧ rSent ≤ r ∧ HonestRowAt S E rho T j x rSent a ∧
    NamesEntry pair .progress a height U

/-- The full gap window and the same honest slot, through its gate deadline. -/
def PromotionGap (I : V2.D.Interface P) (G : Time) (r : Nat) : Prop :=
  (r : Time) * FGCompose.P T + 2 * FGCompose.P T - 4 * T.delta + G ≤ rho.horizon ∧
  ∃ s, (r : Time) * FGCompose.P T + 2 * FGCompose.P T ≤ T.proposal s ∧
    T.proposal s ≤ T.action r + 2 * FGCompose.P T + Γ T G - 10 * T.delta ∧
    Gen.V2.Duty.HonestSlot rho I s ∧
    T.gate s ≤ T.action r + 2 * FGCompose.P T + Γ T G - 4 * T.delta

/-- Inclusive deadline bounds for the selected earlier send. -/
def PromotionRowDeadline (deltaF : Time) (r rSent : Nat) (s : Slot) : Prop :=
  max (T.action rSent) E.t_GST + deltaF ≤ T.action r + deltaF ∧
  T.action r + deltaF ≤ carrierTimeW T deltaF r ∧
  carrierTimeW T deltaF r ≤ ((r : Time) + 1) * FGCompose.P T ∧
  max (T.action rSent) E.t_GST + deltaF ≤ T.proposal s ∧
  max (T.action r) E.t_GST + deltaF ≤ T.proposal s ∧ r * T.roundSlots + 2 ≤ s

/-- The strict trigger adds a full period before the proposal read. -/
def PromotionRowDeadlineStrict (deltaF : Time) (r rSent : Nat) (s : Slot) : Prop :=
  max (T.action rSent) E.t_GST + deltaF ≤ T.action r + deltaF ∧
  T.action r + deltaF ≤ carrierTimeW T deltaF r ∧
  carrierTimeW T deltaF r ≤ ((r : Time) + 1) * FGCompose.P T ∧
  ((r : Time) + 1) * FGCompose.P T < T.proposal s

/-- The age trigger retains the selected honest slot and both actual deadlines. -/
def PromotionAgeGap (I : V2.D.Interface P) (G deltaF : Time) (r : Nat) (q : Slot) : Prop :=
  let U_F := max ((r : Time) * FGCompose.P T + betaF T deltaF - 4 * T.delta)
    (T.proposal q + 2 * FGCompose.P T - 4 * T.delta)
  U_F + G ≤ rho.horizon ∧ ∃ s, U_F < T.proposal s ∧ T.proposal s ≤ U_F + Γ T G ∧
    Gen.V2.Duty.HonestSlot rho I s ∧
    T.proposal s + T.delta ≤ max (T.action r + Γ T G - T.delta + epsF T deltaF)
      (T.proposal q + 2 * FGCompose.P T + Γ T G - 3 * T.delta) ∧
    T.gate s ≤ max (T.action r + Γ T G + 4 * T.delta + epsF T deltaF)
      (T.proposal q + 2 * FGCompose.P T + Γ T G + 2 * T.delta)

end AvailableChain.FGCompose
end

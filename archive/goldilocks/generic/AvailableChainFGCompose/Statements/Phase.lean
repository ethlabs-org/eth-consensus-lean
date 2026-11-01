module
public import AvailableChainFGCompose.Statements.Observations -- shake: keep (re-export)
public import AvailableChainFGCompose.Statements.Timing -- shake: keep (re-export)
public import AvailableChainFGCompose.Statements.ResetCut

@[expose] public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads P n Base Proposal Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V P)
variable (O : FGObservationReads R) (T : FGTiming) (Jst : Time)
variable (voterBlocks : P.State → Slot → Finset (FGBlock (Fin n)))

/-- DC: INTENTIONAL. Cumulative evidence gives gap, top J, or contest. -/
inductive PhaseKind | gap | topJ | contest

/-- P0d1: SAME fieldwise phase observation. -/
def TopEvidence (i m : Nat) : Prop := ∃ x, x ∈ rho.honest ∧
  (R.core (V2.D.Run.stateBefore E rho i x)).fg.h_j + 1 = m

/-- P0d1: SAME fieldwise phase observation. -/
def ContestEvidence (i m : Nat) : Prop := ∃ x, x ∈ rho.honest ∧
  (O.controls (V2.D.Run.stateBefore E rho i x)).H = m ∧
  (O.controls (V2.D.Run.stateBefore E rho i x)).contest = true

/-- P0d1: SAME fieldwise phase observation. -/
def EffectiveEvent (i : Nat) : Prop :=
  frontierAtIdx R E rho i < frontierAtIdx R E rho (i + 1) ∨
  (let m := frontierAtIdx R E rho (i + 1)
   (¬ TopEvidence R E rho i m ∧ TopEvidence R E rho (i + 1) m) ∨
   (¬ ContestEvidence R E rho O i m ∧ ContestEvidence R E rho O (i + 1) m))

/-- P0d1: SAME fieldwise phase observation. -/
def AttemptPhaseAt (i m : Nat) (kind : PhaseKind) : Prop :=
  match kind with
  | .gap => ¬ TopEvidence R E rho i m ∧ ¬ ContestEvidence R E rho O i m
  | .topJ => TopEvidence R E rho i m ∧ ¬ ContestEvidence R E rho O i m
  | .contest => ContestEvidence R E rho O i m

/-- DC: INTENTIONAL. The F-root case retains an accepted finality carrier. -/
def SettledPhaseFrame (nd : P.State) (m : Nat)
    (J : Option (FGBlock (Fin n))) (contested : Bool) : Prop :=
  let frame := O.controls nd
  frame.H = m ∧ frame.contest = contested ∧ frame.lo = (if contested then m else m - 1) ∧
  (match J with
   | some B => frame.rootIsJ = true ∧ frame.J = B ∧ frame.Z = B ∧
       frame.j + 1 = m ∧ contested = false ∧ FGBlock.Preceq (R.core nd).fg.F B
   | none => frame.rootIsJ = false ∧ frame.Z = (R.core nd).fg.F ∧
       (∃ K ∈ (R.core nd).fg.TF, (O.finality K).F = (R.core nd).fg.F ∧
         (O.finality K).h_F < frame.lo) ∧
       ((contested = false ∧ frame.j + 2 ≤ m) ∨
         (contested = true ∧ frame.j + 1 = m))) ∧
  (∃ W ∈ (R.core nd).fg.TF, (O.height W).h = m ∧ FGBlock.Preceq frame.Z W)

/-- DC: INTENTIONAL. The interval fixes phase bits, not the lower F root. -/
def PhaseInterval (u v : Time) (m : Nat) (J : Option (FGBlock (Fin n)))
    (contested : Bool) : Prop := u ≤ v ∧ v ≤ rho.horizon ∧ 1 ≤ m ∧
  ∀ i x, V2.D.Run.idxBefore rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
    let R := O.controls (V2.D.Run.stateBefore E rho i x)
    R.H = m ∧ R.contest = contested ∧
      (match J with | some B => R.rootIsJ = true ∧ R.J = B | none => R.rootIsJ = false)

/-- DC: INTENTIONAL. All five frozen phase clauses, with explicit recovery start. -/
def RPhase : Prop :=
  (∀ a b m, a ≤ b → b ≤ rho.events.length → 1 ≤ m →
    (∀ i, a ≤ i → i ≤ b → frontierAtIdx R E rho i = m) →
    (∀ i j, a ≤ i → i ≤ j → j ≤ b →
      (TopEvidence R E rho i m → TopEvidence R E rho j m) ∧
      (ContestEvidence R E rho O i m → ContestEvidence R E rho O j m)) ∧
    (∀ i, a ≤ i → i ≤ b →
      ContestEvidence R E rho O i m → TopEvidence R E rho i m)) ∧
  (∀ i ev x W m, rho.events[i]? = some ev → x ∈ rho.honest →
    Jst ≤ ev.time → 1 ≤ m → frontierAtIdx R E rho (i + 1) = m →
    W ∉ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF →
    W ∈ (R.core (V2.D.Run.stateBefore E rho (i + 1) x)).fg.TF → (O.height W).h = m →
    (ev.time + T.delta ≤ rho.horizon → ∀ y ∈ rho.honest,
      ∃ j, i < j ∧ j ≤ rho.events.length ∧
        (∀ l e, l < j → rho.events[l]? = some e → e.time < ev.time + T.delta) ∧
        (W ∈ (R.core (V2.D.Run.stateBefore E rho j y)).fg.TF ∨ m < frontierAtIdx R E rho j)) ∧
    (∀ y s nd, y ∈ rho.honest → ev.time + 3 * T.delta ≤ T.vote s →
      T.vote s ≤ rho.horizon →
      postClock E rho y (T.vote s) = some nd →
      (∃ j, i < j ∧ j ≤ timeIdx rho (T.vote s) ∧
        m < frontierAtIdx R E rho j) ∨ W ∈ voterBlocks nd s)) ∧
  (∀ i ev v m kind, rho.events[i]? = some ev → EffectiveEvent R E rho O i →
    Jst ≤ ev.time → ev.time + 3 * T.delta ≤ v → v ≤ rho.horizon → 1 ≤ m →
    frontierAtIdx R E rho (i + 1) = m → AttemptPhaseAt R E rho O (i + 1) m kind →
    (∀ j, i < j → j < timeIdx rho v → ¬ EffectiveEvent R E rho O j) →
    ∃ J,
      let root := match kind with | .topJ => some J | _ => none
      let contested := match kind with | .contest => true | _ => false
      PhaseInterval R E rho O (ev.time + 3 * T.delta) v m root contested ∧
      (∀ y s nd, y ∈ rho.honest → ev.time + 3 * T.delta ≤ T.vote s →
        T.vote s ≤ v →
        postClock E rho y (T.vote s) = some nd →
        SettledPhaseFrame R O nd m root contested)) ∧
  (∀ u v m J contested, Jst ≤ u → PhaseInterval R E rho O u v m J contested →
    ∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
      SettledPhaseFrame R O (V2.D.Run.stateBefore E rho i x) m J contested) ∧
  (∀ i x m (X : Finset (FGBlock (Fin n))) B, x ∈ rho.honest →
    i ≤ rho.events.length → 1 ≤ m → (O.controls (V2.D.Run.stateBefore E rho i x)).H = m →
    X ⊆ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF → B ∈ X →
    (∀ A, FGBlock.Preceq A B → A ∈ X) → (O.height B).h = m →
    FGBlock.Preceq (O.controls (V2.D.Run.stateBefore E rho i x)).Z B ∧
      B ∈ O.viable (V2.D.Run.stateBefore E rho i x) X)

end AvailableChain.FGCompose
end

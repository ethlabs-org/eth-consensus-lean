module
public import AvailableChainFGSAClaims.Statements.Join
public import AvailableChainFGSA.Statements.WindowEntries

@[expose] public section

namespace AvailableChain.FGSA.Run

open Gen.Pure
open AvailableChain.SimplexFG AvailableChain.FGSA.Window
variable (p : Params) {In : Type} (c : AppCodec In)

abbrev WinSpec (Pt : Type) := ∀ {V : Type} [DecidableEq V] [Fintype V],
  Generic.Env V → V2.D.Run V (fgsa p c) → Pt → Time → Prop

structure PtB₀ where
  b₀ : Time
structure PtT where
  t : Time
structure PtOut where
  T : Time
  b₀ : Time
  b₁ : Time

/-- Emission and strict acceptance precede the deadline; the gate is within the bound. -/
def cleanWinAt {V : Type} [DecidableEq V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (s : Slot) (bound : Time) : Prop :=
  ∃ (B : Block) (o : (fgsa p c).Object),
    HonestProposal E rho (fgsaInterface p c) s B ∧
    V2.D.Run.emits E rho (V2.D.proposerOf rho (fgsaInterface p c) s) o
      (V2.D.proposalTime (fgsaInterface p c) s) ∧
    (fgsaInterface p c).block o.payload = some B ∧
    (∀ w ∈ rho.honest,
      joinedAt p E rho w s (SA.voteTime p.toParams s) →
      ∃ i t', V2.D.proposalTime (fgsaInterface p c) s ≤ t' ∧
      t' < max (V2.D.proposalTime (fgsaInterface p c) s) E.t_GST + E.Δ ∧
      V2.D.Run.acceptsAt E rho i w o t') ∧
    SA.gateTime p.toParams s ≤ bound

def cleanWin : WinSpec p c Unit := fun E rho _ H =>
  ∃ s, H ≤ V2.D.proposalTime (fgsaInterface p c) s ∧ cleanWinAt p c E rho s rho.horizon

def cleanPrefixWin : WinSpec p c PtB₀ := fun E rho pt H =>
  ∃ s, H ≤ V2.D.proposalTime (fgsaInterface p c) s ∧ cleanWinAt p c E rho s pt.b₀

def cleanLabelWin {Pt : Type} (sOf : Pt → Slot) : WinSpec p c Pt := fun E rho pt H =>
  H ≤ V2.D.proposalTime (fgsaInterface p c) (sOf pt) ∧ cleanWinAt p c E rho (sOf pt) rho.horizon

def gapWinReady {Pt : Type} (G : Time) : WinSpec p c Pt := fun E rho _ H =>
  ∃ t, max (recoveryStart p E) H ≤ t ∧ t + G ≤ rho.horizon

/-- The time-start recurrence window; it is not the discrete recurrence converse. -/
def formWinAtReady {Pt : Type} (g : Nat) : WinSpec p c Pt := fun E rho _ H =>
  ∃ t, max (recoveryStart p E) 1 ≤ t ∧ H ≤ t ∧ windowEndAtA p.R (P p) p.Δ t g ≤ rho.horizon

def kernelWin {Pt : Type} (rOf : Pt → Nat) (dl : Nat → Time) : WinSpec p c Pt :=
  fun _ rho pt H => H ≤ (rOf pt : Time) * P p ∧ dl (rOf pt) ≤ rho.horizon

def trigWin (dl : Time → Time) : WinSpec p c PtT := fun _ rho pt H =>
  H ≤ pt.t ∧ dl pt.t ≤ rho.horizon

/-- An accepted honest proposal with gate at or before T, and a nonempty
outage interval with an honest node asleep. The regime supplies b₁ ≤ horizon. -/
def outWin : WinSpec p c PtOut := fun E rho pt H =>
  (∃ s, H ≤ V2.D.proposalTime (fgsaInterface p c) s ∧ cleanWinAt p c E rho s pt.T) ∧
  pt.b₀ < pt.b₁ ∧
  ∃ v ∈ rho.honest, ∃ t, pt.b₀ ≤ t ∧ t < pt.b₁ ∧ E.awake v t = false

/-- [bp 22:1265–1272; plan item 12] F8-W retention, separate from carriage.
A is the final-action anchor. The causal producer supplies the cap h(P) ≤ d + 3
from the actual action and terminal carrier. The latest protected key
is (d + 1, U). K_W ≥ 2 excludes eviction; finality can already cover the key.
This contract does not claim that the causal producer or carriage is proved. -/
def TerminalRetention_W (p : Params) : Prop :=
  ∀ (A P : FGBlock (Fin p.n)) (d : Nat) (U : FGBlock (Fin p.n)),
    FGBlock.Preceq A P → RetainedW p A (d + 1) U →
    ((heightView p A).h_j, (heightView p A).J) = (d + 1, U) →
    (heightView p P).h ≤ d + 3 →
    RetainedW p P (d + 1) U ∨ CoveredW p P (d + 1) U

theorem TerminalRetention_W_def (p : Params) :
    TerminalRetention_W p =
      (∀ (A P : FGBlock (Fin p.n)) (d : Nat) (U : FGBlock (Fin p.n)),
        FGBlock.Preceq A P → RetainedW p A (d + 1) U →
        ((heightView p A).h_j, (heightView p A).J) = (d + 1, U) →
        (heightView p P).h ≤ d + 3 →
        RetainedW p P (d + 1) U ∨ CoveredW p P (d + 1) U) := rfl

end AvailableChain.FGSA.Run
end

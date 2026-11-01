module
-- shake: keep-all (F0.5 imports must remain unchanged in this append-only job)
public import Mathlib.Order.Lattice.Nat
public import AvailableChainFGSAClaims.Statements.Channels

@[expose] public section

/-! F0.5: the common witness of 21 H.22 and 22 §1.
F0.8b adds muOf, high, H0 and tstarOf below these declarations. -/

namespace AvailableChain.FGSA.Run

/-- The common tuple (21 H.22:3001–3003; 22 §1:183–185).
`b` is `sStar`; μ is a run function, not a field (21:3006–3009; 22:188–191).
The H0 constraints on these data are added in F0.8b. -/
structure HealingWitness where
  /-- First action round at or after recoveryStart (21 H.22:3046–3047; 22 §1:228–229). -/
  rG : Nat
  /-- Inclusive cut a_(r_G+2) (21 H.22:3047; 22 §1:229). -/
  u₀ : Time
  /-- Maximum honest height at u₀ (21 H.22:3048; 22 §1:230). -/
  M : Nat
  /-- First round with an honest row at height M+1 (21 H.22:3051–3052; 22 §1:233–234). -/
  rStar : Nat
  /-- Slot r*R, also the label b (21 H.22:3052; 22 §1:234). -/
  sStar : Slot
  /-- Actual fresh source of that row (21 H.22:3052–3053; 22 §1:234–235). -/
  CStar : Block
  /-- First honest proposal slot at least s*+2 (21 H.22:3054; 22 §1:236). -/
  u : Slot
  /-- Block of that honest proposal (21 H.22:3054–3055; 22 §1:236–237). -/
  QStar : Block

/-- Healing starts at d_u (21 H.22:3054; 22 §1:236). -/
def tstar (p : Params) (w : HealingWitness) : Time := SA.gateTime p.toParams w.u

-- equation export required by BUILD §7.2 B3a (post-freeze additive _def batch)
theorem tstar_def (p : Params) (w : HealingWitness) :
    tstar p w = SA.gateTime p.toParams w.u := rfl


open AvailableChain.SimplexFG
variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- H.11 (21:1579–1582), L6: heights of NONEMPTY signed honest rows
whose source vote precedes recoveryStart. Consumers: muOf, H0Reset, H.13. -/
def oldRowHeights : Set Nat := {h | ∃ j y r, ∃ (a : RowWire p.n) (e : BlockId),
  HonestRowAt p c E rho j y r a ∧ namedEntry a.payload.height_pair = some (h, e) ∧
    SA.voteTime p.toParams (r * p.R) < recoveryStart p E}
/-- H.11 μ (21:1579–1582), P3 §4.6 and A.8. Consumers: H0Reset and H.13. -/
noncomputable def muOf : Nat := max 1 (sSup (oldRowHeights p c E rho))
/-- H.22 (21:3002–3004), P3 A.6. Consumers: H1, H2, H2.A, F9 and HP. -/
def high (w : HealingWitness) (C : FGBlock (Fin p.n)) : Prop :=
  w.M + 1 ≤ (heightView p C).h
/-- Inclusive honest frontier (21 H.11:1574–1576).
Consumers: H0Reset and the canonical reset read. -/
def honestFrontier (t : Time) : Nat :=
  rho.honest.sup (fun x => (V2.D.Run.readAt E rho t x).st.fg.h_max)
/-- An emitted nonempty honest height row (21 H.11:1584–1587).
Consumers: H0Reset and reset uniqueness. -/
def HeightRow (r h : Nat) : Prop := ∃ j y, ∃ (a : RowWire p.n) (e : BlockId),
  HonestRowAt p c E rho j y r a ∧ namedEntry a.payload.height_pair = some (h, e)

/-- H.11 reset part (21:1572–1595; H.22:3046–3053), P3 A.8/A.10.
Consumers: reset arrival, H.12–H.17, and H0. This contains no Q* service.
Full H0 requires ResetArrivalFullStatement at the H.18 horizon (21:2868–2876). -/
structure H0Reset (w : HealingWitness) : Prop where
  rG_after : recoveryStart p E ≤ p.actionTime w.rG
  rG_first : ∀ r, recoveryStart p E ≤ p.actionTime r → w.rG ≤ r
  cut : w.u₀ = p.actionTime (w.rG + 2)
  frontier : w.M = honestFrontier p c E rho w.u₀
  rowCap : ∀ j y r a h e t, HonestRowAt p c E rho j y r a →
    rho.events[j]? = some (.tick y t) → t ≤ w.u₀ →
    namedEntry a.payload.height_pair = some (h, e) → h ≤ w.M
  mu_le : muOf p c E rho ≤ w.M
  cut_lower : recoveryStart p E + 2 * P p ≤ w.u₀
  cut_upper : w.u₀ < recoveryStart p E + 3 * P p
  reset_row : HeightRow p c E rho w.rStar (w.M + 1)
  reset_first : ∀ r, HeightRow p c E rho r (w.M + 1) → w.rStar ≤ r
  label : w.sStar = w.rStar * p.R
  fresh : ∃ j y, ∃ (a : RowWire p.n) (C : FGBlock (Fin p.n)),
    HonestRowAt p c E rho j y w.rStar a ∧
    namedEntry a.payload.height_pair = some (w.M + 1, (heightView p C).T_h.root) ∧
    actionSourceFG p c E rho y w.rStar = some (some C) ∧
    eraseFG C = w.CStar ∧ (heightView p C).h = w.M + 1
  synchronous : E.t_GST ≤ SA.voteTime p.toParams w.sStar

/-- Full H0 (21 H.22:3044–3055): H.11 reset plus H.18 proposal
(21:2868–2876; 3174–3176). Consumers: HealingInput, tstarOf, joined kernel.
Use ResetArrivalFullStatement, not the reset-only arrival horizon. -/
structure H0 (w : HealingWitness) : Prop extends H0Reset p c E rho w where
  proposal_lower : w.sStar + 2 ≤ w.u
  proposal : HonestProposal E rho (fgsaInterface p c) w.u w.QStar
  proposal_first : ∀ v Q, w.sStar + 2 ≤ v →
    HonestProposal E rho (fgsaInterface p c) v Q → w.u ≤ v
  after_gst : E.t_GST ≤ tstar p w
  source_prefix : Block.Preceq w.CStar w.QStar

/-- Canonical full-H0 time (P3 D44; 21 H.18:2868–2876).
Consumer: joined kernel. No full witness gives no time. -/
noncomputable def tstarOf : Option Time := by
  classical
  exact if h : ∃ w, H0 p c E rho w then some (tstar p (Classical.choose h)) else none

-- equation export required by BUILD §7.2 B3a (post-freeze additive _def batch)
theorem muOf_def : muOf p c E rho = max 1 (sSup (oldRowHeights p c E rho)) := rfl
-- equation export required by BUILD §7.2 B3a (post-freeze additive _def batch)
theorem high_def (w : HealingWitness) (C : FGBlock (Fin p.n)) :
    high p w C = (w.M + 1 ≤ (heightView p C).h) := rfl

end AvailableChain.FGSA.Run
end

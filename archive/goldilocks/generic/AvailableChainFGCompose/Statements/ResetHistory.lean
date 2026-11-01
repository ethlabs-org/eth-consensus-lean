module
public import AvailableChainFGCompose.Statements.Channels
public import Mathlib.Order.Lattice.Nat

@[expose] public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {P : V2.ProtocolSpecD In}
variable [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads P n Base Proposal Wire)
variable (S : FGSafetyReads P n Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V P)
variable (O : FGObservationReads R) (T : FGTiming) (I : V2.D.Interface P)
variable (entry : Wire → Option (Height × BlockId))
variable (carrier : P.Object → Slot → Block → List Wire → Prop)
variable (chainWireRows : P.State → Block → List Wire)
variable (blockWireRows : P.State → List Wire)
variable (parentFG : P.State → Block → Option (FGBlock (Fin n)))
variable (validFor : P.State → Slot → (FGBlock (Fin n)) → Wire → Bool)

structure FGResetHistory where
  rG : Nat
  u0 : Time
  M : Nat
  rStar : Nat
  sStar : Slot
  source : Block

structure FGServicePoint where
  reset : FGResetHistory
  seedSlot : Slot
  seed : Block
  serviceStart : Time

-- Here HonestRowAt S E rho T and actionSourceFG R E rho T use c1's exact definitions, as above.
-- recoveryStart is an explicit Time parameter, not a protocol definition.
def oldRowHeights (recoveryStart : Time) : Set Nat :=
  {h | ∃ j y r, ∃ (a : Wire) (e : BlockId),
    HonestRowAt S E rho T j y r a ∧ entry a = some (h, e) ∧
    T.vote (r * T.roundSlots) < recoveryStart}
noncomputable def muOf (recoveryStart : Time) : Nat :=
  max 1 (sSup (oldRowHeights S E rho T entry recoveryStart))
def honestFrontier (t : Time) : Nat :=
  rho.honest.sup (fun x => (R.core (V2.D.Run.readAt E rho t x)).fg.h_max)
def HeightRow (r h : Nat) : Prop :=
  ∃ j y, ∃ (a : Wire) (e : BlockId), HonestRowAt S E rho T j y r a ∧ entry a = some (h, e)
def high (w : FGResetHistory) (C : (FGBlock (Fin n))) : Prop := w.M + 1 ≤ (O.height C).h

structure H0Reset (recoveryStart : Time) (w : FGResetHistory) : Prop where
  rG_after : recoveryStart ≤ T.action w.rG
  rG_first : ∀ r, recoveryStart ≤ T.action r → w.rG ≤ r
  cut : w.u0 = T.action (w.rG + 2)
  frontier : w.M = honestFrontier R E rho w.u0
  rowCap : ∀ j y r a h e t, HonestRowAt S E rho T j y r a →
    rho.events[j]? = some (.tick y t) → t ≤ w.u0 →
    entry a = some (h, e) → h ≤ w.M
  mu_le : muOf S E rho T entry recoveryStart ≤ w.M
  cut_lower : recoveryStart + 2 * (4 * (T.roundSlots : Time) * T.delta) ≤ w.u0
  cut_upper : w.u0 < recoveryStart + 3 * (4 * (T.roundSlots : Time) * T.delta)
  reset_row : HeightRow S E rho T entry w.rStar (w.M + 1)
  reset_first : ∀ r, HeightRow S E rho T entry r (w.M + 1) → w.rStar ≤ r
  label : w.sStar = w.rStar * T.roundSlots
  fresh : ∃ j y, ∃ (a : Wire) (C : (FGBlock (Fin n))), HonestRowAt S E rho T j y w.rStar a ∧
    entry a = some (w.M + 1, (O.height C).T_h.root) ∧
    actionSourceFG R E rho T y w.rStar = some (some C) ∧
    R.erase C = w.source ∧ (O.height C).h = w.M + 1
  synchronous : E.t_GST ≤ T.vote w.sStar

structure FGServiceStartLaws (T : FGTiming)
    (recoveryStart horizon budget : Time)
    (ResetOK : FGResetHistory → Prop)
    (SeedOK : FGResetHistory → Slot → Block → Prop)
    (pt : FGServicePoint) : Prop where
  reset_ok : ResetOK pt.reset
  seed_ok : SeedOK pt.reset pt.seedSlot pt.seed
  source_prefix : Block.Preceq pt.reset.source pt.seed
  seed_before : T.proposal pt.seedSlot ≤ pt.serviceStart
  after_recovery : recoveryStart ≤ pt.serviceStart
  bounded : pt.serviceStart < recoveryStart + budget
  horizon : pt.serviceStart ≤ horizon

end AvailableChain.FGCompose
end

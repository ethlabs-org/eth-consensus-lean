module
public import AvailableChainFGSAClaims.Statements.Packages.Safety
public import AvailableChainFGSA.Statements.Invariants


@[expose] public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.sameLabel.v1: two honest raw results at one label are compatible. -/
def SameLabelAt (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (s : Slot) : Prop :=
  ∀ x y B C, x ∈ rho.honest → y ∈ rho.honest →
    gateResult p c E rho x s = some (some B) →
    gateResult p c E rho y s = some (some C) → Block.Compatible B C

def SameLabelClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : PtS),
    SameLabelPrem p c E rho pt → SameLabelAt p c E rho pt.s

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
ap.headReachesLo.v7, pure clauses 1–3 only (21 H.3; 02 §7).
The controls and anchor are those of the full store, also for a smaller X. -/
def HeadReachesLoAt (p : Params) (st : State p.n)
    (X : Finset (FGBlock (Fin p.n))) (raw support : List (GridCO.Wire p.n .root)) : Prop :=
  let D := KitFG.filteredFromView (heightView p) (FGSA.controls p st) X
  let A := FGSA.liveRoot p st
  let H := FGSA.headInTree p st (FGSA.erasedList st D) raw support
  ((∃ B ∈ D, eraseFG B = A) ∨
      (∃ B ∈ D, (eraseFG B).parent? = some A ∧ FGSA.eligible p st raw support (eraseFG B) = true) →
    ∃ B ∈ D, eraseFG B = H ∧ (FGSA.controls p st).lo ≤ (heightView p B).h) ∧
  ((¬ ∃ B ∈ D, eraseFG B = A) →
    (∀ B ∈ D, (eraseFG B).parent? = some A → FGSA.eligible p st raw support (eraseFG B) = false) →
    H = A) ∧
  (A = eraseFG (FGSA.controls p st).Z → D.Nonempty → (FGSA.controls p st).Z ∈ D)

def HeadReachesLoClaim (p : Params) : Prop :=
  ∀ (st : State p.n) (X : Finset (FGBlock (Fin p.n)))
    (raw support : List (GridCO.Wire p.n .root)),
    Reachable p st → X ⊆ st.fg.TF →
    (∀ B ∈ X, ∀ A, FGBlock.Preceq A B → A ∈ X) →
    HeadReachesLoAt p st X raw support

/- bp.suffixWalk.v1 is the Gen.Pure statement family in Statements/Pure/Walk:
WalkCoversOfDominatedSuffixStatement, WalkExactOfDominatedSuffixStatement,
WalkReanchorOfDominatedSuffixStatement, WalkAvoidsUnsupportedChildStatement,
WalkCoversOfDominatedSuffixOfAnchorEligibleStatement,
WalkTerminalOfDescendantDepthBoundStatement,
WalkNoEligibleChildOfAnchorClosedStatement, GhostTransferSfxStatement.
GEN-FIRST: cite these statements; do not add aliases or claim wrappers. -/

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.release.v1(a,c), valid for every store without a run premise. -/
def ReleaseStoreAt (p : Params) (st : State p.n) : Prop :=
  ∀ s B,
    GridCO.releaseCount p.toParams.engine (FGSA.actView st) s B ≤
      GridCO.releaseCount p.toParams.engine st.base s B ∧
    (Block.Preceq B (eraseFG st.fg.F) →
      GridCO.releaseCount p.toParams.engine (FGSA.actView st) s B = 0)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The store-only part of bp.release.v1 has no regime premise. -/
def ReleaseStoreClaim (p : Params) : Prop := ∀ st, ReleaseStoreAt p st

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.release.v1(a–c): the store laws and the run fault bound.
The final fault-bound conjunct restates the premise ReleasePrem.lt.
The local vote premise refers to actual emissions and keeps the HEAD label. -/
def ReleaseAt (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) : Prop :=
  ReleaseStoreClaim p ∧
  ∀ i x s B, i ≤ rho.events.length → x ∈ rho.honest →
    (∀ y ∈ rho.honest, ∀ o t, V2.D.Run.emits E rho y o t →
      ∀ k H, o.auth = .seat (.base (.head s)) k →
        HeadTargetAtEmission p c E rho y o t H → Block.Compatible H B) →
    GridCO.releaseCount p.toParams.engine (FGSA.actView (storeAt p c E rho i x)) s B ≤
      (Gen.V2.Duty.faulty rho).card ∧
    (Gen.V2.Duty.faulty rho).card < SA.releaseThreshold p.toParams

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.release.v1, R5-65. The threshold producer is not a premise or conclusion. -/
def ReleaseClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
    ReleasePrem p c E rho pt → ReleaseAt p c E rho

end AvailableChain.FGSA.Run
end

module
public import AvailableChainFGSARun.Statements.AC
public import AvailableChainFGSA.Statements.Invariants
public import AvailableChainFGSAClaims.Statements.Channels
public import AvailableChainGeneric.Statements.Pure.Quorum

@[expose] public section

/-! Stage 0 final frame target (port r2, ruling A).

The canonical declarations keep their text in Stage 0. At SWITCH, `FrameClaimNext`
supplies the aggregate frame field and `FGFoundationNext.frame` supplies its foundation
frame type. `RFrameExact` and `RFrame` then have legacy status (class B).
The run binders, bounds, scopes, metadata, and admission clauses stay the same.
Only the protocol readers and their displayed expansions use the Next model:
guarded FJ controls, retained proposals/voter blocks, and retained carried support.

```text
┌────────────────────────────┬────────────────────────┬───────┐
│ Next statement             │ Canonical counterpart  │ Class │
├────────────────────────────┼────────────────────────┼───────┤
│ frameRNext                 │ frameR                 │ B     │
│ frameRNext_def             │ frameR_def             │ B     │
│ domainRNext                │ domainR                │ B     │
│ domainRNext_def            │ domainR_def            │ B     │
│ RFrameExactNext            │ RFrameExact            │ B     │
│ RFrameExactNext_def        │ RFrameExact_def        │ B     │
│ RFrameNext                 │ RFrame                 │ B     │
│ RFrameNext_def             │ RFrame_def             │ B     │
│ TStartNext                 │ TStart                 │ B     │
│ TWalkNext                  │ TWalk                  │ B     │
│ SettledPhaseFrameNext      │ SettledPhaseFrame      │ B     │
│ SettledPhaseFrameNext_def  │ SettledPhaseFrame_def  │ B     │
│ TGeomNext                  │ TGeom                  │ B     │
│ OpeningCoveredNext         │ OpeningCovered         │ B     │
│ FrameAtNext                │ FrameAt                │ B     │
│ WalkBatchNext              │ WalkBatch              │ A     │
└────────────────────────────┴────────────────────────┴───────┘
```

Canonical-to-Next classes above compare two reader meanings, not two SWITCH stages.
Before/after SWITCH: fixed Next state reads have class A under same-event transport.
`TGeomNext` and `OpeningCoveredNext` have class B (emissions/canonical source).
See docs/reports/fgsa-port-s0f00b.md for the complete class and cause records.

SWITCH deep-digest causes (canonical entry -> cause; one h+i+j switch):
* `RFrameExact`/`RFrame`, including `_def`: legacy reader attribution; source stays fixed.
* `frameR`, `domainR`, `TStart`, `TWalk`, `TGeom`, `OpeningCovered`,
  `SettledPhaseFrame` and equations: canonical reader bodies acquire guarded controls
  and the new head/merge meaning; their target statements are above.
* `FGFoundation`, `.mk`, `.frame`: frame type becomes `RFrameExactNext`.
* `FGSASafetyClaims`, `.mk`, `.frame`: frame type becomes `FrameClaimNext`.
* `FGSASafetyInterfaces`, `.mk`, `.fgFoundation`: foundation claim becomes Next.
* `CleanCutPosClaim`: only its foundation antecedent becomes Next.
* Every entry in this module (including constructors/projections) also reaches
  `fgsa` through the unchanged run binder, or `State` through a local reader.
  These deep changes do not imply class B: fixed Next reads remain class A.
  Local reader-only entries need no exception unless their actual closure changes.

WP00c measures exact old/new deep digests and dependency paths after all Stage 0
packages. These cause records are not digest allowances or a new baseline.
-/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
open Gen.Pure

variable (p : Params)

/-- Next frame surface; counterpart `frameR`, census B. -/
def frameRNext (st : State p.n) : Controls (Fin p.n) := FGSA.Next.controls p st

/-- Next frame surface; counterpart `frameR_def`, census B. -/
theorem frameRNext_def (st : State p.n) : frameRNext p st = FGSA.Next.controls p st := by
  rw [frameRNext]

/-- Next frame surface; counterpart `domainR`, census B. -/
def domainRNext (st : State p.n) (X : Finset (FGBlock (Fin p.n))) :
    Finset (FGBlock (Fin p.n)) := KitFG.filteredFromView (heightView p) (frameRNext p st) X

/-- Next frame surface; counterpart `domainR_def`, census B. -/
theorem domainRNext_def (st : State p.n) (X : Finset (FGBlock (Fin p.n))) :
    domainRNext p st X = KitFG.filteredFromView (heightView p) (frameRNext p st) X := by
  rw [domainRNext]

variable {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- Next frame surface; counterpart `RFrameExact`, census B. -/
def RFrameExactNext : Prop := ∀ i x, x ∈ rho.honest →
  let st := storeAt p c E rho i x
  FGSA.Next.controls p st = KitFG.treeFjControlsView (heightView p) st.fg.F st.fg.TF ∧
  FGSA.Next.fullTree p st = domainRNext p st st.fg.TF

/-- Next frame surface; counterpart `RFrameExact_def`, census B. -/
theorem RFrameExactNext_def :
    RFrameExactNext p c E rho = (∀ i x, x ∈ rho.honest →
  let st := storeAt p c E rho i x
  FGSA.Next.controls p st = KitFG.treeFjControlsView (heightView p) st.fg.F st.fg.TF ∧
  FGSA.Next.fullTree p st = domainRNext p st st.fg.TF) := rfl

/-- Next frame surface; counterpart `RFrame`, census B. -/
def RFrameNext : Prop := ∀ i x, x ∈ rho.honest →
  let st := storeAt p c E rho i x
  (∀ s N P, namedParentHeld st N = true → parentFG st N.erase = some P →
    blockAccepted p st s N P = true →
    (admitBlock p st s N).fg = Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)) ∧
  ((∀ f : GridCO.State p.n .root → GridCO.State p.n .root, (onView f st).fg = st.fg) ∧
    (∀ s k b, (admitHead p st s k b).fg = st.fg) ∧
    (∀ a, (admitRow p st a).fg = st.fg) ∧
    (∀ t, (FGSA.clock p st t).fg = st.fg) ∧
    (∀ s N,
      (namedParentHeld st N = false ∨ parentFG st N.erase = none ∨
        ∃ P, parentFG st N.erase = some P ∧ blockAccepted p st s N P = false) →
      (admitBlock p st s N).fg = st.fg) ∧
    (∀ o, o.decode = none → (FGSA.process p st o).fg = st.fg)) ∧
  (FGSA.Next.controls p (FGSA.reconcile st) = FGSA.Next.controls p st ∧
    ∀ X, domainRNext p (FGSA.reconcile st) X = domainRNext p st X) ∧
  (MetaInv p st ∧
    (∀ s, FGSA.Next.proposalsAtNext p st s = st.proposals.filterMap (fun o => match o.decode with
      | some (.block _ N) =>
        if N.slot = s ∧ ∃ B ∈ FGSA.Next.tree p st, eraseFG B = N.erase then
          some (N.raw, N.support) else none
      | _ => none)) ∧
    (∀ H, FGSA.Next.chainWireRowsNext st H = (st.proposals.filterMap (fun o => match o.decode with
      | some (.block _ N) => if Block.preceq N.erase H then some N.rows else none
      | _ => none)).flatten) ∧
    (FGSA.Next.blockWireRowsNext st = (st.proposals.filterMap (fun o => match o.decode with
      | some (.block _ N) => some N.rows
      | _ => none)).flatten) ∧
    (∀ s, FGSA.Next.voterBlocksNext p st s = (FGSA.Next.tree p st).filter (fun B =>
      decide (GridCO.stampBlock st.base (eraseFG B) < SA.freezeTime p.toParams (s - 1)) ||
      decide (∃ P ∈ FGSA.Next.tree p st, P.slot = s ∧ FGBlock.Preceq B P))) ∧
    (∀ s, FGSA.Next.headVotesNext p st s =
      (((GridCO.votesAt st.base (s - 1)).filter (fun o =>
        decide (GridCO.stampVote st.base o < SA.freezeTime p.toParams (s - 1)))) ++
        (((FGSA.Next.proposalsAtNext p st s).flatMap (fun row => row.1.map baseVote)).filter
          (fun o => GridCO.headLabel? o == some (s - 1)))).eraseDups) ∧
    (∀ s, FGSA.Next.headSupportNext p st s =
      (((GridCO.votesAt st.base (s - 1)).filter (fun o =>
        GridCO.resolvedBefore (FGSA.actView st) o (SA.freezeTime p.toParams (s - 1)))) ++
        (((FGSA.Next.proposalsAtNext p st s).flatMap (fun row => row.2.map baseVote)).filter
          (fun o =>
          GridCO.headLabel? o == some (s - 1) && match GridCO.resolvedHead? st.base o with
          | some h => decide (∃ B ∈ FGSA.Next.tree p st, eraseFG B = h) &&
              decide (h.slot ≤ s - 1)
          | none => false))).eraseDups) ∧
    (∀ H, FGSA.Next.proposalRowsNext p st H =
      match FGSA.Next.fgBlockOfNext st H with
      | none => []
      | some P =>
          (st.rowPool ++ FGSA.Next.blockWireRowsNext st).eraseDups.filter (fun a =>
            Window.rowValidW (parentFoldState p (st.slot p) P) a &&
              !decide (a ∈ FGSA.Next.chainWireRowsNext st H))) ∧
    (V2.D.NoRestart rho → ∀ j, i ≤ j → j ≤ rho.events.length →
      let st' := storeAt p c E rho j x
      st.proposals <+: st'.proposals ∧ st.rowPool <+: st'.rowPool ∧
      st.base.blockStamp <+: st'.base.blockStamp ∧ st.base.voteStamp <+: st'.base.voteStamp))

/-- Next frame surface; counterpart `RFrame_def`, census B. -/
theorem RFrameNext_def : RFrameNext p c E rho =
  (∀ i x, x ∈ rho.honest →
  let st := storeAt p c E rho i x
  (∀ s N P, namedParentHeld st N = true → parentFG st N.erase = some P →
    blockAccepted p st s N P = true →
    (admitBlock p st s N).fg = Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)) ∧
  ((∀ f : GridCO.State p.n .root → GridCO.State p.n .root, (onView f st).fg = st.fg) ∧
    (∀ s k b, (admitHead p st s k b).fg = st.fg) ∧
    (∀ a, (admitRow p st a).fg = st.fg) ∧
    (∀ t, (FGSA.clock p st t).fg = st.fg) ∧
    (∀ s N,
      (namedParentHeld st N = false ∨ parentFG st N.erase = none ∨
        ∃ P, parentFG st N.erase = some P ∧ blockAccepted p st s N P = false) →
      (admitBlock p st s N).fg = st.fg) ∧
    (∀ o, o.decode = none → (FGSA.process p st o).fg = st.fg)) ∧
  (FGSA.Next.controls p (FGSA.reconcile st) = FGSA.Next.controls p st ∧
    ∀ X, domainRNext p (FGSA.reconcile st) X = domainRNext p st X) ∧
  (MetaInv p st ∧
    (∀ s, FGSA.Next.proposalsAtNext p st s = st.proposals.filterMap (fun o => match o.decode with
      | some (.block _ N) =>
        if N.slot = s ∧ ∃ B ∈ FGSA.Next.tree p st, eraseFG B = N.erase then
          some (N.raw, N.support) else none
      | _ => none)) ∧
    (∀ H, FGSA.Next.chainWireRowsNext st H = (st.proposals.filterMap (fun o => match o.decode with
      | some (.block _ N) => if Block.preceq N.erase H then some N.rows else none
      | _ => none)).flatten) ∧
    (FGSA.Next.blockWireRowsNext st = (st.proposals.filterMap (fun o => match o.decode with
      | some (.block _ N) => some N.rows
      | _ => none)).flatten) ∧
    (∀ s, FGSA.Next.voterBlocksNext p st s = (FGSA.Next.tree p st).filter (fun B =>
      decide (GridCO.stampBlock st.base (eraseFG B) < SA.freezeTime p.toParams (s - 1)) ||
      decide (∃ P ∈ FGSA.Next.tree p st, P.slot = s ∧ FGBlock.Preceq B P))) ∧
    (∀ s, FGSA.Next.headVotesNext p st s =
      (((GridCO.votesAt st.base (s - 1)).filter (fun o =>
        decide (GridCO.stampVote st.base o < SA.freezeTime p.toParams (s - 1)))) ++
        (((FGSA.Next.proposalsAtNext p st s).flatMap (fun row => row.1.map baseVote)).filter
          (fun o => GridCO.headLabel? o == some (s - 1)))).eraseDups) ∧
    (∀ s, FGSA.Next.headSupportNext p st s =
      (((GridCO.votesAt st.base (s - 1)).filter (fun o =>
        GridCO.resolvedBefore (FGSA.actView st) o (SA.freezeTime p.toParams (s - 1)))) ++
        (((FGSA.Next.proposalsAtNext p st s).flatMap (fun row => row.2.map baseVote)).filter
          (fun o =>
          GridCO.headLabel? o == some (s - 1) && match GridCO.resolvedHead? st.base o with
          | some h => decide (∃ B ∈ FGSA.Next.tree p st, eraseFG B = h) &&
              decide (h.slot ≤ s - 1)
          | none => false))).eraseDups) ∧
    (∀ H, FGSA.Next.proposalRowsNext p st H =
      match FGSA.Next.fgBlockOfNext st H with
      | none => []
      | some P =>
          (st.rowPool ++ FGSA.Next.blockWireRowsNext st).eraseDups.filter (fun a =>
            Window.rowValidW (parentFoldState p (st.slot p) P) a &&
              !decide (a ∈ FGSA.Next.chainWireRowsNext st H))) ∧
    (V2.D.NoRestart rho → ∀ j, i ≤ j → j ≤ rho.events.length →
      let st' := storeAt p c E rho j x
      st.proposals <+: st'.proposals ∧ st.rowPool <+: st'.rowPool ∧
      st.base.blockStamp <+: st'.base.blockStamp ∧ st.base.voteStamp <+: st'.base.voteStamp))) := by
  rw [RFrameNext]

/-- Next frame surface; counterpart `TStart`, census B. -/
def TStartNext : Prop := Gen.AC.Duty.LeaseBelowOutput (fgsaAC E rho) ∧
  ∀ i x, x ∈ rho.honest →
    let st := storeAt p c E rho i x
    FGSA.Next.liveRootNext p st = eraseFG (FGSA.Next.controls p st).Z ∨
      ∃ row ∈ st.base.obligations, st.base.now < row.2.2 ∧
        row.1 = FGSA.Next.liveRootNext p st ∧
        (∃ B ∈ FGSA.Next.fullTree p st, eraseFG B = row.1) ∧ Block.Preceq row.1 (outputS p st)

/-- Lower batch premise; counterpart `WalkBatch`, class A in both comparisons. -/
def WalkBatchNext (st : State p.n) (s : Slot) (raw support : List (GridCO.Wire p.n .root))
    (Q : Block) (seats : Finset (Fin p.n)) (m : Nat) : Prop :=
  support ⊆ raw ∧ (∀ o ∈ raw, GridCO.headLabel? o = some s) ∧
  (∀ a ∈ seats, rho.seatOf (.base (.head s)) a ∈ rho.honest ∧
    ∃ o ∈ support, o ∈ raw ∧ GridCO.headSeat? o = some a ∧
      ∃ H, GridCO.resolvedHead? st.base o = some H ∧ H.slot ≤ s ∧ Block.Preceq Q H) ∧
  ((GridCO.seats p.n raw).toFinset \ seats).card ≤ m ∧
  (∀ a ∈ seats, GridCO.equivocates raw a = false)

/-- Next frame surface; counterpart `TWalk`, census B. -/
def TWalkNext : Prop := ∀ i x s raw support Q seats m,
  x ∈ rho.honest → Batch seats.card m →
  let st := storeAt p c E rho i x
  Q ∈ FGSA.Next.fullTree p st → Block.Compatible (FGSA.Next.liveRootNext p st) (eraseFG Q) →
  WalkBatchNext p c rho st s raw support (eraseFG Q) seats m →
  Block.Preceq (eraseFG Q) (FGSA.Next.getHeadNext p st raw support) ∧
  ((∀ B ∈ FGSA.Next.fullTree p st, FGBlock.Preceq Q B → B = Q) →
    FGSA.Next.getHeadNext p st raw support = eraseFG Q) ∧
  (∀ B, Block.Prec (FGSA.Next.liveRootNext p st) B →
    Block.Preceq B (FGSA.Next.getHeadNext p st raw support) →
    (∀ a ∈ seats, ∀ o ∈ support, GridCO.headSeat? o = some a →
      ∀ H, GridCO.resolvedHead? st.base o = some H → ¬ Block.Preceq B H) →
    B.slot = st.slot p ∨ ∃ A ∈ st.fg.TF,
      eraseFG A = B.parent ∧ (heightView p A).h < (FGSA.Next.controls p st).lo)

/-- Next frame surface; counterpart `SettledPhaseFrame`, census B. -/
def SettledPhaseFrameNext (st : State p.n) (m : Nat)
    (J : Option (FGBlock (Fin p.n))) (contested : Bool) : Prop :=
  let R := FGSA.Next.controls p st
  R.H = m ∧ R.contest = contested ∧ R.lo = (if contested then m else m - 1) ∧
  (match J with
   | some B => R.rootIsJ = true ∧ R.J = B ∧ R.Z = B ∧
       R.j + 1 = m ∧ contested = false ∧ FGBlock.Preceq st.fg.F B
   | none => R.rootIsJ = false ∧ R.Z = st.fg.F ∧
       (∃ K ∈ st.fg.TF, (finalityView p K).F = st.fg.F ∧
         (finalityView p K).h_F < R.lo) ∧
       ((contested = false ∧ R.j + 2 ≤ m) ∨
         (contested = true ∧ R.j + 1 = m))) ∧
  (∃ W ∈ st.fg.TF, (heightView p W).h = m ∧ FGBlock.Preceq R.Z W)

/-- Next frame surface; counterpart `SettledPhaseFrame_def`, census B. -/
theorem SettledPhaseFrameNext_def (st : State p.n) (m : Nat)
    (J : Option (FGBlock (Fin p.n))) (contested : Bool) :
    SettledPhaseFrameNext p st m J contested =
  (  let R := FGSA.Next.controls p st
  R.H = m ∧ R.contest = contested ∧ R.lo = (if contested then m else m - 1) ∧
  (match J with
   | some B => R.rootIsJ = true ∧ R.J = B ∧ R.Z = B ∧
       R.j + 1 = m ∧ contested = false ∧ FGBlock.Preceq st.fg.F B
   | none => R.rootIsJ = false ∧ R.Z = st.fg.F ∧
       (∃ K ∈ st.fg.TF, (finalityView p K).F = st.fg.F ∧
         (finalityView p K).h_F < R.lo) ∧
       ((contested = false ∧ R.j + 2 ≤ m) ∨
         (contested = true ∧ R.j + 1 = m))) ∧
  (∃ W ∈ st.fg.TF, (heightView p W).h = m ∧ FGBlock.Preceq R.Z W)) := by rfl

/-- Next frame surface; counterpart `TGeom`, census B. -/
def TGeomNext : Prop :=
  (∀ s Q st, HonestProposal E rho (fgsaInterface p c) s Q →
    proposalStateAt p c E rho s = some st → (FGSA.Next.fullTree p st).Nonempty →
    ∃ B ∈ FGSA.Next.fullTree p st, eraseFG B = Q.parent ∧
      (frameRNext p st).lo ≤ (heightView p B).h) ∧
  (∀ x r C, x ∈ rho.honest → actionSourceFG p c E rho x r = some (some C) → C.slot ≤ r * p.R)

/-- Next frame surface; counterpart `OpeningCovered`, census B. -/
def OpeningCoveredNext (r : Nat) (Q : Block) : Prop := ∀ x ∈ rho.honest,
  ∃ K nd j rSent a, postClock E rho x (p.actionTime r) = some nd ∧
    actionSourceFG p c E rho x r = some (some K) ∧ K ∈ FGSA.Next.fullTree p nd.st ∧
    Block.Preceq Q (eraseFG K) ∧ rSent ≤ r ∧
    HonestRowAt p c E rho j x rSent a ∧
    namedEntry a.payload.height_pair =
      some ((heightView p K).h, (heightView p K).T_h.root)

/-- Next claim surface; counterpart `FrameAt`, census B. -/
def FrameAtNext (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) : Prop :=
  RFrameExactNext p c E rho ∧ RFrameNext p c E rho

def RFrameNextEpoch : Prop := ∀ i x, x ∈ rho.honest →
  let st := storeAt p c E rho i x
  (∀ s N P, namedParentHeld st N = true → parentFG st N.erase = some P →
    blockAccepted p st s N P = true →
    (admitBlock p st s N).fg = Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)) ∧
  ((∀ f : GridCO.State p.n .root → GridCO.State p.n .root, (onView f st).fg = st.fg) ∧
    (∀ s k b, (admitHead p st s k b).fg = st.fg) ∧
    (∀ a, (admitRow p st a).fg = st.fg) ∧
    (∀ t, (FGSA.clock p st t).fg = st.fg) ∧
    (∀ s N,
      (namedParentHeld st N = false ∨ parentFG st N.erase = none ∨
        ∃ P, parentFG st N.erase = some P ∧ blockAccepted p st s N P = false) →
      (admitBlock p st s N).fg = st.fg) ∧
    (∀ o, o.decode = none → (FGSA.process p st o).fg = st.fg)) ∧
  (FGSA.Next.controls p (FGSA.reconcile st) = FGSA.Next.controls p st ∧
    ∀ X, domainRNext p (FGSA.reconcile st) X = domainRNext p st X) ∧
  (MetaInv p st ∧
    (∀ s, FGSA.Next.proposalsAtNext p st s = st.proposals.filterMap (fun o => match o.decode with
      | some (.block _ N) =>
        if N.slot = s ∧ ∃ B ∈ FGSA.Next.tree p st, eraseFG B = N.erase then
          some (N.raw, N.support) else none
      | _ => none)) ∧
    (∀ H, FGSA.Next.chainWireRowsNext st H = (st.proposals.filterMap (fun o => match o.decode with
      | some (.block _ N) => if Block.preceq N.erase H then some N.rows else none
      | _ => none)).flatten) ∧
    (FGSA.Next.blockWireRowsNext st = (st.proposals.filterMap (fun o => match o.decode with
      | some (.block _ N) => some N.rows
      | _ => none)).flatten) ∧
    (∀ s, FGSA.Next.voterBlocksNext p st s = (FGSA.Next.tree p st).filter (fun B =>
      decide (GridCO.stampBlock st.base (eraseFG B) < SA.freezeTime p.toParams (s - 1)) ||
      decide (∃ P ∈ FGSA.Next.tree p st, P.slot = s ∧ FGBlock.Preceq B P))) ∧
    (∀ s, FGSA.Next.headVotesNext p st s =
      (((GridCO.votesAt st.base (s - 1)).filter (fun o =>
        decide (GridCO.stampVote st.base o < SA.freezeTime p.toParams (s - 1)))) ++
        (((FGSA.Next.proposalsAtNext p st s).flatMap (fun row => row.1.map baseVote)).filter
          (fun o => GridCO.headLabel? o == some (s - 1)))).eraseDups) ∧
    (∀ s, FGSA.Next.headSupportNext p st s =
      (((GridCO.votesAt st.base (s - 1)).filter (fun o =>
        GridCO.resolvedBefore (FGSA.actView st) o (SA.freezeTime p.toParams (s - 1)))) ++
        (((FGSA.Next.proposalsAtNext p st s).flatMap (fun row => row.2.map baseVote)).filter
          (fun o =>
          GridCO.headLabel? o == some (s - 1) && match GridCO.resolvedHead? st.base o with
          | some h => decide (∃ B ∈ FGSA.Next.tree p st, eraseFG B = h) &&
              decide (h.slot ≤ s - 1)
          | none => false))).eraseDups) ∧
    (∀ H, FGSA.Next.proposalRowsNext p st H =
      match FGSA.Next.fgBlockOfNext st H with
      | none => []
      | some P =>
          (st.rowPool ++ FGSA.Next.blockWireRowsNext st).eraseDups.filter (fun a =>
            Window.rowValidW (parentFoldState p (st.slot p) P) a &&
              !decide (a ∈ FGSA.Next.chainWireRowsNext st H))) ∧
    (∀ j, i ≤ j → j ≤ rho.events.length →
      let st' := storeAt p c E rho j x
      st.proposals <+: st'.proposals ∧ st.rowPool <+: st'.rowPool ∧
      (V2.D.restartFree rho x i j →
        st.base.blockStamp <+: st'.base.blockStamp ∧
        st.base.voteStamp <+: st'.base.voteStamp)))


theorem RFrameNextEpoch_def : RFrameNextEpoch p c E rho =
  (∀ i x, x ∈ rho.honest →
  let st := storeAt p c E rho i x
  (∀ s N P, namedParentHeld st N = true → parentFG st N.erase = some P →
    blockAccepted p st s N P = true →
    (admitBlock p st s N).fg = Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)) ∧
  ((∀ f : GridCO.State p.n .root → GridCO.State p.n .root, (onView f st).fg = st.fg) ∧
    (∀ s k b, (admitHead p st s k b).fg = st.fg) ∧
    (∀ a, (admitRow p st a).fg = st.fg) ∧
    (∀ t, (FGSA.clock p st t).fg = st.fg) ∧
    (∀ s N,
      (namedParentHeld st N = false ∨ parentFG st N.erase = none ∨
        ∃ P, parentFG st N.erase = some P ∧ blockAccepted p st s N P = false) →
      (admitBlock p st s N).fg = st.fg) ∧
    (∀ o, o.decode = none → (FGSA.process p st o).fg = st.fg)) ∧
  (FGSA.Next.controls p (FGSA.reconcile st) = FGSA.Next.controls p st ∧
    ∀ X, domainRNext p (FGSA.reconcile st) X = domainRNext p st X) ∧
  (MetaInv p st ∧
    (∀ s, FGSA.Next.proposalsAtNext p st s = st.proposals.filterMap (fun o => match o.decode with
      | some (.block _ N) =>
        if N.slot = s ∧ ∃ B ∈ FGSA.Next.tree p st, eraseFG B = N.erase then
          some (N.raw, N.support) else none
      | _ => none)) ∧
    (∀ H, FGSA.Next.chainWireRowsNext st H = (st.proposals.filterMap (fun o => match o.decode with
      | some (.block _ N) => if Block.preceq N.erase H then some N.rows else none
      | _ => none)).flatten) ∧
    (FGSA.Next.blockWireRowsNext st = (st.proposals.filterMap (fun o => match o.decode with
      | some (.block _ N) => some N.rows
      | _ => none)).flatten) ∧
    (∀ s, FGSA.Next.voterBlocksNext p st s = (FGSA.Next.tree p st).filter (fun B =>
      decide (GridCO.stampBlock st.base (eraseFG B) < SA.freezeTime p.toParams (s - 1)) ||
      decide (∃ P ∈ FGSA.Next.tree p st, P.slot = s ∧ FGBlock.Preceq B P))) ∧
    (∀ s, FGSA.Next.headVotesNext p st s =
      (((GridCO.votesAt st.base (s - 1)).filter (fun o =>
        decide (GridCO.stampVote st.base o < SA.freezeTime p.toParams (s - 1)))) ++
        (((FGSA.Next.proposalsAtNext p st s).flatMap (fun row => row.1.map baseVote)).filter
          (fun o => GridCO.headLabel? o == some (s - 1)))).eraseDups) ∧
    (∀ s, FGSA.Next.headSupportNext p st s =
      (((GridCO.votesAt st.base (s - 1)).filter (fun o =>
        GridCO.resolvedBefore (FGSA.actView st) o (SA.freezeTime p.toParams (s - 1)))) ++
        (((FGSA.Next.proposalsAtNext p st s).flatMap (fun row => row.2.map baseVote)).filter
          (fun o =>
          GridCO.headLabel? o == some (s - 1) && match GridCO.resolvedHead? st.base o with
          | some h => decide (∃ B ∈ FGSA.Next.tree p st, eraseFG B = h) &&
              decide (h.slot ≤ s - 1)
          | none => false))).eraseDups) ∧
    (∀ H, FGSA.Next.proposalRowsNext p st H =
      match FGSA.Next.fgBlockOfNext st H with
      | none => []
      | some P =>
          (st.rowPool ++ FGSA.Next.blockWireRowsNext st).eraseDups.filter (fun a =>
            Window.rowValidW (parentFoldState p (st.slot p) P) a &&
              !decide (a ∈ FGSA.Next.chainWireRowsNext st H))) ∧
    (∀ j, i ≤ j → j ≤ rho.events.length →
      let st' := storeAt p c E rho j x
      st.proposals <+: st'.proposals ∧ st.rowPool <+: st'.rowPool ∧
      (V2.D.restartFree rho x i j →
        st.base.blockStamp <+: st'.base.blockStamp ∧
        st.base.voteStamp <+: st'.base.voteStamp)))) := rfl

end AvailableChain.FGSA.Run
end

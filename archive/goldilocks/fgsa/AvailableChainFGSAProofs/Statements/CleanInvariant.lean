module
public import AvailableChainFGSAClaims.Statements.ComposeStmt
public import AvailableChainFGSARun.Statements.Client
public import AvailableChainGeneric.Statements.Pure.FirstBad

public section

/-! P3 r3.5.9 §§8.1–8.4; bp02 §5. These are F2 review statements.
Only Proofs/Clean imports this module. The results and label predicate stay
in Claims/Statements/Reads. No step proof is supplied here. -/

namespace AvailableChain.FGSA.Run

variable {ΔF : Time}

open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
P3 §8.2, I1: facts about completed gate events. -/
structure CleanHist (i : Nat) : Prop where
  ordered : ∀ s r B C, (s, B) ∈ cleanResults p c E rho i →
    (r, C) ∈ cleanResults p c E rho i → s < r → Block.Preceq B C
  same : ∀ s B C, (s, B) ∈ cleanResults p c E rho i →
    (s, C) ∈ cleanResults p c E rho i → Block.Compatible B C
  nonempty : ∀ j x s, j < i → enabledGateAt p c E rho j x s →
    ∃ B, gateResultAt p c E rho j = some (some B) ∧ (s = 0 → B = .genesis)
  continues : ∀ j k x y s B, j < i → k < j → IsGateTick p c rho j x s →
    rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1))) →
    joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
    gateResultAt p c E rho j = some (some B) →
    Block.Preceq B (headAtIdx p c E rho k (s + 1))

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
I2 row sources retain the action label and the exact named entry. -/
def CleanRowSources (i : Nat) : Prop :=
  ∀ j x r a e, j < i → HonestRowAt p c E rho j x r a →
    namedEntry a.payload.height_pair = some e →
    ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
      e = (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root) ∧
      FGBlock.Preceq (derive p.E p.cfg C).T_h C ∧
      BelowLabel p c E rho i (r * p.R) (eraseFG C)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
L49 first-unfold equation; bp02 §5, P3 §8.4. -/
theorem CleanRowSources_def (i : Nat) :
    CleanRowSources p c E rho i =
      (∀ j x r a e, j < i → HonestRowAt p c E rho j x r a →
    namedEntry a.payload.height_pair = some e →
    ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
      e = (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root) ∧
      FGBlock.Preceq (derive p.E p.cfg C).T_h C ∧
      BelowLabel p c E rho i (r * p.R) (eraseFG C)) := by rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
I2 certificate sources are earlier honest target rows, with their labels.
The block and certified entry are universal; no common path or tip is chosen. -/
def CleanCertSources (i : Nat) : Prop :=
  ∀ x W e, x ∈ rho.honest → W ∈ (storeAt p c E rho i x).fg.TF →
    e ∈ certified p W → e ≠ .genesis →
    ∃ j x' r a C, j < i ∧ HonestRowAt p c E rho j x' r a ∧
      namedEntry a.payload.height_pair = some (hOf p.E p.cfg e, e.root) ∧
      actionSourceFG p c E rho x' r = some (some C) ∧
      FGBlock.Preceq e C ∧
      BelowLabel p c E rho i (r * p.R) (eraseFG C)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
L49 first-unfold equation; bp02 §5, P3 §8.4. -/
theorem CleanCertSources_def (i : Nat) :
    CleanCertSources p c E rho i =
      (∀ x W e, x ∈ rho.honest → W ∈ (storeAt p c E rho i x).fg.TF →
    e ∈ certified p W → e ≠ .genesis →
    ∃ j x' r a C, j < i ∧ HonestRowAt p c E rho j x' r a ∧
      namedEntry a.payload.height_pair = some (hOf p.E p.cfg e, e.root) ∧
      actionSourceFG p c E rho x' r = some (some C) ∧
      FGBlock.Preceq e C ∧
      BelowLabel p c E rho i (r * p.R) (eraseFG C)) := by rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
P3 §8.2, I2–I4. Each state fact is about this run and this index.
Lease origins include due rows. Saved results are event values. -/
structure CleanState (i : Nat) : Prop where
  sources : CleanRowSources p c E rho i ∧ CleanCertSources p c E rho i
  fOrigin : ∀ v,
    BelowLabel p c E rho i (labelBoundAt p c rho i) (F_at p c E rho i v) ∧
    BelowLabel p c E rho i (labelBoundAt p c rho i) (J_at p c E rho i v)
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
P3:5185–5195, bp02 §5.4: no same-batch label may witness a gate input.
  The strict bound also makes both inputs genesis at label zero. -/
  gateInputs : ∀ v s, IsGateTick p c rho i v s →
    let below := fun X => X = .genesis ∨
      ∃ r B, (r, B) ∈ cleanResults p c E rho i ∧ r < s ∧ Block.Preceq X B
    below (F_at p c E rho i v) ∧ below (J_at p c E rho i v)
  leases : ∀ v row, row ∈ (storeAt p c E rho i v).base.obligations →
    ∃ j < i, ∃ s C, IsGateTick p c rho j v s ∧ gatePassedAt p c E rho j ∧
      gateResultAt p c E rho j = some (some C) ∧ Block.Preceq row.1 C
  saved : ∀ v j s C, j < i → enabledGateAt p c E rho j v s →
    V2.D.restartFree rho v j i → activeCompatible (storeAt p c E rho i v) C = true →
    gateResultAt p c E rho j = some (some C) →
    GridCO.savedGenuine (storeAt p c E rho i v).base s = some (some C)
  savedOnly : ∀ v s C,
    GridCO.savedGenuine (storeAt p c E rho i v).base s = some (some C) →
    ∃ j < i, V2.D.restartFree rho v j i ∧ enabledGateAt p c E rho j v s ∧
      gateResultAt p c E rho j = some (some C)
  fastWrite : ∀ v s X, X ∈ (FGSA.fastWriteAt (storeAt p c E rho i v) s).getD [] →
    ∃ j < i, V2.D.restartFree rho v j i ∧ enabledGateAt p c E rho j v s ∧
      gatePassedAt p c E rho j ∧ ∃ C, gateResultAt p c E rho j = some (some C) ∧
        Block.Preceq X C ∧ fastAt p c E rho v s X
  sOrigin : ∀ v, S_at p c E rho i v = .genesis ∨
    (∃ j < i, ∃ s, IsGateTick p c rho j v s ∧
      gateResultAt p c E rho j = some (some (S_at p c E rho i v))) ∨
    (∃ j ≤ i, S_at p c E rho i v = F_at p c E rho j v)
  harmless : ∀ j v o t, j < i → v ∈ rho.honest →
    rho.events[j]? = some (.deliver v o t) → FAdvanceAt p c E rho j v →
    (storeAt p c E rho (j + 1) v).base.obligations =
      (storeAt p c E rho j v).base.obligations ∧
    (storeAt p c E rho (j + 1) v).base.genuine =
      (storeAt p c E rho j v).base.genuine ∧
    (storeAt p c E rho (j + 1) v).fastWrite = (storeAt p c E rho j v).fastWrite
  nesting : ∀ v, v ∈ rho.honest → FGSA.NestOK (storeAt p c E rho i v)
  store : ∀ v, v ∈ rho.honest → FGSA.CStoreInv p (storeAt p c E rho i v)
  frame : ∀ v, v ∈ rho.honest →
    FGSA.controls p (storeAt p c E rho i v) =
      KitFG.treeFjControlsView (heightView p)
        (storeAt p c E rho i v).fg.F (storeAt p c E rho i v).fg.TF
  client : ∀ v, v ∈ rho.honest → EmittedRowsNoSlash p c E rho v
  sExtends : ∀ v j k, j ≤ k → k ≤ i →
    Block.Preceq (S_at p c E rho j v) (S_at p c E rho k v)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
P3 §8.2: the FG part used in the assume/guarantee rule. -/
structure FGPart (i : Nat) : Prop where
  sources : CleanCertSources p c E rho i
  fOrigin : ∀ v,
    BelowLabel p c E rho i (labelBoundAt p c rho i) (F_at p c E rho i v) ∧
    BelowLabel p c E rho i (labelBoundAt p c rho i) (J_at p c E rho i v)

def GT (b₀ : Time) (j : Nat) : Prop :=
  j < timeIdx rho b₀ → CleanHist p c E rho (j + 1)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
P3 §8.7; first-unfold equation (`:= by rfl`, add-only).
DC counterpart: none; FG-SA-specific statement. -/
theorem GT_def (b₀ : Time) (j : Nat) :
    GT p c E rho b₀ j =
      (
  j < timeIdx rho b₀ → CleanHist p c E rho (j + 1)) := by rfl

def GR (b₀ : Time) (i : Nat) : Prop :=
  i ≤ timeIdx rho b₀ → FGPart p c E rho i

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
P3 §8.7; first-unfold equation (`:= by rfl`, add-only).
DC counterpart: none; FG-SA-specific statement. -/
theorem GR_def (b₀ : Time) (i : Nat) :
    GR p c E rho b₀ i =
      (
  i ≤ timeIdx rho b₀ → FGPart p c E rho i) := by rfl

variable [Fintype V]

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
F2.4 producer for F2.7, bp02 §5.5: each completed honest gate passes
and its result is below S after its tick. CleanState.sExtends transports
this fact to afterTicksIdx for the frozen CleanGateAt export.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
def CleanGateOutputStmt (b₀ : Time) : Prop :=
  CleanCutSet p c E rho b₀ ΔF → Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card →
  FGFoundation p c E rho → SrcFrameAboveStmt p c E rho →
  ∀ i, i ≤ timeIdx rho b₀ → CleanHist p c E rho i →
    ∀ j v s, j < i → v ∈ rho.honest → enabledGateAt p c E rho j v s →
      ∃ B, gateResultAt p c E rho j = some (some B) ∧
        gatePassedAt p c E rho j ∧ Block.Preceq B (S_at p c E rho (j + 1) v)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
P3 §8.7; bp02 §5.5. Class B first-unfold equation.
DC counterpart: none; FG-SA-specific statement.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem CleanGateOutputStmt_def (b₀ : Time) :
    CleanGateOutputStmt (ΔF := ΔF) p c E rho b₀ =
      (
  CleanCutSet p c E rho b₀ ΔF → Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card →
  FGFoundation p c E rho → SrcFrameAboveStmt p c E rho →
  ∀ i, i ≤ timeIdx rho b₀ → CleanHist p c E rho i →
    ∀ j v s, j < i → v ∈ rho.honest → enabledGateAt p c E rho j v s →
      ∃ B, gateResultAt p c E rho j = some (some B) ∧
        gatePassedAt p c E rho j ∧ Block.Preceq B (S_at p c E rho (j + 1) v)) := by rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
F2.7 source export, bp02 §5.6: all nonempty action-source reads,
including asleep nodes that emit no row. TSrc supplies the gate origin;
F2.1 supplies the history-index and label conversion.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
def CleanActionSourcesStmt (b₀ : Time) : Prop :=
  CleanCutSet p c E rho b₀ ΔF → Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card →
  FGFoundation p c E rho → SrcFrameAboveStmt p c E rho →
  ∀ i, i ≤ timeIdx rho b₀ → CleanHist p c E rho i →
    ∀ j x r C, j < i → x ∈ rho.honest →
      rho.events[j]? = some (.tick x (p.actionTime r)) →
      actionSource p c E rho x r = some (some C) →
      BelowLabel p c E rho i (labelBoundAt p c rho j) C

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
P3 §8.7; bp02 §5.6. Class B first-unfold equation.
DC counterpart: none; FG-SA-specific statement.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem CleanActionSourcesStmt_def (b₀ : Time) :
    CleanActionSourcesStmt (ΔF := ΔF) p c E rho b₀ =
      (
  CleanCutSet p c E rho b₀ ΔF → Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card →
  FGFoundation p c E rho → SrcFrameAboveStmt p c E rho →
  ∀ i, i ≤ timeIdx rho b₀ → CleanHist p c E rho i →
    ∀ j x r C, j < i → x ∈ rho.honest →
      rho.events[j]? = some (.tick x (p.actionTime r)) →
      actionSource p c E rho x r = some (some C) →
      BelowLabel p c E rho i (labelBoundAt p c rho j) C) := by rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
F2.2 producer for the F2.7 Clean frame export, bp02 §§3.3–3.4:
no contest, a labelled root origin, and full-domain retention.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
def CleanFrameStmt (b₀ : Time) : Prop :=
  CleanCutSet p c E rho b₀ ΔF → Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card →
  FGFoundation p c E rho → SrcFrameAboveStmt p c E rho →
  ∀ i, i ≤ timeIdx rho b₀ → CleanHist p c E rho i →
    ∀ v, v ∈ rho.honest →
      let st := storeAt p c E rho i v
      (FGSA.controls p st).contest = false ∧
      BelowLabel p c E rho i (labelBoundAt p c rho i) (eraseFG (FGSA.controls p st).Z) ∧
      (∀ B ∈ st.fg.TF,
        BelowLabel p c E rho i (labelBoundAt p c rho i) (eraseFG B) →
        Block.Preceq (eraseFG B) (eraseFG (FGSA.controls p st).Z) ∨
        Block.Preceq (eraseFG B) (eraseFG st.fg.F) ∨
        (FGBlock.Preceq st.fg.F (FGSA.controls p st).Z ∧
          FGBlock.Preceq (FGSA.controls p st).Z B ∧ B ∈ FGSA.fullTree p st))

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
P3 §8.7; bp02 §§3.3–3.4. Class B first-unfold equation.
DC counterpart: none; FG-SA-specific frame bundle.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem CleanFrameStmt_def (b₀ : Time) :
    CleanFrameStmt (ΔF := ΔF) p c E rho b₀ =
      (
  CleanCutSet p c E rho b₀ ΔF → Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card →
  FGFoundation p c E rho → SrcFrameAboveStmt p c E rho →
  ∀ i, i ≤ timeIdx rho b₀ → CleanHist p c E rho i →
    ∀ v, v ∈ rho.honest →
      let st := storeAt p c E rho i v
      (FGSA.controls p st).contest = false ∧
      BelowLabel p c E rho i (labelBoundAt p c rho i) (eraseFG (FGSA.controls p st).Z) ∧
      (∀ B ∈ st.fg.TF,
        BelowLabel p c E rho i (labelBoundAt p c rho i) (eraseFG B) →
        Block.Preceq (eraseFG B) (eraseFG (FGSA.controls p st).Z) ∨
        Block.Preceq (eraseFG B) (eraseFG st.fg.F) ∨
        (FGBlock.Preceq st.fg.F (FGSA.controls p st).Z ∧
          FGBlock.Preceq (FGSA.controls p st).Z B ∧ B ∈ FGSA.fullTree p st))) := by rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
R-F2a: Gen.AGRule.fg takes only `∀ j < i, GT j`.
Gen.Pure.AGRule.holds gives both conclusions at every index once this
instance is proved. There is no same-index GT premise in the FG step.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
def CleanAGStmt (b₀ : Time) : Prop :=
  CleanCutSet p c E rho b₀ ΔF → Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card →
  FGFoundation p c E rho → SrcFrameAboveStmt p c E rho →
  Gen.Pure.AGRule (GR p c E rho b₀) (GT p c E rho b₀)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
P3 §8.7; first-unfold equation (`:= by rfl`, add-only).
DC counterpart: none; FG-SA-specific statement.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem CleanAGStmt_def (b₀ : Time) :
    CleanAGStmt (ΔF := ΔF) p c E rho b₀ =
      (
  CleanCutSet p c E rho b₀ ΔF → Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card →
  FGFoundation p c E rho → SrcFrameAboveStmt p c E rho →
  Gen.Pure.AGRule (GR p c E rho b₀) (GT p c E rho b₀)) := by rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
State step under a fixed completed history, P3 §§8.2, 8.4.
The event predicate separates the handlers without a free path or tip.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
def CleanStateStep (b₀ : Time) (event : Nat → Prop) : Prop :=
  CleanCutSet p c E rho b₀ ΔF → Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card →
  FGFoundation p c E rho → SrcFrameAboveStmt p c E rho →
  ∀ i, i ≤ timeIdx rho b₀ → CleanHist p c E rho i →
    ∀ j, j < i → event j → CleanState p c E rho j → CleanState p c E rho (j + 1)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
L49 first-unfold equation; bp02 §5, P3 §8.4.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem CleanStateStep_def (b₀ : Time) (event : Nat → Prop) :
    CleanStateStep (ΔF := ΔF) p c E rho b₀ event =
      (CleanCutSet p c E rho b₀ ΔF → Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card →
  FGFoundation p c E rho → SrcFrameAboveStmt p c E rho →
  ∀ i, i ≤ timeIdx rho b₀ → CleanHist p c E rho i →
    ∀ j, j < i → event j → CleanState p c E rho j → CleanState p c E rho (j + 1)) := by rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
History step; state facts are available at all earlier indices, P3 §8.4.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
def CleanHistStep (b₀ : Time) (event : Nat → Prop) : Prop :=
  CleanCutSet p c E rho b₀ ΔF → Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card →
  FGFoundation p c E rho → SrcFrameAboveStmt p c E rho →
  ∀ i, i < timeIdx rho b₀ → event i → CleanHist p c E rho i →
    (∀ k, k ≤ i → CleanState p c E rho k) → CleanHist p c E rho (i + 1)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
L49 first-unfold equation; bp02 §5, P3 §8.4.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem CleanHistStep_def (b₀ : Time) (event : Nat → Prop) :
    CleanHistStep (ΔF := ΔF) p c E rho b₀ event =
      (CleanCutSet p c E rho b₀ ΔF → Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card →
  FGFoundation p c E rho → SrcFrameAboveStmt p c E rho →
  ∀ i, i < timeIdx rho b₀ → event i → CleanHist p c E rho i →
    (∀ k, k ≤ i → CleanState p c E rho k) → CleanHist p c E rho (i + 1)) := by rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Vote, row, or refused proposal: no accepted block handler. -/
def CleanOrdinaryDelivery (j : Nat) : Prop :=
  ∃ v o t, rho.events[j]? = some (.deliver v o t) ∧
    ∀ s N P, (toWire p o).decode = some (.block s N) →
      namedParentHeld (storeAt p c E rho j v) N = true →
      parentFG (storeAt p c E rho j v) N.erase = some P →
      blockAccepted p (storeAt p c E rho j v) s N P = false

omit [Fintype V] in
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
ROOT-DIGEST W2b. L49 first-unfold equation; bp02 §5, P3 §8.4. -/
theorem CleanOrdinaryDelivery_def (j : Nat) :
    CleanOrdinaryDelivery p c E rho j =
      (∃ v o t, rho.events[j]? = some (.deliver v o t) ∧
    ∀ s N P, (toWire p o).decode = some (.block s N) →
      namedParentHeld (storeAt p c E rho j v) N = true →
      parentFG (storeAt p c E rho j v) N.erase = some P →
      blockAccepted p (storeAt p c E rho j v) s N P = false) := by rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
ROOT-DIGEST W2b. A checked block receipt. -/
def CleanBlockDelivery (j : Nat) : Prop :=
  ∃ v o t s N P, rho.events[j]? = some (.deliver v o t) ∧
    (toWire p o).decode = some (.block s N) ∧
    namedParentHeld (storeAt p c E rho j v) N = true ∧
    parentFG (storeAt p c E rho j v) N.erase = some P ∧
    blockAccepted p (storeAt p c E rho j v) s N P = true

omit [Fintype V] in
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
ROOT-DIGEST W2b. L49 first-unfold equation; bp02 §5, P3 §8.4. -/
theorem CleanBlockDelivery_def (j : Nat) :
    CleanBlockDelivery p c E rho j =
      (∃ v o t s N P, rho.events[j]? = some (.deliver v o t) ∧
    (toWire p o).decode = some (.block s N) ∧
    namedParentHeld (storeAt p c E rho j v) N = true ∧
    parentFG (storeAt p c E rho j v) N.erase = some P ∧
    blockAccepted p (storeAt p c E rho j v) s N P = true) := by rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
A tick that has no gate. -/
def CleanNoGateTick (j : Nat) : Prop :=
  ∃ v t, rho.events[j]? = some (.tick v t) ∧ isGateTime p t = false

omit [DecidableEq V] [Fintype V] in
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
L49 first-unfold equation; bp02 §5, P3 §8.4. -/
theorem CleanNoGateTick_def (j : Nat) :
    CleanNoGateTick p c rho j =
      (∃ v t, rho.events[j]? = some (.tick v t) ∧ isGateTime p t = false) := by rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
A tick with a gate; the FG action, when due, is part of this tick. -/
def CleanGateTick (j : Nat) : Prop := ∃ v s, IsGateTick p c rho j v s

omit [DecidableEq V] [Fintype V] in
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
L49 first-unfold equation; bp02 §5, P3 §8.4. -/
theorem CleanGateTick_def (j : Nat) :
    CleanGateTick p c rho j =
      (∃ v s, IsGateTick p c rho j v s) := by rfl

def CleanDeliveryStateStep (b₀ : Time) : Prop :=
  CleanStateStep (ΔF := ΔF) p c E rho b₀ (CleanOrdinaryDelivery p c E rho)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
L49 first-unfold equation; bp02 §5, P3 §8.4.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem CleanDeliveryStateStep_def (b₀ : Time) :
    CleanDeliveryStateStep (ΔF := ΔF) p c E rho b₀ =
      (CleanStateStep (ΔF := ΔF) p c E rho b₀ (CleanOrdinaryDelivery p c E rho)) := by rfl
def CleanDeliveryHistStep (b₀ : Time) : Prop :=
  CleanHistStep (ΔF := ΔF) p c E rho b₀ (CleanOrdinaryDelivery p c E rho)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
L49 first-unfold equation; bp02 §5, P3 §8.4.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem CleanDeliveryHistStep_def (b₀ : Time) :
    CleanDeliveryHistStep (ΔF := ΔF) p c E rho b₀ =
      (CleanHistStep (ΔF := ΔF) p c E rho b₀ (CleanOrdinaryDelivery p c E rho)) := by rfl
def CleanBlockStateStep (b₀ : Time) : Prop :=
  CleanStateStep (ΔF := ΔF) p c E rho b₀ (CleanBlockDelivery p c E rho)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
L49 first-unfold equation; bp02 §5, P3 §8.4.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem CleanBlockStateStep_def (b₀ : Time) :
    CleanBlockStateStep (ΔF := ΔF) p c E rho b₀ =
      (CleanStateStep (ΔF := ΔF) p c E rho b₀ (CleanBlockDelivery p c E rho)) := by rfl
def CleanBlockHistStep (b₀ : Time) : Prop :=
  CleanHistStep (ΔF := ΔF) p c E rho b₀ (CleanBlockDelivery p c E rho)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
L49 first-unfold equation; bp02 §5, P3 §8.4.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem CleanBlockHistStep_def (b₀ : Time) :
    CleanBlockHistStep (ΔF := ΔF) p c E rho b₀ =
      (CleanHistStep (ΔF := ΔF) p c E rho b₀ (CleanBlockDelivery p c E rho)) := by rfl
def CleanNoGateStateStep (b₀ : Time) : Prop :=
  CleanStateStep (ΔF := ΔF) p c E rho b₀ (CleanNoGateTick p c rho)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
L49 first-unfold equation; bp02 §5, P3 §8.4.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem CleanNoGateStateStep_def (b₀ : Time) :
    CleanNoGateStateStep (ΔF := ΔF) p c E rho b₀ =
      (CleanStateStep (ΔF := ΔF) p c E rho b₀ (CleanNoGateTick p c rho)) := by rfl
def CleanNoGateHistStep (b₀ : Time) : Prop :=
  CleanHistStep (ΔF := ΔF) p c E rho b₀ (CleanNoGateTick p c rho)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
L49 first-unfold equation; bp02 §5, P3 §8.4.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem CleanNoGateHistStep_def (b₀ : Time) :
    CleanNoGateHistStep (ΔF := ΔF) p c E rho b₀ =
      (CleanHistStep (ΔF := ΔF) p c E rho b₀ (CleanNoGateTick p c rho)) := by rfl
def CleanGateStateStep (b₀ : Time) : Prop :=
  CleanStateStep (ΔF := ΔF) p c E rho b₀ (CleanGateTick p c rho)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
L49 first-unfold equation; bp02 §5, P3 §8.4.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem CleanGateStateStep_def (b₀ : Time) :
    CleanGateStateStep (ΔF := ΔF) p c E rho b₀ =
      (CleanStateStep (ΔF := ΔF) p c E rho b₀ (CleanGateTick p c rho)) := by rfl
def CleanGateHistStep (b₀ : Time) : Prop :=
  CleanHistStep (ΔF := ΔF) p c E rho b₀ (CleanGateTick p c rho)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
L49 first-unfold equation; bp02 §5, P3 §8.4.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem CleanGateHistStep_def (b₀ : Time) :
    CleanGateHistStep (ΔF := ΔF) p c E rho b₀ =
      (CleanHistStep (ΔF := ΔF) p c E rho b₀ (CleanGateTick p c rho)) := by rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
A restart keeps durable state and begins empty receiver caches, P3 §8.4.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
def CleanRestartStep (b₀ : Time) : Prop :=
  CleanCutSet p c E rho b₀ ΔF → FGFoundation p c E rho → SrcFrameAboveStmt p c E rho →
    ∀ j v t, j < timeIdx rho b₀ → rho.events[j]? = some (.restart v t) →
    CleanState p c E rho j → CleanState p c E rho (j + 1)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
P3 §8.7; first-unfold equation (`:= by rfl`, add-only).
DC counterpart: none; FG-SA-specific statement.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem CleanRestartStep_def (b₀ : Time) :
    CleanRestartStep (ΔF := ΔF) p c E rho b₀ =
      (
  CleanCutSet p c E rho b₀ ΔF → FGFoundation p c E rho → SrcFrameAboveStmt p c E rho →
    ∀ j v t, j < timeIdx rho b₀ → rho.events[j]? = some (.restart v t) →
    CleanState p c E rho j → CleanState p c E rho (j + 1)) := by rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
P3 §8.4 and bp02 §5.6: an action's new row belongs to the history
that includes its gate. This is a substep of the same tick, not a new event.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
def CleanActionStep (b₀ : Time) : Prop :=
  CleanCutSet p c E rho b₀ ΔF → Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card →
  FGFoundation p c E rho → SrcFrameAboveStmt p c E rho →
  ∀ i v r, i < timeIdx rho b₀ →
    rho.events[i]? = some (.tick v (p.actionTime r)) →
    CleanHist p c E rho (i + 1) → CleanState p c E rho i →
    CleanRowSources p c E rho (i + 1)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
L49 first-unfold equation; P3 §8.4, bp02 §5.6, lead R2(a).
DC counterpart: none; FG-SA emits action rows in the gate tick.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem CleanActionStep_def (b₀ : Time) :
    CleanActionStep (ΔF := ΔF) p c E rho b₀ =
      (CleanCutSet p c E rho b₀ ΔF → Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card →
  FGFoundation p c E rho → SrcFrameAboveStmt p c E rho →
  ∀ i v r, i < timeIdx rho b₀ →
    rho.events[i]? = some (.tick v (p.actionTime r)) →
    CleanHist p c E rho (i + 1) → CleanState p c E rho i →
    CleanRowSources p c E rho (i + 1)) := by rfl

end AvailableChain.FGSA.Run
end

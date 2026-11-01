module
public import AvailableChainGeneric.Statements.V2.Duty.Counts
public import AvailableChainFGSARun.Statements.Interface
public import AvailableChainFGSAClaims.Statements.Reads
public import AvailableChainFGSAClaims.Statements.Counts
public import AvailableChainFGSAClaims.Statements.BoundsW
public import AvailableChainFGSARun.Statements.Emission

@[expose] public section

namespace AvailableChain.FGSA.Run

variable (p : Params) {In V : Type} {c : AppCodec In} [DecidableEq V] [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

def slotStartZ (s : Int) : Time := 4 * p.Δ * s

def voteZ (s : Int) : Time := slotStartZ p s + p.Δ

def slotAt (t : Time) : Slot := (t / (4 * p.Δ)).toNat

def AwakeClosed (v : V) (a b : Time) : Prop :=
  ∀ t, 0 ≤ t → a ≤ t → t ≤ b → E.awake v t = true

variable {p}

def RestartFreeTime (v : V) (a b : Time) : Prop :=
  ∀ u, a < u → u ≤ b → V2.Event.restart v u ∉ rho.events

variable (p)

def joinedAt (v : V) (s : Slot) (t : Time) : Prop :=
  E.awake v t = true ∧
  (∀ u, 0 < u → u ≤ t → V2.D.Wakes E v u →
    u ≤ slotStartZ p ((s : Int) - 1)) ∧
  (∀ u, 0 ≤ u → u ≤ t → V2.Event.restart v u ∈ rho.events →
    u ≤ slotStartZ p ((s : Int) - 1))

def joinedDuty (v : V) (s : Slot) (t : Time) : Prop :=
  joinedAt p E rho v s t

variable (c)

def enabledGateAt (j : Nat) (v : V) (s : Slot) : Prop :=
  IsGateTick p c rho j v s ∧
  match (storeAt p c E rho j v).restartTime with
  | none => True
  | some w => w ≤ slotStartZ p (s : Int)

def gatePassedAt (j : Nat) : Prop :=
  ∃ x s, enabledGateAt p c E rho j x s ∧
    let st := FGSA.clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s)
    GridCO.savedGenuine st.base s = none ∧
    ∃ h, SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F) (FGSA.actView st) s = some h ∧
      ((FGSA.actView st).obligations.any (fun row => !Block.compatible row.1 h)) = false

def caughtUpAtIdx (v : V) (i : Nat) (t : Time) : Prop :=
  E.awake v t = true ∧
  match (storeAt p c E rho i v).restartTime with
  | none => True
  | some w =>
      ∃ (s : Slot) (j : Nat), w ≤ slotStartZ p (s : Int) ∧
        SA.gateTime p.toParams s ≤ t ∧ j < i ∧
        enabledGateAt p c E rho j v s ∧
        AwakeClosed E v (slotStartZ p (s : Int)) t ∧
        RestartFreeTime rho v (slotStartZ p (s : Int)) t

def caughtUpAt (v : V) (t : Time) : Prop :=
  caughtUpAtIdx p c E rho v (timeIdx rho t) t

def confirmedReaderAtIdx (v : V) (i : Nat) (t : Time) : Prop :=
  v ∈ rho.honest ∧ caughtUpAtIdx p c E rho v i t

def confirmedReader (v : V) (t : Time) : Prop :=
  confirmedReaderAtIdx p c E rho v (timeIdx rho t) t

variable {c}

def headReader (v : V) (s : Slot) (t : Time) : Prop :=
  v ∈ rho.honest ∧ joinedAt p E rho v s t

def ScopedCompat {I : Type} (R : V → I → Prop)
    (f : I → V → Block) (on : I → Prop) : Prop :=
  ∀ i j x y, on i → on j → R x i → R y j → Block.Compatible (f i x) (f j y)

def ScopedMono {I : Type} [Preorder I] (R : V → I → Prop)
    (f : I → V → Block) (on : I → Prop) : Prop :=
  ∀ i j x, on i → on j → i ≤ j → R x i → R x j →
    Block.Preceq (f i x) (f j x)

def ScopedServed {I : Type} (R : V → I → Prop)
    (f : I → V → Block) (B : Block) (on : I → Prop) : Prop :=
  ∀ i x, on i → R x i → Block.Preceq B (f i x)

variable {p}

def prefixTime (i : Nat) : Time :=
  ((rho.events.take i).getLast?.map (fun e => e.time)).getD 0

def WakesAppliedAtIdx (v : V) (i : Nat) (t : Time) : Prop :=
  ∀ w, 0 < w → w ≤ t → V2.D.Wakes E v w →
    ∃ j < i, rho.events[j]? = some (.restart v w)

variable (p) (c)

def confirmedReaderIdx (v : V) (i : Nat) : Prop :=
  confirmedReaderAtIdx p c E rho v i (prefixTime rho i) ∧
  WakesAppliedAtIdx E rho v i (prefixTime rho i)

variable {c}

noncomputable def joinedHonest (t : Time) : Finset V := by
  classical
  exact rho.honest.filter (fun v => joinedAt p E rho v (slotAt p t) t)

noncomputable def sleepyBad (t : Time) : Finset V :=
  awakeHonestIn E rho (t - p.η) t ∪ Gen.V2.Duty.faulty rho

def firstUpdateLabel (a : Time) : Slot :=
  ((max 0 a + 4 * p.Δ - 1) / (4 * p.Δ)).toNat

def tauC (a : Time) : Time :=
  slotStartZ p (firstUpdateLabel p a : Int) + 6 * p.Δ

/-- The single healing start: the first slot start at or after GST, plus 6Δ. -/
def recoveryStart (E : Generic.Env V) : Time :=
  tauC p E.t_GST

def recoveryDelay (E : Generic.Env V) : Time :=
  recoveryStart p E - E.t_GST

def B_HF_sleep (ΔF G : Time) : Time :=
  recoveryDelay p E + B_HF p ΔF G

def B_resetF_sleep (ΔF G : Time) : Time :=
  recoveryDelay p E + B'_resetF p ΔF G

def B_FW_sleep (ΔF G : Time) (g : Nat) : Time :=
  recoveryDelay p E + B_FW p ΔF G g

def coverLabel (b₀ : Time) : Slot :=
  ((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat + 1

def coverDeadline (j : Slot) : Time :=
  SA.gateTime p.toParams j + L p

def slowCoveredSchedule (v : V) (j : Slot) : Prop :=
  p.k ≤ j + 1 ∧
  AwakeClosed E v (slotStartZ p ((j : Int) - (p.k : Int) + 1))
    (SA.gateTime p.toParams j) ∧
  RestartFreeTime rho v (slotStartZ p ((j : Int) - (p.k : Int) + 1))
    (SA.gateTime p.toParams j)

def fastCoveredSchedule (v : V) (j : Slot) : Prop :=
  joinedAt p E rho v (j + 1) (SA.gateTime p.toParams j)

noncomputable def coveredNodes (fast : Bool) (b₀ : Time) : Finset V := by
  classical
  exact rho.honest.filter (fun v =>
    if fast then fastCoveredSchedule p E rho v (coverLabel p b₀)
    else slowCoveredSchedule p E rho v (coverLabel p b₀))

noncomputable def outageH (s : Slot) : Finset V :=
  joinedHonest p E rho (SA.voteTime p.toParams s)

def OutageVoteMember (v : V) (b₀ : Time) (r : Slot) : Prop :=
  ∃ s, b₀ ≤ SA.voteTime p.toParams s ∧ s ≤ r ∧
    E.awake v (SA.voteTime p.toParams s) = true

noncomputable def outageW (fast : Bool) (b₀ : Time) (r : Slot) : Finset V := by
  classical
  exact rho.honest.filter (fun v =>
    v ∉ coveredNodes p E rho fast b₀ ∧ OutageVoteMember p E v b₀ r)

variable (c)

def ReceiptObjectAt (x : V) (o : Obj p) (C : Time) : Prop :=
  (fgsa p c).processed (V2.D.Run.stateBeforeTime E rho C x) o = true ∧
  (∀ s a K, (toWire p o).decode = some (.vote s a K) →
    GridCO.resolvedBefore (FGSA.actView (V2.D.Run.stateBeforeTime E rho C x).st)
      (baseVote (⟨.seat (.head s) a, K⟩ : HeadWire p.n)) C = true) ∧
  (∀ s N, (toWire p o).decode = some (.block s N) →
    ∀ b, Block.Preceq b N.erase →
      ∃ Y ∈ (V2.D.Run.stateBeforeTime E rho C x).st.fg.TF,
        eraseFG Y = b ∧
        GridCO.stampBlock (V2.D.Run.stateBeforeTime E rho C x).st.base b < C)

def BatchReceiptAt (x : V) (s : Slot) (C : Time) : Prop :=
  (∀ y o, y ∈ rho.honest →
    V2.D.Run.emits E rho y o (SA.voteTime p.toParams s) →
    (∀ a, ∀ K, (toWire p o).decode = some (.vote s a K) →
      (∃ H, HeadTargetAtEmission p c E rho y o (SA.voteTime p.toParams s) H ∧
        ¬ Block.Compatible H
          (eraseFG (V2.D.Run.stateBeforeTime E rho C x).st.fg.F)) ∨
      ReceiptObjectAt p c E rho x o C)) ∧
  (∀ y o m, y ∈ rho.honest →
    V2.D.Run.emits E rho y o (V2.D.proposalTime (fgsaInterface p c) m) →
    V2.D.proposalTime (fgsaInterface p c) m ≤ SA.voteTime p.toParams s →
    (fgsa p c).excludes (V2.D.Run.stateBeforeTime E rho C x) o = false →
    (∀ q N, (toWire p o).decode = some (.block q N) →
      ReceiptObjectAt p c E rho x o C))

def OutagePrefixReceipt (fast : Bool) (T b₀ : Time) : Prop :=
  ∀ x ∈ coveredNodes p E rho fast b₀, ∀ q,
    (if fast then q = coverLabel p b₀
     else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ (q : Int) ∧
       q ≤ coverLabel p b₀) →
    T ≤ SA.gateTime p.toParams q →
    SA.earlyTime p.toParams q ≤ b₀ →
    BatchReceiptAt p c E rho x q (SA.earlyTime p.toParams q)

variable {c}

def restoredLabel (b₁ : Time) : Slot :=
  (max 0 (- ((p.Δ - b₁) / (4 * p.Δ)))).toNat

def FirstRestored (b₁ : Time) (r : Slot) : Prop :=
  ∀ s, b₁ ≤ SA.voteTime p.toParams s ↔ r ≤ s

variable (c)

def OutageContinuationReceipt (fast : Bool) (T b₀ b₁ : Time) : Prop :=
  OutagePrefixReceipt p c E rho fast T b₀ ∧
  (∀ x q, restoredLabel p b₁ ≤ q →
    SA.earlyTime p.toParams q ≤ rho.horizon →
    headReader p E rho x (q + 1) (SA.gateTime p.toParams q) →
    BatchReceiptAt p c E rho x q (SA.earlyTime p.toParams q)) ∧
  (∀ x s, 0 < s → restoredLabel p b₁ ≤ s - 1 →
    SA.voteTime p.toParams s ≤ rho.horizon →
    headReader p E rho x s (SA.voteTime p.toParams s) →
    BatchReceiptAt p c E rho x (s - 1) (SA.freezeTime p.toParams (s - 1))) ∧
  (∀ m, 0 < m → restoredLabel p b₁ ≤ m - 1 →
    V2.D.proposalTime (fgsaInterface p c) m ≤ rho.horizon →
    let x := V2.D.proposerOf rho (fgsaInterface p c) m
    headReader p E rho x m (V2.D.proposalTime (fgsaInterface p c) m) →
    BatchReceiptAt p c E rho x (m - 1)
      (V2.D.proposalTime (fgsaInterface p c) m))

variable {c}

def OutageE (fast : Bool) (b₀ b₁ : Time) : Prop :=
  ∃ r, FirstRestored p b₁ r ∧
    ∀ s, r ≤ s → s ≤ r + p.k + 1 →
      (Gen.V2.Duty.faulty rho ∪ outageW p E rho fast b₀ r).card <
        ((outageH p E rho s) \ (outageW p E rho fast b₀ r)).card

def OutageE1 (fast : Bool) (b₀ b₁ : Time) : Prop :=
  ∃ r, FirstRestored p b₁ r ∧
    2 * (Gen.V2.Duty.faulty rho ∪ outageW p E rho fast b₀ r).card < p.n

def OutageEnd (r : Slot) : Time :=
  slotStartZ p ((r + p.k : Nat) : Int) + 5 * p.Δ

def outageHeadReader (fast : Bool) (b₀ b₁ : Time)
    (v : V) (t : Time) : Prop :=
  headReader p E rho v (slotAt p t) t ∧
  let r := restoredLabel p b₁
  let W := outageW p E rho fast b₀ r
  (v ∈ coveredNodes p E rho fast b₀) ∨
  (v ∉ W ∧ SA.voteTime p.toParams (r + 1) ≤ t) ∨
  (OutageEnd p r ≤ t)

variable (c)

def outageConfirmedReader (fast : Bool) (b₀ b₁ : Time)
    (v : V) (t : Time) : Prop :=
  confirmedReader p c E rho v t ∧
  let r := restoredLabel p b₁
  (v ∈ coveredNodes p E rho fast b₀) ∨
  (∃ s j, OutageEnd p r ≤ SA.gateTime p.toParams s ∧
    SA.gateTime p.toParams s ≤ t ∧ j < timeIdx rho t ∧
    enabledGateAt p c E rho j v s ∧
    BatchReceiptAt p c E rho v s (SA.earlyTime p.toParams s) ∧
    AwakeClosed E v (SA.gateTime p.toParams s) t ∧
    RestartFreeTime rho v (SA.gateTime p.toParams s) t)

def DutiesExtendScoped (fast : Bool) (B : Block) (b₀ b₁ : Time) : Prop :=
  ∀ x t o, outageHeadReader p E rho fast b₀ b₁ x t →
    b₀ ≤ t → t < b₁ → V2.D.Run.emits E rho x o t →
    (∀ H, HeadTargetAtEmission p c E rho x o t H → Block.Preceq B H) ∧
    (∀ N, o.payload = .proposal N → Block.Preceq B N.parent.erase)

end AvailableChain.FGSA.Run
end

module
public import AvailableChainGeneric.Statements.AC.Reads
public import AvailableChainEngineV2.Conditions.Duty.Interface
public import AvailableChainEngineV2.Conditions.Duty.Schedule

@[expose] public section

namespace AvailableChain.Gen.AC.Duty

open AvailableChain AvailableChain.V2

/-! The AC read and law interface for protocols with separate duties and
signing labels. The old AC interface remains available for old v2 runs.
Pure lease accessors and output normalization are shared with `Gen.AC`. -/

variable {V : Type} {In : Type} {P : ProtocolSpecD In}
  {E : Generic.Env V} {rho : D.Run V P}

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Store reads and gate observations at event indices.
`activeView` is the view before event `i`: FG-SA filters the block domain by
compatibility with the anchor; SA uses its full state and the genesis anchor.
`raw i s x` is confirmation on the gate view at event `i`, including when
the gate is skipped. `fast i s x` records the fast set written at that event;
it is empty on a skipped gate. These are not saved values after reconciliation
or restart. Repeated ticks of one label can have different observations.
The active view contains the saved label results; it adds no clock operation
or protocol-specific retention predicate to these reads. -/
structure ACReads (E : Generic.Env V) (rho : D.Run V P)
    (mode : GridCO.HeadMode := .block) where
  I : D.Interface P
  prm : SA.Params
  output : Nat → V → Block
  anchor : Nat → V → Block
  head : Nat → V → Option Block
  parent : Slot → Block → Block
  raw : Nat → Slot → V → Option Block
  leases : Nat → V → List (Block × Nat × Time)
  fast : Nat → Slot → V → List Block
  now : Nat → V → Time
  activeView : Nat → V → GridCO.State prm.n mode
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Read the admission levels from the supplied gate view. -/
  admissionLevels : GridCO.State prm.n mode → Slot → Block → List Nat

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Live lease targets are below the output (layout r2:572–574). -/
def LeaseBelowOutput {mode : GridCO.HeadMode} (A : ACReads E rho mode) : Prop :=
  ∀ i x, x ∈ rho.honest → ∀ lease ∈ A.leases i x,
    A.now i x < Lease.deadline lease → Block.Preceq (Lease.target lease) (A.output i x)

theorem LeaseBelowOutput_def {mode : GridCO.HeadMode} (A : ACReads E rho mode) : LeaseBelowOutput
    A =
    (∀ i x, x ∈ rho.honest → ∀ lease ∈ A.leases i x,
      A.now i x < Lease.deadline lease →
        Block.Preceq (Lease.target lease) (A.output i x)) := by
  rw [LeaseBelowOutput]

namespace ACReads

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
A missing label is `none`; an empty saved result is `some none`. -/
def saved {mode : GridCO.HeadMode} (A : ACReads E rho mode) (i : Nat) (x : V) (s : Slot) : Option
    (Option Block) :=
  GridCO.savedGenuine (A.activeView i x) s

theorem saved_def {mode : GridCO.HeadMode} (A : ACReads E rho mode) (i : Nat) (x : V) (s : Slot) :
    A.saved i x s = GridCO.savedGenuine (A.activeView i x) s := by
  rw [saved]

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The gate-relevant view: set the gate time, then expire leases. For SA and
FG-SA, the clock has no release step at this time. Its early-cache write does
not affect confirmation, admission levels, prefix support, or obligations.
The cache fields here need not equal all fields after the clock prefix. -/
def gateView {mode : GridCO.HeadMode} (A : ACReads E rho mode) (i : Nat) (x : V) (s : Slot) :
    GridCO.State A.prm.n mode :=
  GridCO.expire { A.activeView i x with now := SA.gateTime A.prm s } (SA.gateTime A.prm s)

theorem gateView_def {mode : GridCO.HeadMode} (A : ACReads E rho mode) (i : Nat) (x : V) (s :
    Slot) :
    A.gateView i x s =
      GridCO.expire { A.activeView i x with now := SA.gateTime A.prm s }
        (SA.gateTime A.prm s) := by
  rw [gateView]

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Read the instance's admission levels on the gate view. The instance
selects the policy (GLY F-6); Generic fixes no lease policy. -/
def gateLevels {mode : GridCO.HeadMode} (A : ACReads E rho mode) (i : Nat) (x : V) (s : Slot) (b
    : Block) : List Nat :=
  A.admissionLevels (A.gateView i x s) s b

theorem gateLevels_def {mode : GridCO.HeadMode} (A : ACReads E rho mode) (i : Nat) (x : V) (s :
    Slot) (b : Block) :
    A.gateLevels i x s b =
      A.admissionLevels (A.gateView i x s) s b := by
  rw [gateLevels]

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Active non-genesis prefixes of the raw gate result. -/
def gatePrefixes {mode : GridCO.HeadMode} (A : ACReads E rho mode) (i : Nat) (x : V) (s : Slot)
    (h : Block) : List Block :=
  (A.gateView i x s).blocks.filter (fun b => b != .genesis && Block.preceq b h)

theorem gatePrefixes_def {mode : GridCO.HeadMode} (A : ACReads E rho mode) (i : Nat) (x : V) (s :
    Slot) (h : Block) :
    A.gatePrefixes i x s h =
      (A.gateView i x s).blocks.filter (fun b => b != .genesis && Block.preceq b h) := by
  rw [gatePrefixes]

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The exact lease update in an accepted gate. `writeObligation` preserves
other keys and uses the maximum of the old and proposed deadlines. This also
describes renewal when a deadline does not change (GridCO Protocol:409–414).
`gateTime s + lifetime` is the proposed deadline in case (d), not an equality
for the stored deadline when an old deadline is larger. -/
def gateLeases {mode : GridCO.HeadMode} (A : ACReads E rho mode) (i : Nat) (x : V) (s : Slot) (h
    : Block) :
    List (Block × Nat × Time) :=
  ((A.gatePrefixes i x s h).foldl (fun st b =>
    (A.gateLevels i x s b).foldl (fun st g =>
      GridCO.writeObligation st b g (SA.gateTime A.prm s + SA.lifetime A.prm)) st)
    (A.gateView i x s)).obligations

theorem gateLeases_def {mode : GridCO.HeadMode} (A : ACReads E rho mode) (i : Nat) (x : V) (s :
    Slot) (h : Block) :
    A.gateLeases i x s h =
      ((A.gatePrefixes i x s h).foldl (fun st b =>
        (A.gateLevels i x s b).foldl (fun st g =>
          GridCO.writeObligation st b g (SA.gateTime A.prm s + SA.lifetime A.prm)) st)
        (A.gateView i x s)).obligations := by
  rw [gateLeases]

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The fast set of an accepted gate, with the shared prefix-support test. -/
def gateFast {mode : GridCO.HeadMode} (A : ACReads E rho mode) (i : Nat) (x : V) (s : Slot) (h :
    Block) : List Block :=
  (A.gateView i x s).blocks.filter (fun b => b != .genesis && Block.preceq b h &&
    decide (SA.releaseThreshold A.prm ≤ GridCO.prefixSupport A.prm.engine (A.gateView i x s) s b))

theorem gateFast_def {mode : GridCO.HeadMode} (A : ACReads E rho mode) (i : Nat) (x : V) (s :
    Slot) (h : Block) :
    A.gateFast i x s h =
      (A.gateView i x s).blocks.filter (fun b => b != .genesis && Block.preceq b h &&
        decide (SA.releaseThreshold A.prm ≤
          GridCO.prefixSupport A.prm.engine (A.gateView i x s) s b)) := by
  rw [gateFast]

end ACReads

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
A gate event at this node (aclaws-inputs.md:40). It need not change S. -/
def GateWrite {mode : GridCO.HeadMode} (A : ACReads E rho mode) (i : Nat) (x : V) : Prop :=
  ∃ s, rho.events[i]? = some (.tick x (SA.gateTime A.prm s))

theorem GateWrite_def {mode : GridCO.HeadMode} (A : ACReads E rho mode) (i : Nat) (x : V) :
    GateWrite A i x =
    (∃ s, rho.events[i]? = some (.tick x (SA.gateTime A.prm s))) := by
  rw [GateWrite]

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
A block delivery moves the anchor and adjusts S in the same event.
SA's constant genesis anchor makes this case impossible. -/
def Reconcile {mode : GridCO.HeadMode} (A : ACReads E rho mode) (i : Nat) (x : V) : Prop :=
  ∃ o t b, rho.events[i]? = some (.deliver x o t) ∧ A.I.block o.payload = some b ∧
    A.anchor (i + 1) x ≠ A.anchor i x ∧
    A.output (i + 1) x = normalizeOutput (A.anchor (i + 1) x) (A.output i x)

theorem Reconcile_def {mode : GridCO.HeadMode} (A : ACReads E rho mode) (i : Nat) (x : V) :
    Reconcile A i x =
    (∃ o t b, rho.events[i]? = some (.deliver x o t) ∧ A.I.block o.payload = some b ∧
      A.anchor (i + 1) x ≠ A.anchor i x ∧
      A.output (i + 1) x = normalizeOutput (A.anchor (i + 1) x) (A.output i x)) := by
  rw [Reconcile]

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Effects when the gate runs (aclaws-inputs.md:49–54; GridCO Protocol:451–486).
SA runs it even if the label has a saved result. Result storage is a separate
part of `GateWriteAtSpec`. In (b) and (c), `anchor_le_output` makes normalization
fix S. Case (d) retains normalization. Expiry precedes all cases. -/
structure GateRunSpec {mode : GridCO.HeadMode} (A : ACReads E rho mode) (i : Nat) (s : Slot) (x :
    V) : Prop where
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
(b) No lease write and an empty fast set. -/
  empty : A.raw i s x = none →
    A.output (i + 1) x = A.output i x ∧
      A.leases (i + 1) x = (A.gateView i x s).obligations ∧ A.fast i s x = []
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
(c) A live target vetoes the raw result. -/
  veto : ∀ h, A.raw i s x = some h →
    (∃ lease ∈ (A.gateView i x s).obligations, ¬ Block.Compatible (Lease.target lease) h) →
    A.output (i + 1) x = A.output i x ∧
      A.leases (i + 1) x = (A.gateView i x s).obligations ∧ A.fast i s x = []
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
(d) Advance, write leases at the admission levels, then normalize S.
  `gateLeases` takes the maximum of the old and proposed deadlines. -/
  accept : ∀ h, A.raw i s x = some h →
    (∀ lease ∈ (A.gateView i x s).obligations, Block.Compatible (Lease.target lease) h) →
    A.output (i + 1) x = normalizeOutput (A.anchor i x) (GridCO.advance (A.output i x) h) ∧
      A.leases (i + 1) x = A.gateLeases i x s h ∧ A.fast i s x = A.gateFast i x s h

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The gate law at one event. `GateWriteSpec` supplies the tick equation.
Saved results are preserved by gates, not by reconciliation or restart.
The effects allow the protocol choice: FG-SA skips a saved label; SA runs
the gate and preserves the saved result (FGSA Clock:28–33; GridCO:426–486). -/
structure GateWriteAtSpec {mode : GridCO.HeadMode} (A : ACReads E rho mode) (i : Nat) (s : Slot)
    (x : V) : Prop where
  view_output : (A.activeView i x).stableRecord = A.output i x
  view_leases : (A.activeView i x).obligations = A.leases i x
  view_now : (A.activeView i x).now = A.now i x
  anchor_eq : A.anchor (i + 1) x = A.anchor i x
  raw_eq : A.raw i s x = GridCO.confirmationFrom A.prm.engine (A.anchor i x) (A.gateView i x s) s
  saved_other : ∀ r, r ≠ s → A.saved (i + 1) x r = A.saved i x r
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
(a) A saved result stays unchanged, whether the gate skips or runs. -/
  saved : ∀ result, A.saved i x s = some result → A.saved (i + 1) x s = some result
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Save the raw result for a new label, including an empty or vetoed result. -/
  fresh : A.saved i x s = none → A.saved (i + 1) x s = some (A.raw i s x)
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Skip only if saved (FG-SA), or run the gate even if saved (SA).
  A skip keeps S and the leases after expiry and writes no fast set. -/
  effects : ((∃ result, A.saved i x s = some result) ∧
      A.output (i + 1) x = A.output i x ∧
      A.leases (i + 1) x = (A.gateView i x s).obligations ∧ A.fast i s x = []) ∨
    GateRunSpec A i s x

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The law at a tick event for label `s`. It has no schedule premise:
restarts, repeated ticks, and backward ticks are all in its scope. -/
def GateWriteSpec {mode : GridCO.HeadMode} (A : ACReads E rho mode) (i : Nat) (s : Slot) (x : V)
    : Prop :=
  rho.events[i]? = some (.tick x (SA.gateTime A.prm s)) → GateWriteAtSpec A i s x

theorem GateWriteSpec_def {mode : GridCO.HeadMode} (A : ACReads E rho mode) (i : Nat) (s : Slot)
    (x : V) :
    GateWriteSpec A i s x =
      (rho.events[i]? = some (.tick x (SA.gateTime A.prm s)) → GateWriteAtSpec A i s x) := by
  rw [GateWriteSpec]

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Instance laws, proved once by each protocol adapter. The restart branch
resets to the initial output read; it adds no separate initial-output field. -/
structure ACLaws {mode : GridCO.HeadMode} (A : ACReads E rho mode) : Prop where
  anchor_le_output : ∀ i x, Block.Preceq (A.anchor i x) (A.output i x)
  lease_le_output : LeaseBelowOutput A
  output_step : ∀ i x, A.output (i + 1) x = A.output i x ∨ GateWrite A i x ∨ Reconcile A i x ∨
    (∃ t, rho.events[i]? = some (.restart x t) ∧ A.output (i + 1) x = A.output 0 x)
  gate_write : ∀ i s x, GateWriteSpec A i s x

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The separate slot-only form under schedule uniqueness (D01).
`ScheduleWellFormed.nodup` (Conditions/Schedule.lean:26) gives at most one
tick of each node and label. Choose that tick's raw and fast observations;
values at absent ticks are unrestricted. Every gate case then holds with
these slot-only reads. No schedule premise enters `ACLaws`. -/
def GateWriteOfScheduleWellFormedStatement : Prop :=
  ∀ {V In : Type} {P : ProtocolSpecD In} {E : Generic.Env V} {rho : D.Run V P}
    {mode : GridCO.HeadMode} (A : ACReads E rho mode), ACLaws A → D.ScheduleWellFormed E rho →
    ∃ (raw : Slot → V → Option Block) (fast : Slot → V → List Block),
      ∀ i s x, rho.events[i]? = some (.tick x (SA.gateTime A.prm s)) →
        A.raw i s x = raw s x ∧ A.fast i s x = fast s x ∧
          GateWriteAtSpec
            ({ A with raw := fun _ => raw, fast := fun _ => fast } : ACReads E rho mode) i s x

theorem GateWriteOfScheduleWellFormedStatement_def :
    GateWriteOfScheduleWellFormedStatement =
      (∀ {V In : Type} {P : ProtocolSpecD In} {E : Generic.Env V} {rho : D.Run V P}
        {mode : GridCO.HeadMode} (A : ACReads E rho mode), ACLaws A → D.ScheduleWellFormed E rho →
        ∃ (raw : Slot → V → Option Block) (fast : Slot → V → List Block),
          ∀ i s x, rho.events[i]? = some (.tick x (SA.gateTime A.prm s)) →
            A.raw i s x = raw s x ∧ A.fast i s x = fast s x ∧
              GateWriteAtSpec
                ({ A with raw := fun _ => raw, fast := fun _ => fast } : ACReads E rho mode) i s
                  x) := by
  rw [GateWriteOfScheduleWellFormedStatement]

end AvailableChain.Gen.AC.Duty

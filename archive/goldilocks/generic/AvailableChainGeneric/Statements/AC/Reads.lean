module
public import AvailableChainEngineV2.Conditions.Interface
public import AvailableChainEngineV2.Conditions.Schedule
public import AvailableChainKitV2.ClockLaws -- shake: keep (re-export)
public import AvailableChainSA.Model.Protocol
public import AvailableChainModel.Objects.Blocks -- shake: keep (re-export)

@[expose] public section

namespace AvailableChain.Gen.AC

open AvailableChain AvailableChain.V2 AvailableChain.V2.Engine

/-! AC reads and instance laws (layout r2:1090–1106; aclaws-inputs.md:9–56;
step2-rulings.md, B10). The active view supplies the saved results. Admission
levels are an instance read; lifetime and prefix support use the SA model.
No field describes a restart-free interval. -/

namespace Lease

/-- The target of a Grid CO obligation tuple. -/
def target (lease : Block × Nat × Time) : Block := lease.1

theorem target_def (lease : Block × Nat × Time) : target lease = lease.1 := by
  rw [target]

/-- The admission level of a Grid CO obligation tuple. -/
def level (lease : Block × Nat × Time) : Nat := lease.2.1

theorem level_def (lease : Block × Nat × Time) : level lease = lease.2.1 := by
  rw [level]

/-- The deadline of a Grid CO obligation tuple. -/
def deadline (lease : Block × Nat × Time) : Time := lease.2.2

theorem deadline_def (lease : Block × Nat × Time) : deadline lease = lease.2.2 := by
  rw [deadline]

end Lease

variable {V : Type} {In : Type} {P : ProtocolSpec In}
  {E : Generic.Env V} {rho : Run V P}

/-- Store reads and gate observations at event indices.
`activeView` is the view before event `i`: FG-SA filters the block domain by
compatibility with the anchor; SA uses its full state and the genesis anchor.
`raw i s x` is confirmation on the gate view at event `i`, including when
the gate is skipped. `fast i s x` records the fast set written at that event;
it is empty on a skipped gate. These are not saved values after reconciliation
or restart. Repeated ticks of one label can have different observations.
The active view contains the saved label results; it adds no clock operation
or protocol-specific retention predicate to these reads. -/
structure ACReads (E : Generic.Env V) (rho : Run V P) where
  I : Interface P
  prm : SA.Params
  output : Nat → V → Block
  anchor : Nat → V → Block
  head : Nat → V → Option Block
  parent : Slot → Block → Block
  raw : Nat → Slot → V → Option Block
  leases : Nat → V → List (Block × Nat × Time)
  fast : Nat → Slot → V → List Block
  now : Nat → V → Time
  activeView : Nat → V → SA.State prm.n
  /-- Read the admission levels from the supplied gate view. -/
  admissionLevels : SA.State prm.n → Slot → Block → List Nat

/-- Live lease targets are below the output (layout r2:572–574). -/
def LeaseBelowOutput (A : ACReads E rho) : Prop :=
  ∀ i x, x ∈ rho.honest → ∀ lease ∈ A.leases i x,
    A.now i x < Lease.deadline lease → Block.Preceq (Lease.target lease) (A.output i x)

theorem LeaseBelowOutput_def (A : ACReads E rho) : LeaseBelowOutput A =
    (∀ i x, x ∈ rho.honest → ∀ lease ∈ A.leases i x,
      A.now i x < Lease.deadline lease →
        Block.Preceq (Lease.target lease) (A.output i x)) := by
  rw [LeaseBelowOutput]

/-- The output adjustment used after a gate and a finality change
(FGSA/Model/Store.lean:57–59). -/
def normalizeOutput (anchor output : Block) : Block :=
  if Block.preceq anchor output then output else anchor

theorem normalizeOutput_def (anchor output : Block) : normalizeOutput anchor output =
    (if Block.preceq anchor output then output else anchor) := by
  rw [normalizeOutput]

namespace ACReads

/-- A missing label is `none`; an empty saved result is `some none`. -/
def saved (A : ACReads E rho) (i : Nat) (x : V) (s : Slot) : Option (Option Block) :=
  SA.savedGenuine (A.activeView i x) s

theorem saved_def (A : ACReads E rho) (i : Nat) (x : V) (s : Slot) :
    A.saved i x s = SA.savedGenuine (A.activeView i x) s := by
  rw [saved]

/-- The gate-relevant view: set the gate time, then expire leases. For SA and
FG-SA, the clock has no release step at this time. Its early-cache write does
not affect confirmation, admission levels, prefix support, or obligations.
The cache fields here need not equal all fields after the clock prefix. -/
def gateView (A : ACReads E rho) (i : Nat) (x : V) (s : Slot) : SA.State A.prm.n :=
  SA.expire { A.activeView i x with now := SA.gateTime A.prm s } (SA.gateTime A.prm s)

theorem gateView_def (A : ACReads E rho) (i : Nat) (x : V) (s : Slot) :
    A.gateView i x s =
      SA.expire { A.activeView i x with now := SA.gateTime A.prm s }
        (SA.gateTime A.prm s) := by
  rw [gateView]

/-- Read the instance's admission levels on the gate view. The instance
selects the policy (GLY F-6); Generic fixes no lease policy. -/
def gateLevels (A : ACReads E rho) (i : Nat) (x : V) (s : Slot) (b : Block) : List Nat :=
  A.admissionLevels (A.gateView i x s) s b

theorem gateLevels_def (A : ACReads E rho) (i : Nat) (x : V) (s : Slot) (b : Block) :
    A.gateLevels i x s b =
      A.admissionLevels (A.gateView i x s) s b := by
  rw [gateLevels]

/-- Active non-genesis prefixes of the raw gate result. -/
def gatePrefixes (A : ACReads E rho) (i : Nat) (x : V) (s : Slot) (h : Block) : List Block :=
  (A.gateView i x s).blocks.filter (fun b => b != .genesis && Block.preceq b h)

theorem gatePrefixes_def (A : ACReads E rho) (i : Nat) (x : V) (s : Slot) (h : Block) :
    A.gatePrefixes i x s h =
      (A.gateView i x s).blocks.filter (fun b => b != .genesis && Block.preceq b h) := by
  rw [gatePrefixes]

/-- The exact lease update in an accepted gate. `writeObligation` preserves
other keys and uses the maximum of the old and proposed deadlines. This also
describes renewal when a deadline does not change (GridCO Protocol:409–414).
`gateTime s + lifetime` is the proposed deadline in case (d), not an equality
for the stored deadline when an old deadline is larger. -/
def gateLeases (A : ACReads E rho) (i : Nat) (x : V) (s : Slot) (h : Block) :
    List (Block × Nat × Time) :=
  ((A.gatePrefixes i x s h).foldl (fun st b =>
    (A.gateLevels i x s b).foldl (fun st g =>
      GridCO.writeObligation st b g (SA.gateTime A.prm s + SA.lifetime A.prm)) st)
    (A.gateView i x s)).obligations

theorem gateLeases_def (A : ACReads E rho) (i : Nat) (x : V) (s : Slot) (h : Block) :
    A.gateLeases i x s h =
      ((A.gatePrefixes i x s h).foldl (fun st b =>
        (A.gateLevels i x s b).foldl (fun st g =>
          GridCO.writeObligation st b g (SA.gateTime A.prm s + SA.lifetime A.prm)) st)
        (A.gateView i x s)).obligations := by
  rw [gateLeases]

/-- The fast set of an accepted gate, with the shared prefix-support test. -/
def gateFast (A : ACReads E rho) (i : Nat) (x : V) (s : Slot) (h : Block) : List Block :=
  (A.gateView i x s).blocks.filter (fun b => b != .genesis && Block.preceq b h &&
    decide (SA.releaseThreshold A.prm ≤ SA.prefixSupport A.prm (A.gateView i x s) s b))

theorem gateFast_def (A : ACReads E rho) (i : Nat) (x : V) (s : Slot) (h : Block) :
    A.gateFast i x s h =
      (A.gateView i x s).blocks.filter (fun b => b != .genesis && Block.preceq b h &&
        decide (SA.releaseThreshold A.prm ≤
          SA.prefixSupport A.prm (A.gateView i x s) s b)) := by
  rw [gateFast]

end ACReads

/-- A gate event at this node (aclaws-inputs.md:40). It need not change S. -/
def GateWrite (A : ACReads E rho) (i : Nat) (x : V) : Prop :=
  ∃ s, rho.events[i]? = some (.tick x (SA.gateTime A.prm s))

theorem GateWrite_def (A : ACReads E rho) (i : Nat) (x : V) : GateWrite A i x =
    (∃ s, rho.events[i]? = some (.tick x (SA.gateTime A.prm s))) := by
  rw [GateWrite]

/-- A block delivery moves the anchor and adjusts S in the same event.
SA's constant genesis anchor makes this case impossible. -/
def Reconcile (A : ACReads E rho) (i : Nat) (x : V) : Prop :=
  ∃ o t b, rho.events[i]? = some (.deliver x o t) ∧ A.I.block o.payload = some b ∧
    A.anchor (i + 1) x ≠ A.anchor i x ∧
    A.output (i + 1) x = normalizeOutput (A.anchor (i + 1) x) (A.output i x)

theorem Reconcile_def (A : ACReads E rho) (i : Nat) (x : V) : Reconcile A i x =
    (∃ o t b, rho.events[i]? = some (.deliver x o t) ∧ A.I.block o.payload = some b ∧
      A.anchor (i + 1) x ≠ A.anchor i x ∧
      A.output (i + 1) x = normalizeOutput (A.anchor (i + 1) x) (A.output i x)) := by
  rw [Reconcile]

/-- Effects when the gate runs (aclaws-inputs.md:49–54; GridCO Protocol:451–486).
SA runs it even if the label has a saved result. Result storage is a separate
part of `GateWriteAtSpec`. In (b) and (c), `anchor_le_output` makes normalization
fix S. Case (d) retains normalization. Expiry precedes all cases. -/
structure GateRunSpec (A : ACReads E rho) (i : Nat) (s : Slot) (x : V) : Prop where
  /-- (b) No lease write and an empty fast set. -/
  empty : A.raw i s x = none →
    A.output (i + 1) x = A.output i x ∧
      A.leases (i + 1) x = (A.gateView i x s).obligations ∧ A.fast i s x = []
  /-- (c) A live target vetoes the raw result. -/
  veto : ∀ h, A.raw i s x = some h →
    (∃ lease ∈ (A.gateView i x s).obligations, ¬ Block.Compatible (Lease.target lease) h) →
    A.output (i + 1) x = A.output i x ∧
      A.leases (i + 1) x = (A.gateView i x s).obligations ∧ A.fast i s x = []
  /-- (d) Advance, write leases at the admission levels, then normalize S.
  `gateLeases` takes the maximum of the old and proposed deadlines. -/
  accept : ∀ h, A.raw i s x = some h →
    (∀ lease ∈ (A.gateView i x s).obligations, Block.Compatible (Lease.target lease) h) →
    A.output (i + 1) x = normalizeOutput (A.anchor i x) (GridCO.advance (A.output i x) h) ∧
      A.leases (i + 1) x = A.gateLeases i x s h ∧ A.fast i s x = A.gateFast i x s h

/-- The gate law at one event. `GateWriteSpec` supplies the tick equation.
Saved results are preserved by gates, not by reconciliation or restart.
The effects allow the protocol choice: FG-SA skips a saved label; SA runs
the gate and preserves the saved result (FGSA Clock:28–33; GridCO:426–486). -/
structure GateWriteAtSpec (A : ACReads E rho) (i : Nat) (s : Slot) (x : V) : Prop where
  view_output : (A.activeView i x).stableRecord = A.output i x
  view_leases : (A.activeView i x).obligations = A.leases i x
  view_now : (A.activeView i x).now = A.now i x
  anchor_eq : A.anchor (i + 1) x = A.anchor i x
  raw_eq : A.raw i s x = SA.confirmationFrom A.prm (A.anchor i x) (A.gateView i x s) s
  saved_other : ∀ r, r ≠ s → A.saved (i + 1) x r = A.saved i x r
  /-- (a) A saved result stays unchanged, whether the gate skips or runs. -/
  saved : ∀ result, A.saved i x s = some result → A.saved (i + 1) x s = some result
  /-- Save the raw result for a new label, including an empty or vetoed result. -/
  fresh : A.saved i x s = none → A.saved (i + 1) x s = some (A.raw i s x)
  /-- Skip only if saved (FG-SA), or run the gate even if saved (SA).
  A skip keeps S and the leases after expiry and writes no fast set. -/
  effects : ((∃ result, A.saved i x s = some result) ∧
      A.output (i + 1) x = A.output i x ∧
      A.leases (i + 1) x = (A.gateView i x s).obligations ∧ A.fast i s x = []) ∨
    GateRunSpec A i s x

/-- The law at a tick event for label `s`. It has no schedule premise:
restarts, repeated ticks, and backward ticks are all in its scope. -/
def GateWriteSpec (A : ACReads E rho) (i : Nat) (s : Slot) (x : V) : Prop :=
  rho.events[i]? = some (.tick x (SA.gateTime A.prm s)) → GateWriteAtSpec A i s x

theorem GateWriteSpec_def (A : ACReads E rho) (i : Nat) (s : Slot) (x : V) :
    GateWriteSpec A i s x =
      (rho.events[i]? = some (.tick x (SA.gateTime A.prm s)) → GateWriteAtSpec A i s x) := by
  rw [GateWriteSpec]

/-- Instance laws, proved once by each protocol adapter. The restart branch
resets to the initial output read; it adds no separate initial-output field. -/
structure ACLaws (A : ACReads E rho) : Prop where
  anchor_le_output : ∀ i x, Block.Preceq (A.anchor i x) (A.output i x)
  lease_le_output : LeaseBelowOutput A
  output_step : ∀ i x, A.output (i + 1) x = A.output i x ∨ GateWrite A i x ∨ Reconcile A i x ∨
    (∃ t, rho.events[i]? = some (.restart x t) ∧ A.output (i + 1) x = A.output 0 x)
  gate_write : ∀ i s x, GateWriteSpec A i s x

/-- The separate slot-only form under schedule uniqueness (D01).
`ScheduleWellFormed.nodup` (Conditions/Schedule.lean:26) gives at most one
tick of each node and label. Choose that tick's raw and fast observations;
values at absent ticks are unrestricted. Every gate case then holds with
these slot-only reads. No schedule premise enters `ACLaws`. -/
def GateWriteOfScheduleWellFormedStatement : Prop :=
  ∀ {V In : Type} {P : ProtocolSpec In} {E : Generic.Env V} {rho : Run V P}
    (A : ACReads E rho), ACLaws A → ScheduleWellFormed E rho →
    ∃ (raw : Slot → V → Option Block) (fast : Slot → V → List Block),
      ∀ i s x, rho.events[i]? = some (.tick x (SA.gateTime A.prm s)) →
        A.raw i s x = raw s x ∧ A.fast i s x = fast s x ∧
          GateWriteAtSpec
            ({ A with raw := fun _ => raw, fast := fun _ => fast } : ACReads E rho) i s x

theorem GateWriteOfScheduleWellFormedStatement_def :
    GateWriteOfScheduleWellFormedStatement =
      (∀ {V In : Type} {P : ProtocolSpec In} {E : Generic.Env V} {rho : Run V P}
        (A : ACReads E rho), ACLaws A → ScheduleWellFormed E rho →
        ∃ (raw : Slot → V → Option Block) (fast : Slot → V → List Block),
          ∀ i s x, rho.events[i]? = some (.tick x (SA.gateTime A.prm s)) →
            A.raw i s x = raw s x ∧ A.fast i s x = fast s x ∧
              GateWriteAtSpec
                ({ A with raw := fun _ => raw, fast := fun _ => fast } : ACReads E rho) i s x) := by
  rw [GateWriteOfScheduleWellFormedStatement]

end AvailableChain.Gen.AC

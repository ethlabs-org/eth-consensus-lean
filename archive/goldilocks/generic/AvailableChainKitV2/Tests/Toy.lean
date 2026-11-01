module
public import AvailableChainKitV2.Execution
public import AvailableChainEngineV2.Conditions.Delivery
public import AvailableChainEngineV2.Laws.Outputs
public import AvailableChainEngineV2.Laws.SelfDelivery
public import AvailableChainKitV2.RunCheck

@[expose] public section

/-! ROOT-DIGEST W3: explicit roots for finite test fixtures. -/

/-! A toy protocol on engine v2 and a complete valid run (plan 2a, Task 6;
Review Focus 4; Task 5 review M1).

The toy has receipts in the base and the own record outside it, a clock that
keeps the state, one `Linked` self-visible label `row` (two seats, one for
each validator) whose payload is a row that the node has not signed before
and that carries nothing, and one one-seat AP proposal label `prop s` for
each slot `s`. It has `Interface`, `Isolation`, `OutputsFactor` and
`HooksSound` values.

The run `toyRun` has two honest validators and twelve events: at time 0 both
tick and every released object goes to both nodes, among them a self-delivery
at the emission time; at time 1 both tick and the proposal of slot 1 goes to
both nodes. The run is `ExecutionValid`, it satisfies `SelfDelivery`,
`PartialSynchrony` and `HealthyPrefixDelivery` at every cut, and the
hypotheses of `selfDelivery_admissible` hold at the self-delivery of
validator 0. A second, shorter run `pre` shows the append form
`ExecutionValid.snoc_selfDelivery`.

Limits. In the runs, every row is `row 0`: the row label is due only at time
0, when the own record is empty. The row payload reads the own record only
in an off-run check. The toy does not exercise exclusion (`excludes` is
`false`), carried objects (`carries` is `False`), the fresh family (it is
empty) or restarts (`restore` is the identity; restart toys are plan 2c). -/

namespace AvailableChain.V2.Tests.Toy

open AvailableChain AvailableChain.V2 AvailableChain.V2.Engine

/-! ### The toy protocol -/

/-- The labels: one row label and one proposal label for each slot. -/
inductive ToyLabel where
  | row
  | prop (s : Slot)
  deriving DecidableEq

/-- The row label is the only self-visible label. -/
def ToyLabel.isRow : ToyLabel → Bool
  | .row => true
  | .prop _ => false

/-- The row label has one seat for each validator; a proposal label has one
seat. -/
def toySeats : ToyLabel → Nat
  | .row => 2
  | .prop _ => 1

/-- A row `n`, or the proposal of slot `s` with the receipt count `n` and the
input `x` (the block body). -/
inductive ToyPayload where
  | row (n : Nat)
  | prop (s : Slot) (n : Nat) (x : Nat)
  deriving DecidableEq

/-- The wire objects of the toy. -/
abbrev ToyObject : Type := Signed ToyLabel toySeats ToyPayload

/-- The receipts `rcpt` (the base) and the own record `own` (outside the
base). -/
structure ToyState where
  rcpt : List ToyObject
  own : List ToyObject
  deriving DecidableEq

/-- The row label is due at time 0; the proposal label of slot `s` at time
`s`. -/
def toyActTime : ToyLabel → Time
  | .row => 0
  | .prop s => (s : Time)

/-- The labels due at time `t`, in the order row, proposal. -/
def toyDuties (t : Time) : List ToyLabel :=
  (if t = 0 then [.row] else []) ++ (if 0 ≤ t then [.prop t.toNat] else [])

theorem toyDuties_spec (ℓ : ToyLabel) (t : Time) : ℓ ∈ toyDuties t ↔ toyActTime ℓ = t := by
  unfold toyDuties toyActTime
  cases ℓ with
  | row =>
    by_cases h0 : t = 0 <;> by_cases h1 : 0 ≤ t <;> simp [h0, h1, eq_comm]
  | prop s =>
    constructor
    · intro h
      rcases List.mem_append.mp h with h | h
      · split_ifs at h <;> simp at h
      · split_ifs at h with h1
        · rw [List.mem_singleton, ToyLabel.prop.injEq] at h
          subst h; exact Int.toNat_of_nonneg h1
        · simp at h
    · rintro rfl
      refine List.mem_append_right _ ?_
      rw [ite_eq_left (Int.natCast_nonneg s), Int.toNat_natCast]
      exact List.mem_singleton_self _

theorem toyDuties_nodup (t : Time) : (toyDuties t).Nodup := by
  unfold toyDuties
  split_ifs <;> simp

/-- The row payload: the number of rows in the own record, so a node never
signs one row twice. -/
def toyAct : ToyState → ToyLabel → Nat → Option ToyPayload
  | st, .row, _ => some (.row st.own.length)
  | st, .prop s, x => some (.prop s st.rcpt.length x)

/-- The toy protocol. The input is the block body of a proposal. A delivery
adds the object to the receipts; the own record adds it to `own`. A restart
keeps the whole state. -/
abbrev toyP : ProtocolSpec Nat where
  State := ToyState
  Label := ToyLabel
  seats := toySeats
  Payload := ToyPayload
  Durable := ToyState
  init := ⟨[], []⟩
  clock := fun st _ => st
  actTime := toyActTime
  duties := toyDuties
  duties_spec := toyDuties_spec
  duties_nodup := toyDuties_nodup
  act := toyAct
  gossip := fun _ _ => []
  process := fun st o => { st with rcpt := o :: st.rcpt }
  selfVisible := ToyLabel.isRow
  recordOwn := fun st o => { st with own := o :: st.own }
  durable := id
  restore := fun d _ => d
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun st o => decide (o ∈ st.rcpt)
  excludes := fun _ _ => false
  handles := fun _ o o' => o = o'
  carries := fun _ _ => False

/-! ### Families, isolation, interface, outputs -/

/-- Proposal labels are AP labels; the row label is linked; no label is fresh. -/
def toyFam : LabelFamilies toyP :=
  ⟨fun ℓ => ℓ.isRow = false, fun _ => False, fun ℓ => ℓ = .row⟩

/-- The base is the receipt list. -/
def toyIso : Isolation toyP toyFam where
  Base := List ToyObject
  base := ToyState.rcpt
  clockB := fun b _ => b
  clock_base := fun _ _ => rfl
  processB := fun b o => o :: b
  process_base := fun _ _ => rfl
  recordOwn_base := fun _ _ => rfl
  actB := fun b ℓ x => match ℓ with
    | .row => none
    | .prop s => some (.prop s b.length x)
  act_base := fun _ ℓ _ h => by
    cases ℓ with
    | row => exact absurd (show true = false from h) (by decide)
    | prop _ => rfl
  gossipB := fun _ _ => []
  gossip_base := fun _ _ => rfl
  depsB := fun _ _ => true
  processedB := fun b o => decide (o ∈ b)
  excludesB := fun _ _ => false
  handlesB := fun _ o o' => o = o'
  hooks_base := fun _ _ _ => ⟨rfl, rfl, rfl, fun _ _ => Iff.rfl⟩
  separation := fun ℓ h => by
    rcases h with h | h
    · exact h
    · exact h.elim

/-- The block of the latest proposal in a receipt list. -/
def latestBlock : List ToyObject → Block
  | [] => .genesis
  | o :: r => match o.payload with
    | .prop s _ x => .node .genesis s (nodeRoot Block.genesis.root s x) x
    | .row _ => latestBlock r

/-- The confirmed output is the block of the latest received proposal. -/
def toyI : Interface toyP where
  confirmed := fun st => latestBlock st.rcpt
  stable := fun _ => .genesis
  block := fun p => match p with
    | .prop s _ x => some (.node .genesis s (nodeRoot Block.genesis.root s x) x)
    | .row _ => none
  opening := fun _ => True
  propLabel := .prop
  propLabel_single := fun _ => rfl
  propLabel_injective := fun _ _ h => ToyLabel.prop.inj h

/-- Both outputs factor through the receipts. -/
def toyO : OutputsFactor toyI toyIso where
  confirmedB := latestBlock
  confirmed_base := fun _ => rfl
  stableB := fun _ => .genesis
  stable_base := fun _ => rfl

example : SingleSeat toyP toyFam.ap := by
  intro ℓ h
  cases ℓ with
  | row => exact absurd (show true = false from h) (by decide)
  | prop _ => rfl

-- The row label is linked, and it is not an AP label or a fresh label.
example : toyP.selfVisible .row = true ∧ ¬ toyFam.ap .row ∧ ¬ toyFam.fresh .row :=
  ⟨rfl, (toyIso.not_ap_of_selfVisible rfl).1, (toyIso.not_ap_of_selfVisible rfl).2⟩
-- The proposal payload reads the base; the row payload reads the own record.
example (st : ToyState) (s x : Nat) :
    toyP.act st (toyI.propLabel s) x = toyIso.actB (toyIso.base st) (.prop s) x :=
  toyIso.act_base st (.prop s) x rfl
example : toyP.act ⟨[], [⟨.none, .row 0⟩]⟩ .row 0 = some (.row 1) := rfl

/-! ### Hooks -/

section

variable {V : Type} [DecidableEq V]

/-- A step keeps every receipt. -/
theorem rcpt_step (E : Generic.Env V) (rho : Run V toyP) (w : World V toyP)
    (e : Event V toyP.Object) (v : V) {o : ToyObject} (ho : o ∈ (w v).rcpt) :
    o ∈ (World.step E rho w e v).rcpt := by
  cases e with
  | restart u _ =>
    by_cases h : u = v
    · subst h; simpa [World.step] using ho
    · rwa [World.step, Function.update_of_ne (Ne.symm h)]
  | tick u t =>
    by_cases h : u = v
    · subst h
      rw [World.step, Function.update_self]
      have hb := toyIso.base_tick E rho (w u) u t
      exact (show (tick E rho (w u) u t).1.rcpt = (w u).rcpt from hb) ▸ ho
    · rwa [World.step, Function.update_of_ne (Ne.symm h)]
  | deliver u o' _ =>
    by_cases h : u = v
    · subst h
      rw [World.step, Function.update_self]
      exact List.mem_cons_of_mem _ ho
    · rwa [World.step, Function.update_of_ne (Ne.symm h)]

/-- Receipts only grow along a run, restarts included. -/
theorem rcpt_mono (E : Generic.Env V) (rho : Run V toyP) (v : V) {i j : Nat} (hij : i ≤ j)
    {o : ToyObject} (ho : o ∈ (Run.stateBefore E rho i v).rcpt) :
    o ∈ (Run.stateBefore E rho j v).rcpt := by
  induction j, hij using Nat.le_induction with
  | base => exact ho
  | succ j _ ih =>
    cases he : rho.events[j]? with
    | none => simpa [Run.stateBefore, List.take_add_one, he] using ih
    | some e =>
      rw [Run.stateBefore_succ E rho he]
      exact rcpt_step E rho _ e v ih

/-- The toy satisfies the hook obligations. -/
theorem toyHooks : HooksSound toyP where
  excludes_inert := fun _ _ h => absurd h Bool.false_ne_true
  excludes_stable := fun _ _ _ _ _ _ _ _ _ h => h
  processed_stable := fun E rho _ v _ _ _ hij _ h => by
    simp only [decide_eq_true_eq] at h ⊢
    exact rcpt_mono E rho v hij h
  deps_stable := fun _ _ _ _ _ _ _ _ _ h => h
  handles_carries := fun _ _ _ h => Or.inl h
  recordOwn_processed := fun _ _ _ => rfl
  recordOwn_deps := fun _ _ _ => rfl
  recordOwn_excludes := fun _ _ _ h => h

end

/-! ### The run -/

/-- Every node is awake; `Δ = 1`; GST is 0. -/
def toyEnv : Generic.Env (Fin 2) :=
  ⟨1, by decide, 0, le_rfl, fun _ _ => true⟩

/-- The row of validator `i`. -/
def rowObj (i : Fin 2) : toyP.Object := ⟨.seat .row i, .row 0⟩
/-- The proposal of slot 0 by validator 0: no receipt, input 7. -/
def prop0 : toyP.Object := ⟨.seat (.prop 0) ⟨0, by decide⟩, .prop 0 0 7⟩
/-- The proposal of slot 1 by validator 1: three receipts, input 8. -/
def prop1 : toyP.Object := ⟨.seat (.prop 1) ⟨0, by decide⟩, .prop 1 3 8⟩

/-- Two honest validators. Seat `i` of the row label is validator `i`; the
proposer of slot `s` is validator `s % 2`; the input of validator `v` is
`v + 7`. -/
def toyRun : Run (Fin 2) toyP where
  honest := Finset.univ
  horizon := 1
  events :=
    [.tick 0 0, .tick 1 0,
      .deliver 1 (rowObj 0) 0, .deliver 0 (rowObj 0) 0,
      .deliver 1 prop0 0, .deliver 0 prop0 0,
      .deliver 1 (rowObj 1) 0, .deliver 0 (rowObj 1) 0,
      .tick 0 1, .tick 1 1,
      .deliver 1 prop1 1, .deliver 0 prop1 1]
  seatOf := fun ℓ i => match ℓ with
    | .row => i
    | .prop s => ⟨s % 2, Nat.mod_lt _ (by decide)⟩
  input := fun v _ => v.val + 7

-- The releases: rows and the proposal of slot 0 at time 0; the proposal of
-- slot 1 at time 1.
example : Run.emitsAt toyEnv toyRun 0 = [rowObj 0, prop0] := by decide +kernel
example : Run.emitsAt toyEnv toyRun 1 = [rowObj 1] := by decide +kernel
example : Run.emitsAt toyEnv toyRun 8 = [] := by decide +kernel
example : Run.emitsAt toyEnv toyRun 9 = [prop1] := by decide +kernel
-- The tick at index 0 records the row of validator 0 in its own record, not in
-- its receipts.
example : Run.stateBefore toyEnv toyRun 1 0 = ⟨[], [rowObj 0]⟩ := by decide +kernel
-- The row label is linked through the identity bijection.
example : Linked toyFam.linked toyRun := by
  refine ⟨2, Equiv.refl _, fun ℓ hℓ => ?_⟩
  subst hℓ
  exact ⟨rfl, fun _ => rfl⟩
example : proposerOf toyRun toyI 0 = 0 ∧ proposerOf toyRun toyI 1 = 1 := ⟨rfl, rfl⟩
-- The outputs at time 1.
example : outputAt toyEnv toyRun toyI.confirmed 0 1 = .node .genesis 1 (nodeRoot Block.genesis.root
    1 8) 8 := by decide +kernel
example : BlockInRun toyEnv toyI toyRun (.node .genesis 1 (nodeRoot Block.genesis.root 1 8) 8) :=
  Or.inr ⟨0, prop1, 1, _, Or.inl ⟨11, rfl⟩, rfl, by decide⟩

/-! ### Validity (Review Focus 4) -/

/-- No delivery repeats an object at its receiver. -/
theorem toyRun_fresh :
    allDeliveries toyRun (fun k v o _ => !toyP.processed (Run.stateBefore toyEnv toyRun k v) o)
      = true := by
  decide +kernel

/-- An honest holder of a delivered object emitted it at a time at most the
delivery time. -/
theorem toyRun_signed :
    allDeliveries toyRun (fun _ _ o t => (List.finRange 2).all fun u =>
      !decide (Run.holder toyRun o.auth = some u) || emittedBy toyEnv toyRun u o t) = true := by
  decide +kernel

/-- The whole run is valid. -/
theorem toyRun_valid : ExecutionValid toyEnv toyRun := by
  refine { toScheduleWellFormed := ?_, toDeliveryWellFormed := ?_,
           toUnforgeableSignatures := ?_,
           tick_awake := fun _ _ _ => rfl, deliver_awake := fun _ _ _ _ => rfl,
           restart_awake := fun _ _ _ => rfl,
           wake_restart := fun _ _ _ _ _ hw => by cases hw.2 }
  · refine ⟨by decide, by decide +kernel, by decide +kernel, by decide +kernel,
      fun _ _ => Finset.mem_univ _, ?_, ?_⟩
    · intro v t h
      have h0 := ((by decide +kernel : ∀ e ∈ toyRun.events, 0 ≤ e.time ∧ e.time ≤ 1) _ h).1
      exact ⟨t.toNat, by
        change t = (t.toNat : Time) * 1
        rw [mul_one]; exact (Int.toNat_of_nonneg h0).symm⟩
    · intro v _ t _ h0 h1 _
      change t ≤ 1 at h1
      have hv : ∀ u : Fin 2, Event.tick u 0 ∈ toyRun.events ∧ Event.tick u 1 ∈ toyRun.events := by
        decide +kernel
      obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
      have hn : n ≤ 1 := by exact_mod_cast h1
      rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
      · exact (hv v).1
      · exact (hv v).2
  · refine ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun k v o t hk => ?_⟩
    simpa using allDeliveries_spec toyRun_fresh hk
  · refine ⟨?_, fun _ _ _ _ _ hc => hc.elim⟩
    rintro v o t ⟨k, hk⟩ u _ hu
    have h := List.all_eq_true.mp (allDeliveries_spec toyRun_signed hk) u (List.mem_finRange u)
    rw [hu] at h
    exact emittedBy_spec (by simpa using h)

/-! ### Self-delivery -/

/-- The row of validator 0, released by the tick at index 0, passes `EmitOk`
at that tick: well-formed, dependencies present, not processed in the
post-clock state, and it carries nothing. -/
theorem row0_emitOk :
    EmitOk toyEnv toyRun (Run.stateBefore toyEnv toyRun 0 0) 0 0 (rowObj 0) :=
  ⟨rfl, rfl, by decide +kernel, fun _ h => h⟩

-- The hypotheses of `selfDelivery_admissible` at the self-delivery at index 3
-- (validator 0 gets its own row at the emission time 0): the tick at index 0
-- releases the row, `EmitOk` holds, and the state of validator 0 before index
-- 3 is its post-tick state (indices 1 and 2 are events of validator 1).
example : toyRun.events[3]? = some (.deliver 0 (rowObj 0) 0) := rfl
example : toyP.objSelfVisible (rowObj 0) = true := rfl
example : Run.stateBefore toyEnv toyRun 3 0 = Run.stateBefore toyEnv toyRun (0 + 1) 0 := by
  decide +kernel
example : toyP.processed (Run.stateBefore toyEnv toyRun 3 0) (rowObj 0) = false :=
  (selfDelivery_admissible toyHooks (i := 0) (j := 3) rfl (by decide +kernel) row0_emitOk
    (by decide +kernel)).2.2.1

/-! ### The append form (Task 6 review M1)

`ExecutionValid.snoc_selfDelivery` on the toy: a valid prefix `pre` with two
honest validators, an event of the other node after the tick (so `hlast` is
not vacuous), receipts that `processed` reads, and an own record that
changes the state. Its premise `hkey` (every event key at most `(t, 2)`) and
the field `tick_total` force the appended run to end at time `t`: its
horizon is below the next public time. So a witness that continues after the
self-delivery, like `toyRun`, needs the direct proof above. -/

/-- Both validators tick at time 0, and validator 1 gets the row of validator
0; validator 0 has no event after its tick. -/
def pre : Run (Fin 2) toyP where
  honest := Finset.univ
  horizon := 0
  events := [.tick 0 0, .tick 1 0, .deliver 1 (rowObj 0) 0]
  seatOf := toyRun.seatOf
  input := toyRun.input

/-- No delivery of `pre` repeats an object at its receiver. -/
theorem pre_fresh :
    allDeliveries pre (fun k v o _ => !toyP.processed (Run.stateBefore toyEnv pre k v) o)
      = true := by decide +kernel

/-- An honest holder of an object delivered in `pre` emitted it. -/
theorem pre_signed :
    allDeliveries pre (fun _ _ o t => (List.finRange 2).all fun u =>
      !decide (Run.holder pre o.auth = some u) || emittedBy toyEnv pre u o t) = true := by
  decide +kernel

/-- The prefix is valid. -/
theorem pre_valid : ExecutionValid toyEnv pre := by
  refine { toScheduleWellFormed := ?_, toDeliveryWellFormed := ?_,
           toUnforgeableSignatures := ?_,
           tick_awake := fun _ _ _ => rfl, deliver_awake := fun _ _ _ _ => rfl,
           restart_awake := fun _ _ _ => rfl,
           wake_restart := fun _ _ _ _ _ hw => by cases hw.2 }
  · refine ⟨by decide, by decide +kernel, by decide +kernel, by decide +kernel,
      fun _ _ => Finset.mem_univ _, ?_, ?_⟩
    · intro v t h
      have h0 := ((by decide +kernel : ∀ e ∈ pre.events, e.time = 0) _ h)
      exact ⟨0, by change t = ((0 : Nat) : Time) * 1; simpa using! h0⟩
    · intro v _ t _ h0 h1 _
      change t ≤ 0 at h1
      have ht : t = 0 := le_antisymm h1 h0
      subst ht
      have hv : ∀ u : Fin 2, Event.tick u 0 ∈ pre.events := by decide +kernel
      exact hv v
  · refine ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun k v o t hk => ?_⟩
    simpa using allDeliveries_spec pre_fresh hk
  · refine ⟨?_, fun _ _ _ _ _ hc => hc.elim⟩
    rintro v o t ⟨k, hk⟩ u _ hu
    have h := List.all_eq_true.mp (allDeliveries_spec pre_signed hk) u (List.mem_finRange u)
    rw [hu] at h
    exact emittedBy_spec (by simpa using h)

/-- The row of validator 0 passes `EmitOk` at its tick in `pre`. -/
theorem pre_emitOk : EmitOk toyEnv pre (Run.stateBefore toyEnv pre 0 0) 0 0 (rowObj 0) :=
  ⟨rfl, rfl, by decide +kernel, fun _ h => h⟩

-- The append form: `pre` with the self-delivery of the row of validator 0 at
-- time 0 appended is valid.
example : ExecutionValid toyEnv
    ({ pre with events := pre.events ++ [.deliver 0 (rowObj 0) 0] } : Run (Fin 2) toyP) :=
  pre_valid.snoc_selfDelivery toyHooks (i := 0) (by decide +kernel) rfl
    (fun k e hk he => by
      match k, hk, he with
      | 1, _, he => cases he; decide
      | 2, _, he => cases he; decide
      | _ + 3, _, he => simp [pre] at he)
    (by decide +kernel) pre_emitOk

/-! ### The optional condition `SelfDelivery` -/

/-- Every self-visible object that a tick releases goes to its emitter at the
emission time, after the tick. -/
theorem toyRun_selfDelivery_check :
    allTicks toyRun (fun i v t => (Run.emitsAt toyEnv toyRun i).all fun o =>
      !toyP.objSelfVisible o || (List.range toyRun.events.length).any fun j =>
        decide (i < j) && decide (toyRun.events[j]? = some (.deliver v o t))) = true := by
  decide +kernel

example : SelfDelivery toyEnv toyRun := by
  intro i v t hi o ho hsv
  have h := List.all_eq_true.mp (allTicks_spec toyRun_selfDelivery_check hi) o ho
  rw [hsv, Bool.not_true, Bool.false_or] at h
  obtain ⟨j, -, hj⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
  exact ⟨j, hj⟩

/-! ### Delivery conditions with honest nodes (Task 5 review M1) -/

/-- Every released object goes to both nodes at its emission time. -/
theorem toyRun_broadcast_check :
    allTicks toyRun (fun i _ t => (Run.emitsAt toyEnv toyRun i).all fun o =>
      (List.finRange 2).all fun w => decide (Event.deliver w o t ∈ toyRun.events)) = true := by
  decide +kernel

/-- Every delivered object goes to both nodes at its delivery time. -/
theorem toyRun_relay_check :
    allDeliveries toyRun (fun _ _ o t =>
      (List.finRange 2).all fun w => decide (Event.deliver w o t ∈ toyRun.events)) = true := by
  decide +kernel

/-- A delivery of `o` to `w` at time `t` is a handler call for `o`. -/
theorem handlesAt_of_mem {w : Fin 2} {o : toyP.Object} {t : Time}
    (h : Event.deliver w o t ∈ toyRun.events) : ∃ j, Run.handlesAt toyEnv toyRun j w o t := by
  obtain ⟨j, hj⟩ := List.getElem?_of_mem h
  exact ⟨j, o, hj, rfl⟩

/-- Every honest node handles an emitted object at its emission time. -/
theorem handles_emitted {v : Fin 2} {o : toyP.Object} {t : Time}
    (he : Run.emits toyEnv toyRun v o t) (w : Fin 2) :
    ∃ j, Run.handlesAt toyEnv toyRun j w o t := by
  obtain ⟨i, hi, ho⟩ := he
  have h := List.all_eq_true.mp (allTicks_spec toyRun_broadcast_check hi) o ho
  exact handlesAt_of_mem (by simpa using List.all_eq_true.mp h w (List.mem_finRange w))

/-- Every honest node handles an accepted object at its acceptance time. -/
theorem handles_accepted {i : Nat} {v : Fin 2} {o : toyP.Object} {t : Time}
    (ha : Run.acceptsAt toyEnv toyRun i v o t) (w : Fin 2) :
    ∃ j, Run.handlesAt toyEnv toyRun j w o t := by
  obtain ⟨⟨o', hi, rfl⟩, -, -⟩ := ha
  have h := allDeliveries_spec toyRun_relay_check hi
  exact handlesAt_of_mem (by simpa using List.all_eq_true.mp h w (List.mem_finRange w))

private theorem service_of_handled {w : Fin 2} {o : toyP.Object} {t a d : Time}
    (h : ∃ j, Run.handlesAt toyEnv toyRun j w o t) (hta : t ≤ a) (had : a < d) :
    DeliveryService toyEnv toyRun w o a d := by
  by_cases heq : a = t
  · subst a
    exact Or.inr ⟨t, le_rfl, had, h⟩
  · obtain ⟨j, o', hj, hh⟩ := h
    have ho : o' = o := hh
    subst o'
    have hjc := (index_lt_actionCut_iff toyRun_valid.toScheduleWellFormed hj a).mpr
      (Or.inl (lt_of_le_of_ne hta (Ne.symm heq)))
    refine Or.inl ⟨j + 1, Nat.succ_le_of_lt hjc, ?_⟩
    rw [Run.stateBefore_succ toyEnv toyRun hj]
    simp [World.step]

/-- The prefix demand keeps all anchor and horizon guards. -/
theorem toyRun_healthy (cut : Time) : HealthyPrefixDelivery toyEnv toyRun cut where
  broadcast := fun _ _ _ _ he w _ _ hta _ had _ _ _ _ =>
    service_of_handled (handles_emitted he w) hta had
  relay := fun _ _ _ _ _ ha w _ _ hta _ had _ _ _ _ =>
    service_of_handled (handles_accepted ha w) hta had

/-- The full-run demand also permits the historical processing branch. -/
theorem toyRun_partialSynchrony : PartialSynchrony toyEnv toyRun where
  broadcast := fun _ _ _ _ he w _ _ hta _ had _ _ _ _ =>
    service_of_handled (handles_emitted he w) hta had
  relay := fun _ _ _ _ _ ha w _ _ hta _ had _ _ _ _ =>
    service_of_handled (handles_accepted ha w) hta had

-- An honest emitter: validator 0 emits its row at time 0, and at the cut 2,
-- past `0 + Δ`, validator 1 handles it before the deadline 1.
example : (0 : Fin 2) ∈ toyRun.honest ∧ Run.emits toyEnv toyRun 0 (rowObj 0) 0 :=
  ⟨Finset.mem_univ _, 0, rfl, by decide +kernel⟩
example : DeliveryService toyEnv toyRun 1 (rowObj 0) 0 1 :=
  (toyRun_healthy 2).broadcast 0 (Finset.mem_univ _) (rowObj 0) 0
    ⟨0, rfl, by decide +kernel⟩ 1 (Finset.mem_univ _) 0 le_rfl le_rfl
    (by decide) (by decide) (by decide) (fun _ _ _ => rfl) rfl

-- The relay case: validator 1 accepts the row of validator 0 at index 2.
-- Validator 0 has not processed it after index 2, and it handles it at index
-- 3, at time 0, before the deadline 1.
theorem accepts_row0 : Run.acceptsAt toyEnv toyRun 2 1 (rowObj 0) 0 :=
  ⟨⟨rowObj 0, rfl, rfl⟩, by decide +kernel, by decide +kernel⟩
example : toyP.processed (Run.stateBefore toyEnv toyRun (2 + 1) 0) (rowObj 0) = false := by
  decide +kernel
example : Run.handlesAt toyEnv toyRun 3 0 (rowObj 0) 0 := ⟨rowObj 0, rfl, rfl⟩
example : DeliveryService toyEnv toyRun 0 (rowObj 0) 0 1 :=
  (toyRun_healthy 1).relay 1 (Finset.mem_univ _) 2 (rowObj 0) 0 accepts_row0 0
    (Finset.mem_univ _) 0 le_rfl le_rfl (by decide) (by decide) (by decide)
    (fun _ _ _ => rfl) rfl

end AvailableChain.V2.Tests.Toy

end

#print axioms AvailableChain.V2.Tests.Toy.toyRun_valid
#print axioms AvailableChain.V2.Tests.Toy.pre_valid
#print axioms AvailableChain.V2.Tests.Toy.toyRun_healthy
#print axioms AvailableChain.V2.Tests.Toy.toyRun_partialSynchrony
#print axioms AvailableChain.V2.Tests.Toy.accepts_row0

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Relay
@[expose] public section

/-! # A schedule of top-level events and its run trace

For any node AC `A`, a **schedule** lists top-level events `(node, time, event)` on a prefix of
`ℕ` (`Schedule.entry`; a finite run is a list, an infinite one is `fun k => some (e k)`), with an
awake function and an optional observation horizon. `Schedule.trace` is the run trace it
induces: each node's state is threaded through `Node.exec` in entry order from `Node.init A`
(`stBefore`, a fold of `stepAt` over the entries before `k`); entry `k` becomes the handler's
cuts at the consecutive indices `start k, start k + 1, …` (`start`: prefix sums of the group
lengths), under the event id `2k`, at positions `0, 1, …`, with the cut law's post-states
(`midState`, folds of `cutPost`); after the last cut, the trace stutters (no label, event id
`2c + 1`) at `endTime`, the last entry's time or the horizon, whichever is later.

* `state_groupStart`: the trace's state before entry `k` is `stBefore`, for every schedule
  (finite or infinite); `state_add`: the state inside the group; `cutStep_of_callAt`: the cut
  law at every labelled cut.
* `groupAt_entry`: a non-empty entry `k` is a `GroupAt` at `start k`; `groupAt_inv`: every
  `GroupAt` is an entry's group (same event up to a tick's input).

The schedule includes every entry as cuts, whatever its node: list honest entries only (faulty
behaviour is what the honest nodes receive). The laws that make the trace a run are in
`ConsensusLeanTest/Goldilocks/Runs/Schedule/LocalRun`. -/

namespace Consensus.Goldilocks.Test.ScheduleRun

open Node
open SA (SAParams ReplayOrder Payload blockVotes Vote)

/-! ## Prefix sums and the block of an index -/

/-- The prefix sums of `len`: `psum len k = len 0 + … + len (k - 1)`. -/
def psum (len : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => psum len k + len k

theorem psum_zero (len : Nat → Nat) : psum len 0 = 0 := rfl

theorem psum_succ (len : Nat → Nat) (k : Nat) : psum len (k + 1) = psum len k + len k := rfl

theorem psum_mono (len : Nat → Nat) : Monotone (psum len) :=
  monotone_nat_of_le_succ fun _ => Nat.le_add_right _ _

open Classical in
/-- The block of index `c` among consecutive blocks of lengths `len`: the `k` with
`psum len k ≤ c < psum len (k + 1)`, or `none` past every block. -/
noncomputable def locate (len : Nat → Nat) (c : Nat) : Option Nat :=
  if h : ∃ k, c < psum len (k + 1) then some (Nat.find h) else none

theorem locate_eq_some_iff {len : Nat → Nat} {c k : Nat} :
    locate len c = some k ↔ psum len k ≤ c ∧ c < psum len (k + 1) := by
  classical
  unfold locate
  split_ifs with hex
  · rw [Option.some.injEq]
    constructor
    · rintro rfl
      refine ⟨?_, Nat.find_spec hex⟩
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
      · rw [h0]; exact Nat.zero_le _
      · have := Nat.find_min hex (Nat.sub_lt hpos Nat.one_pos)
        rw [Nat.sub_add_cancel hpos] at this
        exact not_lt.mp this
    · rintro ⟨h1, h2⟩
      apply le_antisymm (Nat.find_min' hex h2)
      by_contra hlt
      have h3 : psum len (Nat.find hex + 1) ≤ psum len k := psum_mono len (not_le.mp hlt)
      have h4 : c < psum len (Nat.find hex + 1) := Nat.find_spec hex
      omega
  · simp only [false_iff, not_and, not_lt]
    exact fun _ => not_lt.mp fun h => hex ⟨k, h⟩

theorem locate_eq_none_iff {len : Nat → Nat} {c : Nat} :
    locate len c = none ↔ ∀ k, psum len (k + 1) ≤ c := by
  classical
  unfold locate
  split_ifs with hex
  · simp only [false_iff, not_forall, not_le]
    exact hex
  · simp only [true_iff]
    exact fun k => not_lt.mp fun h => hex ⟨k, h⟩

/-- Position `p` of block `k` is located in block `k`. -/
theorem locate_add {len : Nat → Nat} {k p : Nat} (hp : p < len k) :
    locate len (psum len k + p) = some k :=
  locate_eq_some_iff.2 ⟨Nat.le_add_right _ _, by rw [psum_succ]; omega⟩

/-- Blocks in index order: an index below block `k`'s start is in an earlier block. -/
theorem lt_of_psum_le {len : Nat → Nat} {k k' c : Nat} (h1 : psum len k' ≤ c)
    (h2 : c < psum len k) : k' < k := by
  by_contra h
  have := psum_mono len (not_lt.mp h)
  omega

/-! ## Schedules -/

variable {P : Params} {A : NodeAC P}

/-- One top-level event: node, time, event. -/
abbrev Entry (A : NodeAC P) := Fin P.n × Time × Node.Event A

/-- A schedule: entries on a prefix of `ℕ` (`none` after the last one), the awake function and
the observation horizon of the run (`none` for an infinite schedule). -/
structure Schedule (A : NodeAC P) where
  /-- Entry `k`: its node, time and top-level event. -/
  entry : Nat → Option (Entry A)
  /-- The entries are a prefix of `ℕ`. -/
  prefix_closed : ∀ k, entry k = none → entry (k + 1) = none
  /-- Whether a node is awake at a time. -/
  awake : Fin P.n → Time → Prop
  /-- The observation horizon of the trace. -/
  horizon : Option Time

namespace Schedule

variable (proposer : Nat → Fin P.n) (dg : Digest (List (FG.Att P.n)) A.Payload)
  (sch : Schedule A)

/-- Entry `k` applied to the state `st` of node `y`: its handler's state when the entry is
`y`'s, else `st`. -/
noncomputable def stepAt (y : Fin P.n) (k : Nat) (st : NodeState A) : NodeState A :=
  match sch.entry k with
  | some (x, t, e) => if x = y then (exec proposer dg x st t e).1 else st
  | none => st

/-- The state of node `y` before entry `k`: the fold of `Node.exec` over `y`'s entries before
`k`, from the initial node state. -/
noncomputable def stBefore (y : Fin P.n) (k : Nat) : NodeState A :=
  (List.range k).foldl (fun st i => sch.stepAt proposer dg y i st) (Node.init A)

/-- The cuts of entry `k`: its handler's cuts on its node's state before `k`. -/
noncomputable def cutsAt (k : Nat) : List (Cut A) :=
  match sch.entry k with
  | some (y, t, e) => (exec proposer dg y (sch.stBefore proposer dg y k) t e).2
  | none => []

/-- The cut index where entry `k`'s group starts. -/
noncomputable def start (k : Nat) : Nat := psum (fun i => (sch.cutsAt proposer dg i).length) k

/-- The entry whose group contains cut `c`, if any. -/
noncomputable def entryOf (c : Nat) : Option Nat :=
  locate (fun i => (sch.cutsAt proposer dg i).length) c

/-- The node of entry `k` (`0` when there is none). -/
def entryNode (k : Nat) : Fin P.n := ((sch.entry k).map (·.1)).getD ⟨0, P.hn⟩

/-- The time of entry `k` (`0` when there is none). -/
def entryTime (k : Nat) : Time := ((sch.entry k).map (·.2.1)).getD 0

/-- The state of entry `k`'s node after the first `p` cuts of its group. -/
noncomputable def midState (k p : Nat) : NodeState A :=
  ((sch.cutsAt proposer dg k).take p).foldl (cutPost (sch.entryNode k) (sch.entryTime k))
    (sch.stBefore proposer dg (sch.entryNode k) k)

open Classical in
/-- The time of the last entry (`0` if none; unused for an infinite schedule). -/
noncomputable def lastTime : Time :=
  if h : ∃ N, sch.entry N = none then sch.entryTime (Nat.find h - 1) else 0

/-- The time of the stuttering cuts: the last entry's time, or the horizon if later. -/
noncomputable def endTime : Time := max (sch.horizon.getD 0) sch.lastTime

/-- **The run trace of a schedule.** -/
noncomputable def trace : RunTrace A where
  init _ := Node.init A
  node c := ((sch.entryOf proposer dg c).map sch.entryNode).getD ⟨0, P.hn⟩
  time c := ((sch.entryOf proposer dg c).map sch.entryTime).getD sch.endTime
  event c := ((sch.entryOf proposer dg c).map (2 * ·)).getD (2 * c + 1)
  pos c := ((sch.entryOf proposer dg c).map (c - sch.start proposer dg ·)).getD 0
  label c := (sch.entryOf proposer dg c).bind fun k =>
    (sch.cutsAt proposer dg k)[c - sch.start proposer dg k]?
  post c := ((sch.entryOf proposer dg c).map fun k =>
    sch.midState proposer dg k (c - sch.start proposer dg k + 1)).getD (Node.init A)
  awake := sch.awake
  observationHorizon := sch.horizon

/-! ### Characterising lemmas -/

theorem stBefore_zero (y : Fin P.n) : sch.stBefore proposer dg y 0 = Node.init A := rfl

theorem stBefore_succ (y : Fin P.n) (k : Nat) :
    sch.stBefore proposer dg y (k + 1) =
      sch.stepAt proposer dg y k (sch.stBefore proposer dg y k) := by
  simp only [stBefore, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

variable {proposer dg sch}

theorem stepAt_some {y x : Fin P.n} {k : Nat} {t : Time} {e : Event A}
    (he : sch.entry k = some (x, t, e)) (st : NodeState A) :
    sch.stepAt proposer dg y k st = if x = y then (exec proposer dg x st t e).1 else st := by
  simp only [stepAt, he]

theorem stepAt_none {y : Fin P.n} {k : Nat} (he : sch.entry k = none) (st : NodeState A) :
    sch.stepAt proposer dg y k st = st := by
  simp only [stepAt, he]

theorem cutsAt_some {k : Nat} {y : Fin P.n} {t : Time} {e : Event A}
    (he : sch.entry k = some (y, t, e)) :
    sch.cutsAt proposer dg k = (exec proposer dg y (sch.stBefore proposer dg y k) t e).2 := by
  simp only [cutsAt, he]

theorem cutsAt_none {k : Nat} (he : sch.entry k = none) : sch.cutsAt proposer dg k = [] := by
  simp only [cutsAt, he]

theorem entryNode_of {k : Nat} {y : Fin P.n} {t : Time} {e : Event A}
    (he : sch.entry k = some (y, t, e)) : sch.entryNode k = y := by
  simp [entryNode, he]

theorem entryTime_of {k : Nat} {y : Fin P.n} {t : Time} {e : Event A}
    (he : sch.entry k = some (y, t, e)) : sch.entryTime k = t := by
  simp [entryTime, he]

theorem entry_of_ne_nil {k : Nat} (h : sch.cutsAt proposer dg k ≠ []) :
    ∃ y t e, sch.entry k = some (y, t, e) := by
  cases he : sch.entry k with
  | none => exact absurd (cutsAt_none he) h
  | some v => exact ⟨v.1, v.2.1, v.2.2, rfl⟩

/-- Past a missing entry, every entry is missing. -/
theorem entry_none_of_le {N k : Nat} (hN : sch.entry N = none) (hk : N ≤ k) :
    sch.entry k = none := by
  induction k, hk using Nat.le_induction with
  | base => exact hN
  | succ k _ ih => exact sch.prefix_closed k ih

theorem start_zero : sch.start proposer dg 0 = 0 := rfl

theorem start_succ (k : Nat) :
    sch.start proposer dg (k + 1) = sch.start proposer dg k + (sch.cutsAt proposer dg k).length :=
  rfl

theorem start_mono : Monotone (sch.start proposer dg) := psum_mono _

theorem entryOf_eq_some_iff {c k : Nat} :
    sch.entryOf proposer dg c = some k ↔
      sch.start proposer dg k ≤ c ∧ c < sch.start proposer dg (k + 1) :=
  locate_eq_some_iff

theorem entryOf_eq_none_iff {c : Nat} :
    sch.entryOf proposer dg c = none ↔ ∀ k, sch.start proposer dg (k + 1) ≤ c :=
  locate_eq_none_iff

theorem entryOf_add {k p : Nat} (hp : p < (sch.cutsAt proposer dg k).length) :
    sch.entryOf proposer dg (sch.start proposer dg k + p) = some k :=
  locate_add (len := fun i => (sch.cutsAt proposer dg i).length) hp

theorem entryOf_start {k : Nat} (hp : 0 < (sch.cutsAt proposer dg k).length) :
    sch.entryOf proposer dg (sch.start proposer dg k) = some k :=
  entryOf_add (p := 0) hp

/-- A cut in entry `k`'s block means entry `k` exists. -/
theorem entry_of_entryOf {c k : Nat} (h : sch.entryOf proposer dg c = some k) :
    ∃ y t e, sch.entry k = some (y, t, e) := by
  obtain ⟨h1, h2⟩ := entryOf_eq_some_iff.1 h
  rw [start_succ] at h2
  exact entry_of_ne_nil (proposer := proposer) (dg := dg) (sch := sch) (k := k)
    (List.ne_nil_of_length_pos (by omega))

theorem lt_of_start_le {k k' c : Nat} (h1 : sch.start proposer dg k' ≤ c)
    (h2 : c < sch.start proposer dg k) : k' < k :=
  lt_of_psum_le h1 h2

/-- The fields of the trace at a cut of entry `k`'s group. -/
theorem trace_of_entryOf {c k : Nat} (h : sch.entryOf proposer dg c = some k) :
    (sch.trace proposer dg).node c = sch.entryNode k ∧
      (sch.trace proposer dg).time c = sch.entryTime k ∧
      (sch.trace proposer dg).event c = 2 * k ∧
      (sch.trace proposer dg).pos c = c - sch.start proposer dg k ∧
      (sch.trace proposer dg).label c =
        (sch.cutsAt proposer dg k)[c - sch.start proposer dg k]? ∧
      (sch.trace proposer dg).post c =
        sch.midState proposer dg k (c - sch.start proposer dg k + 1) := by
  simp [trace, h]

/-- The fields of the trace at a stuttering cut. -/
theorem trace_of_entryOf_none {c : Nat} (h : sch.entryOf proposer dg c = none) :
    (sch.trace proposer dg).time c = sch.endTime ∧
      (sch.trace proposer dg).event c = 2 * c + 1 ∧ (sch.trace proposer dg).label c = none := by
  simp [trace, h]

theorem trace_init (y : Fin P.n) : (sch.trace proposer dg).init y = Node.init A := rfl

theorem trace_awake : (sch.trace proposer dg).awake = sch.awake := rfl

theorem trace_observationHorizon : (sch.trace proposer dg).observationHorizon = sch.horizon := rfl

theorem midState_zero (k : Nat) :
    sch.midState proposer dg k 0 = sch.stBefore proposer dg (sch.entryNode k) k := by
  simp [midState]

/-- A labelled cut is cut `p` of an entry's group. -/
theorem label_eq_some {c : Nat} {ℓ : Cut A} (h : (sch.trace proposer dg).label c = some ℓ) :
    ∃ k y t e p, sch.entry k = some (y, t, e) ∧ c = sch.start proposer dg k + p ∧
      ∃ hp : p < (sch.cutsAt proposer dg k).length, (sch.cutsAt proposer dg k)[p] = ℓ := by
  cases hk : sch.entryOf proposer dg c with
  | none => rw [(trace_of_entryOf_none hk).2.2] at h; cases h
  | some k =>
    obtain ⟨h1, -⟩ := entryOf_eq_some_iff.1 hk
    rw [(trace_of_entryOf hk).2.2.2.2.1] at h
    obtain ⟨hp, hl⟩ := List.getElem?_eq_some_iff.1 h
    obtain ⟨y, t, e, he⟩ := entry_of_ne_nil (proposer := proposer) (dg := dg) (sch := sch) (k := k)
      (List.ne_nil_of_length_pos (by omega))
    exact ⟨k, y, t, e, c - sch.start proposer dg k, he, by omega, hp, hl⟩

/-! ### The states of the trace -/

/-- Inside entry `k`'s group, the trace's state of `y` is the group's partial fold for the
entry's node, and the state before the entry for every other node. -/
private theorem state_mid (y : Fin P.n) (k : Nat)
    (hk : (sch.trace proposer dg).state y (sch.start proposer dg k) =
      sch.stBefore proposer dg y k) :
    ∀ p ≤ (sch.cutsAt proposer dg k).length,
      (sch.trace proposer dg).state y (sch.start proposer dg k + p) =
        if sch.entryNode k = y then sch.midState proposer dg k p
        else sch.stBefore proposer dg y k := by
  intro p hp
  induction p with
  | zero =>
    rw [Nat.add_zero, hk]
    split_ifs with hy
    · rw [midState_zero, hy]
    · rfl
  | succ p ih =>
    have hp' : p < (sch.cutsAt proposer dg k).length := hp
    obtain ⟨hn, -, -, -, hl, hpost⟩ := trace_of_entryOf (entryOf_add hp')
    rw [Nat.add_sub_cancel_left] at hl hpost
    have hl' : (sch.trace proposer dg).label (sch.start proposer dg k + p) ≠ none := by
      rw [hl, List.getElem?_eq_getElem hp']
      exact Option.some_ne_none _
    rw [← Nat.add_assoc, Trace.state, hn, ih hp'.le]
    split_ifs with h1 h2 h2
    · exact hpost
    · exact absurd h1.1 h2
    · exact absurd ⟨h2, hl'⟩ h1
    · rfl

/-- **The state before an entry's group is the threaded state** `stBefore`. -/
theorem state_groupStart (y : Fin P.n) (k : Nat) :
    (sch.trace proposer dg).state y (sch.start proposer dg k) = sch.stBefore proposer dg y k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [start_succ, state_mid y k ih _ le_rfl, stBefore_succ]
    cases he : sch.entry k with
    | none =>
      rw [stepAt_none he]
      split_ifs with hy
      · rw [cutsAt_none he, List.length_nil, midState_zero, hy]
      · rfl
    | some v =>
      obtain ⟨x, t, e⟩ := v
      rw [stepAt_some he, entryNode_of he]
      split_ifs with hy
      · subst hy
        simp only [midState, List.take_length, entryNode_of he, entryTime_of he]
        rw [cutsAt_some he]
        exact foldl_cutPost_exec proposer dg x _ t e
      · rfl

/-- The trace's state of `y` at position `p` of entry `k`'s group. -/
theorem state_add (y : Fin P.n) {k p : Nat} (hp : p ≤ (sch.cutsAt proposer dg k).length) :
    (sch.trace proposer dg).state y (sch.start proposer dg k + p) =
      if sch.entryNode k = y then sch.midState proposer dg k p
      else sch.stBefore proposer dg y k :=
  state_mid y k (state_groupStart y k) p hp

/-- A call of `y` is cut `p` of a group of an entry of `y`, at the entry's time. -/
theorem call_inv {y : Fin P.n} {i : Nat} {ℓ : Cut A} (h : (sch.trace proposer dg).CallAt y i ℓ) :
    ∃ k t e p, sch.entry k = some (y, t, e) ∧ i = sch.start proposer dg k + p ∧
      (∃ hp : p < (sch.cutsAt proposer dg k).length, (sch.cutsAt proposer dg k)[p] = ℓ) ∧
      (sch.trace proposer dg).time i = t := by
  obtain ⟨k, x, t, e, p, he, rfl, hp, hl⟩ := label_eq_some h.2
  obtain ⟨hn, ht, -⟩ := trace_of_entryOf (entryOf_add hp)
  obtain rfl : x = y := (entryNode_of he).symm.trans (hn.symm.trans h.1)
  exact ⟨k, t, e, p, he, rfl, ⟨hp, hl⟩, ht.trans (entryTime_of he)⟩

/-- **The cut law** at every labelled cut. -/
theorem cutStep_of_callAt {y : Fin P.n} {i : Nat} {ℓ : Cut A}
    (h : (sch.trace proposer dg).CallAt y i ℓ) :
    CutStep y ((sch.trace proposer dg).time i) ((sch.trace proposer dg).state y i) ℓ
      ((sch.trace proposer dg).post i) := by
  obtain ⟨k, t, e, p, he, rfl, ⟨hp, hl⟩, ht⟩ := call_inv h
  rw [ht, state_add y hp.le, (trace_of_entryOf (entryOf_add hp)).2.2.2.2.2,
    Nat.add_sub_cancel_left]
  simp only [entryNode_of he, ↓reduceIte]
  have hch : CutChain y t (sch.stBefore proposer dg y k) (sch.cutsAt proposer dg k)
      (exec proposer dg y (sch.stBefore proposer dg y k) t e).1 := by
    rw [cutsAt_some he]
    exact Compose.exec_is_cut_chain proposer dg y _ t e
  simp only [midState, entryNode_of he, entryTime_of he]
  exact hl ▸ Simulation.cutStep_of_cutChain hch p hp

/-! ### Groups -/

/-- The key of a handler's first cut: the event, up to the input of a tick. -/
def headKey : Cut A → Option (Event A)
  | .fg (.block B _) => some (.block B)
  | .fg (.attestation a) => some (.attestation a)
  | .fg (.attest _ _) => none
  | .ac ℓ =>
    match ℓ.call with
    | .tick => some (.tick 0)
    | .message m => some (.message m)
    | .restart => some .restart
    | _ => none

/-- An event up to the input of a tick. -/
def normEv : Event A → Event A
  | .tick _ => .tick 0
  | e => e

/-- A handler's first cut has the key of its event. -/
theorem headKey_exec (self : Fin P.n) (st : NodeState A) (t : Time) (e : Event A) {c : Cut A}
    {cs : List (Cut A)} (h : (exec proposer dg self st t e).2 = c :: cs) :
    headKey c = some (normEv e) := by
  cases e with
  | tick x =>
    obtain ⟨ℓ, pc, uc, hℓ, hcs, -, -⟩ := Compose.tick_order proposer dg self st t x
    change (onTick proposer dg self st t x).2 = _ at h
    rw [hcs] at h
    obtain ⟨rfl, -⟩ := List.cons.inj h
    simp [headKey, hℓ, normEv]
  | block B =>
    obtain ⟨acc, rfl⟩ := Simulation.exec_block_head proposer dg self st t B h
    rfl
  | message m =>
    simp only [exec, onMessage, acCall] at h
    obtain ⟨rfl, -⟩ := List.cons.inj h
    rfl
  | attestation a =>
    simp only [exec, onAttestation] at h
    obtain ⟨rfl, -⟩ := List.cons.inj h
    rfl
  | restart =>
    simp only [exec, Node.restart, acCall] at h
    obtain ⟨rfl, -⟩ := List.cons.inj h
    rfl

/-- Events equal up to the input of a tick are equal or both ticks. -/
theorem eq_of_normEv_eq {e e' : Event A} (h : normEv e = normEv e') :
    e = e' ∨ ∃ x x', e = .tick x ∧ e' = .tick x' := by
  cases e <;> cases e' <;> simp_all [normEv]

/-- Only a restart's handler makes an `ac_restart` cut. -/
theorem restart_of_mem_exec (self : Fin P.n) (st : NodeState A) (t : Time) (e : Event A)
    {ℓ : ACLabel A} (h : Cut.ac ℓ ∈ (exec proposer dg self st t e).2)
    (hℓ : ℓ.call = .restart) : e = .restart := by
  cases e with
  | tick x =>
    obtain ⟨ℓ₀, pc, uc, hℓ₀, hcs, hpc, ⟨ℓ₁, hℓ₁, huc⟩⟩ :=
      Compose.tick_order proposer dg self st t x
    change _ ∈ (onTick proposer dg self st t x).2 at h
    rw [hcs] at h
    exfalso
    rcases List.mem_cons.mp h with h | h
    · cases h; simp [hℓ] at hℓ₀
    rcases List.mem_append.mp h with h | h
    · rcases hpc with ⟨-, rfl⟩ | ⟨-, ℓ₂, hℓ₂, hpc⟩
      · simp at h
      rcases hpc with rfl | ⟨B, -, -, rfl | ⟨ℓ₃, hℓ₃, rfl⟩⟩
      · simp only [List.mem_singleton, Cut.ac.injEq] at h; subst h; simp [hℓ] at hℓ₂
      · simp only [List.mem_cons, Cut.ac.injEq, reduceCtorEq, List.not_mem_nil, or_false] at h
        subst h; simp [hℓ] at hℓ₂
      · simp only [List.mem_cons, Cut.ac.injEq, reduceCtorEq, List.not_mem_nil, or_false,
          false_or] at h
        rcases h with rfl | rfl
        · simp [hℓ] at hℓ₂
        · simp [hℓ] at hℓ₃
    · rcases huc with rfl | ⟨C, rfl⟩ | ⟨C, a, rfl⟩ <;>
        simp only [List.mem_cons, Cut.ac.injEq, reduceCtorEq, List.not_mem_nil, or_false] at h <;>
        (subst h; simp [hℓ] at hℓ₁)
  | block B =>
    simp only [exec, onBlock, acCall] at h
    exfalso
    split_ifs at h
    · simp at h
    · split at h
      · simp at h
      · simp only [List.mem_cons, reduceCtorEq, Cut.ac.injEq, List.not_mem_nil, or_false,
          false_or] at h
        subst h; simp at hℓ
  | message m =>
    simp only [exec, onMessage, acCall, List.mem_singleton, Cut.ac.injEq] at h
    subst h; simp at hℓ
  | attestation a => simp [exec, onAttestation] at h
  | restart => rfl

/-- A restart makes exactly its `ac_restart` cut. -/
theorem exec_restart (self : Fin P.n) (st : NodeState A) (t : Time) :
    (exec proposer dg self st t .restart).2 = [(acCall self st t .restart).2] := rfl

/-- **Entry `k`'s group**: a non-empty entry is a `GroupAt` at `start k`. -/
theorem groupAt_entry {k : Nat} {y : Fin P.n} {t : Time} {e : Event A}
    (he : sch.entry k = some (y, t, e))
    (hne : (exec proposer dg y (sch.stBefore proposer dg y k) t e).2 ≠ []) :
    (sch.trace proposer dg).GroupAt proposer dg y (sch.start proposer dg k) t e := by
  rw [← cutsAt_some he] at hne
  have hpos : 0 < (sch.cutsAt proposer dg k).length := List.length_pos_of_ne_nil hne
  have h0 := (trace_of_entryOf (entryOf_add hpos)).2.2.1
  rw [Nat.add_zero] at h0
  simp only [RunTrace.GroupAt, state_groupStart, ← cutsAt_some he]
  refine ⟨hne, fun p hp => ?_, fun i hi => ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, -⟩ := trace_of_entryOf (entryOf_add hp)
    rw [Nat.add_sub_cancel_left] at h4 h5
    exact ⟨h1.trans (entryNode_of he), h2.trans (entryTime_of he), h3.trans h0.symm, h4,
      by rw [h5, List.getElem?_eq_getElem hp]⟩
  · rw [h0] at hi
    cases hk : sch.entryOf proposer dg i with
    | none => rw [(trace_of_entryOf_none hk).2.1] at hi; omega
    | some k' =>
      rw [(trace_of_entryOf hk).2.2.1] at hi
      obtain rfl : k' = k := by omega
      have := entryOf_eq_some_iff.1 hk
      rw [start_succ] at this
      omega

/-- **Every `GroupAt` is an entry's group**: at `start k` for an entry of the node at the time,
with the same event up to a tick's input. -/
theorem groupAt_inv {y : Fin P.n} {j : Nat} {t : Time} {e : Event A}
    (h : (sch.trace proposer dg).GroupAt proposer dg y j t e) :
    ∃ k e', sch.entry k = some (y, t, e') ∧ j = sch.start proposer dg k ∧
      (e = e' ∨ ∃ x x', e = .tick x ∧ e' = .tick x') := by
  obtain ⟨hne, hcuts, hev⟩ := h
  have hpos := List.length_pos_of_ne_nil hne
  obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨hn0, ht0, -, -, hl0⟩ := hcuts 0 hpos
  rw [Nat.add_zero] at hn0 ht0 hl0
  have hc : (exec proposer dg y ((sch.trace proposer dg).state y j) t e).2[0] = c := by
    rw [List.getElem_of_eq hcs hpos]; rfl
  rw [hc] at hl0
  obtain ⟨k, x, t', e', p, he, hj, hp, -⟩ := label_eq_some hl0
  have hpos' : 0 < (sch.cutsAt proposer dg k).length := by omega
  have hk0 := entryOf_add (proposer := proposer) (dg := dg) (sch := sch) hpos'
  rw [Nat.add_zero] at hk0
  obtain ⟨hn, ht, hev0, -, hlab, -⟩ := trace_of_entryOf hk0
  have hevj : (sch.trace proposer dg).event j = 2 * k := by
    rw [hj]; exact (trace_of_entryOf (entryOf_add hp)).2.2.1
  have hjk : j = sch.start proposer dg k := by
    have := (hev _ (hev0.trans hevj.symm)).1
    omega
  subst hjk
  rw [hn0, entryNode_of he] at hn
  rw [ht0, entryTime_of he] at ht
  subst hn ht
  obtain ⟨c', cs', hcs'⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos hpos')
  rw [hl0, Nat.sub_self, hcs', List.getElem?_cons_zero] at hlab
  rw [state_groupStart] at hcs
  rw [cutsAt_some he] at hcs'
  have hk1 := headKey_exec y _ _ e hcs
  rw [Option.some.inj hlab, headKey_exec y _ _ e' hcs'] at hk1
  exact ⟨k, e', he, rfl, eq_of_normEv_eq (Option.some.inj hk1).symm⟩

/-- The event of a group, as `groupAt_inv` relates it, has its entry's phase. -/
theorem phase_eq_of_sim {e e' : Event A} (h : e = e' ∨ ∃ x x', e = .tick x ∧ e' = .tick x') :
    e.phase = e'.phase := by
  rcases h with rfl | ⟨x, x', rfl, rfl⟩ <;> rfl

/-- A cut of `y` in entry `k`'s group (from position `p`) is a call. -/
theorem isCall_start {k : Nat} {y : Fin P.n} {t : Time} {e : Event A}
    (he : sch.entry k = some (y, t, e)) (hpos : 0 < (sch.cutsAt proposer dg k).length) :
    (sch.trace proposer dg).IsCall y (sch.start proposer dg k) := by
  obtain ⟨hn, -, -, -, hl, -⟩ := trace_of_entryOf (entryOf_add hpos)
  rw [Nat.add_zero, Nat.sub_self] at hl
  rw [Nat.add_zero] at hn
  exact ⟨_, hn.trans (entryNode_of he), hl.trans (List.getElem?_eq_getElem hpos)⟩

/-- A restart entry's cut is a restart. -/
theorem restartAt_start {k : Nat} {y : Fin P.n} {t : Time}
    (he : sch.entry k = some (y, t, .restart)) :
    (sch.trace proposer dg).RestartAt y (sch.start proposer dg k) := by
  have hcs := cutsAt_some (proposer := proposer) (dg := dg) he
  rw [exec_restart] at hcs
  have hpos : 0 < (sch.cutsAt proposer dg k).length := by rw [hcs]; exact Nat.one_pos
  obtain ⟨hn, -, -, -, hl, -⟩ := trace_of_entryOf (entryOf_add hpos)
  rw [Nat.add_zero, Nat.sub_self] at hl
  rw [Nat.add_zero] at hn
  refine ⟨⟨.restart, frame (sch.stBefore proposer dg y k),
    (A.step y (sch.stBefore proposer dg y k).ac (frame (sch.stBefore proposer dg y k)) t
      .restart).2⟩, ⟨hn.trans (entryNode_of he), hl.trans ?_⟩, rfl⟩
  rw [hcs]
  rfl

end Schedule

end Consensus.Goldilocks.Test.ScheduleRun

end

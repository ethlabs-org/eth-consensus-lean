module
public import ConsensusLeanTest.Goldilocks.Runs.Data.Sync
public import ConsensusLeanTest.Goldilocks.HalfCommittee.Run
@[expose] public section

/-! # The Initial-Carry run with five validators: schedule, `GoldilocksRun`, `Sync[24, 33]`

The concrete run of the premise-necessity witness for the initial `Carry` premise of
`RecentSourceNextVote`, on the computable mirror (`Goldilocks/Mirror/Node`) and the generic
run on data (`Goldilocks/Runs/Data/Run`, `Goldilocks/Runs/Data/Sync`). Five validators: `a, b, c, d`
honest, `f` faulty and the proposer of every slot (`Five.sp5`: `Δ = Δ_F = 1`, `t_s = 4s`, `k = 4`,
`c = 2`, `δ_t = 6`, genesis root `2`). The block table holds four blocks of `f`: `B` (root `1`,
slot `2`) and `V` (root `3`, slot `1`), children of genesis `G`, and `Da` (root `4`, slot `3`)
and `Db` (root `5`, slot `4`), children of `B`. `a, b, c` are awake on `[0, 35]`, `d` never
wakes, nobody restarts.

The schedule `sched ctl` lists, per time `0, …, 35`, the ticks of `a, b, c` and the deliveries
(`dels`): `V → c` at `4`; `B → a, b, c` at `8`; `Da → a` at `12`; `Db → b` at `16`; at `23`
`Db → a`, `Da → b`, and in the control (`ctl = true`) also `Da, Db → c`; the faulty vote
`f6` (head `B`) to `a, b, c` at `24`; the slot-6 votes `a6` (head `Da`), `b6` (head `Db`), `c6`
(head `V`) to the other two at `25`; the slot-7 votes at `29`; at `30` the attestations of `a, b`
(and of `c` in the control) and then `V → a, b, c` (`c`'s FG refuses the held root, one cut);
the slot-8 votes at `33`. In the rejection run (`ctl = false`) `c` never accepts `Da` or `Db`,
votes `V` in slots `1`–`8`, and keeps its slow lock on `V`; in the control it accepts both at `23`
and votes `B` in slots `7` and `8`.

The run instantiates the generic core (`runD ctl : DataRun.Run X`): its states are the mirror's
and its cuts the rows `rowsD ctl`. `GoldilocksRun` holds for both variants
(`run_goldilocksRun`), with the entry laws (`entryLaws`: order, no drops, ticks, awake calls, the
three restart laws, the wire data of the four roots) and the row laws (`rowLaws`) checked by the
kernel; `Sync[24, 33]` holds for both variants (`run_sync`), from the kernel check `syncD_true`.

Duplication: the fixture-specific part of `Goldilocks/HalfCommittee/Run` (table, digest, schedule,
instance of the run) is written again here for the new table; the run machinery itself is the
generic core, which parallels the stage-2 machinery of `Goldilocks/HalfCommittee/Run` and
`Goldilocks/HalfCommittee/Sync` (left as landed; a later cleanup may move stage 2 onto the core).
The X-free parts of stage 2 (`Five.sp5`, the validators, `Five.H`, `Five.honest`) are imported.

Kind: the common run of the (r) rejection (`ctl = false`, `Goldilocks/InitialCarry/Reject`) and the
(control) (`ctl = true`, `Goldilocks/InitialCarry/Control`). -/

namespace Consensus.Goldilocks.Test.HalfCommittee.Heads

open SA Fix ScheduleRun
open Five (sp5 va vb vc vd vf H honest mem_honest Content)

/-! ## The fixture -/

/-- The block `B`: root `1`, slot `2`, child of genesis. -/
def rowB : Row := ⟨1, 2, 2, 0, [2]⟩

/-- The block `V`: root `3`, slot `1`, child of genesis. -/
def rowV : Row := ⟨3, 2, 1, 0, [2]⟩

/-- The block `Da`: root `4`, slot `3`, child of `B`. -/
def rowDa : Row := ⟨4, 1, 3, 0, [1, 2]⟩

/-- The block `Db`: root `5`, slot `4`, child of `B`. -/
def rowDb : Row := ⟨5, 1, 4, 0, [1, 2]⟩

/-- The fixture: `sp5`, the faulty proposer `f`, the table `{B, V, Da, Db}`. -/
abbrev X : Fix := ⟨sp5, rfl, vf, [rowB, rowV, rowDa, rowDb]⟩

theorem hX : X.OK := by decide

/-- The replay order of the restarts (any one: the mirror is parametric in it). -/
noncomputable abbrev ro : ReplayOrder X.sp (List (FG.Att X.sp.n)) := ReplayOrder.choice X.sp

/-- The node. -/
noncomputable abbrev N5 : NodeAC X.sp.toParams := X.AC ro

/-- The proposer of every slot: `f`. -/
def proposer : Nat → Fin X.sp.n := fun _ => vf

/-- The contents of genesis, `B`, `V`, `Da` and `Db`. -/
def cG : Content := (none, 0, 0, [], ([], []))
@[inherit_doc cG] def cB : Content := (some 2, 2, 0, [], ([], []))
@[inherit_doc cG] def cV : Content := (some 2, 1, 0, [], ([], []))
@[inherit_doc cG] def cDa : Content := (some 1, 3, 0, [], ([], []))
@[inherit_doc cG] def cDb : Content := (some 1, 4, 0, [], ([], []))

/-- The digest of a content: `2, 1, 3, 4, 5` for genesis, `B`, `V`, `Da`, `Db` (and `0` for any
other content, which no block of the run has). -/
def dgC (q : Content) : Nat :=
  if q = cG then 2 else if q = cB then 1 else if q = cV then 3 else if q = cDa then 4
  else if q = cDb then 5 else 0

/-- The digest of the run. -/
def dg : Digest (List (FG.Att X.sp.n)) (Payload X.sp.n) :=
  fun p s x a q => dgC (p, s, x, a, q)

theorem dg_genesis : (X.sp.toParams.genesisBlock N5.genesisPayload).RootOk dg := by
  change (2 : Nat) = dgC cG; simp [dgC]

theorem roots_eq : X.roots = [1, 3, 4, 5] := rfl

/-- **The digest of the four table roots** (the wire check of their deliveries). -/
theorem dg_blk : ∀ r ∈ X.roots, (X.blk r).RootOk dg := by
  intro r hr
  rw [roots_eq] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · change (1 : Nat) = dgC cB; simp [dgC, cB, cG]
  · change (3 : Nat) = dgC cV; simp [dgC, cB, cG, cV]
  · change (4 : Nat) = dgC cDa; simp [dgC, cB, cG, cV, cDa]
  · change (5 : Nat) = dgC cDb; simp [dgC, cB, cG, cV, cDa, cDb]

/-- **The credential of the four table roots**: each names the proposer `f`. -/
theorem blk_proposer : ∀ r ∈ X.roots, (X.blk r).proposer = proposer (X.blk r).slot :=
  fun _ hr => DataRun.blk_proposer hr

/-! ## The schedule -/

/-- A vote. -/
def vt (v : Fin 5) (s h : Nat) : X.V := ⟨v, s, h⟩

/-- The attestation of `v` (the only one the fragment signs). -/
def att (v : Fin 5) : FG.Att X.sp.n := attG (X := X) v

/-- The head of `c`'s votes of slots `7` and `8`: `V` in the rejection run, `B` in the control. -/
def cHead (ctl : Bool) : Nat := if ctl then 1 else 3

/-- Awake: `a, b, c` on `[0, 35]`; `d` never. -/
def awakeB (y : Fin 5) (t : Nat) : Bool := t ≤ 35 && y.val ≤ 2

/-- A vote of `s` delivered to the two other nodes of `a, b, c`. -/
def msgs (L : List (Fin 5 × X.V)) : List (Fin 5 × X.EvD) :=
  L.flatMap fun (s, v) => ([va, vb, vc].filter (· != s)).map fun y => (y, .message v)

/-- The deliveries at time `t`. -/
def dels (ctl : Bool) : Nat → List (Fin 5 × X.EvD)
  | 4 => [(vc, .block 3)]
  | 8 => [(va, .block 1), (vb, .block 1), (vc, .block 1)]
  | 12 => [(va, .block 4)]
  | 16 => [(vb, .block 5)]
  | 23 => [(va, .block 5), (vb, .block 4)] ++ (if ctl then [(vc, .block 4), (vc, .block 5)] else [])
  | 24 => [(va, .message (vt vf 6 1)), (vb, .message (vt vf 6 1)), (vc, .message (vt vf 6 1))]
  | 25 => msgs [(va, vt va 6 4), (vb, vt vb 6 5), (vc, vt vc 6 3)]
  | 29 => msgs [(va, vt va 7 1), (vb, vt vb 7 1), (vc, vt vc 7 (cHead ctl))]
  | 30 => [(vb, .attestation (att va)), (vc, .attestation (att va)),
      (va, .attestation (att vb)), (vc, .attestation (att vb))] ++
      (if ctl then [(va, .attestation (att vc)), (vb, .attestation (att vc))] else []) ++
      [(va, .block 3), (vb, .block 3), (vc, .block 3)]
  | 33 => msgs [(va, vt va 8 1), (vb, vt vb 8 1), (vc, vt vc 8 (cHead ctl))]
  | _ => []

/-- The events of time `t`, in phase order: the ticks of the awake honest nodes, the deliveries
(no restarts: nobody sleeps). -/
def segsD (ctl : Bool) (t : Nat) : List (Fin 5 × X.EvD) :=
  (honest.filter fun y => awakeB y t).map (fun y => (y, .tick 0)) ++ dels ctl t

/-- An entry of the schedule on data: node, time, event. -/
abbrev Ent := DataRun.Ent X

/-- The entries of the schedule: the event lists of the times `0, …, 35`, flattened. -/
def entriesD (ctl : Bool) : List Ent :=
  (List.range 36).flatMap fun t => (segsD ctl t).map fun ye => (ye.1, t, ye.2)

/-- The schedule on data: the entries, the awake function, the horizon `35`, the honest nodes. -/
def dataD (ctl : Bool) : DataRun.Data X := ⟨entriesD ctl, awakeB, 35, honest⟩

theorem entries_ok : ∀ ctl, ∀ en ∈ entriesD ctl, en.1 ≠ vf ∧ EvD.OK X en.2.2 := by
  decide +kernel

/-- The run on data, with its side conditions. -/
noncomputable def runD (ctl : Bool) : DataRun.Run X :=
  ⟨ro, proposer, dg, dataD ctl, ⟨hX, entries_ok ctl, fun _ => rfl, dg_genesis, dg_blk⟩⟩

/-- The schedule of the run. -/
noncomputable def sched (ctl : Bool) : Schedule N5 := DataRun.sched ro (dataD ctl)

/-- The run trace. -/
noncomputable abbrev tr (ctl : Bool) : RunTrace N5 := (sched ctl).trace proposer dg

/-! ## The run on data -/

/-- A cut of the run on data. -/
abbrev RowD : Type := DataRun.RowD X

/-- **The cuts of the run on data**, in order. -/
abbrev rowsD (ctl : Bool) : List RowD := DataRun.rowsD (dataD ctl)

/-- The data of node `y` before cut `c`. -/
abbrev stateD (ctl : Bool) (y : Fin 5) (c : Nat) : X.NodeD := DataRun.stateD (dataD ctl) y c

/-- **The fields of the run at a cut are the row's.** -/
theorem trace_row {ctl : Bool} {c : Nat} {r : RowD} (hr : (rowsD ctl)[c]? = some r) :
    (tr ctl).node c = r.node ∧ (tr ctl).time c = r.time ∧ (tr ctl).pos c = r.pos ∧
      (tr ctl).post c = r.post.interp ro ∧ (tr ctl).state r.node c = r.pre.interp ro :=
  DataRun.trace_row (runD ctl) hr

/-- **The states of the run are the rows' data.** -/
theorem trace_state (ctl : Bool) (y : Fin 5) (c : Nat) :
    (tr ctl).state y c = (stateD ctl y c).interp ro :=
  DataRun.trace_state (runD ctl) y c

theorem rowsD_time {ctl : Bool} {i : Nat} {r : RowD} (hr : (rowsD ctl)[i]? = some r) :
    (tr ctl).time i = r.time := (trace_row hr).2.1

theorem label_row {ctl : Bool} {i : Nat} {ℓ : Cut N5} (h : (tr ctl).label i = some ℓ) :
    ∃ r, (rowsD ctl)[i]? = some r ∧ r.cut.interp ro = ℓ :=
  DataRun.label_row (runD ctl) h

theorem callAt_row {ctl : Bool} {i : Nat} {r : RowD} (hr : (rowsD ctl)[i]? = some r) :
    (tr ctl).CallAt r.node i (r.cut.interp ro) :=
  DataRun.callAt_row (runD ctl) hr

theorem restartAt_iff {ctl : Bool} {y : Fin 5} {k : Nat} :
    (tr ctl).RestartAt y k ↔
      ∃ r, (rowsD ctl)[k]? = some r ∧ r.node = y ∧ DataRun.isRestartCut r.cut :=
  DataRun.restartAt_iff (runD ctl)

/-! ## The laws of the run -/

theorem entryLaws : ∀ ctl, DataRun.EntryLaws (dataD ctl) := by
  intro ctl
  exact ⟨by revert ctl; decide +kernel, by revert ctl; decide +kernel,
    by revert ctl; decide +kernel, by revert ctl; decide +kernel, by revert ctl; decide +kernel,
    by revert ctl; decide +kernel, by revert ctl; decide +kernel, by revert ctl; decide +kernel⟩

/-- **No entry is a restart**, in both variants. -/
theorem entries_no_restart : ∀ ctl, ∀ en ∈ entriesD ctl, DataRun.isRestart en.2.2 = false := by
  decide +kernel

theorem awakeB_le {y : Fin 5} {t : Nat} (h : awakeB y t = true) : t ≤ 35 := by
  simp only [awakeB, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1

/-- **The awake schedule ticks**: an honest node awake at a time ticks there (`RunLaws.ticks`),
in both variants. -/
theorem sched_ticks (ctl : Bool) : ∀ y ∈ H, ∀ t, 0 ≤ t → X.sp.toParams.IsPublic t →
    (sched ctl).awake y t → ∃ k x, (sched ctl).entry k = some (y, t, .tick x) :=
  DataRun.sched_ticks (entryLaws ctl) fun _ _ => awakeB_le

/-- **The awake schedule restarts at every wake** (`RunLaws.restart_at_wake`), in both variants:
vacuously, since `a, b, c` are awake on `[0, 35]` and `d` never wakes. -/
theorem sched_restart_at_wake (ctl : Bool) : ∀ y ∈ H, ∀ u v : Time, 0 ≤ u → u < v →
    ¬ (sched ctl).awake y u → (sched ctl).awake y v →
    ∃ k t, (sched ctl).entry k = some (y, t, .restart) ∧ u < t ∧ t ≤ v :=
  DataRun.sched_restart_at_wake (entryLaws ctl) (fun _ _ => awakeB_le) mem_honest

/-- **The awake schedule is within the horizon `35`** (`RunLaws.horizon`), in both variants. -/
theorem sched_horizon (ctl : Bool) : ∀ y ∈ H, ∀ t, (sched ctl).awake y t →
    (∃ k y' t' e, (sched ctl).entry k = some (y', t', e) ∧ t ≤ t') ∨
      ∃ T, (sched ctl).horizon = some T ∧ t ≤ T :=
  DataRun.sched_horizon (D := dataD ctl) fun _ _ => awakeB_le

/-- **The entry laws of the schedule** (`RunLaws`), in both variants. -/
theorem sched_runLaws (ctl : Bool) : (sched ctl).RunLaws proposer dg H :=
  DataRun.sched_runLaws (runD ctl) (entryLaws ctl) (fun _ _ => awakeB_le) mem_honest

/-- **The wire checks of the deliveries** (`RunLaws.wire`; the blocks are the four table roots,
with their digests `dg_blk`), in both variants. -/
theorem run_wire (ctl : Bool) : ∀ k y t e, y ∈ H → (sched ctl).entry k = some (y, t, e) →
    Node.WireOK dg e :=
  (sched_runLaws ctl).wire

/-- **The credentials of the delivered blocks** (`RunLaws.credential`), in both variants. -/
theorem run_credential (ctl : Bool) : ∀ k y t B, y ∈ H →
    (sched ctl).entry k = some (y, t, .block B) →
    B.proposer = proposer B.slot :=
  (sched_runLaws ctl).credential

/-- The row checks of both variants (the row laws, no restart, the row counts) in one kernel
evaluation of the rows. -/
private theorem rowChecks : (∀ ctl, (rowsD ctl).all (fun r => DataRun.fgBlockOK r.cut) = true ∧
    allPre DataRun.attOK [] (rowsD ctl) = true ∧ allPre DataRun.msgOK [] (rowsD ctl) = true ∧
    (rowsD ctl).all (fun r => !DataRun.isRestartCut r.cut) = true) ∧
    (rowsD false).length = 266 ∧ (rowsD true).length = 274 := by
  decide +kernel

theorem rowLaws : ∀ ctl, DataRun.RowLaws (dataD ctl) := fun ctl =>
  ⟨(rowChecks.1 ctl).1, (rowChecks.1 ctl).2.1, (rowChecks.1 ctl).2.2.1⟩

/-- **No cut is a restart**, in both variants. -/
theorem rows_no_restart : ∀ ctl, (rowsD ctl).all (fun r => !DataRun.isRestartCut r.cut) = true :=
  fun ctl => (rowChecks.1 ctl).2.2.2

/-- No honest node restarts. -/
theorem not_restartAt (ctl : Bool) (y : Fin 5) (k : Nat) : ¬ (tr ctl).RestartAt y k := by
  rintro hk
  obtain ⟨r, hr, -, hres⟩ := restartAt_iff.1 hk
  have := List.all_eq_true.1 (rows_no_restart ctl) r (List.mem_of_getElem? hr)
  rw [hres] at this
  cases this

/-- **The row counts**: `266` cuts in the rejection run, `274` in the control. -/
theorem rowsD_length : (rowsD false).length = 266 ∧ (rowsD true).length = 274 := rowChecks.2

theorem fgBlock_ok {ctl : Bool} {i : Nat} {y : Fin 5} {B : X.Blk}
    (h : (tr ctl).BlockCallAt y i B) : ∃ b ∈ X.roots, B = X.blk b :=
  DataRun.fgBlock_ok (runD ctl) (rowLaws ctl) h

/-- **The run is a Goldilocks run**, in both variants. -/
theorem run_goldilocksRun (ctl : Bool) : GoldilocksRun proposer dg H (tr ctl) :=
  DataRun.run_goldilocksRun (runD ctl) (entryLaws ctl) (rowLaws ctl) (fun _ _ => awakeB_le)
    mem_honest fun h => h rfl

/-! ## `Sync[24, 33]` -/

theorem syncD_true : ∀ ctl, DataRun.syncD (dataD ctl) 24 33 = true ∧
    DataRun.blockPosD (dataD ctl) = true := by
  decide +kernel

/-- **`Sync[24, 33]`**, in both variants: `V`, accepted by `a` and `b` at `30`, reaches `c` at
`30` (refused by its FG as a held root, accepted by its AC at `4`); `Da`, `Db` are accepted
before the window, so they oblige no delivery. -/
theorem run_sync (ctl : Bool) : (tr ctl).SyncRun H 1 24 33 :=
  DataRun.run_sync (runD ctl) mem_honest (syncD_true ctl).1 (syncD_true ctl).2

end Consensus.Goldilocks.Test.HalfCommittee.Heads

end

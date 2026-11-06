module
public import ConsensusLeanTest.Goldilocks.Runs.Data.Sync
public import ConsensusLeanTest.Goldilocks.HalfCommittee.Run
@[expose] public section

/-! # The later-Carry run with five validators: schedule, `GoldilocksRun`, `Sync[24, 33]`

The concrete run of the premise-necessity witness for the premise `carryLater` of
`RecentSourceNextVote`, on the computable mirror (`Goldilocks/Mirror/Node`) and the generic run on
data (`Goldilocks/Runs/Data/Run`, `Goldilocks/Runs/Data/Sync`). Five validators: `a, b, c, d`
honest, `f` faulty and the proposer of every slot (`Five.sp5`: `Δ = Δ_F = 1`, `t_s = 4s`, `k = 4`,
`c = 2`, `δ_t = 6`, genesis root `2`). The block table holds three blocks of `f`: `B` (root `1`,
slot `2`) and `W` (root `4`, slot `8`), children of genesis `G`, and `Y` (root `3`, slot `3`), a
child of `B`. `a, b, d` are awake on `[0, 39]`; `c` sleeps on `[0, 24]` and restarts at `25`,
inside slot `6`, so it is not joined in slot `7` and first votes in slot `8`.

The schedule `sched ctl` lists, per time `0, …, 39`, `c`'s restart, the ticks of the awake honest
nodes and the deliveries (`dels`): `B → a, b, d` at `8`; `Y → a, b` at `12`; `Y → d` at `23`;
at `25` `B → c` and again `B → a, b, d` (each FG refuses the held root; one cut each), and in the
control (`ctl = true`) also `Y → c` and `Y → a, b, d`, then the slot-6 votes `a6`, `b6` (head
`Y`) and `d6` (head `B`) to the other honest nodes; the slot-7 votes (head `Y`) at `29`; the
attestations of `a, b, d` at `30`; at `32` `W → a, b, c, d` and the slot-8 votes; in the control
`c`'s attestation to `a, b, d` at `33`. In the rejection run (`ctl = false`) `c` never accepts
`Y`, which every other honest node accepted before `t_6 = 24`.

The run instantiates the generic core (`runD ctl : DataRun.Run X`): its states are the mirror's
and its cuts the rows `rowsD ctl`. `GoldilocksRun` holds for both variants
(`run_goldilocksRun`), with the entry laws (`entryLaws`: order, no drops, ticks, awake calls, the
three restart laws, the wire data of the three roots) and the row laws (`rowLaws`) checked by
the kernel; only `c` restarts (`rows_restart_c`); `Sync[24, 33]` holds for both variants
(`run_sync`), from the kernel check `syncD_true`.

The fixture-specific part (table, digest, schedule, instance of the run) parallels
`Goldilocks/InitialCarry/Run` for the new table and the restart; the X-free parts of stage 2
(`Five.sp5`, the validators, `Five.H`, `Five.honest`) are imported.

Kind: the common run of the (r) rejection (`ctl = false`, `Goldilocks/CarryLater/Reject`) and the
(control) (`ctl = true`, `Goldilocks/CarryLater/Control`). -/

namespace Consensus.Goldilocks.Test.HalfCommittee.Later

open SA Fix ScheduleRun
open Five (sp5 va vb vc vd vf H honest mem_honest Content)

/-! ## The fixture -/

/-- The block `B`: root `1`, slot `2`, child of genesis. -/
def rowB : Row := ⟨1, 2, 2, 0, [2]⟩

/-- The block `Y`: root `3`, slot `3`, child of `B`. -/
def rowY : Row := ⟨3, 1, 3, 0, [1, 2]⟩

/-- The block `W`: root `4`, slot `8`, child of genesis. -/
def rowW : Row := ⟨4, 2, 8, 0, [2]⟩

/-- The fixture: `sp5`, the faulty proposer `f`, the table `{B, Y, W}`. -/
abbrev X : Fix := ⟨sp5, rfl, vf, [rowB, rowY, rowW]⟩

theorem hX : X.OK := by decide

/-- The replay order of the restarts (any one: the mirror is parametric in it). -/
noncomputable abbrev ro : ReplayOrder X.sp (List (FG.Att X.sp.n)) := ReplayOrder.choice X.sp

/-- The node. -/
noncomputable abbrev N5 : NodeAC X.sp.toParams := X.AC ro

/-- The proposer of every slot: `f`. -/
def proposer : Nat → Fin X.sp.n := fun _ => vf

/-- The contents of genesis, `B`, `Y` and `W`. -/
def cG : Content := (none, 0, 0, [], ([], []))
@[inherit_doc cG] def cB : Content := (some 2, 2, 0, [], ([], []))
@[inherit_doc cG] def cY : Content := (some 1, 3, 0, [], ([], []))
@[inherit_doc cG] def cW : Content := (some 2, 8, 0, [], ([], []))

/-- The digest of a content: `2, 1, 3, 4` for genesis, `B`, `Y`, `W` (and `0` for any other
content, which no block of the run has). -/
def dgC (q : Content) : Nat :=
  if q = cG then 2 else if q = cB then 1 else if q = cY then 3 else if q = cW then 4 else 0

/-- The digest of the run. -/
def dg : Digest (List (FG.Att X.sp.n)) (Payload X.sp.n) :=
  fun p s x a q => dgC (p, s, x, a, q)

theorem dg_genesis : (X.sp.toParams.genesisBlock N5.genesisPayload).RootOk dg := by
  change (2 : Nat) = dgC cG; simp [dgC]

theorem roots_eq : X.roots = [1, 3, 4] := rfl

/-- **The digest of the three table roots** (the wire check of their deliveries). -/
theorem dg_blk : ∀ r ∈ X.roots, (X.blk r).RootOk dg := by
  intro r hr
  rw [roots_eq] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · change (1 : Nat) = dgC cB; simp [dgC, cB, cG]
  · change (3 : Nat) = dgC cY; simp [dgC, cB, cG, cY]
  · change (4 : Nat) = dgC cW; simp [dgC, cB, cG, cY, cW]

/-! ## The schedule -/

/-- A vote. -/
def vt (v : Fin 5) (s h : Nat) : X.V := ⟨v, s, h⟩

/-- The attestation of `v` (the only one the fragment signs). -/
def att (v : Fin 5) : FG.Att X.sp.n := attG (X := X) v

/-- The head of `c`'s slot-8 vote: `W` in the rejection run, `Y` in the control. -/
def cHead (ctl : Bool) : Nat := if ctl then 3 else 4

/-- Awake: `a, b, d` on `[0, 39]`, `c` on `[25, 39]`. -/
def awakeB (y : Fin 5) (t : Nat) : Bool :=
  t ≤ 39 && (y == va || y == vb || y == vd || (y == vc && 25 ≤ t))

/-- A vote of `s` delivered to the other honest nodes. -/
def msgs (L : List (Fin 5 × X.V)) : List (Fin 5 × X.EvD) :=
  L.flatMap fun (s, v) => (honest.filter (· != s)).map fun y => (y, .message v)

/-- The deliveries at time `t`. -/
def dels (ctl : Bool) : Nat → List (Fin 5 × X.EvD)
  | 8 => [(va, .block 1), (vb, .block 1), (vd, .block 1)]
  | 12 => [(va, .block 3), (vb, .block 3)]
  | 23 => [(vd, .block 3)]
  | 25 => [(vc, .block 1)] ++ (if ctl then [(vc, .block 3)] else []) ++
      [(va, .block 1), (vb, .block 1), (vd, .block 1)] ++
      (if ctl then [(va, .block 3), (vb, .block 3), (vd, .block 3)] else []) ++
      msgs [(va, vt va 6 3), (vb, vt vb 6 3), (vd, vt vd 6 1)]
  | 29 => msgs [(va, vt va 7 3), (vb, vt vb 7 3), (vd, vt vd 7 3)]
  | 30 => [va, vb, vd].flatMap fun s => (honest.filter (· != s)).map fun y =>
      (y, .attestation (att s))
  | 32 => [(va, .block 4), (vb, .block 4), (vc, .block 4), (vd, .block 4)] ++
      msgs [(va, vt va 8 3), (vb, vt vb 8 3), (vc, vt vc 8 (cHead ctl)), (vd, vt vd 8 3)]
  | 33 => if ctl then [(va, .attestation (att vc)), (vb, .attestation (att vc)),
      (vd, .attestation (att vc))] else []
  | _ => []

/-- The events of time `t`, in phase order: restarts (of the nodes that wake at `t`), the ticks
of the awake honest nodes, the deliveries. -/
def segsD (ctl : Bool) (t : Nat) : List (Fin 5 × X.EvD) :=
  (honest.filter fun y => t != 0 && awakeB y t && !awakeB y (t - 1)).map
      (fun y => (y, .restart)) ++
    (honest.filter fun y => awakeB y t).map (fun y => (y, .tick 0)) ++ dels ctl t

/-- An entry of the schedule on data: node, time, event. -/
abbrev Ent := DataRun.Ent X

/-- The entries of the schedule: the event lists of the times `0, …, 39`, flattened. -/
def entriesD (ctl : Bool) : List Ent :=
  (List.range 40).flatMap fun t => (segsD ctl t).map fun ye => (ye.1, t, ye.2)

/-- The schedule on data: the entries, the awake function, the horizon `39`, the honest nodes. -/
def dataD (ctl : Bool) : DataRun.Data X := ⟨entriesD ctl, awakeB, 39, honest⟩

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

/-! ## The laws of the run -/

/-- The eight entry checks of both variants in one kernel evaluation of the entries. -/
private theorem entryChecks : ∀ ctl, (entriesD ctl).IsChain DataRun.ordD ∧
    (∀ en ∈ entriesD ctl, DataRun.dropD en = false) ∧
    (∀ y : Fin 5, ∀ t < 39 + 1, awakeB y t = true →
      ∃ en ∈ entriesD ctl, en.1 = y ∧ en.2.1 = t ∧ DataRun.isTick en.2.2 = true) ∧
    (∀ en ∈ entriesD ctl, awakeB en.1 en.2.1 = true) ∧
    allPre (fun acc en => (List.range en.2.1).all fun u =>
      awakeB en.1 u || (acc.any fun en' => en'.1 = en.1 && u ≤ en'.2.1) ||
        DataRun.isRestart en.2.2) [] (entriesD ctl) = true ∧
    (honest.all fun y => (List.range (39 + 1)).all fun v =>
      (List.range v).all fun u => awakeB y u || !awakeB y v || (entriesD ctl).any fun en =>
        en.1 == y && DataRun.isRestart en.2.2 && decide (u < en.2.1) && decide (en.2.1 ≤ v)) =
      true ∧
    allPre (fun acc en => !DataRun.isRestart en.2.2 || (0 < en.2.1 &&
      !awakeB en.1 (en.2.1 - 1) && acc.all fun en' => en'.1 != en.1 || en'.2.1 < en.2.1 - 1))
      [] (entriesD ctl) = true ∧
    (∀ en ∈ entriesD ctl, DataRun.wireD en.2.2 = true) := by
  decide +kernel

theorem entryLaws : ∀ ctl, DataRun.EntryLaws (dataD ctl) := fun ctl =>
  have h := entryChecks ctl
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

theorem awakeB_le {y : Fin 5} {t : Nat} (h : awakeB y t = true) : t ≤ 39 := by
  simp only [awakeB, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1

/-- The checks on the rows of one variant: the row laws, only `c` restarts (once, at `25`), the
row count `n`, `Sync[24, 33]`. -/
private abbrev RowChecks (ctl : Bool) (n : Nat) : Prop :=
  (rowsD ctl).all (fun r => DataRun.fgBlockOK r.cut) = true ∧
    allPre DataRun.attOK [] (rowsD ctl) = true ∧ allPre DataRun.msgOK [] (rowsD ctl) = true ∧
    (rowsD ctl).all (fun r => !DataRun.isRestartCut r.cut || (r.node == vc && r.time == 25)) =
      true ∧ (rowsD ctl).length = n ∧
    DataRun.syncD (dataD ctl) 24 33 = true ∧ DataRun.blockPosD (dataD ctl) = true

/-- The checks of the rejection run in one kernel evaluation of its rows: one kernel declaration
per variant, so the two run in parallel and the kernel's caches hold one run at a time. -/
private theorem rowChecks_false : RowChecks false 344 := by
  decide +kernel

/-- The checks of the control in one kernel evaluation of its rows. -/
private theorem rowChecks_true : RowChecks true 354 := by
  decide +kernel

theorem rowLaws : ∀ ctl, DataRun.RowLaws (dataD ctl) := by
  intro ctl; cases ctl
  exacts [⟨rowChecks_false.1, rowChecks_false.2.1, rowChecks_false.2.2.1⟩,
    ⟨rowChecks_true.1, rowChecks_true.2.1, rowChecks_true.2.2.1⟩]

/-- **Only `c` restarts** (once, at `25`), in both variants. -/
theorem rows_restart_c : ∀ ctl,
    (rowsD ctl).all (fun r => !DataRun.isRestartCut r.cut || (r.node == vc && r.time == 25)) =
      true := by
  intro ctl; cases ctl
  exacts [rowChecks_false.2.2.2.1, rowChecks_true.2.2.2.1]

/-- **The row counts**: `344` cuts in the rejection run, `354` in the control. -/
theorem rowsD_length : (rowsD false).length = 344 ∧ (rowsD true).length = 354 :=
  ⟨rowChecks_false.2.2.2.2.1, rowChecks_true.2.2.2.2.1⟩

/-- **The run is a Goldilocks run**, in both variants. -/
theorem run_goldilocksRun (ctl : Bool) : GoldilocksRun proposer dg H (tr ctl) :=
  DataRun.run_goldilocksRun (runD ctl) (entryLaws ctl) (rowLaws ctl) (fun _ _ => awakeB_le)
    mem_honest fun h => h rfl

/-! ## `Sync[24, 33]` -/

/-- The `Sync[24, 33]` check of the rejection run. -/
theorem syncD_rejection : DataRun.syncD (dataD false) 24 33 = true ∧
    DataRun.blockPosD (dataD false) = true :=
  rowChecks_false.2.2.2.2.2

/-- The `Sync[24, 33]` check of the control. -/
theorem syncD_control : DataRun.syncD (dataD true) 24 33 = true ∧
    DataRun.blockPosD (dataD true) = true :=
  rowChecks_true.2.2.2.2.2

theorem syncD_true : ∀ ctl, DataRun.syncD (dataD ctl) 24 33 = true ∧
    DataRun.blockPosD (dataD ctl) = true
  | false => syncD_rejection
  | true => syncD_control

/-- **`Sync[24, 33]`**, in both variants: `B`, accepted by `c` at `25`, reaches `a, b, d` at `25`
(refused by their FG as a held root); in the control `Y`, accepted by `c` at `25`, too; `Y` is
accepted by `a, b, d` before the window, so it obliges no delivery to `c`. -/
theorem run_sync (ctl : Bool) : (tr ctl).SyncRun H 1 24 33 :=
  DataRun.run_sync (runD ctl) mem_honest (syncD_true ctl).1 (syncD_true ctl).2

end Consensus.Goldilocks.Test.HalfCommittee.Later

end

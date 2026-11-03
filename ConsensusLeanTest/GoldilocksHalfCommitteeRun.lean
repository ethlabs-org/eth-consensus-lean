module
public import ConsensusLeanTest.GoldilocksHalfCommitteeCutLaw
public import ConsensusLeanTest.GoldilocksScheduleLocalRun
@[expose] public section

/-! # The halfCommittee run with five validators: schedule and `GoldilocksRun`

The concrete run of the halfCommittee premise-necessity witness, on the computable mirror
(`GoldilocksHalfCommitteeNode`) and the schedule API (`GoldilocksScheduleRun`,
`GoldilocksScheduleLocalRun`). Five validators: `a, b, c, d` honest, `f` faulty and the proposer
of every slot; `Δ = Δ_F = 1`, `t_s = 4s`, `k = 4`, `c = 2`, `δ_t = 6`, genesis root `2`; the block
table holds `V` (root `3`, slot `1`) and `B` (root `1`, slot `6`), both children of genesis.

The schedule `sched ctl` lists, per integer time `0, …, 35` (`segsD`, flattened to `entriesD`),
the restarts, the ticks of the awake honest nodes and the deliveries, in phase order. `c` sleeps
on `24..27` and restarts at `28`; in the rejection run (`ctl = false`) `d` never wakes, in the
control (`ctl = true`) `d` wakes and restarts at `24`. Deliveries: `V → c` at `4`; at `24` the
block `B`, the slot-6 votes of `a, b` and the faulty vote `f6`; at `28` **the reprocessing**:
`c` receives `B, a6, b6, f6`, and since `c` takes the three votes into its pool and accepts `B`
at `28`, `Sync[24, 33]` obliges `a` and `b` (and `d` in the control) to process `B, a6, b6, f6`
again at `28` (the votes leave the pools unchanged, `B` is refused by the FG as a held root: one
cut each); the slot-7 votes at `29`, the attestations at `30`, the slot-8 votes at `33`. The
faulty `f` has no entries: its blocks and vote appear only as deliveries.

The states of the run are the mirror's (`stBefore_eq`, from `exec_interp`, with `frag_init` as the
base of `Frag` along the schedule), and its cuts are the rows `rowsD` (`trace_label`,
`trace_row`, `trace_state`). `GoldilocksRun` holds for both variants (`run_goldilocksRun`), by
`trace_goldilocksRun` with the run laws checked on the schedule by the kernel; the awake schedule
gives `RunLaws.ticks`, `RunLaws.restart_at_wake` and `RunLaws.horizon` (`sched_ticks`,
`sched_restart_at_wake`, `sched_horizon`, together `sched_awake_laws`).

Kind: the common run of the (r) rejection (`ctl = false`, `GoldilocksHalfCommitteePremises`)
and the (control) (`ctl = true`, `GoldilocksHalfCommitteeControl`). -/

namespace Consensus.Goldilocks.Test.HalfCommittee

open SA

/-! ## The fixture -/

namespace Five

open Fix ScheduleRun

/-- The shared parameters: five validators, `Δ = 1`, `t_s = 4s`, genesis root `2`, `δ_t = 6`. -/
abbrev P5 : Params where
  n := 5
  hn := by decide
  Δ := 1
  hΔ := one_pos
  slotTime := fun s => 4 * (s : Int)
  slotTime_zero := by simp
  slotTime_strictMono := fun a b h => by change 4 * (a : Int) < 4 * (b : Int); omega
  slotTime_public := fun _ => one_dvd _
  genesisRoot := 2
  δt := 6

/-- The SA parameters: `P5` with `k = 4`, `c = 2`. -/
abbrev sp5 : SAParams where
  toParams := P5
  slotTime_eq := fun s => by change 4 * (s : Int) = 4 * 1 * s; omega
  k := 4
  two_le_k := by decide
  c := 2
  two_le_c := le_rfl

/-- The honest validators `a, b, c, d` and the faulty proposer `f`. -/
abbrev va : Fin 5 := ⟨0, by decide⟩
@[inherit_doc va] abbrev vb : Fin 5 := ⟨1, by decide⟩
@[inherit_doc va] abbrev vc : Fin 5 := ⟨2, by decide⟩
@[inherit_doc va] abbrev vd : Fin 5 := ⟨3, by decide⟩
@[inherit_doc va] abbrev vf : Fin 5 := ⟨4, by decide⟩

/-- The block `B`: root `1`, slot `6`, child of genesis. -/
def rowB : Row := ⟨1, 2, 6, 0, [2]⟩

/-- The block `V`: root `3`, slot `1`, child of genesis. -/
def rowV : Row := ⟨3, 2, 1, 0, [2]⟩

/-- The fixture: `sp5`, the faulty proposer `f`, the table `{B, V}`. -/
abbrev X : Fix := ⟨sp5, rfl, vf, [rowB, rowV]⟩

theorem hX : X.OK := by decide

/-- The honest validators. -/
def H : Set (Fin 5) := {y | y ≠ vf}

/-- The replay order of the restarts (any one: the mirror is parametric in it). -/
noncomputable abbrev ro : ReplayOrder X.sp (List (FG.Att X.sp.n)) := ReplayOrder.choice X.sp

/-- The node. -/
noncomputable abbrev N5 : NodeAC X.sp.toParams := X.AC ro

/-- The proposer of every slot: `f`. -/
def proposer : Nat → Fin X.sp.n := fun _ => vf

/-- The content of a block (what its root digests). -/
abbrev Content := Option Nat × Nat × Nat × List (FG.Att 5) × Payload 5

/-- The contents of genesis, `B` and `V`. -/
def cG : Content := (none, 0, 0, [], ([], []))
@[inherit_doc cG] def cB : Content := (some 2, 6, 0, [], ([], []))
@[inherit_doc cG] def cV : Content := (some 2, 1, 0, [], ([], []))

/-- The digest of a content: `2, 1, 3` for genesis, `B`, `V` (and `0` for any other content,
which no block of the run has). -/
def dgC (q : Content) : Nat :=
  if q = cG then 2 else if q = cB then 1 else if q = cV then 3 else 0

/-- The digest of the run. -/
def dg : Digest (List (FG.Att X.sp.n)) (Payload X.sp.n) :=
  fun p s x a q => dgC (p, s, x, a, q)

theorem dg_genesis : (X.sp.toParams.genesisBlock N5.genesisPayload).RootOk dg := by
  change (2 : Nat) = dgC cG; simp [dgC]

theorem dg_blk {r : Nat} (hr : r = 1 ∨ r = 3) : (X.blk r).RootOk dg := by
  rcases hr with rfl | rfl
  · change (1 : Nat) = dgC cB; simp [dgC, cB, cG]
  · change (3 : Nat) = dgC cV; simp [dgC, cB, cG, cV]

/-! ## The schedule -/

/-- A vote. -/
def vt (v : Fin 5) (s h : Nat) : X.V := ⟨v, s, h⟩

/-- The attestation of `v` (the only one the fragment signs). -/
def att (v : Fin 5) : FG.Att X.sp.n := attG (X := X) v

/-- The head of `c`'s slot-8 vote: `V` in the rejection run, `B` in the control. -/
def cHead (ctl : Bool) : Nat := if ctl then 1 else 3

/-- Awake: `a, b` on `[0, 35]`, `c` on `[0, 23] ∪ [28, 35]`, `d` on `[24, 35]` in the control. -/
def awakeB (ctl : Bool) (y : Fin 5) (t : Nat) : Bool :=
  t ≤ 35 && (y.val ≤ 1 || (y.val = 2 && (t < 24 || 28 ≤ t)) || (y.val = 3 && ctl && 24 ≤ t))

/-- The awake function of the run. -/
def awakeT (ctl : Bool) (y : Fin 5) (t : Time) : Prop := 0 ≤ t ∧ awakeB ctl y t.toNat = true

/-- The honest validators, in order. -/
def honest : List (Fin 5) := [va, vb, vc, vd]

/-- The deliveries at time `t`. -/
def dels (ctl : Bool) : Nat → List (Fin 5 × X.EvD)
  | 4 => [(vc, .block 3)]
  | 24 => [(va, .block 1), (vb, .block 1)] ++ (if ctl then [(vd, .block 1)] else []) ++
      [(va, .message (vt vb 6 1)), (vb, .message (vt va 6 1))] ++
      (if ctl then [(vd, .message (vt va 6 1)), (vd, .message (vt vb 6 1))] else []) ++
      [(va, .message (vt vf 6 1)), (vb, .message (vt vf 6 1))] ++
      (if ctl then [(vd, .message (vt vf 6 1))] else [])
  | 28 => (if ctl then [vc, va, vb, vd] else [vc, va, vb]).flatMap fun y =>
      [(y, .block 1), (y, .message (vt va 6 1)), (y, .message (vt vb 6 1)),
        (y, .message (vt vf 6 1))]
  | 29 => [(vb, .message (vt va 7 1)), (vc, .message (vt va 7 1)),
      (va, .message (vt vb 7 1)), (vc, .message (vt vb 7 1))] ++
      (if ctl then [(vd, .message (vt va 7 1)), (vd, .message (vt vb 7 1)),
        (va, .message (vt vd 7 1)), (vb, .message (vt vd 7 1)),
        (vc, .message (vt vd 7 1))] else [])
  | 30 => [(vb, .attestation (att va)), (vc, .attestation (att va)),
      (va, .attestation (att vb)), (vc, .attestation (att vb))] ++
      (if ctl then [(vd, .attestation (att va)), (vd, .attestation (att vb)),
        (va, .attestation (att vd)), (vb, .attestation (att vd)),
        (vc, .attestation (att vd))] else [])
  | 33 => [(vb, .message (vt va 8 1)), (vc, .message (vt va 8 1)),
      (va, .message (vt vb 8 1)), (vc, .message (vt vb 8 1)),
      (va, .message (vt vc 8 (cHead ctl))), (vb, .message (vt vc 8 (cHead ctl)))] ++
      (if ctl then [(vd, .message (vt va 8 1)), (vd, .message (vt vb 8 1)),
        (vd, .message (vt vc 8 1)), (va, .message (vt vd 8 1)),
        (vb, .message (vt vd 8 1)), (vc, .message (vt vd 8 1))] else [])
  | _ => []

/-- The events of time `t`, in phase order: restarts (of the nodes that wake at `t`), the ticks
of the awake honest nodes, the deliveries. -/
def segsD (ctl : Bool) (t : Nat) : List (Fin 5 × X.EvD) :=
  (honest.filter fun y => t != 0 && awakeB ctl y t && !awakeB ctl y (t - 1)).map
      (fun y => (y, .restart)) ++
    (honest.filter fun y => awakeB ctl y t).map (fun y => (y, .tick 0)) ++ dels ctl t

/-- An entry of the schedule on data: node, time, event. -/
abbrev Ent := Fin 5 × Nat × X.EvD

/-- The entries of the schedule: the event lists of the times `0, …, 35`, flattened. -/
def entriesD (ctl : Bool) : List Ent :=
  (List.range 36).flatMap fun t => (segsD ctl t).map fun ye => (ye.1, t, ye.2)

/-- The schedule of the run. -/
noncomputable def sched (ctl : Bool) : Schedule N5 where
  entry k := ((entriesD ctl)[k]?).map fun en => (en.1, (en.2.1 : Time), en.2.2.interp ro)
  prefix_closed k h := by
    simp only [Option.map_eq_none_iff, List.getElem?_eq_none_iff] at h ⊢; omega
  awake := awakeT ctl
  horizon := some 35

/-- The run trace. -/
noncomputable abbrev tr (ctl : Bool) : RunTrace N5 := (sched ctl).trace proposer dg

theorem sched_entry (ctl : Bool) (k : Nat) : (sched ctl).entry k =
    ((entriesD ctl)[k]?).map fun en => (en.1, (en.2.1 : Time), en.2.2.interp ro) := rfl

/-! ## The states on data -/

/-- One entry on the data of all nodes. -/
def stepD (st : Fin 5 → X.NodeD) (en : Ent) : Fin 5 → X.NodeD :=
  Function.update st en.1 (execD (st en.1) en.1 en.2.1 en.2.2).1

/-- The initial data of all nodes. -/
def init0 : Fin 5 → X.NodeD := fun _ => NodeD.init X

/-- The data of all nodes before entry `k`. -/
def stD (ctl : Bool) (k : Nat) : Fin 5 → X.NodeD := ((entriesD ctl).take k).foldl stepD init0

theorem entries_ok : ∀ ctl, ∀ en ∈ entriesD ctl, en.1 ≠ vf ∧ EvD.OK X en.2.2 := by
  decide +kernel

theorem stD_succ {ctl : Bool} {k : Nat} {en : Ent} (h : (entriesD ctl)[k]? = some en) :
    stD ctl (k + 1) = stepD (stD ctl k) en := by
  rw [stD, List.take_add_one, h, Option.toList_some, List.foldl_append]; rfl

theorem stD_of_le {ctl : Bool} {k : Nat} (h : (entriesD ctl)[k]? = none) :
    stD ctl (k + 1) = stD ctl k := by
  rw [stD, List.take_add_one, h, Option.toList_none, List.append_nil]; rfl

theorem stepD_apply (st : Fin 5 → X.NodeD) (en : Ent) (y : Fin 5) :
    stepD st en y = if en.1 = y then (execD (st en.1) en.1 en.2.1 en.2.2).1 else st y := by
  unfold stepD
  by_cases h : en.1 = y
  · subst h; simp
  · simp [h, Function.update_of_ne (Ne.symm h)]

/-- `Frag` along the schedule, from `frag_init`. -/
theorem frag_stD (ctl : Bool) : ∀ k y, X.Frag (stD ctl k y)
  | 0, _ => frag_init X
  | k + 1, y => by
    cases h : (entriesD ctl)[k]? with
    | none => rw [stD_of_le h]; exact frag_stD ctl k y
    | some en =>
      rw [stD_succ h, stepD_apply]
      split_ifs with hy
      · exact frag_execD (frag_stD ctl k _) _ _ (entries_ok ctl en (List.mem_of_getElem? h)).2
      · exact frag_stD ctl k y

theorem exec_eq {ctl : Bool} {k : Nat} {en : Ent} (h : (entriesD ctl)[k]? = some en) :
    Node.exec proposer dg en.1 ((stD ctl k en.1).interp ro) en.2.1 (en.2.2.interp ro) =
      resN ro (execD (stD ctl k en.1) en.1 en.2.1 en.2.2) := by
  have hok := entries_ok ctl en (List.mem_of_getElem? h)
  exact exec_interp ro hX proposer dg en.1 (fun _ e => hok.1 e.symm) (frag_stD ctl k _)
    (Int.natCast_nonneg _) hok.2

/-- **The states of the schedule are the mirror's.** -/
theorem stBefore_eq (ctl : Bool) (y : Fin 5) :
    ∀ k, (sched ctl).stBefore proposer dg y k = (stD ctl k y).interp ro
  | 0 => (NodeD.interp_init ro hX).symm
  | k + 1 => by
    rw [Schedule.stBefore_succ, stBefore_eq ctl y k]
    cases h : (entriesD ctl)[k]? with
    | none => rw [Schedule.stepAt_none (by rw [sched_entry, h]; rfl), stD_of_le h]
    | some en =>
      rw [Schedule.stepAt_some (by rw [sched_entry, h]; rfl), stD_succ h, stepD_apply]
      split_ifs with hy
      · subst hy; rw [exec_eq h]; rfl
      · rfl

/-- The cuts of entry `k` on data. -/
def cutsD (ctl : Bool) (k : Nat) : List (CutD X) :=
  match (entriesD ctl)[k]? with
  | some en => (execD (stD ctl k en.1) en.1 en.2.1 en.2.2).2
  | none => []

theorem cutsD_some {ctl : Bool} {k : Nat} {en : Ent} (h : (entriesD ctl)[k]? = some en) :
    cutsD ctl k = (execD (stD ctl k en.1) en.1 en.2.1 en.2.2).2 := by simp [cutsD, h]

theorem cutsAt_eq (ctl : Bool) (k : Nat) :
    (sched ctl).cutsAt proposer dg k = (cutsD ctl k).map (CutD.interp ro) := by
  cases h : (entriesD ctl)[k]? with
  | none => rw [Schedule.cutsAt_none (by rw [sched_entry, h]; rfl)]; simp [cutsD, h]
  | some en =>
    rw [Schedule.cutsAt_some (by rw [sched_entry, h]; rfl), stBefore_eq, exec_eq h, cutsD_some h]
    rfl

/-- The data of the node of entry `k` after its first `p` cuts. -/
theorem midState_eq {ctl : Bool} {k : Nat} {en : Ent} (h : (entriesD ctl)[k]? = some en) {p : Nat}
    (hp : p ≤ (cutsD ctl k).length) :
    (sched ctl).midState proposer dg k p = ((stD ctl k en.1 :: postsD (stD ctl k en.1) en.1
      en.2.1 en.2.2).getD p (stD ctl k en.1)).interp ro := by
  have he : (sched ctl).entry k = some (en.1, (en.2.1 : Time), en.2.2.interp ro) := by
    rw [sched_entry, h]; rfl
  have hok := entries_ok ctl en (List.mem_of_getElem? h)
  have hc := chainOK_postsD ro hX en.1 (frag_stD ctl k en.1) (Int.natCast_nonneg en.2.1) hok.2
  rw [cutsD_some h] at hp
  rw [Schedule.midState, Schedule.entryNode_of he, Schedule.entryTime_of he, cutsAt_eq,
    cutsD_some h, stBefore_eq, foldl_take_chainOK hc p (by rw [List.length_map]; exact hp)
      ((stD ctl k en.1).interp ro), ← List.map_cons, getD_map]

/-! ## The cuts on data -/

/-- A cut of the run on data: entry, position, node, time, the cut, and the node's data before
and after it. -/
structure RowD where
  /-- The entry. -/
  ent : Nat
  /-- The position in the entry's group. -/
  pos : Nat
  /-- The node. -/
  node : Fin 5
  /-- The time. -/
  time : Nat
  /-- The cut. -/
  cut : CutD X
  /-- The node's data before the cut. -/
  pre : X.NodeD
  /-- The node's data after the cut. -/
  post : X.NodeD

/-- The cuts of entry `k` with the data `st` of the nodes before it. -/
def rowsOf (k : Nat) (st : Fin 5 → X.NodeD) (en : Ent) : List RowD :=
  let d := st en.1
  let ms := d :: postsD d en.1 en.2.1 en.2.2
  (execD d en.1 en.2.1 en.2.2).2.zipIdx.map fun cp =>
    ⟨k, cp.2, en.1, en.2.1, cp.1, ms.getD cp.2 d, ms.getD (cp.2 + 1) d⟩

/-- The cuts of the entries from `k` on. -/
def rowsAux : Nat → (Fin 5 → X.NodeD) → List Ent → List RowD
  | _, _, [] => []
  | k, st, en :: es => rowsOf k st en ++ rowsAux (k + 1) (stepD st en) es

/-- **The cuts of the run on data**, in order. -/
def rowsD (ctl : Bool) : List RowD := rowsAux 0 init0 (entriesD ctl)

theorem rowsAux_append (L₁ L₂ : List Ent) :
    ∀ k st, rowsAux k st (L₁ ++ L₂) =
      rowsAux k st L₁ ++ rowsAux (k + L₁.length) (L₁.foldl stepD st) L₂ := by
  induction L₁ with
  | nil => intro k st; rfl
  | cons en L ih =>
    intro k st
    simp only [List.cons_append, rowsAux, ih, List.append_assoc, List.length_cons,
      List.foldl_cons]
    rw [Nat.add_assoc, Nat.add_comm 1]

theorem length_rowsOf (k : Nat) (st : Fin 5 → X.NodeD) (en : Ent) :
    (rowsOf k st en).length = (execD (st en.1) en.1 en.2.1 en.2.2).2.length := by
  simp [rowsOf]

theorem start_eq (ctl : Bool) : ∀ k,
    (sched ctl).start proposer dg k = (rowsAux 0 init0 ((entriesD ctl).take k)).length
  | 0 => rfl
  | k + 1 => by
    rw [Schedule.start_succ, start_eq ctl k, cutsAt_eq, List.length_map, List.take_add_one,
      rowsAux_append, List.length_append]
    cases h : (entriesD ctl)[k]? with
    | none => simp [cutsD, h, rowsAux]
    | some en =>
      simp only [Option.toList_some, rowsAux, List.append_nil, length_rowsOf, cutsD_some h]; rfl

theorem length_rowsD (ctl : Bool) :
    (rowsD ctl).length = (sched ctl).start proposer dg (entriesD ctl).length := by
  rw [start_eq, List.take_length]; rfl

theorem rowsD_getElem? {ctl : Bool} {k : Nat} {en : Ent} (h : (entriesD ctl)[k]? = some en)
    {p : Nat} (hp : p < (cutsD ctl k).length) :
    (rowsD ctl)[(sched ctl).start proposer dg k + p]? = (rowsOf k (stD ctl k) en)[p]? := by
  have hk : k < (entriesD ctl).length := (List.getElem?_eq_some_iff.1 h).1
  have hL : entriesD ctl = (entriesD ctl).take k ++ en :: (entriesD ctl).drop (k + 1) := by
    conv_lhs => rw [← List.take_append_drop k (entriesD ctl)]
    rw [List.drop_eq_getElem_cons hk, (List.getElem?_eq_some_iff.1 h).2]
  have e : rowsD ctl = rowsAux 0 init0 ((entriesD ctl).take k) ++
      (rowsOf k (stD ctl k) en ++ rowsAux (k + 1) (stepD (stD ctl k) en)
        ((entriesD ctl).drop (k + 1))) := by
    rw [rowsD]; conv_lhs => rw [hL]
    rw [rowsAux_append, List.length_take, Nat.min_eq_left hk.le, Nat.zero_add]; rfl
  rw [e, start_eq, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem?_append_left]
  rw [length_rowsOf]; rwa [cutsD_some h] at hp

theorem rowsOf_getElem? (k : Nat) (st : Fin 5 → X.NodeD) (en : Ent) (p : Nat) :
    (rowsOf k st en)[p]? = ((execD (st en.1) en.1 en.2.1 en.2.2).2[p]?).map fun c =>
      ⟨k, p, en.1, en.2.1, c, (st en.1 :: postsD (st en.1) en.1 en.2.1 en.2.2).getD p (st en.1),
        (st en.1 :: postsD (st en.1) en.1 en.2.1 en.2.2).getD (p + 1) (st en.1)⟩ := by
  simp only [rowsOf, List.getElem?_map, List.getElem?_zipIdx]
  cases (execD (st en.1) en.1 en.2.1 en.2.2).2[p]? <;> simp

/-- A cut index of the rows is a position of an entry's group. -/
theorem row_entry {ctl : Bool} {c : Nat} (hc : c < (rowsD ctl).length) :
    ∃ k en p, (entriesD ctl)[k]? = some en ∧ c = (sched ctl).start proposer dg k + p ∧
      p < (cutsD ctl k).length ∧ (sched ctl).entryOf proposer dg c = some k := by
  cases hk : (sched ctl).entryOf proposer dg c with
  | none =>
    have := Schedule.entryOf_eq_none_iff.1 hk (entriesD ctl).length
    rw [Schedule.start_succ, cutsAt_eq, cutsD, List.getElem?_eq_none le_rfl] at this
    rw [length_rowsD] at hc
    simp at this; omega
  | some k =>
    obtain ⟨h1, h2⟩ := Schedule.entryOf_eq_some_iff.1 hk
    rw [Schedule.start_succ, cutsAt_eq, List.length_map] at h2
    cases h : (entriesD ctl)[k]? with
    | none => simp [cutsD, h] at h2; omega
    | some en =>
      exact ⟨k, en, c - (sched ctl).start proposer dg k, h, by omega, by omega, rfl⟩

/-- **The labels of the run are the rows' cuts.** -/
theorem trace_label (ctl : Bool) (c : Nat) :
    (tr ctl).label c = ((rowsD ctl)[c]?).map fun r => r.cut.interp ro := by
  by_cases hc : c < (rowsD ctl).length
  · obtain ⟨k, en, p, h, rfl, hp, hk⟩ := row_entry hc
    rw [(Schedule.trace_of_entryOf hk).2.2.2.2.1, rowsD_getElem? h hp, rowsOf_getElem?,
      Nat.add_sub_cancel_left, cutsAt_eq, List.getElem?_map, ← cutsD_some h]
    cases (cutsD ctl k)[p]? <;> rfl
  · have hn : (sched ctl).entryOf proposer dg c = none := by
      refine Schedule.entryOf_eq_none_iff.2 fun k => ?_
      rw [length_rowsD] at hc
      refine le_trans ?_ (not_lt.1 hc)
      rcases Nat.lt_or_ge k (entriesD ctl).length with hk | hk
      · exact Schedule.start_mono hk
      · have : ∀ m, (entriesD ctl).length ≤ m → (sched ctl).start proposer dg m =
            (sched ctl).start proposer dg (entriesD ctl).length := by
          intro m hm
          induction m, hm using Nat.le_induction with
          | base => rfl
          | succ m hm ih =>
            rw [Schedule.start_succ, cutsAt_eq, cutsD, List.getElem?_eq_none (by omega)]
            simpa using ih
        rw [this (k + 1) (by omega)]
    rw [(Schedule.trace_of_entryOf_none hn).2.2, List.getElem?_eq_none (not_lt.1 hc)]; rfl

/-- **The fields of the run at a cut are the row's.** -/
theorem trace_row {ctl : Bool} {c : Nat} {r : RowD} (hr : (rowsD ctl)[c]? = some r) :
    (tr ctl).node c = r.node ∧ (tr ctl).time c = r.time ∧ (tr ctl).pos c = r.pos ∧
      (tr ctl).post c = r.post.interp ro ∧ (tr ctl).state r.node c = r.pre.interp ro := by
  have hc : c < (rowsD ctl).length := (List.getElem?_eq_some_iff.1 hr).1
  obtain ⟨k, en, p, h, rfl, hp, hk⟩ := row_entry hc
  have he : (sched ctl).entry k = some (en.1, (en.2.1 : Time), en.2.2.interp ro) := by
    rw [sched_entry, h]; rfl
  rw [rowsD_getElem? h hp, rowsOf_getElem?, ← cutsD_some h, List.getElem?_eq_getElem hp,
    Option.map_some, Option.some.injEq] at hr
  subst hr
  obtain ⟨hn, ht, -, hpos, -, hpost⟩ := Schedule.trace_of_entryOf hk
  rw [Nat.add_sub_cancel_left] at hpos hpost
  refine ⟨hn.trans (Schedule.entryNode_of he), ht.trans (Schedule.entryTime_of he), hpos,
    hpost.trans (midState_eq h hp), ?_⟩
  rw [Schedule.state_add _ (by rw [cutsAt_eq, List.length_map]; exact hp.le),
    Schedule.entryNode_of he]
  simp only [↓reduceIte]
  rw [midState_eq h hp.le]

/-- The data of node `y` before cut `c`: the post of its latest row before `c`. -/
def stateD (ctl : Bool) (y : Fin 5) (c : Nat) : X.NodeD :=
  ((rowsD ctl).take c).foldl (fun d r => if r.node = y then r.post else d) (NodeD.init X)

/-- **The states of the run are the rows' data.** -/
theorem trace_state (ctl : Bool) (y : Fin 5) : ∀ c, (tr ctl).state y c = (stateD ctl y c).interp ro
  | 0 => (NodeD.interp_init ro hX).symm
  | c + 1 => by
    rw [Trace.state, trace_state ctl y c]
    unfold stateD
    rw [List.take_add_one, List.foldl_append, trace_label]
    cases hr : (rowsD ctl)[c]? with
    | none => simp
    | some r =>
      obtain ⟨hn, -, -, hpost, -⟩ := trace_row hr
      simp only [hn, Option.map_some, ne_eq, reduceCtorEq, not_false_eq_true, and_true,
        Option.toList_some, List.foldl_cons, List.foldl_nil, hpost]
      split_ifs <;> rfl

/-! ## The laws of the run -/

/-- The phase of an event (`Node.Event.phase`). -/
def phaseD : X.EvD → Nat
  | .restart => 0
  | .tick _ => 1
  | _ => 2

/-- A tick. -/
def isTick : X.EvD → Bool
  | .tick _ => true
  | _ => false

/-- A restart. -/
def isRestart : X.EvD → Bool
  | .restart => true
  | _ => false

/-- The wire data: a block of the table, a well-formed attestation. -/
def wireD : X.EvD → Bool
  | .block r => r = 1 || r = 3
  | .attestation a => decide a.WellFormed
  | _ => true

theorem phase_interp (e : X.EvD) : (e.interp ro).phase = phaseD e := by cases e <;> rfl

theorem isTick_of {e : X.EvD} {x : Nat} (h : e.interp ro = .tick x) : isTick e = true := by
  cases e <;> simp_all [EvD.interp, isTick]

theorem isRestart_iff {e : X.EvD} : e.interp ro = .restart ↔ isRestart e = true := by
  cases e <;> simp [EvD.interp, isRestart]

theorem eq_tick {e : X.EvD} (h : isTick e = true) : e.interp ro = .tick 0 ∨ ∃ x, e = .tick x := by
  cases e <;> simp_all [isTick]

/-- The entry laws of the schedule on data, checked by the kernel. -/
structure EntryLaws (ctl : Bool) : Prop where
  mono : (entriesD ctl).Pairwise fun a b => a.2.1 ≤ b.2.1
  phase : (entriesD ctl).Pairwise fun a b => a.2.1 = b.2.1 → phaseD a.2.2 ≤ phaseD b.2.2
  tick_unique : (entriesD ctl).Pairwise fun a b =>
    ¬ (a.1 = b.1 ∧ a.2.1 = b.2.1 ∧ isTick a.2.2 = true ∧ isTick b.2.2 = true)
  ticks : ∀ y : Fin 5, ∀ t < 36, awakeB ctl y t = true →
    ∃ en ∈ entriesD ctl, en.1 = y ∧ en.2.1 = t ∧ isTick en.2.2 = true
  awake_call : ∀ en ∈ entriesD ctl, awakeB ctl en.1 en.2.1 = true
  restart_of_sleep : allPre (fun acc en => (List.range en.2.1).all fun u =>
    awakeB ctl en.1 u || (acc.any fun en' => en'.1 = en.1 && u ≤ en'.2.1) || isRestart en.2.2)
    [] (entriesD ctl) = true
  restart_at_wake : (honest.all fun y => (List.range 36).all fun v => (List.range v).all fun u =>
    awakeB ctl y u || !awakeB ctl y v || (entriesD ctl).any fun en =>
      en.1 == y && isRestart en.2.2 && decide (u < en.2.1) && decide (en.2.1 ≤ v)) = true
  sleep_of_restart : allPre (fun acc en => !isRestart en.2.2 || (0 < en.2.1 &&
    !awakeB ctl en.1 (en.2.1 - 1) && acc.all fun en' => en'.1 != en.1 || en'.2.1 < en.2.1 - 1))
    [] (entriesD ctl) = true
  wire : ∀ en ∈ entriesD ctl, wireD en.2.2 = true

theorem entryLaws : ∀ ctl, EntryLaws ctl := by
  intro ctl
  exact ⟨by revert ctl; decide +kernel, by revert ctl; decide +kernel,
    by revert ctl; decide +kernel, by revert ctl; decide +kernel, by revert ctl; decide +kernel,
    by revert ctl; decide +kernel, by revert ctl; decide +kernel, by revert ctl; decide +kernel,
    by revert ctl; decide +kernel⟩

/-- The entries with the data of all nodes before them. -/
def tblAux : (Fin 5 → X.NodeD) → List Ent → List (Ent × (Fin 5 → X.NodeD))
  | _, [] => []
  | st, en :: es => (en, st) :: tblAux (stepD st en) es

theorem tblAux_getElem? : ∀ (L : List Ent) (st : Fin 5 → X.NodeD) (k : Nat),
    (tblAux st L)[k]? = L[k]?.map fun en => (en, (L.take k).foldl stepD st)
  | [], _, _ => rfl
  | _ :: _, _, 0 => rfl
  | _ :: L, st, k + 1 => by simp [tblAux, tblAux_getElem? L _ k]

theorem entries_ne : ∀ ctl, ∀ x ∈ tblAux init0 (entriesD ctl),
    (execD (x.2 x.1.1) x.1.1 x.1.2.1 x.1.2.2).2 ≠ [] := by decide +kernel

theorem cutsD_ne {ctl : Bool} {k : Nat} {en : Ent} (h : (entriesD ctl)[k]? = some en) :
    (execD (stD ctl k en.1) en.1 en.2.1 en.2.2).2 ≠ [] := by
  have hm : (en, stD ctl k) ∈ tblAux init0 (entriesD ctl) := by
    apply List.mem_of_getElem?; rw [tblAux_getElem?, h]; rfl
  exact entries_ne ctl _ hm

theorem sched_entry_some {ctl : Bool} {k : Nat} {y : Fin 5} {t : Time} {e : Node.Event N5}
    (h : (sched ctl).entry k = some (y, t, e)) :
    ∃ en, (entriesD ctl)[k]? = some en ∧ en.1 = y ∧ (en.2.1 : Time) = t ∧ en.2.2.interp ro = e := by
  rw [sched_entry, Option.map_eq_some_iff] at h
  obtain ⟨en, h1, h2⟩ := h
  simp only [Prod.mk.injEq] at h2
  exact ⟨en, h1, h2.1, h2.2.1, h2.2.2⟩

theorem sched_entry_of_mem {ctl : Bool} {en : Ent} (h : en ∈ entriesD ctl) :
    ∃ k, (sched ctl).entry k = some (en.1, (en.2.1 : Time), en.2.2.interp ro) ∧
      (entriesD ctl)[k]? = some en := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem h
  exact ⟨k, by rw [sched_entry, List.getElem?_eq_getElem hk]; rfl, List.getElem?_eq_getElem hk⟩

theorem pw_of {α : Type} {R : α → α → Prop} {L : List α} (h : L.Pairwise R) {k k' : Nat} {a b : α}
    (ha : L[k]? = some a) (hb : L[k']? = some b) (hlt : k < k') : R a b := by
  obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.1 ha
  obtain ⟨hk', rfl⟩ := List.getElem?_eq_some_iff.1 hb
  exact List.pairwise_iff_getElem.1 h k k' hk hk' hlt

theorem mem_honest : ∀ y : Fin 5, y ≠ vf → y ∈ honest := by decide

theorem awakeB_le {ctl : Bool} {y : Fin 5} {t : Nat} (h : awakeB ctl y t = true) : t ≤ 35 := by
  simp only [awakeB, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1

theorem blk_proposer {r : Nat} (hr : r ∈ X.roots) : (X.blk r).proposer = vf := by
  obtain ⟨b, hb⟩ := exists_row hr
  simp [Fix.blk, hb, Fix.mkBlk]

/-- **The awake schedule ticks**: an honest node awake at a time ticks there (`RunLaws.ticks`),
in both variants. -/
theorem sched_ticks (ctl : Bool) : ∀ y ∈ H, ∀ t, 0 ≤ t → X.sp.toParams.IsPublic t →
    (sched ctl).awake y t → ∃ k x, (sched ctl).entry k = some (y, t, .tick x) := by
  rintro y - t - - ⟨ht, haw⟩
  obtain ⟨en, hm, rfl, he, hti⟩ := (entryLaws ctl).ticks y t.toNat
    (by have := awakeB_le haw; omega) haw
  obtain ⟨k, hk, -⟩ := sched_entry_of_mem hm
  obtain ⟨x, hx⟩ : ∃ x, en.2.2 = .tick x := by
    revert hti; cases en.2.2 <;> simp [isTick]
  refine ⟨k, x, ?_⟩
  rw [hk, hx, he, Int.toNat_of_nonneg ht]; rfl

/-- **The awake schedule restarts at every wake** (`RunLaws.restart_at_wake`), in both variants:
`c` at `28` after its sleep on `24..27`, and `d` at `24` in the control (never awake in the
rejection run). -/
theorem sched_restart_at_wake (ctl : Bool) : ∀ y ∈ H, ∀ u v : Time, 0 ≤ u → u < v →
    ¬ (sched ctl).awake y u → (sched ctl).awake y v →
    ∃ k t, (sched ctl).entry k = some (y, t, .restart) ∧ u < t ∧ t ≤ v := by
  rintro y hy (u : Int) (v : Int) (hu : (0 : Int) ≤ u) (huv : u < v) hnu
    ⟨(hv : (0 : Int) ≤ v), hvaw⟩
  have hnu' : awakeB ctl y u.toNat = false := by
    by_contra h'; exact hnu ⟨hu, by simpa using h'⟩
  have h := (entryLaws ctl).restart_at_wake
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  have hv35 := awakeB_le hvaw
  rcases h y (mem_honest y hy) v.toNat (by omega) u.toNat (by omega) with (h | h) | h
  · rw [hnu'] at h; cases h
  · rw [hvaw] at h; cases h
  · obtain ⟨en, hm, ⟨⟨rfl, hr⟩, h1⟩, h2⟩ := h
    obtain ⟨k, hk, -⟩ := sched_entry_of_mem hm
    refine ⟨k, en.2.1, ?_, show (u : Int) < en.2.1 by omega, show (en.2.1 : Int) ≤ v by omega⟩
    rw [hk, isRestart_iff.2 hr]

/-- **The awake schedule is within the horizon `35`** (`RunLaws.horizon`), in both variants. -/
theorem sched_horizon (ctl : Bool) : ∀ y ∈ H, ∀ t, (sched ctl).awake y t →
    (∃ k y' t' e, (sched ctl).entry k = some (y', t', e) ∧ t ≤ t') ∨
      ∃ T, (sched ctl).horizon = some T ∧ t ≤ T := by
  rintro y - (t : Int) ⟨ht, haw⟩
  exact Or.inr ⟨35, rfl, show (t : Int) ≤ 35 by have := awakeB_le haw; omega⟩

/-- The three awake laws of the schedule together, in both variants. -/
theorem sched_awake_laws (ctl : Bool) :
    (∀ y ∈ H, ∀ t, 0 ≤ t → X.sp.toParams.IsPublic t → (sched ctl).awake y t →
      ∃ k x, (sched ctl).entry k = some (y, t, .tick x)) ∧
    (∀ y ∈ H, ∀ u v : Time, 0 ≤ u → u < v → ¬ (sched ctl).awake y u → (sched ctl).awake y v →
      ∃ k t, (sched ctl).entry k = some (y, t, .restart) ∧ u < t ∧ t ≤ v) ∧
    (∀ y ∈ H, ∀ t, (sched ctl).awake y t →
      (∃ k y' t' e, (sched ctl).entry k = some (y', t', e) ∧ t ≤ t') ∨
        ∃ T, (sched ctl).horizon = some T ∧ t ≤ T) :=
  ⟨sched_ticks ctl, sched_restart_at_wake ctl, sched_horizon ctl⟩

/-- **The entry laws of the schedule** (`RunLaws`), in both variants. -/
theorem sched_runLaws (ctl : Bool) : (sched ctl).RunLaws proposer dg H where
  ne k y t e he := by
    obtain ⟨en, h, rfl, rfl, rfl⟩ := sched_entry_some he
    rw [stBefore_eq, exec_eq h]
    simpa [resN] using cutsD_ne h
  mono k k' y y' t t' e e' hkk he he' := by
    obtain ⟨en, h, -, rfl, -⟩ := sched_entry_some he
    obtain ⟨en', h', -, rfl, -⟩ := sched_entry_some he'
    rcases Nat.eq_or_lt_of_le hkk with rfl | hlt
    · rw [h] at h'; cases h'; exact le_rfl
    · exact_mod_cast pw_of (entryLaws ctl).mono h h' hlt
  nonneg k y t e he := by
    obtain ⟨en, -, -, rfl, -⟩ := sched_entry_some he; exact Int.natCast_nonneg _
  phase k k' y y' t e e' _ _ hlt he he' := by
    obtain ⟨en, h, -, rfl, rfl⟩ := sched_entry_some he
    obtain ⟨en', h', -, ht, rfl⟩ := sched_entry_some he'
    rw [phase_interp, phase_interp]
    exact pw_of (entryLaws ctl).phase h h' hlt (by exact_mod_cast ht.symm)
  tick_public _ _ _ _ _ _ := one_dvd _
  tick_unique k k' y t x x' _ he he' := by
    obtain ⟨en, h, h1, rfl, h2⟩ := sched_entry_some he
    obtain ⟨en', h', h1', ht, h2'⟩ := sched_entry_some he'
    by_contra hne
    have key : ∀ {a b : Ent} {i j : Nat}, (entriesD ctl)[i]? = some a →
        (entriesD ctl)[j]? = some b → i < j → a.1 = b.1 → a.2.1 = b.2.1 →
        isTick a.2.2 = true → isTick b.2.2 = true → False :=
      fun ha hb hij e1 e2 e3 e4 => pw_of (entryLaws ctl).tick_unique ha hb hij ⟨e1, e2, e3, e4⟩
    have ht' : en.2.1 = en'.2.1 := by exact_mod_cast ht.symm
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact key h h' hlt (h1.trans h1'.symm) ht' (isTick_of h2) (isTick_of h2')
    · exact key h' h hlt (h1'.trans h1.symm) ht'.symm (isTick_of h2') (isTick_of h2)
  ticks := sched_ticks ctl
  awake_call k y t e _ he := by
    obtain ⟨en, h, rfl, rfl, -⟩ := sched_entry_some he
    exact ⟨Int.natCast_nonneg _, by
      rw [Int.toNat_natCast]; exact (entryLaws ctl).awake_call en (List.mem_of_getElem? h)⟩
  restart_of_sleep k y t e (u : Int) _ he hu hut hnu hbefore := by
    obtain ⟨en, h, rfl, rfl, rfl⟩ := sched_entry_some he
    obtain ⟨hk, hen⟩ := List.getElem?_eq_some_iff.1 h
    have hc := allPre_spec (entryLaws ctl).restart_of_sleep k hk
    rw [hen] at hc
    simp only [List.append_nil, List.all_eq_true, List.mem_range, Bool.or_eq_true,
      List.any_eq_true, List.mem_reverse, Bool.and_eq_true, decide_eq_true_eq] at hc
    have hnu' : awakeB ctl en.1 u.toNat = false := by
      by_contra h'; exact hnu ⟨hu, by simpa using h'⟩
    have hu : (0 : Int) ≤ u := hu
    have hut : u < (en.2.1 : Int) := hut
    rcases hc u.toNat (by omega) with (h1 | ⟨en', hm, h1', h2⟩) | h3
    · rw [hnu'] at h1; cases h1
    · obtain ⟨j, hj, hjk, rfl⟩ := mem_take_getElem hm
      have := hbefore j hjk _ _ (by rw [sched_entry, List.getElem?_eq_getElem hj, ← h1']; rfl)
      have : ((entriesD ctl)[j].2.1 : Int) < u := this
      omega
    · exact isRestart_iff.2 h3
  restart_at_wake := sched_restart_at_wake ctl
  sleep_of_restart k y t _ he := by
    obtain ⟨en, h, rfl, rfl, hr⟩ := sched_entry_some he
    obtain ⟨hk, hen⟩ := List.getElem?_eq_some_iff.1 h
    have hc := allPre_spec (entryLaws ctl).sleep_of_restart k hk
    rw [hen, isRestart_iff.1 hr] at hc
    simp only [List.append_nil, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq,
      Bool.not_eq_true', List.all_eq_true, List.mem_reverse, Bool.or_eq_true, bne_iff_ne,
      ne_eq] at hc
    obtain ⟨⟨h0, haw⟩, hall⟩ := hc
    refine ⟨((en.2.1 - 1 : Nat) : Time), Int.natCast_nonneg _,
      show ((en.2.1 - 1 : Nat) : Int) < en.2.1 by omega, ?_, ?_⟩
    · rintro ⟨-, h'⟩; rw [Int.toNat_natCast, haw] at h'; cases h'
    · intro j hj t' e' he'
      obtain ⟨en', h', h1', rfl, -⟩ := sched_entry_some he'
      obtain ⟨hj', rfl⟩ := List.getElem?_eq_some_iff.1 h'
      rcases hall _ (List.mem_take_iff_getElem.2 ⟨j, by simp; omega, rfl⟩) with h1 | h1
      · exact absurd h1' h1
      · exact_mod_cast h1
  horizon := sched_horizon ctl
  finite T := by
    refine (Set.finite_Iio (entriesD ctl).length).subset ?_
    rintro k ⟨y, t, e, he, -⟩
    obtain ⟨en, h, -⟩ := sched_entry_some he
    exact (List.getElem?_eq_some_iff.1 h).1
  wire k y t e _ he := by
    obtain ⟨en, h, -, -, rfl⟩ := sched_entry_some he
    have hw := (entryLaws ctl).wire en (List.mem_of_getElem? h)
    revert hw
    cases en.2.2 with
    | block r =>
      intro hw
      simp only [wireD, Bool.or_eq_true, decide_eq_true_eq] at hw
      refine ⟨dg_blk hw, by simp [blk_fgPayload], ?_⟩
      simp [validPayload, blockVotes, blockSupport, blk_acPayload]
    | attestation a => intro hw; simpa [wireD, EvD.interp, Node.WireOK] using hw
    | _ => intro; trivial
  credential k y t B _ he := by
    obtain ⟨⟨y', t', e⟩, h, -, -, he'⟩ := sched_entry_some he
    have hok := (entries_ok ctl _ (List.mem_of_getElem? h)).2
    cases e with
    | block r => cases he'; exact blk_proposer hok
    | _ => cases he'

/-! ## Unforgeability and `GoldilocksRun` -/

/-- A processed block is a block of the table. -/
def fgBlockOK : CutD X → Bool
  | .fgBlock b _ => b == 1 || b == 3
  | _ => true

/-- What a cut signs. -/
def signD : CutD X → Option (FG.Att X.sp.n)
  | .fgAttest _ s => s
  | _ => none

/-- What a cut emits. -/
def emitsD : CutD X → List X.V
  | .ac _ _ ems => ems.map EmD.vote
  | _ => []

/-- An honest attestation processed at a row was signed at an earlier row. -/
def attOK (acc : List RowD) (r : RowD) : Bool :=
  match r.cut with
  | .fgAtt a => a.val == vf || acc.any fun r' => r'.node == a.val && decide (signD r'.cut = some a)
  | _ => true

/-- An honest vote received at a row was emitted at an earlier row. -/
def msgOK (acc : List RowD) (r : RowD) : Bool :=
  match r.cut with
  | .ac (.message v) _ _ =>
    v.val == vf || acc.any fun r' => r'.node == v.val && (emitsD r'.cut).contains v
  | _ => true

/-- The row laws of the run, checked by the kernel. -/
structure RowLaws (ctl : Bool) : Prop where
  blocks : (rowsD ctl).all (fun r => fgBlockOK r.cut) = true
  atts : allPre attOK [] (rowsD ctl) = true
  msgs : allPre msgOK [] (rowsD ctl) = true

theorem rowLaws : ∀ ctl, RowLaws ctl := by
  intro ctl
  exact ⟨by revert ctl; decide +kernel, by revert ctl; decide +kernel,
    by revert ctl; decide +kernel⟩

theorem label_row {ctl : Bool} {i : Nat} {ℓ : Cut N5} (h : (tr ctl).label i = some ℓ) :
    ∃ r, (rowsD ctl)[i]? = some r ∧ r.cut.interp ro = ℓ := by
  rw [trace_label, Option.map_eq_some_iff] at h; exact h

theorem callAt_row {ctl : Bool} {i : Nat} {r : RowD} (hr : (rowsD ctl)[i]? = some r) :
    (tr ctl).CallAt r.node i (r.cut.interp ro) :=
  ⟨(trace_row hr).1, by rw [trace_label, hr]; rfl⟩

theorem cut_fgBlock {c : CutD X} {B : X.Blk} {acc : Bool}
    (h : c.interp ro = .fg (.block B acc)) : ∃ b, c = .fgBlock b acc ∧ B = X.blk b := by
  cases c <;> simp_all [CutD.interp]

theorem cut_fgAtt {c : CutD X} {a : FG.Att X.sp.n} (h : c.interp ro = .fg (.attestation a)) :
    c = .fgAtt a := by
  cases c <;> simp_all [CutD.interp]

theorem cut_ac {c : CutD X} {ℓ : ACLabel N5} (h : c.interp ro = .ac ℓ) :
    ∃ call M ems, c = .ac call M ems ∧ ℓ = ⟨call.interp ro, X.frameOf M, ems.map EmD.interp⟩ := by
  cases c <;> simp_all [CutD.interp]

theorem call_message {call : CallD X} {m : X.V} (h : call.interp ro = .message m) :
    call = .message m := by
  cases call <;> simp_all [CallD.interp]

theorem signD_some {c : CutD X} {a : FG.Att X.sp.n} (h : signD c = some a) :
    ∃ b, c = .fgAttest b (some a) := by
  cases c <;> simp_all [signD]

theorem emitsD_mem {c : CutD X} {v : X.V} (h : v ∈ emitsD c) :
    ∃ call M ems, c = .ac call M ems ∧ ∃ e ∈ ems, e.vote = v := by
  cases c <;> simp_all [emitsD]

theorem fgBlock_ok {ctl : Bool} {i : Nat} {y : Fin 5} {B : X.Blk}
    (h : (tr ctl).BlockCallAt y i B) : ∃ b, (b = 1 ∨ b = 3) ∧ B = X.blk b := by
  obtain ⟨acc, -, hl⟩ := h
  obtain ⟨r, hr, hc⟩ := label_row hl
  obtain ⟨b, hb, rfl⟩ := cut_fgBlock hc
  have := List.all_eq_true.1 (rowLaws ctl).blocks r (List.mem_of_getElem? hr)
  rw [hb] at this
  simp only [fgBlockOK, Bool.or_eq_true, beq_iff_eq] at this
  exact ⟨b, this, rfl⟩

/-- **The run is a Goldilocks run**, in both variants. -/
theorem run_goldilocksRun (ctl : Bool) : GoldilocksRun proposer dg H (tr ctl) := by
  refine trace_goldilocksRun (sched_runLaws ctl) ?_ ?_ ?_ dg_genesis ?_
  · intro y _ i B hB hp
    obtain ⟨b, hb, rfl⟩ := fgBlock_ok hB
    exact absurd (blk_proposer (by rcases hb with rfl | rfl <;> decide)) hp
  · rintro y - i a (⟨-, hl⟩ | ⟨B, hB, ha⟩) hH
    · obtain ⟨r, hr, hc⟩ := label_row hl
      have hcut := cut_fgAtt hc
      have hk := allPre_spec (rowLaws ctl).atts i (List.getElem?_eq_some_iff.1 hr).1
      rw [List.getElem?_eq_some_iff.1 hr |>.2, attOK, hcut] at hk
      simp only [List.append_nil, Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.mem_reverse,
        Bool.and_eq_true, decide_eq_true_eq] at hk
      rcases hk with hf | ⟨r', hm, hn, hs⟩
      · exact absurd hf hH
      · obtain ⟨j, hj, hji, rfl⟩ := mem_take_getElem hm
        obtain ⟨b, hb⟩ := signD_some hs
        have hc' := callAt_row (List.getElem?_eq_getElem hj)
        rw [hb, hn] at hc'
        exact ⟨j, hji, _, hc'⟩
    · obtain ⟨b, -, rfl⟩ := fgBlock_ok hB
      simp [blk_fgPayload] at ha
  · rintro y - i m ⟨ℓ, ⟨-, hl⟩, hcall⟩ hH
    obtain ⟨r, hr, hc⟩ := label_row hl
    obtain ⟨call, M, ems, hcut, rfl⟩ := cut_ac hc
    have hm := call_message hcall
    have hk := allPre_spec (rowLaws ctl).msgs i (List.getElem?_eq_some_iff.1 hr).1
    rw [List.getElem?_eq_some_iff.1 hr |>.2, msgOK, hcut, hm] at hk
    simp only [List.append_nil, Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.mem_reverse,
      Bool.and_eq_true, List.contains_iff_mem] at hk
    rcases hk with hf | ⟨r', hmem, hn, he⟩
    · exact absurd hf hH
    · obtain ⟨j, hj, hji, rfl⟩ := mem_take_getElem hmem
      obtain ⟨call', M', ems', hcut', e, he', rfl⟩ := emitsD_mem he
      have hc' := callAt_row (List.getElem?_eq_getElem hj)
      rw [hcut', hn] at hc'
      exact ⟨j, hji, _, hc', e.interp, List.mem_map_of_mem he', rfl⟩
  · intro y _ i B hB v hv
    obtain ⟨b, -, rfl⟩ := fgBlock_ok hB
    simp [blockVotes, blk_acPayload] at hv

end Five

end Consensus.Goldilocks.Test.HalfCommittee

end

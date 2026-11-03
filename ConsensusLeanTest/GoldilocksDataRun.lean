module
public import ConsensusLeanTest.GoldilocksHalfCommitteeCutLaw
public import ConsensusLeanTest.GoldilocksScheduleLocalRun
@[expose] public section

/-! # A run on data of the mirror: states, rows, trace, and `GoldilocksRun`

The generic core of the concrete runs on the computable mirror (`GoldilocksHalfCommitteeNode`),
for any fixture `X` and any schedule on data `D : Data X` (entries, awake function, horizon,
honest nodes). The schedule `sched ro D` (`GoldilocksScheduleRun`) runs the entries. A run
`R : Run X` bundles the replay order, the proposer, the digest and `D` with the side conditions
`Wf` (table check, entries of honest nodes and of the fragment, the table's proposer in every
slot, the digest of the table); the states of `R.tr` are the mirror's (`stBefore_eq`, from
`exec_interp` with `frag_init` as the base of `Frag`), and its cuts are the rows `rowsD R.D`
(`trace_label`, `trace_row`, `trace_state`). With the entry laws `EntryLaws R.D` and the row laws
`RowLaws R.D`, both checked by the kernel on the data, the trace is a Goldilocks run
(`run_goldilocksRun`, by `trace_goldilocksRun`). -/

namespace Consensus.Goldilocks.Test.HalfCommittee.DataRun

open SA Fix ScheduleRun

variable {X : Fix}

/-- An entry of a schedule on data: node, time, event. -/
abbrev Ent (X : Fix) : Type := Fin X.sp.n × Nat × X.EvD

/-- A schedule on data: the entries, the awake function on natural times, the horizon, and the
honest nodes in a list. -/
structure Data (X : Fix) where
  /-- The entries, in order. -/
  entries : List (Ent X)
  /-- Whether a node is awake at a time. -/
  awake : Fin X.sp.n → Nat → Bool
  /-- The horizon. -/
  horizon : Nat
  /-- The honest nodes. -/
  honest : List (Fin X.sp.n)

variable (ro : ReplayOrder X.sp (List (FG.Att X.sp.n))) (D : Data X)

/-- The schedule of a run on data. -/
noncomputable def sched : Schedule (X.AC ro) where
  entry k := (D.entries[k]?).map fun en => (en.1, (en.2.1 : Time), en.2.2.interp ro)
  prefix_closed k h := by
    simp only [Option.map_eq_none_iff, List.getElem?_eq_none_iff] at h ⊢; omega
  awake y t := 0 ≤ t ∧ D.awake y t.toNat = true
  horizon := some D.horizon

/-- The side conditions of a run on data: the table check, entries of nodes other than the
table's proposer with events of the fragment, the table's proposer in every slot, and the digest
of genesis and of the table's blocks. -/
structure Wf (proposer : Nat → Fin X.sp.n)
    (dg : Digest (List (FG.Att X.sp.n)) (Payload X.sp.n)) : Prop where
  /-- The table check. -/
  table : X.OK
  /-- The entries. -/
  ents : ∀ en ∈ D.entries, en.1 ≠ X.f ∧ EvD.OK X en.2.2
  /-- The proposer. -/
  prop : ∀ s, proposer s = X.f
  /-- The genesis root. -/
  genesis : (X.sp.toParams.genesisBlock (X.AC ro).genesisPayload).RootOk dg
  /-- The roots of the table. -/
  blk : ∀ r ∈ X.roots, (X.blk r).RootOk dg

/-- **A run on data**: the replay order, the proposer, the digest and the schedule on data, with
the side conditions. -/
structure Run (X : Fix) where
  /-- The replay order of the restarts. -/
  ro : ReplayOrder X.sp (List (FG.Att X.sp.n))
  /-- The proposer of each slot. -/
  proposer : Nat → Fin X.sp.n
  /-- The digest. -/
  dg : Digest (List (FG.Att X.sp.n)) (Payload X.sp.n)
  /-- The schedule on data. -/
  D : Data X
  /-- The side conditions. -/
  wf : Wf ro D proposer dg

/-- The run trace. -/
noncomputable abbrev Run.tr (R : Run X) : RunTrace (X.AC R.ro) :=
  (sched R.ro R.D).trace R.proposer R.dg

variable {ro D}

theorem sched_entry (k : Nat) : (sched ro D).entry k =
    (D.entries[k]?).map fun en => (en.1, (en.2.1 : Time), en.2.2.interp ro) := rfl

/-! ## The states on data -/

/-- One entry on the data of all nodes. -/
def stepD (st : Fin X.sp.n → X.NodeD) (en : Ent X) : Fin X.sp.n → X.NodeD :=
  Function.update st en.1 (execD (st en.1) en.1 en.2.1 en.2.2).1

/-- The initial data of all nodes. -/
def init0 (X : Fix) : Fin X.sp.n → X.NodeD := fun _ => NodeD.init X

variable (D) in
/-- The data of all nodes before entry `k`. -/
def stD (k : Nat) : Fin X.sp.n → X.NodeD := (D.entries.take k).foldl stepD (init0 X)

theorem stD_succ {k : Nat} {en : Ent X} (h : D.entries[k]? = some en) :
    stD D (k + 1) = stepD (stD D k) en := by
  rw [stD, List.take_add_one, h, Option.toList_some, List.foldl_append]; rfl

theorem stD_of_le {k : Nat} (h : D.entries[k]? = none) : stD D (k + 1) = stD D k := by
  rw [stD, List.take_add_one, h, Option.toList_none, List.append_nil]; rfl

theorem stepD_apply (st : Fin X.sp.n → X.NodeD) (en : Ent X) (y : Fin X.sp.n) :
    stepD st en y = if en.1 = y then (execD (st en.1) en.1 en.2.1 en.2.2).1 else st y := by
  unfold stepD
  by_cases h : en.1 = y
  · subst h; simp
  · simp [h, Function.update_of_ne (Ne.symm h)]

/-- `Frag` along the schedule, from `frag_init`. -/
theorem frag_stD (hE : ∀ en ∈ D.entries, EvD.OK X en.2.2) : ∀ k y, X.Frag (stD D k y)
  | 0, _ => frag_init X
  | k + 1, y => by
    cases h : D.entries[k]? with
    | none => rw [stD_of_le h]; exact frag_stD hE k y
    | some en =>
      rw [stD_succ h, stepD_apply]
      split_ifs with hy
      · exact frag_execD (frag_stD hE k _) _ _ (hE en (List.mem_of_getElem? h))
      · exact frag_stD hE k y

theorem exec_eq (R : Run X) {k : Nat} {en : Ent X} (h : R.D.entries[k]? = some en) :
    Node.exec R.proposer R.dg en.1 ((stD R.D k en.1).interp R.ro) en.2.1 (en.2.2.interp R.ro) =
      resN R.ro (execD (stD R.D k en.1) en.1 en.2.1 en.2.2) := by
  have hok := R.wf.ents en (List.mem_of_getElem? h)
  exact exec_interp R.ro R.wf.table R.proposer R.dg en.1 (fun s e => hok.1 (e ▸ R.wf.prop s))
    (frag_stD (fun en h => (R.wf.ents en h).2) k _) (Int.natCast_nonneg _) hok.2

/-- **The states of the schedule are the mirror's.** -/
theorem stBefore_eq (R : Run X) (y : Fin X.sp.n) :
    ∀ k, (sched R.ro R.D).stBefore R.proposer R.dg y k = (stD R.D k y).interp R.ro
  | 0 => (NodeD.interp_init R.ro R.wf.table).symm
  | k + 1 => by
    rw [Schedule.stBefore_succ, stBefore_eq R y k]
    cases h : R.D.entries[k]? with
    | none => rw [Schedule.stepAt_none (by rw [sched_entry, h]; rfl), stD_of_le h]
    | some en =>
      rw [Schedule.stepAt_some (by rw [sched_entry, h]; rfl), stD_succ h, stepD_apply]
      split_ifs with hy
      · subst hy; rw [exec_eq R h]; rfl
      · rfl

variable (D) in
/-- The cuts of entry `k` on data. -/
def cutsD (k : Nat) : List (CutD X) :=
  match D.entries[k]? with
  | some en => (execD (stD D k en.1) en.1 en.2.1 en.2.2).2
  | none => []

theorem cutsD_some {k : Nat} {en : Ent X} (h : D.entries[k]? = some en) :
    cutsD D k = (execD (stD D k en.1) en.1 en.2.1 en.2.2).2 := by simp [cutsD, h]

theorem cutsAt_eq (R : Run X) (k : Nat) :
    (sched R.ro R.D).cutsAt R.proposer R.dg k = (cutsD R.D k).map (CutD.interp R.ro) := by
  cases h : R.D.entries[k]? with
  | none => rw [Schedule.cutsAt_none (by rw [sched_entry, h]; rfl)]; simp [cutsD, h]
  | some en =>
    rw [Schedule.cutsAt_some (by rw [sched_entry, h]; rfl), stBefore_eq R, exec_eq R h,
      cutsD_some h]
    rfl

/-- The data of the node of entry `k` after its first `p` cuts. -/
theorem midState_eq (R : Run X) {k : Nat} {en : Ent X} (h : R.D.entries[k]? = some en)
    {p : Nat} (hp : p ≤ (cutsD R.D k).length) :
    (sched R.ro R.D).midState R.proposer R.dg k p = ((stD R.D k en.1 :: postsD (stD R.D k en.1) en.1
      en.2.1 en.2.2).getD p (stD R.D k en.1)).interp R.ro := by
  have he : (sched R.ro R.D).entry k = some (en.1, (en.2.1 : Time), en.2.2.interp R.ro) := by
    rw [sched_entry, h]; rfl
  have hok := R.wf.ents en (List.mem_of_getElem? h)
  have hc := chainOK_postsD R.ro R.wf.table en.1 (frag_stD (fun en h => (R.wf.ents en h).2) k en.1)
    (Int.natCast_nonneg en.2.1) hok.2
  rw [cutsD_some h] at hp
  rw [Schedule.midState, Schedule.entryNode_of he, Schedule.entryTime_of he, cutsAt_eq R,
    cutsD_some h, stBefore_eq R, foldl_take_chainOK hc p (by rw [List.length_map]; exact hp)
      ((stD R.D k en.1).interp R.ro), ← List.map_cons, getD_map]

/-! ## The cuts on data -/

/-- A cut of the run on data: entry, position, node, time, the cut, and the node's data before
and after it. -/
structure RowD (X : Fix) where
  /-- The entry. -/
  ent : Nat
  /-- The position in the entry's group. -/
  pos : Nat
  /-- The node. -/
  node : Fin X.sp.n
  /-- The time. -/
  time : Nat
  /-- The cut. -/
  cut : CutD X
  /-- The node's data before the cut. -/
  pre : X.NodeD
  /-- The node's data after the cut. -/
  post : X.NodeD

/-- The cuts of entry `k` with the data `st` of the nodes before it. -/
def rowsOf (k : Nat) (st : Fin X.sp.n → X.NodeD) (en : Ent X) : List (RowD X) :=
  let d := st en.1
  let ms := d :: postsD d en.1 en.2.1 en.2.2
  (execD d en.1 en.2.1 en.2.2).2.zipIdx.map fun cp =>
    ⟨k, cp.2, en.1, en.2.1, cp.1, ms.getD cp.2 d, ms.getD (cp.2 + 1) d⟩

/-- The cuts of the entries from `k` on. -/
def rowsAux : Nat → (Fin X.sp.n → X.NodeD) → List (Ent X) → List (RowD X)
  | _, _, [] => []
  | k, st, en :: es => rowsOf k st en ++ rowsAux (k + 1) (stepD st en) es

variable (D) in
/-- **The cuts of the run on data**, in order. -/
def rowsD : List (RowD X) := rowsAux 0 (init0 X) D.entries

theorem rowsAux_append (L₁ L₂ : List (Ent X)) :
    ∀ k st, rowsAux k st (L₁ ++ L₂) =
      rowsAux k st L₁ ++ rowsAux (k + L₁.length) (L₁.foldl stepD st) L₂ := by
  induction L₁ with
  | nil => intro k st; rfl
  | cons en L ih =>
    intro k st
    simp only [List.cons_append, rowsAux, ih, List.append_assoc, List.length_cons,
      List.foldl_cons]
    rw [Nat.add_assoc, Nat.add_comm 1]

theorem length_rowsOf (k : Nat) (st : Fin X.sp.n → X.NodeD) (en : Ent X) :
    (rowsOf k st en).length = (execD (st en.1) en.1 en.2.1 en.2.2).2.length := by
  simp [rowsOf]

theorem start_eq (R : Run X) : ∀ k,
    (sched R.ro R.D).start R.proposer R.dg k = (rowsAux 0 (init0 X) (R.D.entries.take k)).length
  | 0 => rfl
  | k + 1 => by
    rw [Schedule.start_succ, start_eq R k, cutsAt_eq R, List.length_map, List.take_add_one,
      rowsAux_append, List.length_append]
    cases h : R.D.entries[k]? with
    | none => simp [cutsD, h, rowsAux]
    | some en =>
      simp only [Option.toList_some, rowsAux, List.append_nil, length_rowsOf, cutsD_some h]; rfl

theorem length_rowsD (R : Run X) :
    (rowsD R.D).length = (sched R.ro R.D).start R.proposer R.dg R.D.entries.length := by
  rw [start_eq R, List.take_length]; rfl

theorem rowsD_getElem? (R : Run X) {k : Nat} {en : Ent X}
    (h : R.D.entries[k]? = some en) {p : Nat} (hp : p < (cutsD R.D k).length) :
    (rowsD R.D)[(sched R.ro R.D).start R.proposer R.dg k + p]? = (rowsOf k (stD R.D k) en)[p]? := by
  have hk : k < R.D.entries.length := (List.getElem?_eq_some_iff.1 h).1
  have hL : R.D.entries = R.D.entries.take k ++ en :: R.D.entries.drop (k + 1) := by
    conv_lhs => rw [← List.take_append_drop k R.D.entries]
    rw [List.drop_eq_getElem_cons hk, (List.getElem?_eq_some_iff.1 h).2]
  have e : rowsD R.D = rowsAux 0 (init0 X) (R.D.entries.take k) ++
      (rowsOf k (stD R.D k) en ++ rowsAux (k + 1) (stepD (stD R.D k) en)
        (R.D.entries.drop (k + 1))) := by
    rw [rowsD]; conv_lhs => rw [hL]
    rw [rowsAux_append, List.length_take, Nat.min_eq_left hk.le, Nat.zero_add]; rfl
  rw [e, start_eq R, List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left, List.getElem?_append_left]
  rw [length_rowsOf]; rwa [cutsD_some h] at hp

theorem rowsOf_getElem? (k : Nat) (st : Fin X.sp.n → X.NodeD) (en : Ent X) (p : Nat) :
    (rowsOf k st en)[p]? = ((execD (st en.1) en.1 en.2.1 en.2.2).2[p]?).map fun c =>
      ⟨k, p, en.1, en.2.1, c, (st en.1 :: postsD (st en.1) en.1 en.2.1 en.2.2).getD p (st en.1),
        (st en.1 :: postsD (st en.1) en.1 en.2.1 en.2.2).getD (p + 1) (st en.1)⟩ := by
  simp only [rowsOf, List.getElem?_map, List.getElem?_zipIdx]
  cases (execD (st en.1) en.1 en.2.1 en.2.2).2[p]? <;> simp

/-- A cut index of the rows is a position of an entry's group. -/
theorem row_entry (R : Run X) {c : Nat} (hc : c < (rowsD R.D).length) :
    ∃ k en p, R.D.entries[k]? = some en ∧ c = (sched R.ro R.D).start R.proposer R.dg k + p ∧
      p < (cutsD R.D k).length ∧ (sched R.ro R.D).entryOf R.proposer R.dg c = some k := by
  cases hk : (sched R.ro R.D).entryOf R.proposer R.dg c with
  | none =>
    have := Schedule.entryOf_eq_none_iff.1 hk R.D.entries.length
    rw [Schedule.start_succ, cutsAt_eq R, cutsD, List.getElem?_eq_none le_rfl] at this
    rw [length_rowsD R] at hc
    simp at this; omega
  | some k =>
    obtain ⟨h1, h2⟩ := Schedule.entryOf_eq_some_iff.1 hk
    rw [Schedule.start_succ, cutsAt_eq R, List.length_map] at h2
    cases h : R.D.entries[k]? with
    | none => simp [cutsD, h] at h2; omega
    | some en =>
      exact ⟨k, en, c - (sched R.ro R.D).start R.proposer R.dg k, h, by omega, by omega, rfl⟩

/-- **The labels of the run are the rows' cuts.** -/
theorem trace_label (R : Run X) (c : Nat) :
    R.tr.label c = ((rowsD R.D)[c]?).map fun r => r.cut.interp R.ro := by
  by_cases hc : c < (rowsD R.D).length
  · obtain ⟨k, en, p, h, rfl, hp, hk⟩ := row_entry R hc
    rw [(Schedule.trace_of_entryOf hk).2.2.2.2.1, rowsD_getElem? R h hp, rowsOf_getElem?,
      Nat.add_sub_cancel_left, cutsAt_eq R, List.getElem?_map, ← cutsD_some h]
    cases (cutsD R.D k)[p]? <;> rfl
  · have hn : (sched R.ro R.D).entryOf R.proposer R.dg c = none := by
      refine Schedule.entryOf_eq_none_iff.2 fun k => ?_
      rw [length_rowsD R] at hc
      refine le_trans ?_ (not_lt.1 hc)
      rcases Nat.lt_or_ge k R.D.entries.length with hk | hk
      · exact Schedule.start_mono hk
      · have : ∀ m, R.D.entries.length ≤ m → (sched R.ro R.D).start R.proposer R.dg m =
            (sched R.ro R.D).start R.proposer R.dg R.D.entries.length := by
          intro m hm
          induction m, hm using Nat.le_induction with
          | base => rfl
          | succ m hm ih =>
            rw [Schedule.start_succ, cutsAt_eq R, cutsD, List.getElem?_eq_none (by omega)]
            simpa using ih
        rw [this (k + 1) (by omega)]
    rw [(Schedule.trace_of_entryOf_none hn).2.2, List.getElem?_eq_none (not_lt.1 hc)]; rfl

/-- **The fields of the run at a cut are the row's.** -/
theorem trace_row (R : Run X) {c : Nat} {r : RowD X} (hr : (rowsD R.D)[c]? = some r) :
    R.tr.node c = r.node ∧ R.tr.time c = r.time ∧
      R.tr.pos c = r.pos ∧ R.tr.post c = r.post.interp R.ro ∧
      R.tr.state r.node c = r.pre.interp R.ro := by
  have hc : c < (rowsD R.D).length := (List.getElem?_eq_some_iff.1 hr).1
  obtain ⟨k, en, p, h, rfl, hp, hk⟩ := row_entry R hc
  have he : (sched R.ro R.D).entry k = some (en.1, (en.2.1 : Time), en.2.2.interp R.ro) := by
    rw [sched_entry, h]; rfl
  rw [rowsD_getElem? R h hp, rowsOf_getElem?, ← cutsD_some h, List.getElem?_eq_getElem hp,
    Option.map_some, Option.some.injEq] at hr
  subst hr
  obtain ⟨hn, ht, -, hpos, -, hpost⟩ := Schedule.trace_of_entryOf hk
  rw [Nat.add_sub_cancel_left] at hpos hpost
  refine ⟨hn.trans (Schedule.entryNode_of he), ht.trans (Schedule.entryTime_of he), hpos,
    hpost.trans (midState_eq R h hp), ?_⟩
  rw [Schedule.state_add _ (by rw [cutsAt_eq R, List.length_map]; exact hp.le),
    Schedule.entryNode_of he]
  simp only [↓reduceIte]
  rw [midState_eq R h hp.le]

variable (D) in
/-- The data of node `y` before cut `c`: the post of its latest row before `c`. -/
def stateD (y : Fin X.sp.n) (c : Nat) : X.NodeD :=
  ((rowsD D).take c).foldl (fun d r => if r.node = y then r.post else d) (NodeD.init X)

/-- **The states of the run are the rows' data.** -/
theorem trace_state (R : Run X) (y : Fin X.sp.n) :
    ∀ c, R.tr.state y c = (stateD R.D y c).interp R.ro
  | 0 => (NodeD.interp_init R.ro R.wf.table).symm
  | c + 1 => by
    rw [Trace.state, trace_state R y c]
    unfold stateD
    rw [List.take_add_one, List.foldl_append, trace_label R]
    cases hr : (rowsD R.D)[c]? with
    | none => simp
    | some r =>
      obtain ⟨hn, -, -, hpost, -⟩ := trace_row R hr
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
  | .block r => decide (r ∈ X.roots)
  | .attestation a => decide a.WellFormed
  | _ => true

theorem phase_interp (e : X.EvD) : (e.interp ro).phase = phaseD e := by cases e <;> rfl

theorem isTick_of {e : X.EvD} {x : Nat} (h : e.interp ro = .tick x) : isTick e = true := by
  cases e <;> simp_all [EvD.interp, isTick]

theorem isRestart_iff {e : X.EvD} : e.interp ro = .restart ↔ isRestart e = true := by
  cases e <;> simp [EvD.interp, isRestart]

theorem eq_tick {e : X.EvD} (h : isTick e = true) : e.interp ro = .tick 0 ∨ ∃ x, e = .tick x := by
  cases e <;> simp_all [isTick]

/-- The order of the entries: by time, then phase, and the ticks of one time by node. -/
def ordD (a b : Ent X) : Prop :=
  a.2.1 < b.2.1 ∨ (a.2.1 = b.2.1 ∧ (phaseD a.2.2 < phaseD b.2.2 ∨
    (phaseD a.2.2 = phaseD b.2.2 ∧ (phaseD a.2.2 = 1 → a.1 < b.1))))

instance : DecidableRel (ordD (X := X)) := fun a b => by unfold ordD; infer_instance

instance : Trans (ordD (X := X)) ordD ordD where
  trans {a b c} hab hbc := by
    unfold ordD at *
    have := Fin.lt_def (a := a.1) (b := b.1)
    have := Fin.lt_def (a := b.1) (b := c.1)
    have := Fin.lt_def (a := a.1) (b := c.1)
    omega

/-- A drop of a future-slot block (no cut). -/
def dropD (en : Ent X) : Bool :=
  match en.2.2 with
  | .block r => decide (slotT en.2.1 < X.slotR r)
  | _ => false

variable (D) in
/-- The entry laws of a schedule on data, checked by the kernel. -/
structure EntryLaws : Prop where
  /-- The entries are ordered. -/
  order : D.entries.IsChain ordD
  /-- No entry drops its block. -/
  drop : ∀ en ∈ D.entries, dropD en = false
  /-- A node awake at a time ticks there. -/
  ticks : ∀ y : Fin X.sp.n, ∀ t < D.horizon + 1, D.awake y t = true →
    ∃ en ∈ D.entries, en.1 = y ∧ en.2.1 = t ∧ isTick en.2.2 = true
  /-- Entries only while awake. -/
  awake_call : ∀ en ∈ D.entries, D.awake en.1 en.2.1 = true
  /-- A node asleep since its latest entry restarts. -/
  restart_of_sleep : allPre (fun acc en => (List.range en.2.1).all fun u =>
    D.awake en.1 u || (acc.any fun en' => en'.1 = en.1 && u ≤ en'.2.1) || isRestart en.2.2)
    [] D.entries = true
  /-- An honest node restarts at every wake. -/
  restart_at_wake : (D.honest.all fun y => (List.range (D.horizon + 1)).all fun v =>
    (List.range v).all fun u => D.awake y u || !D.awake y v || D.entries.any fun en =>
      en.1 == y && isRestart en.2.2 && decide (u < en.2.1) && decide (en.2.1 ≤ v)) = true
  /-- A restart follows a sleep, with no entry of the node during it. -/
  sleep_of_restart : allPre (fun acc en => !isRestart en.2.2 || (0 < en.2.1 &&
    !D.awake en.1 (en.2.1 - 1) && acc.all fun en' => en'.1 != en.1 || en'.2.1 < en.2.1 - 1))
    [] D.entries = true
  /-- The wire data. -/
  wire : ∀ en ∈ D.entries, wireD en.2.2 = true

theorem entries_pw (hL : EntryLaws D) : D.entries.Pairwise ordD :=
  List.isChain_iff_pairwise.1 hL.order

theorem isTick_phase {e : X.EvD} (h : isTick e = true) : phaseD e = 1 := by
  cases e <;> simp_all [isTick, phaseD]

theorem cutsD_ne (hL : EntryLaws D) {k : Nat} {en : Ent X} (h : D.entries[k]? = some en) :
    (execD (stD D k en.1) en.1 en.2.1 en.2.2).2 ≠ [] := by
  refine execD_ne_nil _ _ _ fun r hr => ?_
  have hd := hL.drop en (List.mem_of_getElem? h)
  simp only [dropD, hr, decide_eq_false_iff_not, not_lt] at hd
  exact hd

theorem sched_entry_some {k : Nat} {y : Fin X.sp.n} {t : Time} {e : Node.Event (X.AC ro)}
    (h : (sched ro D).entry k = some (y, t, e)) :
    ∃ en, D.entries[k]? = some en ∧ en.1 = y ∧ (en.2.1 : Time) = t ∧ en.2.2.interp ro = e := by
  rw [sched_entry, Option.map_eq_some_iff] at h
  obtain ⟨en, h1, h2⟩ := h
  simp only [Prod.mk.injEq] at h2
  exact ⟨en, h1, h2.1, h2.2.1, h2.2.2⟩

theorem sched_entry_of_mem {en : Ent X} (h : en ∈ D.entries) :
    ∃ k, (sched ro D).entry k = some (en.1, (en.2.1 : Time), en.2.2.interp ro) ∧
      D.entries[k]? = some en := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem h
  exact ⟨k, by rw [sched_entry, List.getElem?_eq_getElem hk]; rfl, List.getElem?_eq_getElem hk⟩

theorem pw_of {α : Type} {R : α → α → Prop} {L : List α} (h : L.Pairwise R) {k k' : Nat} {a b : α}
    (ha : L[k]? = some a) (hb : L[k']? = some b) (hlt : k < k') : R a b := by
  obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.1 ha
  obtain ⟨hk', rfl⟩ := List.getElem?_eq_some_iff.1 hb
  exact List.pairwise_iff_getElem.1 h k k' hk hk' hlt

theorem blk_proposer {r : Nat} (hr : r ∈ X.roots) : (X.blk r).proposer = X.f := by
  obtain ⟨b, hb⟩ := exists_row hr
  simp [Fix.blk, hb, Fix.mkBlk]

variable {H : Set (Fin X.sp.n)}

/-- **The awake schedule ticks** (`RunLaws.ticks`). -/
theorem sched_ticks (hL : EntryLaws D) (hle : ∀ y t, D.awake y t = true → t ≤ D.horizon) :
    ∀ y ∈ H, ∀ t, 0 ≤ t → X.sp.toParams.IsPublic t →
      (sched ro D).awake y t → ∃ k x, (sched ro D).entry k = some (y, t, .tick x) := by
  rintro y - t - - ⟨ht, haw⟩
  obtain ⟨en, hm, rfl, he, hti⟩ := hL.ticks y t.toNat
    (by have := hle _ _ haw; omega) haw
  obtain ⟨k, hk, -⟩ := sched_entry_of_mem (ro := ro) hm
  obtain ⟨x, hx⟩ : ∃ x, en.2.2 = .tick x := by
    revert hti; cases en.2.2 <;> simp [isTick]
  refine ⟨k, x, ?_⟩
  rw [hk, hx, he, Int.toNat_of_nonneg ht]; rfl

/-- **The awake schedule restarts at every wake** (`RunLaws.restart_at_wake`). -/
theorem sched_restart_at_wake (hL : EntryLaws D)
    (hle : ∀ y t, D.awake y t = true → t ≤ D.horizon) (hH : ∀ y ∈ H, y ∈ D.honest) :
    ∀ y ∈ H, ∀ u v : Time, 0 ≤ u → u < v →
      ¬ (sched ro D).awake y u → (sched ro D).awake y v →
      ∃ k t, (sched ro D).entry k = some (y, t, .restart) ∧ u < t ∧ t ≤ v := by
  rintro y hy (u : Int) (v : Int) (hu : (0 : Int) ≤ u) (huv : u < v) hnu
    ⟨(hv : (0 : Int) ≤ v), hvaw⟩
  have hnu' : D.awake y u.toNat = false := by
    by_contra h'; exact hnu ⟨hu, by simpa using h'⟩
  have h := hL.restart_at_wake
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  have hvT := hle _ _ hvaw
  rcases h y (hH y hy) v.toNat (by omega) u.toNat (by omega) with (h | h) | h
  · rw [hnu'] at h; cases h
  · rw [hvaw] at h; cases h
  · obtain ⟨en, hm, ⟨⟨rfl, hr⟩, h1⟩, h2⟩ := h
    obtain ⟨k, hk, -⟩ := sched_entry_of_mem (ro := ro) hm
    refine ⟨k, en.2.1, ?_, show (u : Int) < en.2.1 by omega, show (en.2.1 : Int) ≤ v by omega⟩
    rw [hk, isRestart_iff.2 hr]

/-- **The awake schedule is within the horizon** (`RunLaws.horizon`). -/
theorem sched_horizon (hle : ∀ y t, D.awake y t = true → t ≤ D.horizon) :
    ∀ y ∈ H, ∀ t, (sched ro D).awake y t →
      (∃ k y' t' e, (sched ro D).entry k = some (y', t', e) ∧ t ≤ t') ∨
        ∃ T, (sched ro D).horizon = some T ∧ t ≤ T := by
  rintro y - (t : Int) ⟨ht, haw⟩
  exact Or.inr ⟨D.horizon, rfl, show (t : Int) ≤ D.horizon by have := hle _ _ haw; omega⟩

/-- **The entry laws of the schedule** (`RunLaws`). -/
theorem sched_runLaws (R : Run X) (hL : EntryLaws R.D)
    (hle : ∀ y t, R.D.awake y t = true → t ≤ R.D.horizon) (hH : ∀ y ∈ H, y ∈ R.D.honest) :
    (sched R.ro R.D).RunLaws R.proposer R.dg H where
  ne k y t e he := by
    obtain ⟨en, h, rfl, rfl, rfl⟩ := sched_entry_some he
    rw [stBefore_eq R, exec_eq R h]
    simpa [resN] using cutsD_ne hL h
  mono k k' y y' t t' e e' hkk he he' := by
    obtain ⟨en, h, -, rfl, -⟩ := sched_entry_some he
    obtain ⟨en', h', -, rfl, -⟩ := sched_entry_some he'
    rcases Nat.eq_or_lt_of_le hkk with rfl | hlt
    · rw [h] at h'; cases h'; exact le_rfl
    · have := pw_of (entries_pw hL) h h' hlt
      unfold ordD at this
      exact_mod_cast (show en.2.1 ≤ en'.2.1 by omega)
  nonneg k y t e he := by
    obtain ⟨en, -, -, rfl, -⟩ := sched_entry_some he; exact Int.natCast_nonneg _
  phase k k' y y' t e e' _ _ hlt he he' := by
    obtain ⟨en, h, -, rfl, rfl⟩ := sched_entry_some he
    obtain ⟨en', h', -, ht, rfl⟩ := sched_entry_some he'
    rw [phase_interp, phase_interp]
    have := pw_of (entries_pw hL) h h' hlt
    have ht' : en.2.1 = en'.2.1 := by exact_mod_cast ht.symm
    unfold ordD at this
    omega
  tick_public _ _ _ _ _ _ := by change X.sp.Δ ∣ _; rw [X.hΔ]; exact one_dvd _
  tick_unique k k' y t x x' _ he he' := by
    obtain ⟨en, h, h1, rfl, h2⟩ := sched_entry_some he
    obtain ⟨en', h', h1', ht, h2'⟩ := sched_entry_some he'
    by_contra hne
    have key : ∀ {a b : Ent X} {i j : Nat}, R.D.entries[i]? = some a →
        R.D.entries[j]? = some b → i < j → a.1 = b.1 → a.2.1 = b.2.1 →
        isTick a.2.2 = true → isTick b.2.2 = true → False :=
      fun {a b} {_ _} ha hb hij e1 e2 e3 e4 => by
        have hab := pw_of (entries_pw hL) ha hb hij
        have hp := isTick_phase e3
        have hq := isTick_phase e4
        unfold ordD at hab
        rw [e1] at hab
        rcases hab with h | ⟨-, h | ⟨-, h⟩⟩
        · omega
        · omega
        · exact absurd (h hp) (lt_irrefl _)
    have ht' : en.2.1 = en'.2.1 := by exact_mod_cast ht.symm
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact key h h' hlt (h1.trans h1'.symm) ht' (isTick_of h2) (isTick_of h2')
    · exact key h' h hlt (h1'.trans h1.symm) ht'.symm (isTick_of h2') (isTick_of h2)
  ticks := sched_ticks hL hle
  awake_call k y t e _ he := by
    obtain ⟨en, h, rfl, rfl, -⟩ := sched_entry_some he
    exact ⟨Int.natCast_nonneg _, by
      rw [Int.toNat_natCast]; exact hL.awake_call en (List.mem_of_getElem? h)⟩
  restart_of_sleep k y t e (u : Int) _ he hu hut hnu hbefore := by
    obtain ⟨en, h, rfl, rfl, rfl⟩ := sched_entry_some he
    obtain ⟨hk, hen⟩ := List.getElem?_eq_some_iff.1 h
    have hc := allPre_spec hL.restart_of_sleep k hk
    rw [hen] at hc
    simp only [List.append_nil, List.all_eq_true, List.mem_range, Bool.or_eq_true,
      List.any_eq_true, List.mem_reverse, Bool.and_eq_true, decide_eq_true_eq] at hc
    have hnu' : R.D.awake en.1 u.toNat = false := by
      by_contra h'; exact hnu ⟨hu, by simpa using h'⟩
    have hu : (0 : Int) ≤ u := hu
    have hut : u < (en.2.1 : Int) := hut
    rcases hc u.toNat (by omega) with (h1 | ⟨en', hm, h1', h2⟩) | h3
    · rw [hnu'] at h1; cases h1
    · obtain ⟨j, hj, hjk, rfl⟩ := mem_take_getElem hm
      have := hbefore j hjk _ _ (by rw [sched_entry, List.getElem?_eq_getElem hj, ← h1']; rfl)
      have : (R.D.entries[j].2.1 : Int) < u := this
      omega
    · exact isRestart_iff.2 h3
  restart_at_wake := sched_restart_at_wake hL hle hH
  sleep_of_restart k y t _ he := by
    obtain ⟨en, h, rfl, rfl, hr⟩ := sched_entry_some he
    obtain ⟨hk, hen⟩ := List.getElem?_eq_some_iff.1 h
    have hc := allPre_spec hL.sleep_of_restart k hk
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
  horizon := sched_horizon hle
  finite T := by
    refine (Set.finite_Iio R.D.entries.length).subset ?_
    rintro k ⟨y, t, e, he, -⟩
    obtain ⟨en, h, -⟩ := sched_entry_some he
    exact (List.getElem?_eq_some_iff.1 h).1
  wire k y t e _ he := by
    obtain ⟨en, h, -, -, rfl⟩ := sched_entry_some he
    have hw := hL.wire en (List.mem_of_getElem? h)
    revert hw
    cases en.2.2 with
    | block r =>
      intro hw
      simp only [wireD, decide_eq_true_eq] at hw
      refine ⟨R.wf.blk r hw, by simp [blk_fgPayload], ?_⟩
      simp [validPayload, blockVotes, blockSupport, blk_acPayload]
    | attestation a => intro hw; simpa [wireD, EvD.interp, Node.WireOK] using hw
    | _ => intro; trivial
  credential k y t B _ he := by
    obtain ⟨⟨y', t', e⟩, h, -, -, he'⟩ := sched_entry_some he
    have hok := (R.wf.ents _ (List.mem_of_getElem? h)).2
    cases e with
    | block r => cases he'; rw [R.wf.prop]; exact blk_proposer hok
    | _ => cases he'

/-! ## Unforgeability and `GoldilocksRun` -/

/-- A processed block is a block of the table. -/
def fgBlockOK : CutD X → Bool
  | .fgBlock b _ => decide (b ∈ X.roots)
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
def attOK (acc : List (RowD X)) (r : RowD X) : Bool :=
  match r.cut with
  | .fgAtt a => a.val == X.f || acc.any fun r' => r'.node == a.val && decide (signD r'.cut = some a)
  | _ => true

/-- An honest vote received at a row was emitted at an earlier row. -/
def msgOK (acc : List (RowD X)) (r : RowD X) : Bool :=
  match r.cut with
  | .ac (.message v) _ _ =>
    v.val == X.f || acc.any fun r' => r'.node == v.val && (emitsD r'.cut).contains v
  | _ => true

variable (D) in
/-- The row laws of a run on data, checked by the kernel. -/
structure RowLaws : Prop where
  /-- Every processed block is a table block. -/
  blocks : (rowsD D).all (fun r => fgBlockOK r.cut) = true
  /-- Attestation provenance. -/
  atts : allPre attOK [] (rowsD D) = true
  /-- Vote provenance. -/
  msgs : allPre msgOK [] (rowsD D) = true

theorem label_row (R : Run X) {i : Nat} {ℓ : Cut (X.AC R.ro)}
    (h : R.tr.label i = some ℓ) :
    ∃ r, (rowsD R.D)[i]? = some r ∧ r.cut.interp R.ro = ℓ := by
  rw [trace_label R, Option.map_eq_some_iff] at h; exact h

theorem callAt_row (R : Run X) {i : Nat} {r : RowD X} (hr : (rowsD R.D)[i]? = some r) :
    R.tr.CallAt r.node i (r.cut.interp R.ro) :=
  ⟨(trace_row R hr).1, by rw [trace_label R, hr]; rfl⟩

theorem cut_fgBlock {c : CutD X} {B : X.Blk} {acc : Bool}
    (h : c.interp ro = .fg (.block B acc)) : ∃ b, c = .fgBlock b acc ∧ B = X.blk b := by
  cases c <;> simp_all [CutD.interp]

theorem cut_fgAtt {c : CutD X} {a : FG.Att X.sp.n} (h : c.interp ro = .fg (.attestation a)) :
    c = .fgAtt a := by
  cases c <;> simp_all [CutD.interp]

theorem cut_ac {c : CutD X} {ℓ : ACLabel (X.AC ro)} (h : c.interp ro = .ac ℓ) :
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

theorem fgBlock_ok (R : Run X) (hR : RowLaws R.D) {i : Nat} {y : Fin X.sp.n} {B : X.Blk}
    (h : R.tr.BlockCallAt y i B) : ∃ b ∈ X.roots, B = X.blk b := by
  obtain ⟨acc, -, hl⟩ := h
  obtain ⟨r, hr, hc⟩ := label_row R hl
  obtain ⟨b, hb, rfl⟩ := cut_fgBlock hc
  have := List.all_eq_true.1 hR.blocks r (List.mem_of_getElem? hr)
  rw [hb] at this
  simp only [fgBlockOK, decide_eq_true_eq] at this
  exact ⟨b, this, rfl⟩

/-- **The run is a Goldilocks run.** -/
theorem run_goldilocksRun (R : Run X) (hL : EntryLaws R.D) (hR : RowLaws R.D)
    (hle : ∀ y t, R.D.awake y t = true → t ≤ R.D.horizon) (hH : ∀ y ∈ H, y ∈ R.D.honest)
    (hf : X.f ∉ H) : GoldilocksRun R.proposer R.dg H R.tr := by
  refine trace_goldilocksRun (sched_runLaws R hL hle hH) ?_ ?_ ?_ R.wf.genesis ?_
  · intro y _ i B hB hp
    obtain ⟨b, hb, rfl⟩ := fgBlock_ok R hR hB
    exact absurd (blk_proposer hb ▸ hp) hf
  · rintro y - i a (⟨-, hl⟩ | ⟨B, hB, ha⟩) hH
    · obtain ⟨r, hr, hc⟩ := label_row R hl
      have hcut := cut_fgAtt hc
      have hk := allPre_spec hR.atts i (List.getElem?_eq_some_iff.1 hr).1
      rw [List.getElem?_eq_some_iff.1 hr |>.2, attOK, hcut] at hk
      simp only [List.append_nil, Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.mem_reverse,
        Bool.and_eq_true, decide_eq_true_eq] at hk
      rcases hk with hf' | ⟨r', hm, hn, hs⟩
      · exact absurd (hf' ▸ hH) hf
      · obtain ⟨j, hj, hji, rfl⟩ := mem_take_getElem hm
        obtain ⟨b, hb⟩ := signD_some hs
        have hc' := callAt_row R (List.getElem?_eq_getElem hj)
        rw [hb, hn] at hc'
        exact ⟨j, hji, _, hc'⟩
    · obtain ⟨b, -, rfl⟩ := fgBlock_ok R hR hB
      simp [blk_fgPayload] at ha
  · rintro y - i m ⟨ℓ, ⟨-, hl⟩, hcall⟩ hH
    obtain ⟨r, hr, hc⟩ := label_row R hl
    obtain ⟨call, M, ems, hcut, rfl⟩ := cut_ac hc
    have hm := call_message hcall
    have hk := allPre_spec hR.msgs i (List.getElem?_eq_some_iff.1 hr).1
    rw [List.getElem?_eq_some_iff.1 hr |>.2, msgOK, hcut, hm] at hk
    simp only [List.append_nil, Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.mem_reverse,
      Bool.and_eq_true, List.contains_iff_mem] at hk
    rcases hk with hf' | ⟨r', hmem, hn, he⟩
    · exact absurd (hf' ▸ hH) hf
    · obtain ⟨j, hj, hji, rfl⟩ := mem_take_getElem hmem
      obtain ⟨call', M', ems', hcut', e, he', rfl⟩ := emitsD_mem he
      have hc' := callAt_row R (List.getElem?_eq_getElem hj)
      rw [hcut', hn] at hc'
      exact ⟨j, hji, _, hc', e.interp, List.mem_map_of_mem he', rfl⟩
  · intro y _ i B hB v hv
    obtain ⟨b, -, rfl⟩ := fgBlock_ok R hR hB
    simp [blockVotes, blk_acPayload] at hv

end Consensus.Goldilocks.Test.HalfCommittee.DataRun

end

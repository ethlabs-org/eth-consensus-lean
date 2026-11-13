module
public import ConsensusLeanTest.Goldilocks.Runs.Data.Sync
public import ConsensusLeanTest.Goldilocks.Runs.Data.Five
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Restart
@[expose] public section

/-! # The halfCommittee run with five validators

The rejection and control use the shared run-on-data machinery. The table holds `B` (root `1`,
slot `6`) and `V` (root `3`, slot `1`), both children of genesis (root `2`). The faulty node
proposes every slot. Nodes `a, b` stay awake; `c` sleeps on `24..27` and restarts at `28`;
in the control only, `d` wakes and restarts at `24`.

Deliveries at `28` reprocess `B, a6, b6, f6` at the other awake nodes as well as `c`, so the
new acceptance and pool entries of `c` satisfy `Sync[24, 33]`. The fixture's schedule and wire
data are unchanged between the shared and specialized run constructions. Entry checks are
bundled, and the row laws and synchrony checks share one kernel evaluation per variant.

Kind: common run of the premise-necessity rejection and its positive control. -/

namespace Consensus.Goldilocks.Test.HalfCommittee.Five

open SA Fix ScheduleRun

/-- The block `B`: root `1`, slot `6`, child of genesis. -/
def rowB : Row := ⟨1, 2, 6, 0, [2]⟩

/-- The block `V`: root `3`, slot `1`, child of genesis. -/
def rowV : Row := ⟨3, 2, 1, 0, [2]⟩

/-- The fixture: `sp5`, the faulty proposer `f`, the table `{B, V}`. -/
abbrev X : Fix := ⟨sp5, rfl, vf, [rowB, rowV]⟩

theorem hX : X.OK := by decide

/-- The replay order of the restarts. -/
noncomputable abbrev ro : ReplayOrder X.sp (List (FG.Att X.sp.n)) := ReplayOrder.choice X.sp

/-- The node. -/
noncomputable abbrev N5 : NodeAC X.sp.toParams := X.AC ro

/-- The proposer of every slot: `f`. -/
def proposer : Nat → Fin X.sp.n := fun _ => vf

/-- The contents of genesis, `B` and `V`. -/
def cG : Content := (none, 0, 0, [], ([], []))
@[inherit_doc cG] def cB : Content := (some 2, 6, 0, [], ([], []))
@[inherit_doc cG] def cV : Content := (some 2, 1, 0, [], ([], []))

/-- The digest of the three fixture contents; unused contents map to `0`. -/
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

/-- Restarts, ticks of awake honest nodes, then deliveries, in phase order. -/
def segsD (ctl : Bool) (t : Nat) : List (Fin 5 × X.EvD) :=
  (honest.filter fun y => t != 0 && awakeB ctl y t && !awakeB ctl y (t - 1)).map
      (fun y => (y, .restart)) ++
    (honest.filter fun y => awakeB ctl y t).map (fun y => (y, .tick 0)) ++ dels ctl t

/-- An entry of the schedule on data. -/
abbrev Ent := DataRun.Ent X

/-- The entries at times `0, …, 35`, flattened. -/
def entriesD (ctl : Bool) : List Ent :=
  (List.range 36).flatMap fun t => (segsD ctl t).map fun ye => (ye.1, t, ye.2)

/-- The schedule's data. -/
def dataD (ctl : Bool) : DataRun.Data X := ⟨entriesD ctl, awakeB ctl, 35, honest⟩

/-- The entry laws and side conditions, sharing one evaluation of the entries. -/
private abbrev EntryChecks (ctl : Bool) : Prop :=
    (entriesD ctl).IsChain DataRun.ordD ∧
    (∀ en ∈ entriesD ctl, DataRun.dropD en = false) ∧
    (∀ y : Fin 5, ∀ t < 36, awakeB ctl y t = true →
      ∃ en ∈ entriesD ctl, en.1 = y ∧ en.2.1 = t ∧ DataRun.isTick en.2.2 = true) ∧
    (∀ en ∈ entriesD ctl, awakeB ctl en.1 en.2.1 = true) ∧
    allPre (fun acc en => (List.range en.2.1).all fun u =>
      awakeB ctl en.1 u || (acc.any fun en' => en'.1 = en.1 && u ≤ en'.2.1) ||
        DataRun.isRestart en.2.2) [] (entriesD ctl) = true ∧
    (honest.all fun y => (List.range 36).all fun v => (List.range v).all fun u =>
      awakeB ctl y u || !awakeB ctl y v || (entriesD ctl).any fun en =>
        en.1 == y && DataRun.isRestart en.2.2 && decide (u < en.2.1) && decide (en.2.1 ≤ v)) =
      true ∧
    allPre (fun acc en => !DataRun.isRestart en.2.2 || (0 < en.2.1 &&
      !awakeB ctl en.1 (en.2.1 - 1) && acc.all fun en' => en'.1 != en.1 || en'.2.1 < en.2.1 - 1))
      [] (entriesD ctl) = true ∧
    (∀ en ∈ entriesD ctl, DataRun.wireD en.2.2 = true) ∧
    ∀ en ∈ entriesD ctl, en.1 ≠ vf ∧ EvD.OK X en.2.2

private theorem entryChecks_false : EntryChecks false := by decide +kernel
private theorem entryChecks_true : EntryChecks true := by decide +kernel

private theorem entryChecks (ctl : Bool) : EntryChecks ctl := by
  cases ctl
  exacts [entryChecks_false, entryChecks_true]

theorem entriesValid : ∀ ctl, ∀ en ∈ entriesD ctl, en.1 ≠ vf ∧ EvD.OK X en.2.2 :=
  fun ctl => (entryChecks ctl).2.2.2.2.2.2.2.2

/-- The run on data, with its side conditions. -/
noncomputable def runD (ctl : Bool) : DataRun.Run X :=
  ⟨ro, proposer, dg, dataD ctl, ⟨hX, entriesValid ctl, fun _ => rfl, dg_genesis,
    fun _ hr => dg_blk (by simpa [Fix.roots, X, rowB, rowV] using hr)⟩⟩

/-- The schedule of the run. -/
noncomputable def sched (ctl : Bool) : Schedule N5 := DataRun.sched ro (dataD ctl)

/-- The run trace. -/
noncomputable abbrev tr (ctl : Bool) : RunTrace N5 := (sched ctl).trace proposer dg

/-- A cut of the run on data. -/
abbrev DataRow : Type := DataRun.RowD X

/-- The cuts of the run on data, in order. -/
abbrev dataRows (ctl : Bool) : List DataRow := DataRun.rowsD (dataD ctl)

/-- The data of node `y` before cut `c`. -/
abbrev stateD (ctl : Bool) (y : Fin 5) (c : Nat) : X.NodeD := DataRun.stateD (dataD ctl) y c

/-! ## The laws of the run -/

private theorem entryLaws : ∀ ctl, DataRun.EntryLaws (dataD ctl) := fun ctl =>
  have h := entryChecks ctl
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1⟩

theorem awakeB_le {ctl : Bool} {y : Fin 5} {t : Nat} (h : awakeB ctl y t = true) : t ≤ 35 := by
  simp only [awakeB, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1

/-- Row laws and synchrony of one variant, evaluated together. -/
private abbrev RowChecks (ctl : Bool) : Prop :=
  (dataRows ctl).all (fun r => DataRun.fgBlockOK r.cut) = true ∧
    allPre DataRun.attOK [] (dataRows ctl) = true ∧ allPre DataRun.msgOK [] (dataRows ctl) = true ∧
    DataRun.syncD (dataD ctl) 24 33 = true ∧ DataRun.blockPosD (dataD ctl) = true

private theorem rowChecks_false : RowChecks false := by decide +kernel
private theorem rowChecks_true : RowChecks true := by decide +kernel

private theorem rowChecks (ctl : Bool) : RowChecks ctl := by
  cases ctl
  exacts [rowChecks_false, rowChecks_true]

theorem dataRowLaws : ∀ ctl, DataRun.RowLaws (dataD ctl) := by
  intro ctl
  exact ⟨(rowChecks ctl).1, (rowChecks ctl).2.1, (rowChecks ctl).2.2.1⟩

/-- The run is a Goldilocks run, in both variants. -/
theorem run_goldilocksRun (ctl : Bool) : GoldilocksRun proposer dg H (tr ctl) :=
  DataRun.run_goldilocksRun (runD ctl) (entryLaws ctl) (dataRowLaws ctl) rfl (fun _ _ => awakeB_le)
    mem_honest fun h => h rfl

private theorem syncD_true : ∀ ctl, DataRun.syncD (dataD ctl) 24 33 = true ∧
    DataRun.blockPosD (dataD ctl) = true := by
  exact fun ctl => (rowChecks ctl).2.2.2

/-- `Sync[24, 33]`, in both variants. -/
theorem run_sync (ctl : Bool) : (tr ctl).SyncRun H 1 24 33 :=
  DataRun.run_sync (runD ctl) mem_honest (syncD_true ctl).1 (syncD_true ctl).2

end Consensus.Goldilocks.Test.HalfCommittee.Five

end

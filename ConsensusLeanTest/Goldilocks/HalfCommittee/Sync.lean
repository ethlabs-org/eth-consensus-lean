module
public import ConsensusLeanTest.Goldilocks.HalfCommittee.Run
@[expose] public section

/-! # The halfCommittee run with five validators: `Sync[24, 33]`

`Sync[t_6, t_8 + Δ] = Sync[24, 33]` (`SyncRun`, with `Δ_F = 1`) for both variants of the run of
`Goldilocks/HalfCommittee/Run` (`run_sync`), by enumeration: for every cut in the window, every
object the cut sends or forwards (an AC vote: an emission, or a vote its pool did not hold
before and holds after; a block it accepts; an attestation it signs or newly pools) and every
honest node `y`, the kernel scans `y`'s cuts in order (`syncD`): the first one that processes
the object at a time in `[τ, deadline)` comes before every call of `y` at or after its deadline
`max(τ, w_y) + 1` (`w_y` its latest wake, `lastWake`: `trace_lastWake`). The lower bound `τ` is
what forces the reprocessing at `28`: `c`'s new pool entries `a6, b6, f6` and its acceptance of
`B` at `28` are sends at `28`, so `a` and `b` (and `d`) must process them at `28` again, which
the schedule delivers. A cut that processes a block is always the first of a delivery, so no
honest node proposes (`OwnBlockAt` never holds).

Kind: a premise of the (r) rejection and of the (control). -/

namespace Consensus.Goldilocks.Test.HalfCommittee.Five

open SA Fix ScheduleRun

/-! ## Wakes and deadlines -/

/-- An `ac_restart` cut. -/
def isRestartCut : CutD X → Bool
  | .ac .restart _ _ => true
  | _ => false

/-- The latest wake of `y` after the row `r`. -/
def wkD (y : Fin 5) (w : Option Nat) (r : RowD) : Option Nat :=
  if r.node = y ∧ isRestartCut r.cut = true then some r.time else w

/-- The latest wake of `y` at or before cut `k`, on data. -/
def lwD (ctl : Bool) (y : Fin 5) (k : Nat) : Option Nat :=
  ((rowsD ctl).take (k + 1)).foldl (wkD y) none

/-- The deadline `max(τ, w) + 1` without the `+ 1`. -/
def dlN (w : Option Nat) (τ : Nat) : Nat :=
  match w with
  | none => τ
  | some w => max τ w

theorem restartAt_iff {ctl : Bool} {y : Fin 5} {k : Nat} :
    (tr ctl).RestartAt y k ↔ ∃ r, (rowsD ctl)[k]? = some r ∧ r.node = y ∧ isRestartCut r.cut := by
  constructor
  · rintro ⟨ℓ, ⟨hn, hl⟩, hc⟩
    obtain ⟨r, hr, hcut⟩ := label_row hl
    obtain ⟨call, M, ems, hcr, rfl⟩ := cut_ac hcut
    refine ⟨r, hr, (trace_row hr).1 ▸ hn, ?_⟩
    rw [hcr]
    cases call <;> simp_all [CallD.interp, isRestartCut]
  · rintro ⟨r, hr, rfl, hres⟩
    have hc := callAt_row hr
    cases hcut : r.cut with
    | ac call M ems =>
      cases call <;> simp only [hcut, isRestartCut, Bool.false_eq_true] at hres
      rw [hcut] at hc; exact ⟨_, hc, rfl⟩
    | _ => simp [hcut, isRestartCut] at hres

theorem foldl_take_succ {α β : Type} (f : β → α → β) (b : β) (L : List α) (k : Nat) :
    (L.take (k + 1)).foldl f b =
      (L[k]?).elim ((L.take k).foldl f b) (f ((L.take k).foldl f b)) := by
  rw [List.take_add_one, List.foldl_append]; cases L[k]? <;> rfl

/-- A wake on the extended line. -/
def wbOf : Option Nat → WithBot Time
  | none => ⊥
  | some w => ((w : Time) : WithBot Time)

open Classical in
theorem wk_step {ctl : Bool} {y : Fin 5} (k : Nat) (w : Option Nat) :
    wbOf (((rowsD ctl)[k]?).elim w (wkD y w)) =
      if (tr ctl).RestartAt y k then (((tr ctl).time k : Time) : WithBot Time) else wbOf w := by
  cases hr : (rowsD ctl)[k]? with
  | none =>
    have : ¬ (tr ctl).RestartAt y k := by
      rw [restartAt_iff]; rintro ⟨r, h, -⟩; rw [hr] at h; cases h
    simp [this]
  | some r =>
    have hiff : (tr ctl).RestartAt y k ↔ r.node = y ∧ isRestartCut r.cut = true := by
      rw [restartAt_iff]; simp [hr]
    simp only [Option.elim_some, wkD]
    by_cases hc : r.node = y ∧ isRestartCut r.cut = true
    · simp only [hc, hiff.2 hc, and_self, ↓reduceIte, wbOf, (trace_row hr).2.1]
    · simp [hc, mt hiff.1 hc]

/-- **The latest wakes of the run are the rows'.** -/
theorem trace_lastWake (ctl : Bool) (y : Fin 5) : ∀ k, (tr ctl).lastWake y k = wbOf (lwD ctl y k)
  | 0 => by
    rw [RunTrace.lastWake, lwD, foldl_take_succ, wk_step]; rfl
  | k + 1 => by
    rw [RunTrace.lastWake, lwD, foldl_take_succ, wk_step, ← lwD, trace_lastWake ctl y k]

theorem trace_deadline (ctl : Bool) (y : Fin 5) (k τ : Nat) (d : Time) :
    (tr ctl).deadline y k τ d = (dlN (lwD ctl y k) τ : Int) + d := by
  rw [RunTrace.deadline, trace_lastWake]
  cases lwD ctl y k with
  | none => rfl
  | some w => simp [wbOf, dlN]; rfl

/-! ## The sends and their deliveries on data -/

/-- A row processes the vote `m` (receives it, or emits it). -/
def procMsgB (r : RowD) (m : X.V) : Bool :=
  (match r.cut with
    | .ac (.message v) _ _ => decide (v = m)
    | _ => false) || (emitsD r.cut).contains m

/-- An `ac_restart` call. -/
def isRestartCall : CallD X → Bool
  | .restart => true
  | _ => false

/-- A row sends or forwards the vote `m` (`SendOrAdmitAt`). -/
def sendMsgB (r : RowD) (m : X.V) : Bool :=
  match r.cut with
  | .ac call _ ems => (ems.map EmD.vote).contains m || (!isRestartCall call &&
      !(r.pre.ac.pool m.slot).contains m && (r.post.ac.pool m.slot).contains m)
  | _ => false

/-- The votes a row may send or forward. -/
def msgCands (r : RowD) : List X.V := emitsD r.cut ++ r.post.ac.adm.map Prod.fst

/-- The block a row accepts. -/
def acceptD : CutD X → Option Nat
  | .fgBlock b true => some b
  | _ => none

/-- The root of the block a row processes. -/
def blockD : CutD X → Option Nat
  | .fgBlock b _ => some b
  | _ => none

/-- An FG cut. -/
def isFG : CutD X → Bool
  | .ac _ _ _ => false
  | _ => true

/-- The attestation an `fg_on_attestation` cut processes. -/
def attD : CutD X → Option (FG.Att X.sp.n)
  | .fgAtt a => some a
  | _ => none

/-- A row signs or forwards the attestation `a` (`SendOrAdmitAttAt`). -/
def sendAttB (r : RowD) (a : FG.Att X.sp.n) : Bool :=
  decide (signD r.cut = some a) ||
    (isFG r.cut && !r.pre.fg.atts.contains a && r.post.fg.atts.contains a)

/-- The attestations a row may sign or forward. -/
def attCands (r : RowD) : List (FG.Att X.sp.n) := (signD r.cut).toList ++ r.post.fg.atts

/-- A call of `y` at or after the deadline of an object of time `τ`. -/
def oblD (y : Fin 5) (τ : Nat) (w : Option Nat) (r : RowD) : Bool :=
  r.node == y && decide (dlN w τ + 1 ≤ r.time)

/-- A processing of `y` in `[τ, deadline)` (with `lo`) or before the deadline (without). -/
def inWin (y : Fin 5) (τ : Nat) (lo : Bool) (w : Option Nat) (r : RowD) : Bool :=
  r.node == y && (!lo || decide (τ ≤ r.time)) && decide (r.time < dlN w τ + 1)

/-- The scan of `y`'s cuts for an object of time `τ` processed where `p` holds. -/
def svcD (ctl : Bool) (y : Fin 5) (τ : Nat) (lo : Bool) (p : RowD → Bool) : Bool :=
  scanOK (wkD y) (fun w r => inWin y τ lo w r && p r) (oblD y τ) (rowsD ctl) none

/-- **The `Sync[24, 33]` check**: every send in the window is served for every honest node. -/
def syncD (ctl : Bool) : Bool :=
  (rowsD ctl).all fun r => !(24 ≤ r.time && r.time ≤ 33) || (
    ((msgCands r).all fun m => !sendMsgB r m ||
      honest.all fun y => svcD ctl y r.time true (procMsgB · m)) &&
    ((acceptD r.cut).toList.all fun b => honest.all fun y =>
      svcD ctl y r.time true (fun r' => blockD r'.cut == some b) &&
        svcD ctl y r.time false (fun r' => acceptD r'.cut == some b)) &&
    ((attCands r).all fun a => !sendAttB r a ||
      honest.all fun y => svcD ctl y r.time true (fun r' => attD r'.cut == some a)))

/-- Every block cut is the first cut of its group. -/
def blockPosD (ctl : Bool) : Bool := (rowsD ctl).all fun r => (blockD r.cut).isNone || r.pos == 0

theorem syncD_true : ∀ ctl, syncD ctl = true ∧ blockPosD ctl = true := by decide +kernel

/-! ## From the checks to `Sync` -/

theorem blockD_some {c : CutD X} {b : Nat} (h : blockD c = some b) : ∃ acc, c = .fgBlock b acc := by
  cases c <;> simp_all [blockD]

theorem acceptD_some {c : CutD X} {b : Nat} (h : acceptD c = some b) : c = .fgBlock b true := by
  cases c with
  | fgBlock b' acc => cases acc <;> simp_all [acceptD]
  | _ => simp [acceptD] at h

theorem attD_some {c : CutD X} {a : FG.Att X.sp.n} (h : attD c = some a) : c = .fgAtt a := by
  cases c <;> simp_all [attD]

theorem procMsgB_true {r : RowD} {m : X.V} (h : procMsgB r m = true) :
    (∃ M ems, r.cut = .ac (.message m) M ems) ∨ m ∈ emitsD r.cut := by
  unfold procMsgB at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · left
    revert h
    cases r.cut with
    | ac call M ems => cases call <;> simp
    | _ => simp
  · exact Or.inr (List.contains_iff_mem.1 h)

theorem isCall_row {ctl : Bool} {y : Fin 5} {j : Nat} (h : (tr ctl).IsCall y j) :
    ∃ r, (rowsD ctl)[j]? = some r ∧ r.node = y := by
  obtain ⟨c, hn, hl⟩ := h
  obtain ⟨r, hr, -⟩ := label_row hl
  exact ⟨r, hr, (trace_row hr).1 ▸ hn⟩

/-- A successful scan serves every call at or after the deadline. -/
theorem svc_spec {ctl : Bool} {y : Fin 5} {τ : Nat} {lo : Bool} {p : RowD → Bool}
    (h : svcD ctl y τ lo p = true) {j : Nat} (hj : (tr ctl).IsCall y j)
    (hd : (tr ctl).deadline y j τ 1 ≤ (tr ctl).time j) :
    ∃ k ≤ j, ∃ r, (rowsD ctl)[k]? = some r ∧ r.node = y ∧ (lo → τ ≤ r.time) ∧
      (tr ctl).time k < (tr ctl).deadline y k τ 1 ∧ p r = true := by
  obtain ⟨rj, hrj, hny⟩ := isCall_row hj
  have hlt := (List.getElem?_eq_some_iff.1 hrj).1
  have hq : oblD y τ (((rowsD ctl).take (j + 1)).foldl (wkD y) none) (rowsD ctl)[j] = true := by
    rw [(List.getElem?_eq_some_iff.1 hrj).2]
    rw [trace_deadline, (trace_row hrj).2.1] at hd
    simp only [oblD, hny, beq_self_eq_true, Bool.true_and, decide_eq_true_eq]
    exact_mod_cast hd
  obtain ⟨i, hij, hi, hp⟩ := scanOK_spec h j hlt hq
  simp only [inWin, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_eq] at hp
  obtain ⟨⟨⟨hn, hlo⟩, htime⟩, hpr⟩ := hp
  refine ⟨i, hij, _, List.getElem?_eq_getElem hi, hn, fun hl => ?_, ?_, hpr⟩
  · rcases hlo with h0 | h0
    · rw [hl] at h0; cases h0
    · exact h0
  · rw [trace_deadline, (trace_row (List.getElem?_eq_getElem hi)).2.1]
    exact_mod_cast htime

theorem syncD_row {ctl : Bool} {i : Nat} {r : RowD} (hr : (rowsD ctl)[i]? = some r)
    (hW : 24 ≤ (tr ctl).time i ∧ (tr ctl).time i ≤ 33) :
    ((msgCands r).all fun m => !sendMsgB r m ||
      honest.all fun y => svcD ctl y r.time true (procMsgB · m)) = true ∧
    ((acceptD r.cut).toList.all fun b => honest.all fun y =>
      svcD ctl y r.time true (fun r' => blockD r'.cut == some b) &&
        svcD ctl y r.time false (fun r' => acceptD r'.cut == some b)) = true ∧
    ((attCands r).all fun a => !sendAttB r a ||
      honest.all fun y => svcD ctl y r.time true (fun r' => attD r'.cut == some a)) = true := by
  have h := List.all_eq_true.1 (syncD_true ctl).1 r (List.mem_of_getElem? hr)
  rw [(trace_row hr).2.1] at hW
  obtain ⟨(hW1 : (24 : Int) ≤ r.time), (hW2 : (r.time : Int) ≤ 33)⟩ := hW
  have h1 : (24 ≤ r.time && r.time ≤ 33) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
  simp only [h1, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem svc_of {y : Fin 5} (hy : y ∈ H) {P : Fin 5 → Bool}
    (h : (honest.all fun y => P y) = true) : P y = true :=
  List.all_eq_true.1 h y (mem_honest y hy)

theorem rowsD_time {ctl : Bool} {i : Nat} {r : RowD} (hr : (rowsD ctl)[i]? = some r) :
    (tr ctl).time i = r.time := (trace_row hr).2.1

/-- **`Sync[24, 33]`**, in both variants. -/
theorem run_sync (ctl : Bool) : (tr ctl).SyncRun H 1 24 33 where
  deltaF := one_pos
  delta_le := le_rfl
  message x _ i m hs hW y hy j hj hd := by
    obtain ⟨ℓ, ⟨hn, hl⟩, hor⟩ := hs
    obtain ⟨r, hr, hc⟩ := label_row hl
    obtain ⟨call, M, ems, hcut, rfl⟩ := cut_ac hc
    have hxr : r.node = x := (trace_row hr).1 ▸ hn
    have hpre := (trace_row hr).2.2.2.2
    have hpost := (trace_row hr).2.2.2.1
    rw [hxr] at hpre
    have hsend : m ∈ msgCands r ∧ sendMsgB r m = true := by
      rcases hor with ⟨e, he, rfl⟩ | ⟨hne, hh1, hh2⟩
      · obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
        have hv : e'.interp.msg = e'.vote := rfl
        have : e'.vote ∈ ems.map EmD.vote := List.mem_map_of_mem he'
        rw [hv]
        refine ⟨List.mem_append_left _ (by simpa [emitsD, hcut] using this), ?_⟩
        simp [sendMsgB, hcut, this]
      · change ¬ m ∈ ((tr ctl).state x i).ac.pool m.slot at hh1
        change m ∈ ((tr ctl).post i).ac.pool m.slot at hh2
        rw [hpre] at hh1; rw [hpost] at hh2
        simp only [NodeD.interp_ac, interp_pool] at hh1 hh2
        refine ⟨List.mem_append_right _ ?_, ?_⟩
        · obtain ⟨t, ht⟩ := mem_pool_iff.1 hh2; exact List.mem_map.2 ⟨_, ht, rfl⟩
        · have hr' : isRestartCall call = false := by
            cases call <;> first | rfl | exact absurd rfl hne
          simp [sendMsgB, hcut, hr', hh1, hh2]
    have h1 := List.all_eq_true.1 (syncD_row hr hW).1 m hsend.1
    rw [hsend.2, Bool.not_true, Bool.false_or] at h1
    obtain ⟨k, hkj, rk, hrk, hny, hlo, htk, hp⟩ := svc_spec (svc_of hy h1) hj
      (by rw [rowsD_time hr] at hd; exact hd)
    refine ⟨k, hkj, ?_, ?_, ?_⟩
    · rw [rowsD_time hr, rowsD_time hrk]; exact_mod_cast hlo rfl
    · have hc' := callAt_row hrk
      rw [hny] at hc'
      rcases procMsgB_true hp with ⟨M', ems', hcut'⟩ | hp
      · left
        rw [hcut'] at hc'
        exact ⟨_, hc', rfl⟩
      · right
        obtain ⟨call', M', ems', hcut', e, he, rfl⟩ := emitsD_mem hp
        rw [hcut'] at hc'
        exact ⟨_, hc', e.interp, List.mem_map_of_mem he, rfl⟩
    · rw [rowsD_time hr]; exact htk
  block x _ i B hs hW y hy j hj hd := by
    obtain ⟨r, hr, b, hb, rfl⟩ : ∃ r, (rowsD ctl)[i]? = some r ∧ ∃ b, acceptD r.cut = some b ∧
        B = X.blk b := by
      rcases hs with ⟨-, hl⟩ | ⟨⟨acc, -, hl⟩, hpos⟩
      · obtain ⟨r, hr, hc⟩ := label_row hl
        obtain ⟨b, hcut, rfl⟩ := cut_fgBlock hc
        exact ⟨r, hr, b, by rw [hcut]; rfl, rfl⟩
      · obtain ⟨r, hr, hc⟩ := label_row hl
        obtain ⟨b, hcut, rfl⟩ := cut_fgBlock hc
        have := List.all_eq_true.1 (syncD_true ctl).2 r (List.mem_of_getElem? hr)
        rw [hcut] at this
        simp only [blockD, Option.isNone_some, Bool.false_or, beq_iff_eq] at this
        exact absurd ((trace_row hr).2.2.1.trans this) hpos
    have h1 := List.all_eq_true.1 (syncD_row hr hW).2.1 b
      (by rw [hb]; exact List.mem_singleton_self _)
    have h2 := svc_of hy h1
    simp only [Bool.and_eq_true] at h2
    obtain ⟨k, hkj, rk, hrk, hny, hlo, htk, hp⟩ :=
      svc_spec h2.1 hj (by rw [rowsD_time hr] at hd; exact hd)
    refine ⟨k, hkj, ?_, ?_, by rw [rowsD_time hr]; exact htk⟩
    · rw [rowsD_time hr, rowsD_time hrk]; exact_mod_cast hlo rfl
    · have hc' := callAt_row hrk
      rw [hny] at hc'
      obtain ⟨acc, hcut'⟩ := blockD_some (beq_iff_eq.1 hp)
      rw [hcut'] at hc'
      exact ⟨_, hc'⟩
  relay x _ i B hs hW y hy j hj hd _ := by
    obtain ⟨r, hr, hc⟩ := label_row hs.2
    obtain ⟨b, hcut, rfl⟩ := cut_fgBlock hc
    have h1 := List.all_eq_true.1 (syncD_row hr hW).2.1 b
      (by rw [hcut]; exact List.mem_singleton_self _)
    have h2 := svc_of hy h1
    simp only [Bool.and_eq_true] at h2
    obtain ⟨k, hkj, rk, hrk, hny, -, htk, hp⟩ :=
      svc_spec h2.2 hj (by rw [rowsD_time hr] at hd; exact hd)
    refine ⟨k, hkj, ?_, by rw [rowsD_time hr]; exact htk⟩
    have hc' := callAt_row hrk
    rw [hny] at hc'
    rw [acceptD_some (beq_iff_eq.1 hp)] at hc'
    exact hc'
  attestation x _ i a hs hW y hy j hj hd := by
    obtain ⟨r, hr, hsend⟩ : ∃ r, (rowsD ctl)[i]? = some r ∧ a ∈ attCands r ∧ sendAttB r a := by
      rcases hs with ⟨src, hn, hl⟩ | ⟨ℓ, ⟨hn, hl⟩, hh1, hh2⟩
      · obtain ⟨r, hr, hc⟩ := label_row hl
        have hsg : signD r.cut = some a := by
          revert hc; cases r.cut <;> simp [CutD.interp, signD]
        exact ⟨r, hr, List.mem_append_left _ (by simp [hsg]), by simp [sendAttB, hsg]⟩
      · obtain ⟨r, hr, hc⟩ := label_row hl
        have hxr : r.node = x := (trace_row hr).1 ▸ hn
        have hpre := (trace_row hr).2.2.2.2
        rw [hxr] at hpre
        rw [hpre] at hh1; rw [(trace_row hr).2.2.2.1] at hh2
        change ¬ a ∈ r.pre.fg.atts at hh1
        change a ∈ r.post.fg.atts at hh2
        have hfg : isFG r.cut = true := by revert hc; cases r.cut <;> simp [CutD.interp, isFG]
        exact ⟨r, hr, List.mem_append_right _ hh2, by simp [sendAttB, hfg, hh1, hh2]⟩
    have h1 := List.all_eq_true.1 (syncD_row hr hW).2.2 a hsend.1
    rw [hsend.2, Bool.not_true, Bool.false_or] at h1
    obtain ⟨k, hkj, rk, hrk, hny, -, htk, hp⟩ := svc_spec (svc_of hy h1) hj
      (by rw [rowsD_time hr] at hd; exact hd)
    refine ⟨k, hkj, ?_, by rw [rowsD_time hr]; exact htk⟩
    have hc' := callAt_row hrk
    rw [hny] at hc'
    rw [attD_some (beq_iff_eq.1 hp)] at hc'
    exact Or.inl hc'

end Consensus.Goldilocks.Test.HalfCommittee.Five

end

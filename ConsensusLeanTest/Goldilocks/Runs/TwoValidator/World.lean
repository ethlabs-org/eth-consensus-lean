module
public import ConsensusLeanTest.Goldilocks.Runs.TwoValidator.Step
@[expose] public section

/-! # The healthy two-validator run: the events of every time

The run of `TwoValidator.Run` time by time:

* **The shape of the events** (`plan t`): the node, the event and the cuts (each cut without its
  frame, `sk`) of every segment of time `t`, by the residue of `t` modulo a slot (`4`) and of the
  slot modulo the period (`10`); `segs_plan`: the run's segments have that shape.
* **The queue of `v1`'s rows** (`qOf`): `v1` signs its row of height `q` at `rt q`, and `v0` is
  delivered it thirty-five time units later (`world_queue_eq`).
* **The states** (`world_good`): before every time both nodes are in the state `Good` of
  `TwoValidator.Step`; it follows from one step lemma per residue (`step_time`).
* **The pools at every cut** (`pool_sub`, `pool_full`, `atts_sub`, `atts_full` and their post-cut
  forms): the votes of slot `σ` are held from their vote time `vt σ` on, the rows from their receipt
  time `rowRecv` on, and nothing else is ever held. -/

namespace Consensus.Goldilocks.Witness.TwoRun

open SA Node

/-! ## The shape of the events -/

/-- A cut without its frame: an AC call with its emitted messages, or an FG call. -/
inductive Sk where
  /-- An AC call and the messages it emits. -/
  | ac (c : N.Call) (es : List (Vote sp.n))
  /-- An FG call. -/
  | fg (ℓ : FGLabel sp.toParams N.Payload)

/-- The cut `c` without its frame. -/
def sk : Cut N → Sk
  | .ac ℓ => .ac ℓ.call (ℓ.emits.map (·.msg))
  | .fg ℓ => .fg ℓ

/-- The shape of the segments of time `t`: node, event and the frameless cuts. -/
noncomputable def segsSk (t : Nat) : List (Fin sp.n × Node.Event N × List Sk) :=
  (segs t).map fun sg => (sg.node, sg.ev, sg.cuts.map sk)

/-- The cuts of a tick with no proposal and no row: `ac_on_tick` (with its emissions) and
`ac_to_fg`. -/
def tickSk (es : List (Vote sp.n)) : List Sk := [.ac .tick es, .ac .toFG []]

/-- **The shape of the events of time `t`.**
* `t = 1`: both ticks cast the votes of slot `0`, then each node receives the other's vote.
* `t = t_s`, `s ≥ 1`: `v0` proposes `blk s`, accepts it and votes; `v1` ticks; `v1` receives
  `blk s` (accepts it and votes), then `v0`'s vote; `v0` receives `v1`'s vote; when `s ≡ 0 mod 10`,
  `v0` then receives `v1`'s row of height `s / 10`.
* `t = t_s + 1`, `s ≥ 1`: both ticks report `blk s` to the FG; when `s ≡ 1 mod 10` each node
  signs and processes its row of height `hgt s`, and `v1` then receives `v0`'s; otherwise nobody
  signs.
* otherwise: both ticks do nothing but `ac_on_tick` and `ac_to_fg`. -/
noncomputable def plan (t : Nat) : List (Fin sp.n × Node.Event N × List Sk) :=
  if t = 1 then
    [(w0, .tick 0, tickSk [vote w0 0]), (w1, .tick 0, tickSk [vote w1 0]),
      (w1, .message (vote w0 0), [.ac (.message (vote w0 0)) []]),
      (w0, .message (vote w1 0), [.ac (.message (vote w1 0)) []])]
  else if t % 4 = 0 ∧ 4 ≤ t then
    [(w0, .tick 0, [.ac .tick [], .ac .proposal [], .fg (.block (blk (t / 4)) true),
        .ac (.block (blk (t / 4))) [vote w0 (t / 4)], .ac .toFG []]),
      (w1, .tick 0, tickSk []),
      (w1, .block (blk (t / 4)), [.fg (.block (blk (t / 4)) true),
        .ac (.block (blk (t / 4))) [vote w1 (t / 4)]]),
      (w1, .message (vote w0 (t / 4)), [.ac (.message (vote w0 (t / 4))) []]),
      (w0, .message (vote w1 (t / 4)), [.ac (.message (vote w1 (t / 4))) []])] ++
    (if (t / 4) % 10 = 0 then
      [(w0, .attestation (row w1 (t / 40)), [.fg (.attestation (row w1 (t / 40)))])] else [])
  else if t % 4 = 1 ∧ 4 ≤ t ∧ (t / 4) % 10 = 1 then
    [(w0, .tick 0, tickSk [] ++ [.fg (.attest (blk (t / 4)) (some (row w0 (hgt (t / 4))))),
        .fg (.attestation (row w0 (hgt (t / 4))))]),
      (w1, .tick 0, tickSk [] ++ [.fg (.attest (blk (t / 4)) (some (row w1 (hgt (t / 4))))),
        .fg (.attestation (row w1 (hgt (t / 4))))]),
      (w1, .attestation (row w0 (hgt (t / 4))), [.fg (.attestation (row w0 (hgt (t / 4))))])]
  else if t % 4 = 1 ∧ 4 ≤ t then
    [(w0, .tick 0, tickSk [] ++ [.fg (.attest (blk (t / 4)) none)]),
      (w1, .tick 0, tickSk [] ++ [.fg (.attest (blk (t / 4)) none)])]
  else
    [(w0, .tick 0, tickSk []), (w1, .tick 0, tickSk [])]

/-! ## The queue of `v1`'s rows -/

/-- The rows `v1` signs at time `t'`: its row of height `t' / 40 + 1` when `t' ≡ 5 mod 40`
(`t' = rt q`), none otherwise. -/
noncomputable def qOf (t' : Nat) : List (FG.Att sp.n) :=
  if t' % 40 = 5 then [row w1 (t' / 40 + 1)] else []

/-! ## The shape at each residue -/

theorem plan_one : plan 1 =
    [(w0, .tick 0, tickSk [vote w0 0]), (w1, .tick 0, tickSk [vote w1 0]),
      (w1, .message (vote w0 0), [.ac (.message (vote w0 0)) []]),
      (w0, .message (vote w1 0), [.ac (.message (vote w1 0)) []])] := by
  unfold plan; rw [ite_eq_left rfl]

theorem plan_four {s : Nat} (hs : 1 ≤ s) : plan (4 * s) =
    [(w0, .tick 0, [.ac .tick [], .ac .proposal [], .fg (.block (blk s) true),
        .ac (.block (blk s)) [vote w0 s], .ac .toFG []]),
      (w1, .tick 0, tickSk []),
      (w1, .block (blk s), [.fg (.block (blk s) true), .ac (.block (blk s)) [vote w1 s]]),
      (w1, .message (vote w0 s), [.ac (.message (vote w0 s)) []]),
      (w0, .message (vote w1 s), [.ac (.message (vote w1 s)) []])] ++
    (if s % 10 = 0 then
      [(w0, .attestation (row w1 (s / 10)), [.fg (.attestation (row w1 (s / 10)))])] else []) := by
  unfold plan
  rw [ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩,
    show 4 * s / 4 = s by omega, show 4 * s / 40 = s / 10 by omega]

theorem plan_four1_row {s : Nat} (hs : 1 ≤ s) (h10 : s % 10 = 1) : plan (4 * s + 1) =
    [(w0, .tick 0, tickSk [] ++ [.fg (.attest (blk s) (some (row w0 (hgt s)))),
        .fg (.attestation (row w0 (hgt s)))]),
      (w1, .tick 0, tickSk [] ++ [.fg (.attest (blk s) (some (row w1 (hgt s)))),
        .fg (.attestation (row w1 (hgt s)))]),
      (w1, .attestation (row w0 (hgt s)), [.fg (.attestation (row w0 (hgt s)))])] := by
  unfold plan
  rw [ite_eq_right (by omega), ite_eq_right (by omega), show (4 * s + 1) / 4 = s by omega,
    ite_eq_left ⟨by omega, by omega, h10⟩]

theorem plan_four1 {s : Nat} (hs : 1 ≤ s) (h10 : s % 10 ≠ 1) : plan (4 * s + 1) =
    [(w0, .tick 0, tickSk [] ++ [.fg (.attest (blk s) none)]),
      (w1, .tick 0, tickSk [] ++ [.fg (.attest (blk s) none)])] := by
  unfold plan
  rw [ite_eq_right (by omega), ite_eq_right (by omega), show (4 * s + 1) / 4 = s by omega,
    ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩]

/-- The other times (`0`, `2`, `3`, `t_s + 2`, `t_s + 3`): two quiet ticks. -/
theorem plan_quiet {t : Nat} (h1 : t ≠ 1) (h0 : ¬ (t % 4 = 0 ∧ 4 ≤ t))
    (h4 : ¬ (t % 4 = 1 ∧ 4 ≤ t)) :
    plan t = [(w0, .tick 0, tickSk []), (w1, .tick 0, tickSk [])] := by
  unfold plan
  rw [ite_eq_right h1, ite_eq_right h0, ite_eq_right (fun h => h4 ⟨h.1, h.2.1⟩), ite_eq_right h4]

/-! ## The step of a time (statements) -/

/-- The states of both nodes before time `t`. -/
def WorldGood (t : Nat) : Prop := ∀ y, Good ((world t).1 y) y t

/-- The queue of `v1`'s rows before time `t`. -/
def QueueGood (t : Nat) : Prop := ∀ t', (world t).2 t' = if t' < t then qOf t' else []

/-! ## Stepping the schedule -/

theorem runEvs_cons_eq {t : Nat} {w : Wld} {y : Fin sp.n} {e : Node.Event N}
    {es : List (Fin sp.n × Node.Event N)} {st : St} {cs : List (Cut N)}
    (h : exec prop dg y (w y) (t : Int) e = (st, cs)) :
    runEvs t w ((y, e) :: es) = ((runEvs t (Function.update w y st) es).1,
      ⟨y, e, w, cs⟩ :: (runEvs t (Function.update w y st) es).2) := by
  change (let r := ex w y t e
    let rest := runEvs t (Function.update w y r.1) es
    (rest.1, (⟨y, e, w, r.2⟩ : Seg) :: rest.2)) = _
  simp only [ex, h]

theorem qa_eq {t : Nat} (hq : QueueGood t) : qa t = if 35 ≤ t then qOf (t - 35) else [] := by
  unfold qa
  split_ifs with h
  · rw [hq, ite_eq_left (by omega)]
  · rfl

theorem qa_nil {t : Nat} (hq : QueueGood t) (h : ¬ (35 ≤ t ∧ (t - 35) % 40 = 5)) :
    qa t = [] := by
  rw [qa_eq hq]
  split_ifs with h1
  · unfold qOf; rw [ite_eq_right (fun h2 => h ⟨h1, h2⟩)]
  · rfl

theorem queue_step {t : Nat} (hq : QueueGood t) (h : (tk1 t).2.filterMap attOf = qOf t) :
    QueueGood (t + 1) := by
  intro t'
  rw [world_succ]
  change Function.update (world t).2 t _ t' = _
  by_cases ht : t' = t
  · subst ht; rw [Function.update_self, h, ite_eq_left (by omega)]
  · rw [Function.update_of_ne ht, hq]
    split_ifs <;> first | rfl | omega

theorem qOf_of {t' : Nat} (h : t' % 40 ≠ 5) : qOf t' = [] := by unfold qOf; rw [ite_eq_right h]

theorem sk_ac (c : N.Call) (Φ : N.Frm) (es : List N.Em) :
    sk (.ac ⟨c, Φ, es⟩) = .ac c (es.map (·.msg)) := rfl

theorem poolT_congr {y : Fin sp.n} {t t' : Nat} (h1 : tip t = tip t') (h2 : 2 ≤ t ↔ 2 ≤ t') :
    poolT y t = poolT y t' := by
  funext σ; unfold poolT; rw [h1]; simp only [h2]

theorem good_congr {st : St} {y : Fin sp.n} {t t' : Nat} (h1 : tip t = tip t')
    (h2 : cnt y t = cnt y t') (h3 : nrw t = nrw t') (h4 : vsT t = vsT t')
    (h5 : poolT y t = poolT y t') (h6 : rep t = rep t') (h7 : nsv t = nsv t')
    (h : Good st y t) : Good st y t' := by
  unfold Good at h ⊢; rw [← h1, ← h2, ← h3, ← h4, ← h5, ← h6, ← h7]; exact h

/-- **Two ticks with nothing to deliver**: the worlds and the shape of the time. -/
theorem step_ticks {t : Nat} {s0 s1 : St} {Φ0 Φ0' Φ1 Φ1' : N.Frm} {l0 l1 : List (Cut N)}
    (h0 : Node.onTick prop dg w0 ((world t).1 w0) (t : Int) 0 =
      (s0, [.ac ⟨.tick, Φ0, []⟩, .ac ⟨.toFG, Φ0', []⟩] ++ l0))
    (h1 : Node.onTick prop dg w1 ((world t).1 w1) (t : Int) 0 =
      (s1, [.ac ⟨.tick, Φ1, []⟩, .ac ⟨.toFG, Φ1', []⟩] ++ l1))
    (hl0 : l0.filterMap toW1 = []) (hl1 : l1.filterMap voteOf = [])
    (hq : QueueGood t) (hqa : qa t = []) (hatt : l1.filterMap attOf = qOf t) :
    (world (t + 1)).1 = Function.update (Function.update (world t).1 w0 s0) w1 s1 ∧
      QueueGood (t + 1) ∧
      segsSk t =
        [(w0, .tick 0, tickSk [] ++ l0.map sk), (w1, .tick 0, tickSk [] ++ l1.map sk)] := by
  have htk0 : tk0 t = (s0, [.ac ⟨.tick, Φ0, []⟩, .ac ⟨.toFG, Φ0', []⟩] ++ l0) := h0
  have hwA : wA t w1 = (world t).1 w1 := Function.update_of_ne w1_ne _ _
  have htk1 : tk1 t = (s1, [.ac ⟨.tick, Φ1, []⟩, .ac ⟨.toFG, Φ1', []⟩] ++ l1) := by
    change exec prop dg w1 (wA t w1) (t : Int) (.tick 0) = _; rw [hwA]; exact h1
  have hevs1 : evs1 t = [] := by
    unfold evs1; rw [htk0, List.filterMap_append, hl0]; rfl
  have hrun1 : run1 t = (wB t, []) := by unfold run1; rw [hevs1]; rfl
  have hevs0 : evs0 t = [] := by
    unfold evs0; rw [hrun1, htk1, hqa]
    simp only [List.flatMap_nil, List.append_nil, List.filterMap_append, hl1]; rfl
  refine ⟨?_, queue_step hq (by rw [htk1, List.filterMap_append, hatt]; rfl), ?_⟩
  · rw [world_succ, hrun1, hevs0]
    change wB t = _
    unfold wB wA; rw [htk0, htk1]
  · unfold segsSk; rw [segs_eq, hrun1, hevs0, htk0, htk1]
    rfl

theorem upd2_w0 (W : Wld) (a b : St) : Function.update (Function.update W w0 a) w1 b w0 = a := by
  rw [Function.update_of_ne (Ne.symm w1_ne), Function.update_self]

theorem upd2_w1 (W : Wld) (a b : St) : Function.update (Function.update W w0 a) w1 b w1 = b :=
  Function.update_self _ _ _

theorem forall_y {p : Fin sp.n → Prop} (h0 : p w0) (h1 : p w1) : ∀ y, p y := fun y => by
  rcases eq_w0_or_w1 y with rfl | rfl
  · exact h0
  · exact h1

/-- A quiet tick of `y` at `t` from a state `Good` at `t`. -/
theorem quiet_tick {st : St} {y : Fin sp.n} {t : Nat} (h : Good st y t)
    (hnp : ¬ (y = w0 ∧ t % 4 = 0 ∧ 4 ≤ t)) (h2 : ¬ (t % 4 = 2 ∧ 4 ≤ t)) (h1 : t % 4 ≠ 1)
    (hlk : tip t ≤ rep t) (hrp : rep t ≤ tip t) :
    Node.onTick prop dg y st (t : Int) 0 =
      (st, [.ac ⟨.tick, Node.frame st, []⟩, .ac ⟨.toFG, Node.frame st, []⟩] ++ []) := by
  rw [List.append_nil]
  exact tick_noop h hnp (by rw [acOnTick_eq _ _ _ _ h.ac.restart, ite_eq_right h2,
    ite_eq_right h1]) hlk hrp (by omega)

/-- **The step of a quiet time** (`0`, `2`, `3`, `t_s + 3`): both states stay. -/
theorem step_quiet {t : Nat} (hw : WorldGood t) (hq : QueueGood t)
    (hnp : ¬ (t % 4 = 0 ∧ 4 ≤ t)) (h2 : ¬ (t % 4 = 2 ∧ 4 ≤ t)) (h1 : t % 4 ≠ 1)
    (hlk : tip t ≤ rep t) (hrp : rep t ≤ tip t) (hqa : qa t = []) (hqo : qOf t = [])
    (hg : ∀ y st, Good st y t → Good st y (t + 1)) :
    WorldGood (t + 1) ∧ QueueGood (t + 1) ∧
      segsSk t = [(w0, .tick 0, tickSk []), (w1, .tick 0, tickSk [])] := by
  obtain ⟨hW, hQ, hS⟩ := step_ticks
    (quiet_tick (hw w0) (fun h => hnp h.2) h2 h1 hlk hrp)
    (quiet_tick (hw w1) (fun h => hnp h.2) h2 h1 hlk hrp) rfl rfl hq hqa (by rw [hqo]; rfl)
  refine ⟨forall_y ?_ ?_, hQ, by rw [hS]; rfl⟩
  · rw [hW, upd2_w0]; exact hg _ _ (hw w0)
  · rw [hW, upd2_w1]; exact hg _ _ (hw w1)

/-- The state after the tick (and deliveries) of `t_s + 1`, before `t_s + 2`. -/
theorem good_of_report {st : St} {y : Fin sp.n} {s c : Nat} (hs : 1 ≤ s)
    (h : NS st y s c (hgt s) (vsT (4 * s + 1)) (poolT y (4 * s + 1)) s s s s (nsv (4 * s + 1)))
    (hc : c = cnt y (4 * s + 2)) : Good st y (4 * s + 2) := by
  unfold Good
  rw [tip_four2, rep_four2, ← hc, nrw_row_succ hs,
    show vsT (4 * s + 2) = vsT (4 * s + 1) by
      unfold vsT; rw [tip_four1, tip_four2, ite_eq_right (by omega), ite_eq_right (by omega)],
    poolT_congr (t := 4 * s + 2) (t' := 4 * s + 1) (by rw [tip_four1, tip_four2]) (by omega),
    show nsv (4 * s + 2) = nsv (4 * s + 1) by rw [nsv_four1, nsv_four2]]
  exact h

theorem cnt_report0 {s : Nat} (hs : 1 ≤ s) (h10 : s % 10 = 1) :
    cnt w0 (4 * s + 1) + 1 = cnt w0 (4 * s + 2) := by
  have := hgt_pos s
  unfold cnt; rw [ite_eq_left rfl, ite_eq_left rfl, nrw_row hs, ite_eq_left h10, nrw_row_succ hs,
    nrv_succ_of (t := 4 * s + 1) (by omega)]
  omega

theorem cnt_report1 {s : Nat} (hs : 1 ≤ s) (h10 : s % 10 = 1) :
    cnt w1 (4 * s + 1) + 1 + 1 = cnt w1 (4 * s + 2) := by
  have := hgt_pos s
  unfold cnt; rw [ite_eq_right w1_ne, ite_eq_right w1_ne, nrw_row hs, ite_eq_left h10,
    nrw_row_succ hs]
  omega

theorem poolAt_report1 {s : Nat} (hs : 1 ≤ s) (h10 : s % 10 = 1) :
    poolAt w1 (cnt w1 (4 * s + 1) + 1) = row w0 (hgt s) := by
  have := hgt_pos s
  unfold poolAt cnt
  rw [ite_eq_right w1_ne, nrw_row hs, ite_eq_left h10, ite_eq_right (by omega)]
  congr 1; omega

theorem qOf_report {s : Nat} (hs : 1 ≤ s) (h10 : s % 10 = 1) :
    qOf (4 * s + 1) = [row w1 (hgt s)] := by
  unfold qOf hgt; rw [ite_eq_left (by omega), ite_eq_right (by omega)]; congr 2; omega

theorem good_of_voted' {st : St} {y : Fin sp.n} {s c : Nat}
    (h : NS st y s c (nrw (4 * s + 1)) (vsT (4 * s + 1)) (poolT y (4 * s + 1)) s s s
      (rep (4 * s + 1)) (nsv (4 * s + 1))) (hc : c = cnt y (4 * s + 1)) :
    Good st y (4 * s + 1) := by
  unfold Good; rw [tip_four1, ← hc]; exact h

theorem poolAt_delayed {s : Nat} (hs : 1 ≤ s) (h10 : s % 10 = 0) :
    poolAt w0 (cnt w0 (4 * s)) = row w1 (s / 10) := by
  have hc : cnt w0 (4 * s) = 2 * (s / 10) - 1 := by
    unfold cnt nrw nrv; rw [ite_eq_left rfl]; split_ifs <;> omega
  unfold poolAt; rw [hc, ite_eq_right (by omega), other_w0]; congr 1; omega

theorem qa_four {s : Nat} (hs : 1 ≤ s) (hq : QueueGood (4 * s)) :
    qa (4 * s) = if s % 10 = 0 then [row w1 (s / 10)] else [] := by
  rw [qa_eq hq]
  split_ifs with h1 h2 h2
  · unfold qOf; rw [ite_eq_left (by omega)]; congr 2; omega
  · exact qOf_of (by omega)
  · omega
  · rfl

theorem other_w1 : other w1 = w0 := by decide

/-- **The step of times `0, 2, 3`**: two ticks with nothing to do. -/
theorem step_small {t : Nat} (ht : t = 0 ∨ t = 2 ∨ t = 3) (hw : WorldGood t) (hq : QueueGood t) :
    WorldGood (t + 1) ∧ QueueGood (t + 1) ∧ segsSk t = plan t := by
  have hp : plan t = [(w0, .tick 0, tickSk []), (w1, .tick 0, tickSk [])] :=
    plan_quiet (by omega) (by omega) (by omega)
  rw [hp]
  refine step_quiet hw hq (by omega) (by omega) (by omega) ?_ ?_
    (by rw [qa_eq hq, ite_eq_right (by omega)]) (qOf_of (by omega)) ?_
  · rcases ht with rfl | rfl | rfl <;> decide
  · rcases ht with rfl | rfl | rfl <;> decide
  · intro y st h
    rcases ht with rfl | rfl | rfl <;>
      exact good_congr (by decide) (by unfold cnt; split_ifs <;> decide) (by decide)
        (by decide) (poolT_congr (by decide) (by decide)) (by decide) (by decide) h

/-- **The step of time `1`**: the votes of slot `0`. -/
theorem step_one (hw : WorldGood 1) (hq : QueueGood 1) :
    WorldGood 2 ∧ QueueGood 2 ∧ segsSk 1 = plan 1 := by
  obtain ⟨A0, e0, h0, he0, hn0⟩ := tick_vote0 (hw w0)
  obtain ⟨A1, e1, h1, he1, hn1⟩ := tick_vote0 (hw w1)
  obtain ⟨B1, hd1, hg1⟩ := deliver_vote0 hn1
  obtain ⟨B0, hd0, hg0⟩ := deliver_vote0 hn0
  set W := (world 1).1
  set st0 : St := { W w0 with ac := A0 }
  set st1 : St := { W w1 with ac := A1 }
  have htk0 : tk0 1 = (st0, [.ac ⟨.tick, Node.frame (W w0), [e0]⟩,
      .ac ⟨.toFG, Node.frame (W w0), []⟩]) := h0
  have hwA : wA 1 w1 = W w1 := Function.update_of_ne w1_ne _ _
  have htk1 : tk1 1 = (st1, [.ac ⟨.tick, Node.frame (W w1), [e1]⟩,
      .ac ⟨.toFG, Node.frame (W w1), []⟩]) := by
    change exec prop dg w1 (wA _ w1) _ (.tick 0) = _; rw [hwA]; exact h1
  have hwB : wB 1 = Function.update (Function.update W w0 st0) w1 st1 := by
    unfold wB wA; rw [htk0, htk1]
  have hevs1 : evs1 1 = [(w1, .message (vote w0 0))] := by
    unfold evs1; rw [htk0]; change [(w1, Node.Event.message e0.msg)] = _; rw [he0]
  have hrun1 : run1 1 = (Function.update (wB 1) w1 { st1 with ac := B1 },
      [⟨w1, .message (vote w0 0), wB 1,
        [.ac ⟨.message (vote w0 0), Node.frame st1, []⟩]⟩]) := by
    unfold run1
    rw [hevs1, runEvs_cons_eq (st := { st1 with ac := B1 })
      (cs := [.ac ⟨.message (vote w0 0), Node.frame st1, []⟩])
      (by rw [hwB, upd2_w1]; exact hd1)]; rfl
  have hqa : qa 1 = [] := rfl
  have hevs0 : evs0 1 = [(w0, .message (vote w1 0))] := by
    unfold evs0; rw [hrun1, htk1, hqa]
    change [(w0, Node.Event.message e1.msg)] ++ [] = _; rw [he1]; rfl
  have hr1 : (run1 1).1 w0 = st0 := by
    rw [hrun1]; dsimp only; rw [Function.update_of_ne (Ne.symm w1_ne), hwB, upd2_w0]
  have hrun3 : runEvs 1 (run1 1).1 (evs0 1) =
      (Function.update (run1 1).1 w0 { st0 with ac := B0 },
        [⟨w0, .message (vote w1 0), (run1 1).1,
          [.ac ⟨.message (vote w1 0), Node.frame st0, []⟩]⟩]) := by
    rw [hevs0, runEvs_cons_eq (st := { st0 with ac := B0 })
      (cs := [.ac ⟨.message (vote w1 0), Node.frame st0, []⟩])
      (by rw [hr1]; exact hd0)]; rfl
  have hW : (world 2).1 = Function.update (Function.update (wB 1) w1 { st1 with ac := B1 }) w0
      { st0 with ac := B0 } := by
    rw [world_succ, hrun3, hrun1]
  refine ⟨forall_y ?_ ?_, queue_step hq (by rw [htk1]; rfl), ?_⟩
  · rw [hW, Function.update_self]; exact hg0
  · rw [hW, Function.update_of_ne w1_ne, Function.update_self]; exact hg1
  · unfold segsSk; rw [segs_eq, hrun3, hrun1, htk0, htk1, plan_one]
    rw [← he0, ← he1]; rfl

/-- **The step of time `t_s`**, `s ≥ 1`: the proposal of `blk s`, the votes, and at `s ≡ 0 mod 10`
the delayed row of `v1`. -/
theorem step_four {s : Nat} (hs : 1 ≤ s) (hw : WorldGood (4 * s)) (hq : QueueGood (4 * s)) :
    WorldGood (4 * s + 1) ∧ QueueGood (4 * s + 1) ∧ segsSk (4 * s) = plan (4 * s) := by
  set W := (world (4 * s)).1
  obtain ⟨st0, e0, h0, he0, hv0⟩ := tick_propose hs (hw w0)
  have h1 := quiet_tick (hw w1) (fun h => w1_ne h.1) (by omega) (by omega)
    (by rw [tip_four, rep_four]) (by rw [tip_four, rep_four])
  rw [List.append_nil] at h1
  have hg1 : NS (W w1) w1 (s - 1) (cnt w1 (4 * s)) (nrw (4 * s)) (vsT (4 * s)) (poolT w1 (4 * s))
      (s - 1) (s - 1) (s - 1) (s - 1) (nsv (4 * s)) := by
    have := hw w1; unfold Good at this; rwa [tip_four, rep_four] at this
  obtain ⟨st1, e1, hb1, he1, hv1⟩ := onBlock_blk hs hg1
  obtain ⟨B1, hm1, hn1⟩ := deliver_vote hs hv1
  obtain ⟨B0, hm0, hn0⟩ := deliver_vote hs hv0
  rw [other_w1] at hm1
  rw [other_w0] at hm0
  have htk0 : tk0 (4 * s) = (st0, [.ac ⟨.tick, Node.frame (W w0), []⟩,
      .ac ⟨.proposal, Node.frame (W w0), []⟩, .fg (.block (blk s) true),
      .ac ⟨.block (blk s), Node.frame st0, [e0]⟩, .ac ⟨.toFG, Node.frame st0, []⟩]) := h0
  have hwA : wA (4 * s) w1 = W w1 := Function.update_of_ne w1_ne _ _
  have htk1 : tk1 (4 * s) = (W w1, [.ac ⟨.tick, Node.frame (W w1), []⟩,
      .ac ⟨.toFG, Node.frame (W w1), []⟩]) := by
    change exec prop dg w1 (wA _ w1) _ (.tick 0) = _; rw [hwA]; exact h1
  have hwB : wB (4 * s) = Function.update (Function.update W w0 st0) w1 (W w1) := by
    unfold wB wA; rw [htk0, htk1]
  have hevs1 : evs1 (4 * s) = [(w1, .block (blk s)), (w1, .message (vote w0 s))] := by
    unfold evs1; rw [htk0]
    change [(w1, Node.Event.block (blk s)), (w1, Node.Event.message e0.msg)] = _; rw [he0]
  have hrun1 : run1 (4 * s) = (Function.update (Function.update (wB (4 * s)) w1 st1) w1
        { st1 with ac := B1 },
      [⟨w1, .block (blk s), wB (4 * s), [.fg (.block (blk s) true),
          .ac ⟨.block (blk s), Node.frame st1, [e1]⟩]⟩,
        ⟨w1, .message (vote w0 s), Function.update (wB (4 * s)) w1 st1,
          [.ac ⟨.message (vote w0 s), Node.frame st1, []⟩]⟩]) := by
    unfold run1
    rw [hevs1, runEvs_cons_eq (st := st1) (cs := [.fg (.block (blk s) true),
        .ac ⟨.block (blk s), Node.frame st1, [e1]⟩]) (by rw [hwB, upd2_w1]; exact hb1),
      runEvs_cons_eq (st := { st1 with ac := B1 })
        (cs := [.ac ⟨.message (vote w0 s), Node.frame st1, []⟩])
        (by rw [Function.update_self]; exact hm1)]
    rfl
  have hr1 : (run1 (4 * s)).1 w0 = st0 := by
    rw [hrun1]; dsimp only
    rw [Function.update_of_ne (Ne.symm w1_ne), Function.update_of_ne (Ne.symm w1_ne), hwB,
      upd2_w0]
  have hr1' : (run1 (4 * s)).1 w1 = { st1 with ac := B1 } := by
    rw [hrun1]; dsimp only; exact Function.update_self _ _ _
  have hvs : ((tk1 (4 * s)).2 ++ (run1 (4 * s)).2.flatMap Seg.cuts).filterMap voteOf =
      [(.message (vote w1 s) : Node.Event N)] := by
    rw [htk1, hrun1]; change [Node.Event.message e1.msg] = _; rw [he1]
  have hqa := qa_four hs hq
  have hQ := queue_step hq (by rw [htk1, qOf_of (by omega)]; rfl)
  set S0 : St := { st0 with ac := B0 }
  have hg1' : Good { st1 with ac := B1 } w1 (4 * s + 1) :=
    good_of_voted' hn1 (by rw [cnt_four1, ite_eq_right (fun h => w1_ne h.1)])
  by_cases h10 : s % 10 = 0
  · -- the delayed row of `v1`
    obtain ⟨X, hd0, hn0'⟩ : ∃ X, Node.onAttestation S0 (row w1 (s / 10)) =
        (X, [.fg (.attestation (row w1 (s / 10)))]) ∧
        NS X w0 s (cnt w0 (4 * s) + 1) (nrw (4 * s + 1)) (vsT (4 * s + 1)) (poolT w0 (4 * s + 1))
          s s s (rep (4 * s + 1)) (nsv (4 * s + 1)) := by
      have := deliver_att hn0; rw [poolAt_delayed hs h10] at this; exact ⟨_, this⟩
    have hevs0 : evs0 (4 * s) =
        [(w0, .message (vote w1 s)), (w0, .attestation (row w1 (s / 10)))] := by
      unfold evs0; rw [hvs, hqa, ite_eq_left h10]; rfl
    have hrun3 : runEvs (4 * s) (run1 (4 * s)).1 (evs0 (4 * s)) =
        (Function.update (Function.update (run1 (4 * s)).1 w0 S0) w0 X,
          [⟨w0, .message (vote w1 s), (run1 (4 * s)).1,
              [.ac ⟨.message (vote w1 s), Node.frame st0, []⟩]⟩,
            ⟨w0, .attestation (row w1 (s / 10)), Function.update (run1 (4 * s)).1 w0 S0,
              [.fg (.attestation (row w1 (s / 10)))]⟩]) := by
      rw [hevs0, runEvs_cons_eq (st := S0)
        (cs := [.ac ⟨.message (vote w1 s), Node.frame st0, []⟩]) (by rw [hr1]; exact hm0),
        runEvs_cons_eq (st := X) (cs := [.fg (.attestation (row w1 (s / 10)))])
          (by rw [Function.update_self]; exact hd0)]
      rfl
    have hW : (world (4 * s + 1)).1 =
        Function.update (Function.update (run1 (4 * s)).1 w0 S0) w0 X := by
      rw [world_succ, hrun3]
    refine ⟨forall_y ?_ ?_, hQ, ?_⟩
    · rw [hW, Function.update_self]
      exact good_of_voted' hn0' (by rw [cnt_four1, ite_eq_left ⟨rfl, h10, by omega⟩])
    · rw [hW, Function.update_of_ne w1_ne, Function.update_of_ne w1_ne, hr1']; exact hg1'
    · unfold segsSk; rw [segs_eq, hrun3, hrun1, htk0, htk1, plan_four hs, ite_eq_left h10,
        ← he0, ← he1]
      rfl
  · have hevs0 : evs0 (4 * s) = [(w0, .message (vote w1 s))] := by
      unfold evs0; rw [hvs, hqa, ite_eq_right h10]; rfl
    have hrun3 : runEvs (4 * s) (run1 (4 * s)).1 (evs0 (4 * s)) =
        (Function.update (run1 (4 * s)).1 w0 S0,
          [⟨w0, .message (vote w1 s), (run1 (4 * s)).1,
              [.ac ⟨.message (vote w1 s), Node.frame st0, []⟩]⟩]) := by
      rw [hevs0, runEvs_cons_eq (st := S0)
        (cs := [.ac ⟨.message (vote w1 s), Node.frame st0, []⟩]) (by rw [hr1]; exact hm0)]
      rfl
    have hW : (world (4 * s + 1)).1 = Function.update (run1 (4 * s)).1 w0 S0 := by
      rw [world_succ, hrun3]
    refine ⟨forall_y ?_ ?_, hQ, ?_⟩
    · rw [hW, Function.update_self]
      exact good_of_voted' hn0 (by rw [cnt_four1, ite_eq_right (fun h => h10 h.2.1)])
    · rw [hW, Function.update_of_ne w1_ne, hr1']; exact hg1'
    · unfold segsSk; rw [segs_eq, hrun3, hrun1, htk0, htk1, plan_four hs, ite_eq_right h10,
        ← he0, ← he1]
      rfl

/-- **The step of time `t_s + 1`**, `s ≥ 1`: the reports to the FG and, at `s ≡ 1 mod 10`, the
rows. -/
theorem step_four1 {s : Nat} (hs : 1 ≤ s) (hw : WorldGood (4 * s + 1))
    (hq : QueueGood (4 * s + 1)) :
    WorldGood (4 * s + 2) ∧ QueueGood (4 * s + 2) ∧ segsSk (4 * s + 1) = plan (4 * s + 1) := by
  have hqa : qa (4 * s + 1) = [] := qa_nil hq (by omega)
  by_cases h10 : s % 10 = 1
  · obtain ⟨st0, h0, hn0⟩ := tick_report_new hs h10 (hw w0)
    obtain ⟨st1, h1, hn1⟩ := tick_report_new hs h10 (hw w1)
    obtain ⟨st1', hd, hn1'⟩ : ∃ st1', Node.onAttestation st1 (row w0 (hgt s)) =
        (st1', [.fg (.attestation (row w0 (hgt s)))]) ∧
        NS st1' w1 s (cnt w1 (4 * s + 1) + 1 + 1) (hgt s) (vsT (4 * s + 1)) (poolT w1 (4 * s + 1))
          s s s s (nsv (4 * s + 1)) := by
      have := deliver_att hn1; rw [poolAt_report1 hs h10] at this; exact ⟨_, this⟩
    have htk0 : tk0 (4 * s + 1) = (st0, [.ac ⟨.tick, Node.frame ((world (4 * s + 1)).1 w0), []⟩,
        .ac ⟨.toFG, Node.frame ((world (4 * s + 1)).1 w0), []⟩,
        .fg (.attest (blk s) (some (row w0 (hgt s)))), .fg (.attestation (row w0 (hgt s)))]) := h0
    have hwA : wA (4 * s + 1) w1 = (world (4 * s + 1)).1 w1 := Function.update_of_ne w1_ne _ _
    have htk1 : tk1 (4 * s + 1) = (st1, [.ac ⟨.tick, Node.frame ((world (4 * s + 1)).1 w1), []⟩,
        .ac ⟨.toFG, Node.frame ((world (4 * s + 1)).1 w1), []⟩,
        .fg (.attest (blk s) (some (row w1 (hgt s)))), .fg (.attestation (row w1 (hgt s)))]) := by
      change exec prop dg w1 (wA _ w1) _ (.tick 0) = _; rw [hwA]; exact h1
    have hevs1 : evs1 (4 * s + 1) = [(w1, .attestation (row w0 (hgt s)))] := by
      unfold evs1; rw [htk0]; rfl
    have hwB : wB (4 * s + 1) = Function.update (Function.update (world (4 * s + 1)).1 w0 st0)
        w1 st1 := by unfold wB wA; rw [htk0, htk1]
    have hrun1 : run1 (4 * s + 1) = (Function.update (wB (4 * s + 1)) w1 st1',
        [⟨w1, .attestation (row w0 (hgt s)), wB (4 * s + 1),
          [.fg (.attestation (row w0 (hgt s)))]⟩]) := by
      unfold run1
      rw [hevs1, runEvs_cons_eq (st := st1') (cs := [.fg (.attestation (row w0 (hgt s)))])
        (by rw [hwB, upd2_w1]; exact hd)]; rfl
    have hevs0 : evs0 (4 * s + 1) = [] := by unfold evs0; rw [hrun1, htk1, hqa]; rfl
    have hW : (world (4 * s + 2)).1 = Function.update (Function.update
        (world (4 * s + 1)).1 w0 st0) w1 st1' := by
      rw [world_succ, hevs0]; change (run1 _).1 = _; rw [hrun1, hwB, Function.update_idem]
    refine ⟨forall_y ?_ ?_, queue_step hq (by rw [htk1, qOf_report hs h10]; rfl), ?_⟩
    · rw [hW, upd2_w0]
      exact good_of_report hs hn0 (cnt_report0 hs h10)
    · rw [hW, upd2_w1]
      exact good_of_report hs hn1' (cnt_report1 hs h10)
    · unfold segsSk; rw [segs_eq, hrun1, hevs0, htk0, htk1, plan_four1_row hs h10]; rfl
  · have h0 := (tick_report_old hs h10 (hw w0))
    have h1 := (tick_report_old hs h10 (hw w1))
    obtain ⟨hW, hQ, hS⟩ := step_ticks (l0 := [.fg (.attest (blk s) none)])
      (l1 := [.fg (.attest (blk s) none)]) h0.1 h1.1 rfl rfl hq hqa
      (by rw [qOf_of (by omega)]; rfl)
    refine ⟨forall_y ?_ ?_, hQ, by rw [hS, plan_four1 hs h10]; rfl⟩
    · rw [hW, upd2_w0]; exact h0.2
    · rw [hW, upd2_w1]; exact h1.2

/-- **The step of time `t_s + 2`**, `s ≥ 1`: the confirmation updates of slot `s − 1`. -/
theorem step_four2 {s : Nat} (hs : 1 ≤ s) (hw : WorldGood (4 * s + 2))
    (hq : QueueGood (4 * s + 2)) :
    WorldGood (4 * s + 3) ∧ QueueGood (4 * s + 3) ∧ segsSk (4 * s + 2) = plan (4 * s + 2) := by
  obtain ⟨A0, h0, hg0⟩ := tick_update hs (hw w0)
  obtain ⟨A1, h1, hg1⟩ := tick_update hs (hw w1)
  rw [← List.append_nil [Cut.ac _, Cut.ac _]] at h0 h1
  obtain ⟨hW, hQ, hS⟩ := step_ticks h0 h1 rfl rfl hq
    (qa_nil hq (by omega)) (by rw [qOf_of (by omega)]; rfl)
  refine ⟨forall_y ?_ ?_, hQ, by rw [hS, plan_quiet (by omega) (by omega) (by omega)]; rfl⟩
  · rw [hW, upd2_w0]; exact hg0
  · rw [hW, upd2_w1]; exact hg1

/-- **The step of time `t_s + 3`**, `s ≥ 1`: two ticks with nothing to do. -/
theorem step_four3 {s : Nat} (hs : 1 ≤ s) (hw : WorldGood (4 * s + 3))
    (hq : QueueGood (4 * s + 3)) :
    WorldGood (4 * s + 4) ∧ QueueGood (4 * s + 4) ∧ segsSk (4 * s + 3) = plan (4 * s + 3) := by
  rw [plan_quiet (by omega) (by omega) (by omega)]
  refine step_quiet hw hq (by omega) (by omega) (by omega) (by rw [tip_four3, rep_four3])
    (by rw [tip_four3, rep_four3]) (qa_nil hq (by omega))
    (qOf_of (by omega)) ?_
  intro y st h
  refine good_congr ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · rw [tip_four3]; unfold tip; omega
  · unfold cnt
    rw [nrw_succ_of (t := 4 * s + 3) (by omega), nrv_succ_of (t := 4 * s + 3) (by omega)]
  · rw [nrw_succ_of (t := 4 * s + 3) (by omega)]
  · unfold vsT; rw [tip_four3, show 4 * s + 3 + 1 = 4 * (s + 1) by ring, tip_four]
    split_ifs <;> first | rfl | omega
  · funext σ; unfold poolT; rw [tip_four3, show 4 * s + 3 + 1 = 4 * (s + 1) by ring, tip_four]
    simp only [Nat.add_sub_cancel]; split_ifs <;> first | rfl | omega
  · rw [rep_four3]; unfold rep; omega
  · rw [nsv_four3]; unfold nsv; omega

theorem worldGood_zero : WorldGood 0 := fun y => good_init y

theorem queueGood_zero : QueueGood 0 := fun _ => rfl

/-- **The step of every time.** -/
theorem step_time (t : Nat) (hw : WorldGood t) (hq : QueueGood t) :
    WorldGood (t + 1) ∧ QueueGood (t + 1) ∧ segsSk t = plan t := by
  obtain ⟨s, r, hr, rfl⟩ : ∃ s r, r < 4 ∧ t = 4 * s + r := ⟨t / 4, t % 4, by omega, by omega⟩
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl
    · exact step_small (Or.inl rfl) hw hq
    · exact step_one hw hq
    · exact step_small (Or.inr (Or.inl rfl)) hw hq
    · exact step_small (Or.inr (Or.inr rfl)) hw hq
  · rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl
    · exact step_four hs hw hq
    · exact step_four1 hs hw hq
    · exact step_four2 hs hw hq
    · exact step_four3 hs hw hq

theorem world_good_queue : ∀ t, WorldGood t ∧ QueueGood t
  | 0 => ⟨worldGood_zero, queueGood_zero⟩
  | t + 1 => by
    obtain ⟨hw, hq⟩ := world_good_queue t
    obtain ⟨hw', hq', -⟩ := step_time t hw hq
    exact ⟨hw', hq'⟩

/-- **The states of the run**: before every time both nodes are in the state `Good`. -/
theorem world_good : ∀ t y, Good ((world t).1 y) y t := fun t => (world_good_queue t).1

/-- **The queue of `v1`'s rows.** -/
theorem world_queue_eq (t t' : Nat) : (world t).2 t' = if t' < t then qOf t' else [] :=
  (world_good_queue t).2 t'

/-- **The events of every time** have the shape `plan t`. -/
theorem segs_plan (t : Nat) : segsSk t = plan t :=
  (step_time t (world_good_queue t).1 (world_good_queue t).2).2.2

/-! ## Cuts by the shape -/

theorem segs_get_plan {t j : Nat} {sg : Seg} (hs : (segs t)[j]? = some sg) :
    (plan t)[j]? = some (sg.node, sg.ev, sg.cuts.map sk) := by
  rw [← segs_plan, segsSk, List.getElem?_map, hs]; rfl

theorem plan_get_segs {t j : Nat} {p : Fin sp.n × Node.Event N × List Sk}
    (hp : (plan t)[j]? = some p) :
    ∃ sg, (segs t)[j]? = some sg ∧ p = (sg.node, sg.ev, sg.cuts.map sk) := by
  rw [← segs_plan, segsSk, List.getElem?_map] at hp
  rcases hs : (segs t)[j]? with _ | sg
  · rw [hs] at hp; cases hp
  · rw [hs] at hp; exact ⟨sg, rfl, (Option.some.inj hp).symm⟩

/-- **The label of a cut**, by the shape: cut `k` of segment `j` of time `t`. -/
theorem label_sk (t j k : Nat) (hj : j < 128) (hk : k < 8) :
    (run.label (1024 * t + 8 * j + k)).map sk = ((plan t)[j]?).bind fun p => p.2.2[k]? := by
  rw [run_label t j k hj hk]
  rcases hs : (segs t)[j]? with _ | sg
  · rw [← segs_plan, segsSk, List.getElem?_map, hs]; rfl
  · rw [segs_get_plan hs]
    simp only [Option.bind_some, List.getElem?_map]

/-- The node of a cut of segment `j` of time `t`, by the shape. -/
theorem node_plan {t j k : Nat} (hj : j < 128) (hk : k < 8)
    {p : Fin sp.n × Node.Event N × List Sk} (hp : (plan t)[j]? = some p) :
    run.node (1024 * t + 8 * j + k) = p.1 := by
  obtain ⟨sg, hs, rfl⟩ := plan_get_segs hp
  exact run_node hj hk hs

/-- A cut of the shape is a labelled cut of the run with that frameless form. -/
theorem label_at {t j k : Nat} (hj : j < 128) (hk : k < 8)
    {p : Fin sp.n × Node.Event N × List Sk} (hp : (plan t)[j]? = some p) {c : Sk}
    (hc : p.2.2[k]? = some c) :
    ∃ c', run.label (1024 * t + 8 * j + k) = some c' ∧ sk c' = c ∧
      run.node (1024 * t + 8 * j + k) = p.1 ∧ run.time (1024 * t + 8 * j + k) = (t : Int) := by
  have h := label_sk t j k hj hk
  rw [hp, Option.bind_some, hc] at h
  rcases hl : run.label (1024 * t + 8 * j + k) with _ | c'
  · rw [hl] at h; cases h
  · rw [hl] at h
    exact ⟨c', rfl, Option.some.inj h, node_plan hj hk hp, run_time t j k hj hk⟩

/-- A labelled cut of the run is a cut of the shape. -/
theorem sk_of_label {i : Nat} {c : Cut N} (h : run.label i = some c) :
    ∃ t j k p, j < 128 ∧ k < 8 ∧ i = 1024 * t + 8 * j + k ∧ (plan t)[j]? = some p ∧
      p.2.2[k]? = some (sk c) ∧ run.node i = p.1 ∧ run.time i = (t : Int) := by
  obtain ⟨t, j, k, hj, hk, rfl⟩ := cut_decomp i
  have h' := label_sk t j k hj hk
  rw [h, Option.map_some] at h'
  rcases hp : (plan t)[j]? with _ | p
  · rw [hp] at h'; cases h'
  · rw [hp, Option.bind_some] at h'
    exact ⟨t, j, k, p, hj, hk, rfl, hp, h'.symm, node_plan hj hk hp, run_time t j k hj hk⟩

/-! ## The pools at every cut -/

theorem atts_onAttestation' (fg : Store sp.toParams N.Payload) (a : FG.Att sp.n) :
    fg.atts ⊆ (fg.onAttestation a).atts := by
  unfold Store.onAttestation
  split_ifs
  · exact fun _ h => h
  · exact List.subset_append_left _ _

theorem atts_addAtts' (fg : Store sp.toParams N.Payload) (l : List (FG.Att sp.n)) :
    fg.atts ⊆ (fg.addAtts l).atts := by
  induction l generalizing fg with
  | nil => exact fun _ h => h
  | cons a l ih =>
    rw [Store.addAtts, List.foldl_cons, ← Store.addAtts]
    exact fun b hb => ih _ (atts_onAttestation' fg a hb)

theorem atts_onBlock' {fg fg' : Store sp.toParams N.Payload} {B : N.Blk}
    (h : fg.onBlock B = some fg') : fg.atts ⊆ fg'.atts := by
  obtain ⟨-, σ', -, -, -, -, -, rfl⟩ := Store.onBlock_eq_some h
  intro a ha
  refine atts_addAtts' _ _ ?_
  rw [(Store.updateFinality_spec _ _).2.2.1]
  exact ha

theorem plan_no_restart (t : Nat) :
    ∀ p ∈ plan t, ∀ c ∈ p.2.2, ∀ es, c ≠ .ac .restart es := by
  unfold plan
  split_ifs <;> simp [tickSk]

/-- No cut of the run is a restart. -/
theorem label_not_restart {i : Nat} {ℓ : ACLabel N} (h : run.label i = some (.ac ℓ)) :
    ℓ.call ≠ .restart := by
  obtain ⟨t, j, k, p, -, -, -, hp, hk, -, -⟩ := sk_of_label h
  intro hr
  refine plan_no_restart t p (List.mem_of_getElem? hp) _ (List.mem_of_getElem? hk)
    (ℓ.emits.map (·.msg)) ?_
  rw [sk, hr]

/-- A cut grows the pools. -/
theorem cutStep_mono {y : Fin sp.n} {t : Time} {st st' : St} {c : Cut N}
    (h : CutStep y t st c st') (hnr : ∀ ℓ, c = .ac ℓ → ℓ.call ≠ .restart) :
    (∀ σ, st.ac.pool σ ⊆ st'.ac.pool σ) ∧ st.fg.atts ⊆ st'.fg.atts := by
  cases c with
  | ac ℓ =>
    obtain ⟨-, hs, hfg, -⟩ := h
    refine ⟨fun σ => ?_, by rw [hfg]⟩
    have := SA.step_pool_subset (ro := ro) y st.ac ℓ.frame t ℓ.call (hnr ℓ rfl) σ
    change st.ac.pool σ ⊆ (N.step y st.ac ℓ.frame t ℓ.call).1.pool σ at this
    rw [hs] at this; exact this
  | fg ℓ =>
    cases ℓ with
    | block B acc =>
      cases acc with
      | false => obtain ⟨-, rfl⟩ := h; exact ⟨fun _ => fun _ h => h, fun _ h => h⟩
      | true =>
        obtain ⟨-, hb, hac, -⟩ := h
        exact ⟨fun σ => by rw [hac], atts_onBlock' hb⟩
    | attestation a =>
      obtain ⟨hfg, hac, -⟩ := h
      exact ⟨fun σ => by rw [hac], by rw [hfg]; exact atts_onAttestation' _ _⟩
    | attest C sg =>
      cases sg with
      | none => obtain ⟨-, rfl⟩ := h; exact ⟨fun _ => fun _ h => h, fun _ h => h⟩
      | some a =>
        obtain ⟨-, hfg, hac⟩ := h
        exact ⟨fun σ => by rw [hac], by rw [hfg]⟩

/-- The pools of a node only grow along the run. -/
theorem state_mono (y : Fin sp.n) {i : Nat} :
    ∀ {i'}, i ≤ i' → (∀ σ, (run.state y i).ac.pool σ ⊆ (run.state y i').ac.pool σ) ∧
      (run.state y i).fg.atts ⊆ (run.state y i').fg.atts := by
  intro i' h
  induction i', h using Nat.le_induction with
  | base => exact ⟨fun _ => fun _ h => h, fun _ h => h⟩
  | succ i' _ ih =>
    simp only [Trace.state]
    split_ifs with hc
    · obtain ⟨hn, hl⟩ := hc
      obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 hl
      have hcs := run_cutStep (y := y) ⟨hn, hc⟩
      obtain ⟨h1, h2⟩ := cutStep_mono hcs (fun ℓ he => label_not_restart (by rw [hc, he]))
      exact ⟨fun σ => List.Subset.trans (ih.1 σ) (h1 σ), List.Subset.trans ih.2 h2⟩
    · exact ih

/-- The state before the first cut of time `t` is the world of `t`. -/
theorem state_start (y : Fin sp.n) (t : Nat) : run.state y (1024 * t) = (world t).1 y := by
  rw [run_state]
  unfold preState
  rw [show 1024 * t = 1024 * t + 8 * 0 + 0 by ring, segOf_eq t 0 0 (by omega) (by omega),
    segs_zero]
  dsimp only
  rw [show (1024 * t + 8 * 0 + 0) % 8 = 0 by omega]
  split_ifs with h
  · subst h; rfl
  · rfl

/-- The state after a labelled cut, by its node. -/
theorem post_state {i : Nat} (hl : run.label i ≠ none) :
    run.post i = run.state (run.node i) (i + 1) := by
  simp only [Trace.state, true_and]; exact (ite_eq_left hl).symm

theorem time_lt {i : Nat} : i < 1024 * ((i / 1024 : Nat) + 1) := by omega

theorem pools_end (y : Fin sp.n) (i : Nat) :
    (∀ σ, (run.state y i).ac.pool σ ⊆ ((world (i / 1024 + 1)).1 y).ac.pool σ) ∧
      (run.state y i).fg.atts ⊆ ((world (i / 1024 + 1)).1 y).fg.atts := by
  rw [← state_start]; exact state_mono y (by omega)

theorem pools_start (y : Fin sp.n) (i : Nat) :
    (∀ σ, ((world (i / 1024)).1 y).ac.pool σ ⊆ (run.state y i).ac.pool σ) ∧
      ((world (i / 1024)).1 y).fg.atts ⊆ (run.state y i).fg.atts := by
  rw [← state_start]; exact state_mono y (by omega)

theorem run_time_nat (i : Nat) : run.time i = ((i / 1024 : Nat) : Int) := rfl

theorem poolT_sub {y : Fin sp.n} {t σ : Nat} {v : Vote sp.n} (h : v ∈ poolT y (t + 1) σ) :
    ∃ z, v = vote z σ ∧ vt σ ≤ t := by
  unfold poolT at h
  split_ifs at h with h1
  · have : vt σ ≤ t := by unfold vt tip at *; split_ifs <;> omega
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact ⟨y, rfl, this⟩
    · exact ⟨other y, rfl, this⟩
  · cases h

theorem poolT_full (y z : Fin sp.n) {t σ : Nat} (h : vt σ < t) : vote z σ ∈ poolT y t σ := by
  unfold poolT
  rw [ite_eq_left ⟨by unfold vt at h; split_ifs at h <;> omega,
    by unfold vt tip at *; split_ifs at h <;> omega⟩]
  rcases fin2_cases z y with rfl | rfl
  · exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)

/-- The rows of `y`'s pool before time `t`: exactly those received before `t`. -/
theorem mem_poolOf_cnt {y : Fin sp.n} {t : Nat} {a : FG.Att sp.n} :
    a ∈ poolOf y (cnt y t) ↔ ∃ z q, 1 ≤ q ∧ a = row z q ∧ rowRecv y z q < t := by
  rw [mem_poolOf]
  have hne : w0 ≠ w1 := Ne.symm w1_ne
  rcases eq_w0_or_w1 y with rfl | rfl
  · have hc : cnt w0 t = nrw t + nrv t := by unfold cnt; rw [ite_eq_left rfl]
    constructor
    · rintro ⟨i, hi, rfl⟩
      unfold poolAt
      by_cases hp : i % 2 = 0
      · refine ⟨w0, i / 2 + 1, by omega, by rw [ite_eq_left hp], ?_⟩
        unfold rowRecv rt; rw [ite_eq_right (fun h => hne h.2)]
        rw [hc] at hi; unfold nrw nrv at hi; split_ifs at hi <;> omega
      · refine ⟨w1, i / 2 + 1, by omega, by rw [ite_eq_right hp, other_w0], ?_⟩
        unfold rowRecv rt; rw [ite_eq_left ⟨rfl, rfl⟩]
        rw [hc] at hi; unfold nrw nrv at hi; split_ifs at hi <;> omega
    · rintro ⟨z, q, hq, rfl, hr⟩
      rcases eq_w0_or_w1 z with rfl | rfl
      · unfold rowRecv rt at hr; rw [ite_eq_right (fun h => hne h.2)] at hr
        refine ⟨2 * (q - 1), ?_, ?_⟩
        · rw [hc]; unfold nrw nrv; split_ifs <;> omega
        · unfold poolAt; rw [ite_eq_left (by omega)]; congr 1; omega
      · unfold rowRecv rt at hr; rw [ite_eq_left ⟨rfl, rfl⟩] at hr
        refine ⟨2 * (q - 1) + 1, ?_, ?_⟩
        · rw [hc]; unfold nrw nrv; split_ifs <;> omega
        · unfold poolAt; rw [ite_eq_right (by omega), other_w0]; congr 1; omega
  · have hc : cnt w1 t = 2 * nrw t := by unfold cnt; rw [ite_eq_right w1_ne]
    have hrr : ∀ z q, rowRecv w1 z q = rt q := fun z q => by
      unfold rowRecv; rw [ite_eq_right (fun h => w1_ne h.1)]
    constructor
    · rintro ⟨i, hi, rfl⟩
      refine ⟨if i % 2 = 0 then w1 else other w1, i / 2 + 1, by omega, rfl, ?_⟩
      rw [hrr]; unfold rt; rw [hc] at hi; unfold nrw at hi; split_ifs at hi <;> omega
    · rintro ⟨z, q, hq, rfl, hr⟩
      rw [hrr] at hr; unfold rt at hr
      rcases eq_w0_or_w1 z with rfl | rfl
      · refine ⟨2 * (q - 1) + 1, ?_, ?_⟩
        · rw [hc]; unfold nrw; split_ifs <;> omega
        · unfold poolAt; rw [ite_eq_right (by omega), other_w1]; congr 1; omega
      · refine ⟨2 * (q - 1), ?_, ?_⟩
        · rw [hc]; unfold nrw; split_ifs <;> omega
        · unfold poolAt; rw [ite_eq_left (by omega)]; congr 1; omega

theorem pool_sub (y : Fin sp.n) (i σ : Nat) {v : Vote sp.n}
    (hv : v ∈ (run.state y i).ac.pool σ) :
    ∃ z, v = vote z σ ∧ ((vt σ : Nat) : Int) ≤ run.time i := by
  have h := (pools_end y i).1 σ hv
  rw [((world_good _ y).ac.pool)] at h
  obtain ⟨z, rfl, hz⟩ := poolT_sub h
  exact ⟨z, rfl, by rw [run_time_nat]; omega⟩

theorem post_pool_sub (i σ : Nat) (hl : run.label i ≠ none) {v : Vote sp.n}
    (hv : v ∈ (run.post i).ac.pool σ) :
    ∃ z, v = vote z σ ∧ ((vt σ : Nat) : Int) ≤ run.time i := by
  rw [post_state hl] at hv
  have h := (state_mono (run.node i) (i := i + 1) (i' := 1024 * ((i / 1024 : Nat) + 1))
    (by omega)).1 σ hv
  rw [state_start, ((world_good _ _).ac.pool)] at h
  obtain ⟨z, rfl, hz⟩ := poolT_sub h
  exact ⟨z, rfl, by rw [run_time_nat]; omega⟩

theorem pool_full (y z : Fin sp.n) (i σ : Nat) (h : ((vt σ : Nat) : Int) < run.time i) :
    vote z σ ∈ (run.state y i).ac.pool σ := by
  refine (pools_start y i).1 σ ?_
  rw [((world_good _ y).ac.pool)]
  rw [run_time_nat] at h
  exact poolT_full y z (by omega)

theorem atts_sub (y : Fin sp.n) (i : Nat) {a : FG.Att sp.n} (ha : a ∈ (run.state y i).fg.atts) :
    ∃ z q, 1 ≤ q ∧ a = row z q ∧ ((rowRecv y z q : Nat) : Int) ≤ run.time i := by
  have h := (pools_end y i).2 ha
  rw [(world_good _ y).atts] at h
  obtain ⟨z, q, hq, rfl, hr⟩ := mem_poolOf_cnt.1 h
  exact ⟨z, q, hq, rfl, by rw [run_time_nat]; omega⟩

theorem post_atts_sub (i : Nat) (hl : run.label i ≠ none) {a : FG.Att sp.n}
    (ha : a ∈ (run.post i).fg.atts) :
    ∃ z q, 1 ≤ q ∧ a = row z q ∧ ((rowRecv (run.node i) z q : Nat) : Int) ≤ run.time i := by
  rw [post_state hl] at ha
  have h := (state_mono (run.node i) (i := i + 1) (i' := 1024 * ((i / 1024 : Nat) + 1))
    (by omega)).2 ha
  rw [state_start, (world_good _ _).atts] at h
  obtain ⟨z, q, hq, rfl, hr⟩ := mem_poolOf_cnt.1 h
  exact ⟨z, q, hq, rfl, by rw [run_time_nat]; omega⟩

theorem atts_full (y z : Fin sp.n) (q i : Nat) (hq : 1 ≤ q)
    (h : ((rowRecv y z q : Nat) : Int) < run.time i) : row z q ∈ (run.state y i).fg.atts := by
  refine (pools_start y i).2 ?_
  rw [(world_good _ y).atts]
  rw [run_time_nat] at h
  exact mem_poolOf_cnt.2 ⟨z, q, hq, rfl, by omega⟩

end Consensus.Goldilocks.Witness.TwoRun

end

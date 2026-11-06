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

/-! ## The step of a time (statements) -/

/-- The states of both nodes before time `t`. -/
def WorldGood (t : Nat) : Prop := ∀ y, Good ((world t).1 y) y t

/-- The queue of `v1`'s rows before time `t`. -/
def QueueGood (t : Nat) : Prop := ∀ t', (world t).2 t' = if t' < t then qOf t' else []

/-- **The step of times `0, 2, 3`**: two ticks with nothing to do. -/
theorem step_small {t : Nat} (ht : t = 0 ∨ t = 2 ∨ t = 3) (hw : WorldGood t) (hq : QueueGood t) :
    WorldGood (t + 1) ∧ QueueGood (t + 1) ∧ segsSk t = plan t := by
  sorry

/-- **The step of time `1`**: the votes of slot `0`. -/
theorem step_one (hw : WorldGood 1) (hq : QueueGood 1) :
    WorldGood 2 ∧ QueueGood 2 ∧ segsSk 1 = plan 1 := by
  sorry

/-- **The step of time `t_s`**, `s ≥ 1`: the proposal of `blk s`, the votes, and at `s ≡ 0 mod 10`
the delayed row of `v1`. -/
theorem step_four {s : Nat} (hs : 1 ≤ s) (hw : WorldGood (4 * s)) (hq : QueueGood (4 * s)) :
    WorldGood (4 * s + 1) ∧ QueueGood (4 * s + 1) ∧ segsSk (4 * s) = plan (4 * s) := by
  sorry

/-- **The step of time `t_s + 1`**, `s ≥ 1`: the reports to the FG and, at `s ≡ 1 mod 10`, the
rows. -/
theorem step_four1 {s : Nat} (hs : 1 ≤ s) (hw : WorldGood (4 * s + 1))
    (hq : QueueGood (4 * s + 1)) :
    WorldGood (4 * s + 2) ∧ QueueGood (4 * s + 2) ∧ segsSk (4 * s + 1) = plan (4 * s + 1) := by
  sorry

/-- **The step of time `t_s + 2`**, `s ≥ 1`: the confirmation updates of slot `s − 1`. -/
theorem step_four2 {s : Nat} (hs : 1 ≤ s) (hw : WorldGood (4 * s + 2))
    (hq : QueueGood (4 * s + 2)) :
    WorldGood (4 * s + 3) ∧ QueueGood (4 * s + 3) ∧ segsSk (4 * s + 2) = plan (4 * s + 2) := by
  sorry

/-- **The step of time `t_s + 3`**, `s ≥ 1`: two ticks with nothing to do. -/
theorem step_four3 {s : Nat} (hs : 1 ≤ s) (hw : WorldGood (4 * s + 3))
    (hq : QueueGood (4 * s + 3)) :
    WorldGood (4 * s + 4) ∧ QueueGood (4 * s + 4) ∧ segsSk (4 * s + 3) = plan (4 * s + 3) := by
  sorry

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

/-! ## The pools at every cut (statements) -/

/-- Every vote held before a cut is a vote of its slot, held from its vote time on. -/
theorem pool_sub (y : Fin sp.n) (i σ : Nat) {v : Vote sp.n}
    (hv : v ∈ (run.state y i).ac.pool σ) :
    ∃ z, v = vote z σ ∧ ((vt σ : Nat) : Int) ≤ run.time i := by
  sorry

/-- Every vote held after a cut, by the cut's node, is a vote of its slot, from its vote time on. -/
theorem post_pool_sub (i σ : Nat) (hl : run.label i ≠ none) {v : Vote sp.n}
    (hv : v ∈ (run.post i).ac.pool σ) :
    ∃ z, v = vote z σ ∧ ((vt σ : Nat) : Int) ≤ run.time i := by
  sorry

/-- After its vote time, both votes of a slot are held by both nodes. -/
theorem pool_full (y z : Fin sp.n) (i σ : Nat) (h : ((vt σ : Nat) : Int) < run.time i) :
    vote z σ ∈ (run.state y i).ac.pool σ := by
  sorry

/-- Every attestation held before a cut of `y` is a row, held from its receipt time at `y` on. -/
theorem atts_sub (y : Fin sp.n) (i : Nat) {a : FG.Att sp.n} (ha : a ∈ (run.state y i).fg.atts) :
    ∃ z q, 1 ≤ q ∧ a = row z q ∧ ((rowRecv y z q : Nat) : Int) ≤ run.time i := by
  sorry

/-- Every attestation held after a cut, by the cut's node, is a row, from its receipt time on. -/
theorem post_atts_sub (i : Nat) (hl : run.label i ≠ none) {a : FG.Att sp.n}
    (ha : a ∈ (run.post i).fg.atts) :
    ∃ z q, 1 ≤ q ∧ a = row z q ∧ ((rowRecv (run.node i) z q : Nat) : Int) ≤ run.time i := by
  sorry

/-- After its receipt time at `y`, every row is held by `y`. -/
theorem atts_full (y z : Fin sp.n) (q i : Nat) (hq : 1 ≤ q)
    (h : ((rowRecv y z q : Nat) : Int) < run.time i) : row z q ∈ (run.state y i).fg.atts := by
  sorry

end Consensus.Goldilocks.Witness.TwoRun

end

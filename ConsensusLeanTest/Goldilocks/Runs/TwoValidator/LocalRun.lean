module
public import ConsensusLeanTest.Goldilocks.Runs.TwoValidator.World
@[expose] public section

/-! # The healthy two-validator run is a Goldilocks run

`run_goldilocksRun`: the run of `TwoValidator.Run` is a `GoldilocksRun` with both validators
honest, read off the shape of its events (`plan`, `segs_plan`, `label_at`, `sk_of_label`):

* **Bookkeeping laws** (`run_localRun`): the cut law and the groups are the run's construction
  (`run_cutStep`, `group_seg`, `groupAt_seg`); every time has the ticks of `v0` and `v1` as its
  segments `0` and `1` and only deliveries after them (`seg_phase`, `seg_node`), so the phases
  are in order and each node ticks exactly once at every time (`tick_group`); both nodes are awake
  from `0` on and nobody restarts (`plan_no_restart`).
* **Wire and credentials**: a delivered block is a chain block `blk s`, `s ≥ 1`, proposed by
  `v0` (`plan_ev`); a delivered attestation is a row.
* **Unforgeability**: every processed object is located in the shape after the cut that made it:
  `blk s` after `v0`'s own call at `t_s` (`plan_fgBlock`, `own_blk`), a row after its signing at
  `rt q` (`plan_fgAtt`, `sign_row`), a vote, received or carried, after its emission
  (`plan_msg`, `emitIdx`, `emit_vote`). -/

namespace Consensus.Goldilocks.Witness.TwoRun

open SA Node

/-! ## The shape, cut by cut -/

/-- The residues of a time, by the shape of its events. -/
theorem plan_cases (Q : Nat → Prop) (h1 : Q 1) (h4 : ∀ s, 1 ≤ s → Q (4 * s))
    (h4r : ∀ s, 1 ≤ s → s % 10 = 1 → Q (4 * s + 1))
    (h41 : ∀ s, 1 ≤ s → s % 10 ≠ 1 → Q (4 * s + 1))
    (hq : ∀ t, plan t = [(w0, .tick 0, tickSk []), (w1, .tick 0, tickSk [])] → Q t) (t : Nat) :
    Q t := by
  by_cases t1 : t = 1
  · exact t1 ▸ h1
  by_cases t4 : t % 4 = 0 ∧ 4 ≤ t
  · obtain ⟨s, rfl⟩ : ∃ s, t = 4 * s := ⟨t / 4, by omega⟩
    exact h4 s (by omega)
  by_cases t41 : t % 4 = 1 ∧ 4 ≤ t
  · obtain ⟨s, rfl⟩ : ∃ s, t = 4 * s + 1 := ⟨t / 4, by omega⟩
    by_cases h : s % 10 = 1
    · exact h4r s (by omega) h
    · exact h41 s (by omega) h
  exact hq t (plan_quiet t1 t4 t41)

/-- Every event of the shape makes a cut. -/
theorem plan_ne {t j : Nat} {p : Fin sp.n × Node.Event N × List Sk}
    (hp : (plan t)[j]? = some p) : p.2.2 ≠ [] := by
  induction t using plan_cases with
  | h1 =>
    rw [plan_one] at hp
    rcases j with _ | _ | _ | _ | j <;> simp at hp <;> subst hp <;> simp [tickSk]
  | h4 s hs =>
    rw [plan_four hs] at hp
    split_ifs at hp <;>
    rcases j with _ | _ | _ | _ | _ | _ | j <;> simp at hp <;> subst hp <;> simp [tickSk]
  | h4r s hs h10 =>
    rw [plan_four1_row hs h10] at hp
    rcases j with _ | _ | _ | j <;> simp at hp <;> subst hp <;> simp [tickSk]
  | h41 s hs h10 =>
    rw [plan_four1 hs h10] at hp
    rcases j with _ | _ | j <;> simp at hp <;> subst hp <;> simp [tickSk]
  | hq t h =>
    rw [h] at hp
    rcases j with _ | _ | j <;> simp at hp <;> subst hp <;> simp [tickSk]

theorem w0_val : w0.val = 0 := rfl

theorem w1_val : w1.val = 1 := rfl

/-- The events of the shape: deliveries from segment `2` on, of chain blocks and rows. -/
theorem plan_ev {t j : Nat} {p : Fin sp.n × Node.Event N × List Sk}
    (hp : (plan t)[j]? = some p) :
    (2 ≤ j → p.2.1.phase = 2) ∧ (∀ B, p.2.1 = .block B → ∃ s, 1 ≤ s ∧ B = blk s) ∧
      ∀ a, p.2.1 = .attestation a → ∃ z q, 1 ≤ q ∧ a = row z q := by
  induction t using plan_cases with
  | h1 =>
    rw [plan_one] at hp
    rcases j with _ | _ | _ | _ | j <;> simp at hp <;> subst hp <;> simp [Event.phase]
  | h4 s hs =>
    rw [plan_four hs] at hp
    split_ifs at hp with h10 <;>
    rcases j with _ | _ | _ | _ | _ | _ | j <;> simp at hp <;> subst hp <;>
      simp [Event.phase] <;> first | exact ⟨s, hs, rfl⟩ | exact ⟨w1, s / 10, by omega, rfl⟩
  | h4r s hs h10 =>
    rw [plan_four1_row hs h10] at hp
    rcases j with _ | _ | _ | j <;> simp at hp <;> subst hp <;> simp [Event.phase]
    exact ⟨w0, hgt s, hgt_pos s, rfl⟩
  | h41 s hs h10 =>
    rw [plan_four1 hs h10] at hp
    rcases j with _ | _ | j <;> simp at hp <;> subst hp <;> simp [Event.phase]
  | hq t h =>
    rw [h] at hp
    rcases j with _ | _ | j <;> simp at hp <;> subst hp <;> simp [Event.phase]

/-- A block call of the shape: `blk s` at `t_s`, after `v0`'s proposal step. -/
theorem plan_fgBlock {t j k : Nat} {p : Fin sp.n × Node.Event N × List Sk}
    (hp : (plan t)[j]? = some p) {B : N.Blk} {acc : Bool}
    (hc : p.2.2[k]? = some (.fg (.block B acc))) :
    ∃ s, 1 ≤ s ∧ t = 4 * s ∧ B = blk s ∧ 2 ≤ 8 * j + k := by
  induction t using plan_cases with
  | h1 =>
    rw [plan_one] at hp
    rcases j with _ | _ | _ | _ | j <;> simp at hp <;> subst hp <;>
      rcases k with _ | _ | _ | _ | _ | _ | k <;> simp [tickSk] at hc
  | h4 s hs =>
    rw [plan_four hs] at hp
    split_ifs at hp with h10 <;>
    rcases j with _ | _ | _ | _ | _ | _ | j <;> simp at hp <;> subst hp <;>
      rcases k with _ | _ | _ | _ | _ | _ | k <;> simp [tickSk] at hc <;>
      exact ⟨s, hs, rfl, hc.1.symm, by omega⟩
  | h4r s hs h10 =>
    rw [plan_four1_row hs h10] at hp
    rcases j with _ | _ | _ | j <;> simp at hp <;> subst hp <;>
      rcases k with _ | _ | _ | _ | _ | _ | k <;> simp [tickSk] at hc
  | h41 s hs h10 =>
    rw [plan_four1 hs h10] at hp
    rcases j with _ | _ | j <;> simp at hp <;> subst hp <;>
      rcases k with _ | _ | _ | _ | _ | _ | k <;> simp [tickSk] at hc
  | hq t h =>
    rw [h] at hp
    rcases j with _ | _ | j <;> simp at hp <;> subst hp <;>
      rcases k with _ | _ | _ | _ | _ | _ | k <;> simp [tickSk] at hc

/-- An attestation call of the shape: a row, after its signing cut. -/
theorem plan_fgAtt {t j k : Nat} {p : Fin sp.n × Node.Event N × List Sk}
    (hp : (plan t)[j]? = some p) {a : FG.Att sp.n}
    (hc : p.2.2[k]? = some (.fg (.attestation a))) :
    ∃ z q, 1 ≤ q ∧ a = row z q ∧ 1024 * rt q + 8 * z.val + 2 < 1024 * t + 8 * j + k := by
  induction t using plan_cases with
  | h1 =>
    rw [plan_one] at hp
    rcases j with _ | _ | _ | _ | j <;> simp at hp <;> subst hp <;>
      rcases k with _ | _ | _ | _ | _ | _ | k <;> simp [tickSk] at hc
  | h4 s hs =>
    rw [plan_four hs] at hp
    split_ifs at hp with h10 <;>
    rcases j with _ | _ | _ | _ | _ | _ | j <;> simp at hp <;> subst hp <;>
      rcases k with _ | _ | _ | _ | _ | _ | k <;> simp [tickSk] at hc
    exact ⟨w1, s / 10, by omega, hc.symm, by rw [w1_val]; unfold rt; omega⟩
  | h4r s hs h10 =>
    rw [plan_four1_row hs h10] at hp
    rcases j with _ | _ | _ | j <;> simp at hp <;> subst hp <;>
      rcases k with _ | _ | _ | _ | _ | _ | k <;> simp [tickSk] at hc
    all_goals first
      | exact ⟨w0, hgt s, hgt_pos s, hc.symm, by rw [w0_val]; unfold rt hgt; split_ifs <;> omega⟩
      | exact ⟨w1, hgt s, hgt_pos s, hc.symm, by rw [w1_val]; unfold rt hgt; split_ifs <;> omega⟩
  | h41 s hs h10 =>
    rw [plan_four1 hs h10] at hp
    rcases j with _ | _ | j <;> simp at hp <;> subst hp <;>
      rcases k with _ | _ | _ | _ | _ | _ | k <;> simp [tickSk] at hc
  | hq t h =>
    rw [h] at hp
    rcases j with _ | _ | j <;> simp at hp <;> subst hp <;>
      rcases k with _ | _ | _ | _ | _ | _ | k <;> simp [tickSk] at hc

/-- The cut that emits the vote of `z` in slot `σ`: the tick at time `1` for slot `0`; for
`σ ≥ 1`, position `3` of `v0`'s tick at `t_σ` and position `1` of `v1`'s receipt of `blk σ`
(segment `2`). -/
def emitIdx (z : Fin sp.n) (σ : Nat) : Nat :=
  if σ = 0 then 1024 + 8 * z.val else 1024 * (4 * σ) + 3 + 14 * z.val

/-- An AC message call of the shape: a vote, after its emission. -/
theorem plan_msg {t j k : Nat} {p : Fin sp.n × Node.Event N × List Sk}
    (hp : (plan t)[j]? = some p) {m : Vote sp.n} {es : List (Vote sp.n)}
    (hc : p.2.2[k]? = some (.ac (.message m) es)) :
    ∃ z σ, m = vote z σ ∧ emitIdx z σ < 1024 * t + 8 * j + k := by
  induction t using plan_cases with
  | h1 =>
    rw [plan_one] at hp
    rcases j with _ | _ | _ | _ | j <;> simp at hp <;> subst hp <;>
      rcases k with _ | _ | _ | _ | _ | _ | k <;> simp [tickSk] at hc
    · exact ⟨w0, 0, hc.1.symm, by unfold emitIdx; rw [w0_val]; split_ifs <;> omega⟩
    · exact ⟨w1, 0, hc.1.symm, by unfold emitIdx; rw [w1_val]; split_ifs <;> omega⟩
  | h4 s hs =>
    rw [plan_four hs] at hp
    split_ifs at hp with h10 <;>
    rcases j with _ | _ | _ | _ | _ | _ | j <;> simp at hp <;> subst hp <;>
      rcases k with _ | _ | _ | _ | _ | _ | k <;> simp [tickSk] at hc
    all_goals first
      | exact ⟨w0, s, hc.1.symm, by unfold emitIdx; rw [w0_val]; split_ifs <;> omega⟩
      | exact ⟨w1, s, hc.1.symm, by unfold emitIdx; rw [w1_val]; split_ifs <;> omega⟩
  | h4r s hs h10 =>
    rw [plan_four1_row hs h10] at hp
    rcases j with _ | _ | _ | j <;> simp at hp <;> subst hp <;>
      rcases k with _ | _ | _ | _ | _ | _ | k <;> simp [tickSk] at hc
  | h41 s hs h10 =>
    rw [plan_four1 hs h10] at hp
    rcases j with _ | _ | j <;> simp at hp <;> subst hp <;>
      rcases k with _ | _ | _ | _ | _ | _ | k <;> simp [tickSk] at hc
  | hq t h =>
    rw [h] at hp
    rcases j with _ | _ | j <;> simp at hp <;> subst hp <;>
      rcases k with _ | _ | _ | _ | _ | _ | k <;> simp [tickSk] at hc

/-! ## Cuts of the run from the shape -/

/-- A cut with the frameless form of an FG call is that call. -/
theorem sk_eq_fg {c : Cut N} {ℓ : FGLabel sp.toParams N.Payload} (h : sk c = .fg ℓ) :
    c = .fg ℓ := by
  cases c with
  | fg ℓ' => cases h; rfl
  | ac ℓ' => cases h

/-- A cut with the frameless form of an AC call is an AC call with that call and those
emissions. -/
theorem sk_eq_ac {c : Cut N} {call : N.Call} {es : List (Vote sp.n)} (h : sk c = .ac call es) :
    ∃ ℓ : ACLabel N, c = .ac ℓ ∧ ℓ.call = call ∧ ℓ.emits.map (·.msg) = es := by
  cases c with
  | fg ℓ' => cases h
  | ac ℓ' => cases h; exact ⟨ℓ', rfl, rfl, rfl⟩

/-- A cut of the shape is a call of its node. -/
theorem call_of_plan {t j k i : Nat} (hj : j < 128) (hk : k < 8) (hi : i = 1024 * t + 8 * j + k)
    {p : Fin sp.n × Node.Event N × List Sk} (hp : (plan t)[j]? = some p) {c : Sk}
    (hc : p.2.2[k]? = some c) : ∃ c', run.CallAt p.1 i c' ∧ sk c' = c := by
  subst hi
  obtain ⟨c', hl, hs, hn, -⟩ := label_at hj hk hp hc
  exact ⟨c', ⟨hn, hl⟩, hs⟩

/-- An AC cut of the shape emits its messages. -/
theorem emit_of_plan {t j k i : Nat} (hj : j < 128) (hk : k < 8) (hi : i = 1024 * t + 8 * j + k)
    {p : Fin sp.n × Node.Event N × List Sk} (hp : (plan t)[j]? = some p) {call : N.Call}
    {es : List (Vote sp.n)} (hc : p.2.2[k]? = some (.ac call es)) {m : Vote sp.n}
    (hm : m ∈ es) : run.EmitAt p.1 i m := by
  obtain ⟨c', hcall, hs⟩ := call_of_plan hj hk hi hp hc
  obtain ⟨ℓ, rfl, -, hem⟩ := sk_eq_ac hs
  subst hem
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm
  exact ⟨ℓ, hcall, e, he, rfl⟩

/-- `v0`'s tick at `t_s`. -/
theorem plan_four_zero {s : Nat} (hs : 1 ≤ s) : (plan (4 * s))[0]? =
    some (w0, .tick 0, [.ac .tick [], .ac .proposal [], .fg (.block (blk s) true),
      .ac (.block (blk s)) [vote w0 s], .ac .toFG []]) := by
  rw [plan_four hs]; simp

/-- `v1`'s receipt of `blk s` at `t_s`. -/
theorem plan_four_two {s : Nat} (hs : 1 ≤ s) : (plan (4 * s))[2]? =
    some (w1, .block (blk s), [.fg (.block (blk s) true), .ac (.block (blk s)) [vote w1 s]]) := by
  rw [plan_four hs]; simp

/-- **The emission of every vote.** -/
theorem emit_vote (z : Fin sp.n) (σ : Nat) : run.EmitAt z (emitIdx z σ) (vote z σ) := by
  rcases Nat.eq_zero_or_pos σ with rfl | hσ
  · rcases eq_w0_or_w1 z with rfl | rfl
    · exact emit_of_plan (t := 1) (j := 0) (k := 0) (p := (w0, .tick 0, tickSk [vote w0 0]))
        (by omega) (by omega) rfl (by rw [plan_one]; rfl) rfl (List.mem_singleton_self _)
    · exact emit_of_plan (t := 1) (j := 1) (k := 0) (p := (w1, .tick 0, tickSk [vote w1 0]))
        (by omega) (by omega) rfl (by rw [plan_one]; rfl) rfl (List.mem_singleton_self _)
  · rcases eq_w0_or_w1 z with rfl | rfl
    · exact emit_of_plan (i := emitIdx w0 σ) (k := 3) (by omega) (by omega)
        (by unfold emitIdx; rw [w0_val, ite_eq_right (by omega)]) (plan_four_zero hσ) rfl
        (List.mem_singleton_self _)
    · exact emit_of_plan (i := emitIdx w1 σ) (k := 1) (by omega) (by omega)
        (by unfold emitIdx; rw [w1_val, ite_eq_right (by omega)]) (plan_four_two hσ) rfl
        (List.mem_singleton_self _)

/-- `z`'s tick at `rt q`, `q ≥ 1`: it signs `row z q` at position `2`. -/
theorem plan_sign (z : Fin sp.n) {q : Nat} (hq : 1 ≤ q) : ∃ s, rt q = 4 * s + 1 ∧
    (plan (4 * s + 1))[z.val]? = some (z, .tick 0, tickSk [] ++
      [.fg (.attest (blk s) (some (row z q))), .fg (.attestation (row z q))]) := by
  have hh : hgt (10 * (q - 1) + 1) = q := by rw [hgt, ite_eq_right (by omega)]; omega
  refine ⟨10 * (q - 1) + 1, by unfold rt; omega, ?_⟩
  rw [plan_four1_row (by omega) (by omega), hh]
  rcases eq_w0_or_w1 z with rfl | rfl <;> rfl

/-- **The signing of every row** `row z q`, `q ≥ 1`: at `rt q`, position `2` of `z`'s tick. -/
theorem sign_row (z : Fin sp.n) {q : Nat} (hq : 1 ≤ q) :
    run.SignAt z (1024 * rt q + 8 * z.val + 2) (row z q) := by
  obtain ⟨s, hrt, hp⟩ := plan_sign z hq
  obtain ⟨c', hcall, hsk⟩ := call_of_plan (i := 1024 * rt q + 8 * z.val + 2) (k := 2)
    (by have := z.isLt; change z.val < 2 at this; omega) (by omega) (by rw [hrt]) hp
    (c := .fg (.attest (blk s) (some (row z q)))) rfl
  rw [sk_eq_fg hsk] at hcall
  exact ⟨_, hcall⟩

/-- **`v0`'s own block** `blk s`, `s ≥ 1`: position `2` of its tick at `t_s`. -/
theorem own_blk {s : Nat} (hs : 1 ≤ s) : run.OwnBlockAt w0 (1024 * (4 * s) + 2) (blk s) := by
  obtain ⟨c', hcall, hsk⟩ := call_of_plan (i := 1024 * (4 * s) + 2) (k := 2) (by omega)
    (by omega) rfl (plan_four_zero hs) (c := .fg (.block (blk s) true)) rfl
  rw [sk_eq_fg hsk] at hcall
  exact ⟨⟨true, hcall⟩, by change (1024 * (4 * s) + 2) % 8 ≠ 0; omega⟩

/-! ## Segments and groups -/

/-- `normEv` keeps the phase. -/
theorem phase_normEv (e : Node.Event N) : (normEv e).phase = e.phase := by cases e <;> rfl

/-- Only a block delivery has the key of a block delivery. -/
theorem normEv_block {e : Node.Event N} {B : N.Blk} (h : normEv e = .block B) : e = .block B := by
  cases e <;> first | exact h | cases h

/-- Only an attestation delivery has the key of an attestation delivery. -/
theorem normEv_attestation {e : Node.Event N} {a : FG.Att sp.n} (h : normEv e = .attestation a) :
    e = .attestation a := by
  cases e <;> first | exact h | cases h

/-- Every segment makes a cut. -/
theorem seg_ne {t a : Nat} {sg : Seg} (hs : (segs t)[a]? = some sg) : sg.cuts ≠ [] := by
  intro h
  have := plan_ne (segs_get_plan hs)
  simp [h] at this

/-- The phase of a segment: the two ticks, then deliveries. -/
theorem seg_phase {t a : Nat} {sg : Seg} (hs : (segs t)[a]? = some sg) :
    (normEv sg.ev).phase = if a < 2 then 1 else 2 := by
  rcases (by omega : a = 0 ∨ a = 1 ∨ 2 ≤ a) with rfl | rfl | ha
  · rw [segs_zero] at hs; cases hs; rfl
  · rw [segs_one] at hs; cases hs; rfl
  · rw [ite_eq_right (by omega), phase_normEv]
    exact (plan_ev (segs_get_plan hs)).1 ha

/-- The node of a tick segment: `v0` at segment `0`, `v1` at segment `1`. -/
theorem seg_node {t a : Nat} {sg : Seg} (hs : (segs t)[a]? = some sg) (ha : a < 2) :
    sg.node.val = a := by
  rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl
  · rw [segs_zero] at hs; cases hs; rfl
  · rw [segs_one] at hs; cases hs; rfl

/-- **The tick of `y` at every time `n`**: segment `y.val`. -/
theorem tick_group (n : Nat) (y : Fin sp.n) :
    run.TickAt prop dg y (1024 * n + 8 * y.val) (n : Int) := by
  rcases eq_w0_or_w1 y with rfl | rfl
  · exact ⟨0, group_seg (by omega) (segs_zero n) (seg_ne (segs_zero n))⟩
  · exact ⟨0, group_seg (by omega) (segs_one n) (seg_ne (segs_one n))⟩

/-- A delivered block is a chain block `blk s`, `s ≥ 1`. -/
theorem group_block {y : Fin sp.n} {j0 : Nat} {tt : Time} {B : N.Blk}
    (h : run.GroupAt prop dg y j0 tt (.block B)) : ∃ s, 1 ≤ s ∧ B = blk s := by
  obtain ⟨t, a, sg, -, -, hs, -, -, he⟩ := groupAt_seg h
  exact (plan_ev (segs_get_plan hs)).2.1 B (normEv_block he.symm)

/-! ## The run is a run of the node -/

/-- **The two-validator run is a run of the node.** -/
theorem run_localRun : Node.LocalRun prop dg Set.univ (fun v : Vote sp.n => v.val) run where
  init _ _ := rfl
  grouped y _ i c hc := by
    obtain ⟨t, j, k, sg, hj, hk, rfl, hs, hck, hn⟩ := label_some hc.2
    have hy : sg.node = y := hn.symm.trans hc.1
    subst hy
    refine ⟨1024 * t + 8 * j, sg.ev, ?_⟩
    rw [run_time t j k hj hk]
    refine ⟨group_seg hj hs (seg_ne hs), by omega, ?_⟩
    have hst : run.state sg.node (1024 * t + 8 * j) = sg.pre sg.node := by
      simpa using run_state_seg hj (k := 0) (by omega) hs
    rw [hst, ← segs_cuts_eq hs]
    have := (List.getElem?_eq_some_iff.1 hck).1
    omega
  cutLaw _ _ _ _ hc := run_cutStep hc
  wire y _ j t e h := by
    obtain ⟨t', a, sg, -, -, hs, -, -, he⟩ := groupAt_seg h
    obtain ⟨-, hB, hA⟩ := plan_ev (segs_get_plan hs)
    cases e with
    | tick x => trivial
    | restart => trivial
    | message m => trivial
    | attestation a =>
      obtain ⟨z, q, hq, rfl⟩ := hA a (normEv_attestation he.symm)
      exact row_wellFormed z hq
    | block B =>
      obtain ⟨s, hs1, rfl⟩ := hB B (normEv_block he.symm)
      obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · unfold Block.RootOk
        rw [blk_root_succ, blk_parent_succ, blk_slot, blk_input]
      · intro a ha
        rcases mem_blk_fgPayload.1 ha with ⟨q, hq, -, rfl⟩ | ⟨q, hq, -, rfl⟩ <;>
          exact row_wellFormed _ hq
      · intro v hv
        change v ∈ blockVotes (blk (s + 1)) at hv
        rw [blockVotes_blk] at hv
        rw [blk_slot]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl <;> rfl
      · intro v hv
        change v ∈ blockSupport (blk (s + 1)) at hv
        change v ∈ blockVotes (blk (s + 1))
        rw [blockSupport_blk] at hv
        rw [blockVotes_blk]
        exact hv
  proposerCredential y _ j t B h := by
    obtain ⟨s, -, rfl⟩ := group_block h
    exact blk_proposer s
  time_nonneg i := by change (0 : Int) ≤ ((i / 1024 : Nat) : Int); omega
  time_mono a b h := by
    change ((a / 1024 : Nat) : Int) ≤ ((b / 1024 : Nat) : Int)
    exact Int.ofNat_le.2 (Nat.div_le_div_right h)
  finite T := by
    refine (Set.finite_Iio (1024 * (T.toNat + 1))).subset fun i hi => ?_
    have h1 : ((i / 1024 : Nat) : Int) ≤ T := hi.2
    have h2 := Int.self_le_toNat T
    simp only [Set.mem_Iio]
    omega
  phase_order y _ y' _ j j' t e e' h h' hlt := by
    obtain ⟨t1, a, sg, -, rfl, hs, -, ht1, he⟩ := groupAt_seg h
    obtain ⟨t2, b, sg', -, rfl, hs', -, ht2, he'⟩ := groupAt_seg h'
    have : t1 = t2 := by exact_mod_cast ht1.symm.trans ht2
    subst this
    rw [← phase_normEv e, ← phase_normEv e', he, he', seg_phase hs, seg_phase hs']
    split_ifs <;> omega
  tick_public _ _ _ _ _ := one_dvd _
  tick_unique y _ j j' t := by
    rintro ⟨x, h⟩ ⟨x', h'⟩
    obtain ⟨t1, a, sg, -, rfl, hs, hny, ht1, he⟩ := groupAt_seg h
    obtain ⟨t2, b, sg', -, rfl, hs', hny', ht2, he'⟩ := groupAt_seg h'
    have : t1 = t2 := by exact_mod_cast ht1.symm.trans ht2
    subst this
    have hpa := seg_phase hs
    have hpb := seg_phase hs'
    rw [← he] at hpa
    rw [← he'] at hpb
    have ha : a < 2 := by by_contra hc; rw [ite_eq_right hc] at hpa; cases hpa
    have hb : b < 2 := by by_contra hc; rw [ite_eq_right hc] at hpb; cases hpb
    have := seg_node hs ha
    have := seg_node hs' hb
    rw [hny] at *
    rw [hny'] at *
    omega
  tick_of_awake y _ t ht _ _ := by
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ht
    exact ⟨_, tick_group n y⟩
  awake_in_horizon y _ t ht := by
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ht
    obtain ⟨x, hne, hk, -⟩ := tick_group n w0
    obtain ⟨-, htm, -, -, hl⟩ := hk 0 (List.length_pos_of_ne_nil hne)
    exact ⟨_, Or.inl (by rw [hl]; exact Option.some_ne_none _), le_of_eq htm.symm⟩
  awake_of_call _ _ i _ := by change (0 : Int) ≤ ((i / 1024 : Nat) : Int); omega
  restart_of_sleep _ _ _ _ _ hu _ hna _ := absurd hu hna
  restart_at_wake _ _ _ _ hu _ hna _ := absurd hu hna
  sleep_of_restart y _ i := by
    rintro ⟨ℓ, hc, hℓ⟩
    obtain ⟨t, j, k, p, -, -, -, hp, hsk, -⟩ := sk_of_label hc.2
    have : sk (.ac ℓ) = .ac .restart (ℓ.emits.map (·.msg)) := by
      change Sk.ac ℓ.call _ = _; rw [hℓ]
    rw [this] at hsk
    exact (plan_no_restart t p (List.mem_of_getElem? hp) _ (List.mem_of_getElem? hsk) _
      rfl).elim
  block_unforgeable y _ i B := by
    rintro ⟨acc, hc⟩ -
    obtain ⟨t, j, k, p, -, -, rfl, hp, hsk, -⟩ := sk_of_label hc.2
    obtain ⟨s, hs, rfl, rfl, hjk⟩ := plan_fgBlock hp hsk
    rw [blk_proposer]
    exact ⟨_, by omega, own_blk hs⟩
  att_unforgeable y _ i a h _ := by
    rcases h with hc | ⟨B, ⟨acc, hc⟩, ha⟩
    · obtain ⟨t, j, k, p, -, -, rfl, hp, hsk, -⟩ := sk_of_label hc.2
      obtain ⟨z, q, hq, rfl, hlt⟩ := plan_fgAtt hp hsk
      exact ⟨_, hlt, sign_row z hq⟩
    · obtain ⟨t, j, k, p, -, -, rfl, hp, hsk, -⟩ := sk_of_label hc.2
      obtain ⟨s, hs, rfl, rfl, -⟩ := plan_fgBlock hp hsk
      rcases mem_blk_fgPayload.1 ha with ⟨q, hq, hm, rfl⟩ | ⟨q, hq, hm, rfl⟩
      · refine ⟨_, ?_, sign_row w0 hq⟩
        rw [w0_val]; unfold rt; unfold car0 at hm; omega
      · refine ⟨_, ?_, sign_row w1 hq⟩
        rw [w1_val]; unfold rt; unfold car1 at hm; omega
  msg_unforgeable y _ i m := by
    rintro ⟨ℓ, hc, hℓ⟩ -
    obtain ⟨t, j, k, p, -, -, rfl, hp, hsk, -⟩ := sk_of_label hc.2
    have : sk (.ac ℓ) = .ac (.message m) (ℓ.emits.map (·.msg)) := by
      change Sk.ac ℓ.call _ = _; rw [hℓ]
    rw [this] at hsk
    obtain ⟨z, σ, rfl, hlt⟩ := plan_msg hp hsk
    exact ⟨_, hlt, emit_vote z σ⟩

/-- **The two-validator run is a Goldilocks run**, with both validators honest. -/
theorem run_goldilocksRun : GoldilocksRun prop dg Set.univ run where
  stock := rfl
  toLocalRun := run_localRun
  genesis_root_ok := dg_genesis
  vstart := fun _ => SA.voteStart_initial _
  carried_vote_unforgeable y _ i B := by
    rintro ⟨acc, hc⟩ v hv -
    obtain ⟨t, j, k, p, -, -, rfl, hp, hsk, -⟩ := sk_of_label hc.2
    obtain ⟨s, hs, rfl, rfl, -⟩ := plan_fgBlock hp hsk
    obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    rw [blockVotes_blk] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact ⟨_, by unfold emitIdx; rw [w0_val]; split_ifs <;> omega, emit_vote w0 s⟩
    · exact ⟨_, by unfold emitIdx; rw [w1_val]; split_ifs <;> omega, emit_vote w1 s⟩

end Consensus.Goldilocks.Witness.TwoRun

end

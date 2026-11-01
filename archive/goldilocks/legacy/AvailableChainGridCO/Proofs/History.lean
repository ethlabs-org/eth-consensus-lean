module
public import AvailableChainGridCO.Proofs.StoreFacts
public import AvailableChainGridCO.Proofs.Windows

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- Ancestry is transitive, including at genesis. -/
theorem prefix_trans (A B C : Block)
    (hAB : Block.Preceq A B) (hBC : Block.Preceq B C) : Block.Preceq A C := by
  induction C with
  | genesis =>
      have h : B = .genesis := by simpa [Block.Preceq, Block.preceq] using hBC
      subst B
      exact hAB
  | node parent slot r_slot root ih =>
      obtain h | h : B = .node parent slot r_slot root ∨ Block.Preceq B parent := by
        simpa [Block.Preceq, Block.preceq, Bool.or_eq_true] using hBC
      · subst B; exact hAB
      · simp only [Block.Preceq, Block.preceq, Bool.or_eq_true]
        exact Or.inr (ih h)

theorem ancestors_compatible (A B C : Block)
    (hA : Block.Preceq A C) (hB : Block.Preceq B C) : Block.Compatible A B := by
  change Block.preceq A C = true at hA
  change Block.preceq B C = true at hB
  induction C with
  | genesis =>
      have h : A = .genesis := by simpa [Block.Preceq, Block.preceq] using hA
      subst A
      simp only [Block.Compatible, Block.compatible, Bool.or_eq_true]
      exact Or.inl (genesis_prefix B)
  | node parent slot r_slot root ih =>
      obtain ha | ha : A = .node parent slot r_slot root ∨ Block.Preceq A parent := by
        simpa [Block.Preceq, Block.preceq, Bool.or_eq_true] using hA
      · subst A; simp [Block.Compatible, Block.compatible, hB]
      · obtain hb | hb : B = .node parent slot r_slot root ∨ Block.Preceq B parent := by
          simpa [Block.Preceq, Block.preceq, Bool.or_eq_true] using hB
        · subst B; simp [Block.Compatible, Block.compatible, hA]
        · exact ih ha hb

private theorem fold_stable {n : Nat} {α : Type}
    (xs : List α) (f : State n → α → State n)
    (hf : ∀ st x, (f st x).stableRecord = st.stableRecord) (st : State n) :
    (xs.foldl f st).stableRecord = st.stableRecord := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih, hf]

/-- Deliveries do not change the exposed record. -/
theorem process_stable (p : Params) {n : Nat} (st : State n) (o : Wire n) :
    (process p st o).stableRecord = st.stableRecord := by
  unfold process
  split
  · exact admitVote_stable p st o
  · unfold admitProposal
    dsimp only
    split <;> split
    all_goals first
      | rfl
      | exact fold_stable _ _ (fun s v => admitVote_stable p s (fromHead v)) _
  · rfl

theorem clockPreGate_stable (p : Params) {n : Nat} (st : State n) (t : Time) :
    (clockPreGate p st t).stableRecord = st.stableRecord := by
  unfold clockPreGate
  dsimp only
  split <;> split <;> split <;> rfl

/-- Only a confirmation gate can change a record. -/
theorem clock_stable_of_no_gate (p : Params) {n : Nat} (st : State n) (t : Time)
    (h : ∀ r, t ≠ gateTime p r) :
    (clock p st t).stableRecord = st.stableRecord := by
  rw [clock_eq_gate_prestate]
  have hn : (0 ≤ t - 6 * p.Δ && t == gateTime p
      ((t - 6 * p.Δ) / (4 * p.Δ)).toNat) = false := by
    simp [h]
  simp only [hn, Bool.false_eq_true, ↓reduceIte]
  exact clockPreGate_stable p st t

/-- A gate retains the old record or installs its genuine result. -/
theorem gate_stable_cases (p : Params) {n : Nat} (st : State n) (r : Slot) :
    (gate p st r).stableRecord = st.stableRecord ∨
      ∃ B, confirmation p st r = some B ∧ (gate p st r).stableRecord = B := by
  cases hc : confirmation p st r with
  | none => exact Or.inl (by simp [gate, hc])
  | some B =>
      by_cases hg : st.obligations.any (fun (b, _, _) => !Block.compatible b B) = true
      · exact Or.inl (gate_veto p st r B hc hg).1
      · have hs : (gate p st r).stableRecord = advance st.stableRecord B := by
          have hgf : st.obligations.any (fun (b, _, _) => !Block.compatible b B) = false :=
            Bool.eq_false_iff.mpr hg
          simp only [gate, hc, hgf, Bool.false_eq_true, ↓reduceIte]
          apply fold_stable
          intro acc b
          apply fold_stable
          intro acc g
          rfl
        rw [hs]
        unfold advance
        split
        · exact Or.inl rfl
        · exact Or.inr ⟨B, rfl, rfl⟩

private theorem time_le_of_key_le {V : Type} {O : Type}
    (e f : Event V O) (h : e.key ≤ f.key) : e.time ≤ f.time := by
  rcases Prod.Lex.toLex_le_toLex.mp h with h | ⟨h, _⟩
  · exact le_of_lt h
  · exact le_of_eq h

private theorem filter_split_time {V O : Type} (xs : List (Event V O))
    (hs : xs.Pairwise (fun e f => e.time ≤ f.time)) (a b : Time) (hab : a ≤ b) :
    xs.filter (fun e => decide (e.time ≤ b)) =
      xs.filter (fun e => decide (e.time ≤ a)) ++
      xs.filter (fun e => decide (a < e.time ∧ e.time ≤ b)) := by
  induction xs with
  | nil => rfl
  | cons e xs ih =>
      obtain ⟨he, hs⟩ := List.pairwise_cons.mp hs
      by_cases ha : e.time ≤ a
      · have hb := le_trans ha hab
        simp [ha, hb, not_lt.mpr ha, ih hs]
      · have hempty : xs.filter (fun f => decide (f.time ≤ a)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro f hf
          simpa only [decide_eq_true_eq] using
            (not_le.mpr (lt_of_lt_of_le (lt_of_not_ge ha) (he f hf)))
        have ih' := ih hs
        rw [hempty, List.nil_append] at ih'
        simp only [List.filter_cons, decide_eq_true_eq, ha, ↓reduceIte, hempty, List.nil_append]
        by_cases hb : e.time ≤ b
        · simp only [hb, lt_of_not_ge ha, and_self, ↓reduceIte, ih']
        · simp only [hb, and_false, ↓reduceIte, ih']

/-- A field is constant across events whose clocks and receipts preserve it.
The engine proof is shared by SA and SA-PC. -/
theorem fold_field_unchanged {V : Type} [DecidableEq V] {n : Nat}
    {P : ProtocolSpec n} {α : Type} (field : P.State → α)
    (hprocess : ∀ st o, field (P.process st o) = field st)
    (xs : List (Event V P.Object))
    (hclock : ∀ e ∈ xs, ∀ st, field (P.clock st e.time) = field st)
    (w : World V P) (v : V) : field ((xs.foldl World.step w) v) = field (w v) := by
  induction xs generalizing w with
  | nil => rfl
  | cons e xs ih =>
      rw [List.foldl_cons, ih (by intro e he; exact hclock e (by simp [he]))]
      cases e with
      | tick u t =>
          by_cases h : v = u
          · subst v; simpa [World.step] using! hclock (.tick u t) (by simp) (w u)
          · simp [World.step, h]
      | deliver u o t =>
          by_cases h : v = u
          · subst v; simpa [World.step] using hprocess (w u) o
          · simp [World.step, h]

private theorem fold_record_unchanged {V : Type} [DecidableEq V]
    (p : Params) (xs : List (Event V (gridCO p).Object))
    (hgate : ∀ e ∈ xs, ∀ r, e.time ≠ gateTime p r)
    (w : World V (gridCO p)) (v : V) :
    ((xs.foldl World.step w) v).stableRecord = (w v).stableRecord :=
  fold_field_unchanged State.stableRecord (process_stable p) xs
    (fun e he st => clock_stable_of_no_gate p st e.time (hgate e he)) w v

/-- A field is constant between reads if each clock in the interval and
all receipts preserve it. Only the fixed engine order is used. -/
theorem read_field_eq_of_no_clock_change {V : Type} [DecidableEq V] {n : Nat}
    {P : ProtocolSpec n} {α : Type} (field : P.State → α)
    (hprocess : ∀ st o, field (P.process st o) = field st)
    (E : Env V) (rho : Run V P) (hs : ScheduleWellFormed E rho)
    (a b : Time) (hab : a ≤ b)
    (hclock : ∀ t, a < t → t ≤ b → ∀ st, field (P.clock st t) = field st) (v : V) :
    field (Run.readAt P rho b v) = field (Run.readAt P rho a v) := by
  have htime := hs.sorted.imp (fun h => time_le_of_key_le _ _ h)
  unfold Run.readAt
  rw [filter_split_time rho.events htime a b hab, List.foldl_append]
  apply fold_field_unchanged field hprocess
  intro e he st
  have he' := of_decide_eq_true (List.mem_filter.mp he).2
  exact hclock e.time he'.1 he'.2 st

/-- Reads are constant on any interval without a gate. Delivery, release,
expiry, and sleep do not change this fact. -/
theorem read_stable_eq_of_no_gate {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (hs : ScheduleWellFormed E rho) (a b : Time) (hab : a ≤ b)
    (hgate : ∀ r, ¬ (a < gateTime p r ∧ gateTime p r ≤ b)) (v : V) :
    stable (Run.readAt (gridCO p) rho b v) =
      stable (Run.readAt (gridCO p) rho a v) := by
  apply read_field_eq_of_no_clock_change State.stableRecord (process_stable p) E rho hs a b hab
  intro t hlo hhi st
  exact clock_stable_of_no_gate p st t (fun r eq => hgate r (eq ▸ ⟨hlo, hhi⟩))

/-- Before the first gate, every exposed record is genesis. -/
theorem read_stable_before_first_gate {V : Type} [DecidableEq V]
    (p : Params) (rho : Run V (gridCO p)) (t : Time)
    (ht : t < gateTime p 0) (v : V) :
    stable (Run.readAt (gridCO p) rho t v) = .genesis := by
  apply fold_record_unchanged p _ ?_ World.init v
  intro e he r h
  have he' := of_decide_eq_true (List.mem_filter.mp he).2
  have hg : gateTime p 0 ≤ gateTime p r := by
    dsimp [gateTime, proposalTime]
    have : 0 ≤ 4 * p.Δ * (r : Time) :=
      mul_nonneg (mul_nonneg (by norm_num) (le_of_lt p.deltaPos))
        (Int.natCast_nonneg r)
    linarith
  exact (not_le.mpr ht) (le_trans hg (by simpa [h] using he'))

/-- Gates have the slot order. -/
theorem gateTime_le_iff (p : Params) (r s : Slot) :
    gateTime p r ≤ gateTime p s ↔ r ≤ s := by
  have hd := p.deltaPos
  simp only [gateTime, proposalTime]
  constructor
  · intro h
    have : (r : Time) ≤ s := by nlinarith
    exact_mod_cast this
  · intro h
    have hc : (r : Time) ≤ s := by exact_mod_cast h
    nlinarith

/-- Every time after the first gate has a last completed gate. -/
theorem exists_latest_gate (p : Params) (t : Time) (ht : gateTime p 0 ≤ t) :
    ∃ r : Slot, gateTime p r ≤ t ∧ t < gateTime p (r + 1) := by
  have hd : 0 < 4 * p.Δ := by linarith [p.deltaPos]
  have hn : 0 ≤ t - 6 * p.Δ := by simpa [gateTime, proposalTime] using ht
  have hk : 0 ≤ (t - 6 * p.Δ) / (4 * p.Δ) :=
    Int.ediv_nonneg hn (le_of_lt hd)
  refine ⟨((t - 6 * p.Δ) / (4 * p.Δ)).toNat, ?_, ?_⟩
  all_goals
    have hcast := Int.toNat_of_nonneg hk
    have hmod := Int.emod_nonneg (t - 6 * p.Δ) (ne_of_gt hd)
    have hlt := Int.emod_lt_of_pos (t - 6 * p.Δ) hd
    have heq := Int.mul_ediv_add_emod (t - 6 * p.Δ) (4 * p.Δ)
    simp only [gateTime, proposalTime, Nat.cast_add, Nat.cast_one, hcast]
    nlinarith

/-- An arbitrary read between two gates equals the preceding gate read. -/
theorem read_stable_eq_latest_gate {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (hs : ScheduleWellFormed E rho) (r : Slot) (t : Time)
    (hlo : gateTime p r ≤ t) (hhi : t < gateTime p (r + 1)) (v : V) :
    stable (Run.readAt (gridCO p) rho t v) =
      stable (Run.readAt (gridCO p) rho (gateTime p r) v) := by
  apply read_stable_eq_of_no_gate p E rho hs _ _ hlo
  intro s ⟨hrs, hst⟩
  have hsr : r < s := by
    by_contra h
    have := (gateTime_le_iff p s r).mpr (Nat.le_of_not_gt h)
    linarith
  have := (gateTime_le_iff p (r + 1) s).mpr hsr
  linarith

end AvailableChain.GridCO
end

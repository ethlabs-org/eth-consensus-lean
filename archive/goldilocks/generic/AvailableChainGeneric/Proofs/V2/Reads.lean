module
public import AvailableChainGeneric.Statements.V2.Reads
public import AvailableChainKitV2.Stable

public section

open AvailableChain AvailableChain.V2 AvailableChain.V2.Engine

namespace AvailableChain.Gen.V2

-- S3-01; Statements/V2/Reads.lean:97–100; KitV2/Execution.lean:53–65.
theorem stateBefore_idxBefore_statement : StateBeforeIdxBeforeStatement := by
  intro V _ In P E rho t hS
  rw [Run.idxBefore_def]
  unfold Run.stateBefore Run.stateBeforeTime
  apply congrArg (fun events : List (Event V P.Object) =>
    events.foldl (World.step E rho) World.init)
  exact (filter_eq_take hS (fun e => decide (e.time < t)) (by
    intro e f hk hf
    exact decide_eq_true
      (lt_of_le_of_lt (time_le_of_key_le e f hk) (of_decide_eq_true hf)))).symm

-- S3-01 LINK; preserve all frozen binders.
set_option linter.unusedVariables false in
theorem stateBefore_idxBefore :
    ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
      (E : Generic.Env V) (rho : Run V P) (t : Time) (hS : ScheduleWellFormed E rho),
      Run.stateBefore E rho (Run.idxBefore rho t) = Run.stateBeforeTime E rho t :=
  @stateBefore_idxBefore_statement

-- S3-01; pubFloor_def and positive-divisor integer division.
theorem pubFloor_le {V : Type} (E : Generic.Env V) (t : Time) :
    pubFloor E t ≤ t := by
  rw [pubFloor_def, Int.mul_comm]
  exact Int.mul_ediv_self_le (ne_of_gt E.Δ_pos)

-- S3-01; EngineV2/Conditions/Schedule.lean:18–19.
theorem publicTime_le_pubFloor {V : Type} (E : Generic.Env V) {a t : Time}
    (hpub : PublicTime E a) (hat : a ≤ t) : a ≤ pubFloor E t := by
  unfold PublicTime at hpub
  rcases hpub with ⟨k, rfl⟩
  rw [pubFloor_def]
  exact Int.mul_le_mul_of_nonneg_right
    ((Int.le_ediv_iff_mul_le E.Δ_pos).mpr hat) (le_of_lt E.Δ_pos)

-- S3-01; strict variant of KitV2/Execution.lean:99–115, using :59 and :67.
theorem index_lt_idxBefore_iff {V In : Type} {P : ProtocolSpec In}
    {E : Generic.Env V} {rho : Run V P} (hS : ScheduleWellFormed E rho)
    {i : Nat} {e : Event V P.Object} (hi : rho.events[i]? = some e) (t : Time) :
    i < Run.idxBefore rho t ↔ e.time < t := by
  rw [Run.idxBefore_def]
  let q := fun f : Event V P.Object => decide (f.time < t)
  have hdown : ∀ a b, a.key ≤ b.key → q b = true → q a = true := by
    intro a b hk hb
    exact decide_eq_true
      (lt_of_le_of_lt (time_le_of_key_le a b hk) (of_decide_eq_true hb))
  constructor
  · intro hl
    have hm : e ∈ rho.events.filter q := by
      rw [filter_eq_take hS q hdown]
      exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hl]; exact hi)
    exact of_decide_eq_true (List.mem_filter.mp hm).2
  · intro ht
    by_contra hn
    have hf := filter_false_of_index_ge hS q hdown (Nat.le_of_not_gt hn) hi
    simp [q, ht] at hf

-- GLY r3.16 READS; S3d §2.9 J-10. The deadline cut is an event prefix.
-- NoRestart and MonoAlong are used only from the index form to the state form.
theorem holdsBefore_iff_exists_idx_statement : HoldsBeforeIffExistsIdxStatement := by
  rw [HoldsBeforeIffExistsIdxStatement_def]
  intro V inst In P E rho Q d x hNR hS hmono
  rw [HoldsBefore_def, ← stateBefore_idxBefore E rho d hS]
  have hlen : Run.idxBefore rho d ≤ rho.events.length := by
    rw [Run.idxBefore_def]
    exact List.length_filter_le ..
  constructor
  · intro hQ
    refine ⟨Run.idxBefore rho d, hlen, ?_, hQ⟩
    intro k hk
    have hklen : k < rho.events.length := lt_of_lt_of_le hk hlen
    have he := List.getElem?_eq_getElem hklen
    exact ⟨rho.events[k], he, (index_lt_idxBefore_iff hS he d).mp hk⟩
  · rintro ⟨i, hi, hbefore, hQ⟩
    have hiCut : i ≤ Run.idxBefore rho d := by
      by_contra hn
      obtain ⟨e, he, ht⟩ := hbefore (Run.idxBefore rho d) (Nat.lt_of_not_ge hn)
      exact (Nat.lt_irrefl _) ((index_lt_idxBefore_iff hS he d).mpr ht)
    rw [MonoAlong_def] at hmono
    exact stateBefore_stable Q hmono.1 hmono.2.1 hmono.2.2 E rho hiCut x
      (hNR.restartFree x i (Run.idxBefore rho d)) hQ

-- LINK; keep the closed Statement's binder names.
set_option linter.unusedVariables false in
theorem holdsBefore_iff_exists_idx
    {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
    {E : Generic.Env V} {rho : Run V P} {Q : P.State → Prop} {d : Time} {x : V}
    (hNR : NoRestart rho) (hS : ScheduleWellFormed E rho) (hmono : MonoAlong Q) :
    HoldsBefore E rho Q d x ↔
      ∃ i ≤ rho.events.length,
        (∀ k < i, ∃ e, rho.events[k]? = some e ∧ e.time < d) ∧
        Q (Run.stateBefore E rho i x) :=
  @holdsBefore_iff_exists_idx_statement V _ In P E rho Q d x hNR hS hmono

/-- A restore-safe property has the strict-time read characterization. -/
theorem holdsBefore_iff_exists_idx_restore
    {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
    {E : Generic.Env V} {rho : Run V P} {Q : P.State → Prop} {d : Time} {x : V}
    (hS : ScheduleWellFormed E rho) (hmono : MonoAlong Q)
    (hrestore : ∀ st t, Q st → Q (P.restore (P.durable st) t)) :
    HoldsBefore E rho Q d x ↔
      ∃ i ≤ rho.events.length,
        (∀ k < i, ∃ e, rho.events[k]? = some e ∧ e.time < d) ∧
        Q (Run.stateBefore E rho i x) := by
  rw [HoldsBefore_def, ← stateBefore_idxBefore E rho d hS]
  have hlen : Run.idxBefore rho d ≤ rho.events.length := by
    rw [Run.idxBefore_def]
    exact List.length_filter_le ..
  constructor
  · intro hQ
    refine ⟨Run.idxBefore rho d, hlen, ?_, hQ⟩
    intro k hk
    have hklen : k < rho.events.length := lt_of_lt_of_le hk hlen
    have he := List.getElem?_eq_getElem hklen
    exact ⟨rho.events[k], he, (index_lt_idxBefore_iff hS he d).mp hk⟩
  · rintro ⟨i, hi, hbefore, hQ⟩
    have hiCut : i ≤ Run.idxBefore rho d := by
      by_contra hn
      obtain ⟨e, he, ht⟩ := hbefore (Run.idxBefore rho d) (Nat.lt_of_not_ge hn)
      exact (Nat.lt_irrefl _) ((index_lt_idxBefore_iff hS he d).mpr ht)
    rw [MonoAlong_def] at hmono
    exact stateBefore_stable_restore Q hmono.1 hmono.2.1 hmono.2.2 E rho hiCut x
      hrestore hQ

end AvailableChain.Gen.V2

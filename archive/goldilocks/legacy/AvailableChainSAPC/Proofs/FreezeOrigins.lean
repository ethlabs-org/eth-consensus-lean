module
public import AvailableChainSAPC.Proofs.FrozenCertificates
public import AvailableChainSAPC.Proofs.ClockBounds

@[expose] public section
namespace AvailableChain.SAPC

open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

theorem clock_frozenPC (p : Params) {n : Nat} (st : State n) (t : Time) :
    (clock p st t).frozenPC =
      let r := ((t - 3 * p.Δ) / (4 * p.Δ)).toNat
      if 0 ≤ t - 3 * p.Δ && t == freezeTime p r then
        if st.frozenPC.any (fun row => row.1 == r) then st.frozenPC
        else st.frozenPC ++ [(r, st.bestPC)]
      else st.frozenPC := by
  unfold clock
  dsimp only
  split_ifs <;> simp only [gate, saveTimely]
  all_goals (try split_ifs) <;> rfl

theorem clock_frozenPC_origin (p : Params) {n : Nat} (st : State n) (t : Time)
    (r : Slot) (c : Option (PC n)) (hm : (r, c) ∈ (clock p st t).frozenPC) :
    (r, c) ∈ st.frozenPC ∨ t = freezeTime p r ∧ c = st.bestPC := by
  rw [clock_frozenPC] at hm
  dsimp only at hm
  split at hm
  · rename_i htime
    split at hm
    · exact Or.inl hm
    · rcases List.mem_append.mp hm with hold | hnew
      · exact Or.inl hold
      · have he := List.mem_singleton.mp hnew
        have hr := congrArg Prod.fst he
        have hc := congrArg Prod.snd he
        dsimp only at hr hc
        exact Or.inr ⟨by simpa only [← hr, beq_iff_eq] using
          (Bool.and_eq_true_iff.mp htime).2, hc⟩
  · exact Or.inl hm

/-- Each frozen row names the live PC immediately before its own freeze
tick. The row can contain `none`; it still records that tick. -/
theorem frozenPC_origin_before {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) (index : Nat) (v : V) (r : Slot) (c : Option (PC p.n))
    (hm : (r, c) ∈ (Run.stateBefore (sapc p) rho index v).frozenPC) :
    ∃ j < index, rho.events[j]? = some (.tick v (freezeTime p r)) ∧
      c = (Run.stateBefore (sapc p) rho j v).bestPC := by
  obtain ⟨j, hj, t, ht, htime, hc⟩ := clock_field_origin
    (P := sapc p) State.frozenPC rfl (process_frozenPC p)
    (fun st t row => t = freezeTime p row.1 ∧ row.2 = st.bestPC)
    (fun st t row hm => clock_frozenPC_origin p st t row.1 row.2 hm)
    rho index v (r, c) hm
  subst t
  exact ⟨j, hj, ht, hc⟩

theorem stateBefore_frozenPC_prefix {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) {i j : Nat} (hij : i ≤ j) (v : V) :
    (Run.stateBefore (sapc p) rho i v).frozenPC <+:
      (Run.stateBefore (sapc p) rho j v).frozenPC := by
  set_option backward.isDefEq.respectTransparency false in
  apply stateBefore_field_prefix (P := sapc p) State.frozenPC ?_ ?_ rho hij v
  · intro st t
    rcases clock_frozenPC_cases p st t with he | ⟨r, he⟩
    · rw [show (sapc p).clock = clock p from rfl, he]
    · rw [show (sapc p).clock = clock p from rfl, he]
      exact List.prefix_append _ _
  · intro st o
    rw [show (sapc p).process = process p from rfl, process_frozenPC]

/-- Once a nonempty PC is frozen, later live receipts and clocks cannot
replace that label's selection. -/
theorem frozenPCAt_at_later_input {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) {i j : Nat} (hij : i ≤ j) (v : V) (r : Slot) (c : PC p.n)
    (h : frozenPCAt (Run.stateBefore (sapc p) rho i v) r = some c) :
    frozenPCAt (Run.stateBefore (sapc p) rho j v) r = some c := by
  obtain ⟨suffix, he⟩ := stateBefore_frozenPC_prefix p rho hij v
  unfold frozenPCAt at h ⊢
  rw [← he, List.find?_append]
  cases hf : (Run.stateBefore (sapc p) rho i v).frozenPC.find? (fun row => row.1 == r) with
  | none => simp [hf] at h
  | some row => simpa [hf] using h

end AvailableChain.SAPC
end

module
public import AvailableChainPCSA.Model.Clock

public section

/-! Frozen PC views and gate rank reads (pcsa34-r4.3 §3.3, §3.7). -/

namespace AvailableChain.PCSA
variable {n : Nat}

/-- A missing freeze label has an empty snapshot. -/
theorem pcSnapshotAt_absent (st : State n) (s : Slot)
    (h : st.pcSnapshot.find? (fun row => row.1 == s) = none) :
    pcSnapshotAt st s = [] := by
  dsimp only [pcSnapshotAt]
  simp only [h, Option.map_none, Option.getD_none]

/-- Appending a new freeze label records the full PC list. -/
theorem pcSnapshotAt_append (st : State n) (s : Slot) (cs : List (PC n))
    (h : st.pcSnapshot.find? (fun row => row.1 == s) = none) :
    pcSnapshotAt { st with pcSnapshot := st.pcSnapshot ++ [(s, cs)] } s = cs := by
  dsimp only [pcSnapshotAt]
  simp [List.find?_append, h]

/-- Changing fields outside the frozen list does not change the snapshot. -/
theorem pcSnapshotAt_eq_of_list_eq (st st' : State n) (s : Slot)
    (h : st.pcSnapshot = st'.pcSnapshot) : pcSnapshotAt st s = pcSnapshotAt st' s := by
  dsimp only [pcSnapshotAt]
  simp only [h]

/-- The pre-gate clock preserves the held PC set. -/
theorem clockPre_pcs (p : Params) (st : State p.n) (t : Time) :
    (clockPre p st t).pcs = st.pcs := by
  unfold clockPre
  dsimp only
  split <;> split <;> split <;> rfl

/-- The pre-gate clock preserves first-acceptance stamps. -/
theorem clockPre_pcStamps (p : Params) (st : State p.n) (t : Time) :
    (clockPre p st t).pcStamps = st.pcStamps := by
  unfold clockPre
  dsimp only
  split <;> split <;> split <;> rfl

/-- The pre-gate clock does not change F or S. -/
theorem clockPre_output_fields (p : Params) (st : State p.n) (t : Time) :
    (clockPre p st t).fg = st.fg ∧
    (clockPre p st t).base.stableRecord = st.base.stableRecord := by
  unfold clockPre
  dsimp only
  split <;> split <;> split <;> exact ⟨rfl, rfl⟩

/-- The gate changes no held PC or FG state. -/
theorem gateFrom_pc_frame (p : Params) (a : Block) (cs : List (PC n)) (ρ : Option PCRank)
    (st : State n) (s : Slot) :
    (gateFrom p a cs ρ st s).pcs = st.pcs ∧ (gateFrom p a cs ρ st s).fg = st.fg := by
  rw [gateFrom_def]
  dsimp only
  cases hc : SA.Root.confirmationFrom p.toParams a (actView st) s
  · exact ⟨rfl, rfl⟩
  · dsimp only
    split
    · exact ⟨rfl, rfl⟩
    · apply List.foldlRecOn (motive := fun a : State n => a.pcs = st.pcs ∧ a.fg = st.fg)
      · exact ⟨rfl, rfl⟩
      · intro acc ha b _
        apply List.foldlRecOn (motive := fun a : State n => a.pcs = st.pcs ∧ a.fg = st.fg)
        · exact ha
        · intro acc' ha' g _
          exact ha'

/-- A first freeze stores exactly the pre-tick PC list. -/
theorem clockPre_freeze_snapshot (p : Params) (st : State p.n) (s : Slot)
    (h : st.pcSnapshot.find? (fun row => row.1 == s) = none) :
    pcSnapshotAt (clockPre p st (SA.freezeTime p.toParams s)) s = st.pcs := by
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  have hf : ((SA.freezeTime p.toParams s - 3 * p.Δ) / (4 * p.Δ)).toNat = s := by
    change ((4 * p.Δ * (s : Int) + 3 * p.Δ - 3 * p.Δ) / (4 * p.Δ)).toNat = s
    rw [add_sub_cancel_right, Int.mul_ediv_cancel_left _ (by omega), Int.toNat_natCast]
  have hz : 0 ≤ SA.freezeTime p.toParams s - 3 * p.Δ := by
    change 0 ≤ 4 * p.Δ * (s : Int) + 3 * p.Δ - 3 * p.Δ
    rw [add_sub_cancel_right]
    positivity
  unfold clockPre
  simp only [hf, hz, decide_true, BEq.rfl, Bool.and_self, ite_true,
    onView, h, Option.isSome_none, Bool.false_eq_true, ite_false]
  split <;> split <;> dsimp only [pcSnapshotAt] <;> simp [List.find?_append, h]

/-- A freeze time is not a gate time. -/
theorem freezeTime_ne_gateTime (p : Params) (s d : Slot) :
    SA.freezeTime p.toParams s ≠ SA.gateTime p.toParams d := by
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  change 4 * p.Δ * (s : Int) + 3 * p.Δ ≠ 4 * p.Δ * (d : Int) + 6 * p.Δ
  intro he
  by_cases hsd : s ≤ d
  · have hsd' : (s : Int) ≤ d := by exact_mod_cast hsd
    nlinarith
  · have hdsN : d + 1 ≤ s := Nat.succ_le_of_lt (Nat.lt_of_not_ge hsd)
    have hds : (d : Int) + 1 ≤ s := by exact_mod_cast hdsN
    nlinarith

/-- At a freeze time the full clock has only the pre-gate steps. -/
theorem clock_freeze (p : Params) (st : State p.n) (s : Slot) :
    clock p st (SA.freezeTime p.toParams s) = clockPre p st (SA.freezeTime p.toParams s) := by
  unfold clock
  dsimp only
  have hn := freezeTime_ne_gateTime p s
  simp only [beq_iff_eq, Bool.and_eq_true]
  split
  · rename_i h
    exact (hn _ h.2).elim
  · rfl

/-- A first freeze leaves the snapshot equal to the post-tick held PC list. -/
theorem clock_freeze_snapshot (p : Params) (st : State p.n) (s : Slot)
    (h : st.pcSnapshot.find? (fun row => row.1 == s) = none) :
    pcSnapshotAt (clock p st (SA.freezeTime p.toParams s)) s =
      (clock p st (SA.freezeTime p.toParams s)).pcs := by
  rw [clock_freeze, clockPre_pcs, clockPre_freeze_snapshot p st s h]

/-- A gate rank candidate is held, frame-active, and stamped before the early time. -/
theorem gateRank_candidate_iff (p : Params) (st : State p.n) (s : Slot) (c : PC p.n) :
    c ∈ st.pcs.filter (fun c => frameActive p st c &&
      (pcStamp? st c).any (fun t => t < SA.earlyTime p.toParams s)) ↔
      c ∈ st.pcs ∧ frameActive p st c = true ∧
        ∃ t, pcStamp? st c = some t ∧ t < SA.earlyTime p.toParams s := by
  cases hs : pcStamp? st c <;> simp [hs]

/-- A store without held PCs has no gate rank. -/
theorem gateRank_empty (p : Params) (st : State p.n) (s : Slot) (h : st.pcs = []) :
    gateRank p st s = none := by
  simp only [gateRank_def, h]
  rfl

/-- Gate rank depends only on held PCs, stamps, and the full filtered tree. -/
theorem gateRank_eq (p : Params) (st st' : State p.n) (s : Slot)
    (hc : st.pcs = st'.pcs) (ht : st.pcStamps = st'.pcStamps)
    (hf : fullTree p st = fullTree p st') : gateRank p st s = gateRank p st' s := by
  simp only [gateRank_def, hc, frameActive_def, hf, pcStamp?_def, ht]

end AvailableChain.PCSA
end

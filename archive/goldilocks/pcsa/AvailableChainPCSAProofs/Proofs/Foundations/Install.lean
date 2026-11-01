module
public import AvailableChainPCSA.Model.PC

public section

/-! PC admission and assembly facts (pcsa34-r4.3 §3.6–3.7). -/

namespace AvailableChain.PCSA
variable {n : Nat}

/-- PC admission preserves the time, tree, ack pool, and frozen PCs. -/
theorem installPC_frame (st : State n) (c : PC n) :
    (installPC st c).base.now = st.base.now ∧
    (installPC st c).base.blocks = st.base.blocks ∧
    (installPC st c).ackPool = st.ackPool ∧
    (installPC st c).pcSnapshot = st.pcSnapshot ∧
    (installPC st c).fg = st.fg := by
  unfold installPC deleteConflictingLeases
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A duplicate slot and target do not change the store. -/
theorem installPC_duplicate (st : State n) (c : PC n)
    (h : st.pcs.any (fun o => o.slot == c.slot && o.target == c.target) = true) :
    installPC st c = st := by
  simp only [installPC_def, h, ite_true]

/-- A new slot and target append one PC. -/
theorem installPC_pcs_new (st : State n) (c : PC n)
    (h : st.pcs.any (fun o => o.slot == c.slot && o.target == c.target) = false) :
    (installPC st c).pcs = st.pcs ++ [c] := by
  simp only [installPC_def, h, Bool.false_eq_true, ite_false, deleteConflictingLeases_def]

/-- PC admission keeps every held PC. -/
theorem installPC_pcs_mono (st : State n) (c : PC n) : st.pcs ⊆ (installPC st c).pcs := by
  unfold installPC deleteConflictingLeases
  split
  · exact List.Subset.refl _
  · exact List.subset_append_left _ _

/-- Every PC after admission was held, or is the offered PC. -/
theorem mem_installPC_pcs (st : State n) (c d : PC n)
    (h : d ∈ (installPC st c).pcs) : d ∈ st.pcs ∨ d = c := by
  unfold installPC deleteConflictingLeases at h
  split at h
  · exact Or.inl h
  · simpa only [List.mem_append, List.mem_singleton] using h

/-- A newly admitted PC receives the current store time. -/
theorem installPC_stamp_new (st : State n) (c : PC n)
    (h : st.pcs.any (fun o => o.slot == c.slot && o.target == c.target) = false) :
    pcStamp? (installPC st c) c = some st.base.now := by
  simp only [installPC_def, h, Bool.false_eq_true, ite_false, deleteConflictingLeases_def,
    pcStamp?_def]
  have hn : (st.pcStamps.filter
      (fun row => !(row.1 == c.slot && row.2.1 == c.target.root))).find?
      (fun row => row.1 == c.slot && row.2.1 == c.target.root) = none := by
    apply List.find?_eq_none.mpr
    intro row hr he
    have hh := (List.mem_filter.mp hr).2
    rw [he] at hh
    contradiction
  rw [List.find?_append, hn]
  simp

/-- Assembly returns exactly its candidate and its validity check. -/
theorem assemblePC_some_iff (st : State n) (s : Slot) (b : Block) (c : PC n) :
    assemblePC st s b = some c ↔
      c = ⟨s, b, firstPerSeat (acksOn st s b.root)⟩ ∧ pcValid st c = true := by
  unfold assemblePC
  dsimp only
  split
  · rename_i hv
    constructor
    · intro he
      have he' := Option.some.inj he
      subst c
      exact ⟨rfl, hv⟩
    · rintro ⟨rfl, _⟩
      rfl
  · rename_i hv
    constructor
    · intro he
      contradiction
    · rintro ⟨rfl, hc⟩
      exact (hv hc).elim

/-- Assembly cannot create an invalid PC. -/
theorem pcsa_assemblePC_valid (st : State n) (s : Slot) (b : Block) (c : PC n)
    (h : assemblePC st s b = some c) : pcValid st c = true :=
  ((assemblePC_some_iff st s b c).mp h).2

/-- Collection preserves any observation preserved by one installation. -/
theorem collectPCs_preserves {α : Type} (f : State n → α)
    (hi : ∀ st c, f (installPC st c) = f st) (st : State n) :
    f (collectPCs st) = f st := by
  delta collectPCs
  generalize (st.ackPool.filterMap (fun a =>
    a.decode?.map (fun x => (x.1, x.2.2)))).eraseDups = cs
  induction cs generalizing st with
  | nil => rfl
  | cons sr cs ih =>
    rw [List.foldl_cons]
    cases hb : st.base.blocks.find? (fun b => b.root == sr.2) with
    | none => exact ih st
    | some b =>
      dsimp only
      cases hc : assemblePC st sr.1 b <;> dsimp only
      · exact ih st
      · exact (ih _).trans (hi _ _)

/-- Collection preserves an invariant when valid installations preserve it. -/
theorem collectPCs_invariant (P : State n → Prop)
    (hi : ∀ st c, P st → pcValid st c = true → P (installPC st c))
    (st : State n) (h : P st) : P (collectPCs st) := by
  delta collectPCs
  apply List.foldlRecOn
  · exact h
  · intro acc ha sr _
    cases hb : acc.base.blocks.find? (fun b => b.root == sr.2) with
    | none => exact ha
    | some b =>
      dsimp only
      cases hc : assemblePC acc sr.1 b <;> dsimp only
      · exact ha
      · rename_i c
        exact hi acc c ha (pcsa_assemblePC_valid acc sr.1 _ c hc)

/-- PC collection keeps every previously held PC. -/
theorem collectPCs_pcs_mono (st : State n) : st.pcs ⊆ (collectPCs st).pcs := by
  apply collectPCs_invariant (fun acc => st.pcs ⊆ acc.pcs)
  · intro acc c ha _ d hd
    exact installPC_pcs_mono acc c (ha hd)
  · exact List.Subset.refl _

/-- Collection keeps the ack pool and the frozen PCs. -/
theorem collectPCs_frame (st : State n) :
    (collectPCs st).base.now = st.base.now ∧
    (collectPCs st).base.blocks = st.base.blocks ∧
    (collectPCs st).ackPool = st.ackPool ∧
    (collectPCs st).pcSnapshot = st.pcSnapshot ∧
    (collectPCs st).fg = st.fg := by
  exact ⟨collectPCs_preserves (fun s => s.base.now) (fun s c => (installPC_frame s c).1) st,
    collectPCs_preserves (fun s => s.base.blocks) (fun s c => (installPC_frame s c).2.1) st,
    collectPCs_preserves State.ackPool (fun s c => (installPC_frame s c).2.2.1) st,
    collectPCs_preserves State.pcSnapshot (fun s c => (installPC_frame s c).2.2.2.1) st,
    collectPCs_preserves State.fg (fun s c => (installPC_frame s c).2.2.2.2) st⟩

end AvailableChain.PCSA
end

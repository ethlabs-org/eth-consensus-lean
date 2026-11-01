module
public import AvailableChainPCSAProofs.Proofs.Foundations.Install

public section

/-! Ack pool facts (pcsa34-r4.3 §3.6). The duty schedule supplies the
one-ack rule; the store has no `acked` field. -/

namespace AvailableChain.PCSA
variable {n : Nat}

/-- Raw pooling keeps the old acks. -/
theorem poolAckRaw_mono (st : State n) (a : AckWire n) :
    st.ackPool ⊆ (poolAckRaw st a).ackPool := by
  delta poolAckRaw
  cases hdecode : a.decode? <;> dsimp only
  rotate_left
  · split
    · exact List.Subset.refl _
    · exact List.subset_append_left _ _
  · exact List.Subset.refl _

/-- Raw pooling adds only the supplied ack. -/
theorem mem_poolAckRaw (st : State n) (a b : AckWire n)
    (h : b ∈ (poolAckRaw st a).ackPool) : b ∈ st.ackPool ∨ b = a := by
  delta poolAckRaw at h
  cases hdecode : a.decode? <;> rw [hdecode] at h <;> dsimp only at h
  rotate_left
  · split at h
    · exact Or.inl h
    · simpa only [List.mem_append, List.mem_singleton] using h
  · exact Or.inl h

/-- A decoded raw ack is present after pooling. -/
theorem poolAckRaw_mem (st : State n) (a : AckWire n) (s : Slot) (i : Fin n) (r : BlockId)
    (h : a.decode? = some (s, i, r)) : a ∈ (poolAckRaw st a).ackPool := by
  delta poolAckRaw
  rw [h]
  dsimp only
  split
  · assumption
  · simp

/-- Pooling does not change the PC set, stamps, time, or frame. -/
theorem poolAckRaw_frame (st : State n) (a : AckWire n) :
    (poolAckRaw st a).pcs = st.pcs ∧ (poolAckRaw st a).pcStamps = st.pcStamps ∧
    (poolAckRaw st a).base = st.base ∧ (poolAckRaw st a).fg = st.fg := by
  delta poolAckRaw
  cases hdecode : a.decode? <;> dsimp only
  rotate_left
  · split <;> exact ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-- Checked pooling keeps the old acks. -/
theorem poolAck_mono (p : Params) (st : State p.n) (a : AckWire p.n) :
    st.ackPool ⊆ (poolAck p st a).ackPool := by
  delta poolAck
  cases hdecode : a.decode? <;> dsimp only
  rotate_left
  · rename_i v
    rcases v with ⟨_, _, _⟩
    split
    · exact List.Subset.refl _
    · split
      · exact List.Subset.refl _
      · exact List.subset_append_left _ _
  · exact List.Subset.refl _

/-- Checked pooling adds only the supplied ack. -/
theorem mem_poolAck (p : Params) (st : State p.n) (a b : AckWire p.n)
    (h : b ∈ (poolAck p st a).ackPool) : b ∈ st.ackPool ∨ b = a := by
  delta poolAck at h
  cases hdecode : a.decode? <;> rw [hdecode] at h <;> dsimp only at h
  rotate_left
  · rename_i v
    rcases v with ⟨_, _, _⟩
    split at h
    · exact Or.inl h
    · split at h
      · exact Or.inl h
      · simpa only [List.mem_append, List.mem_singleton] using h
  · exact Or.inl h

/-- Every selected ack is in the pool. -/
theorem acksOn_subset (st : State n) (s : Slot) (r : BlockId) :
    acksOn st s r ⊆ st.ackPool := by
  intro a h
  exact (List.mem_filter.mp h).1

/-- The slot and root filter selects exactly matching decoded acks. -/
theorem mem_acksOn_iff (st : State n) (s : Slot) (r : BlockId) (a : AckWire n) :
    a ∈ acksOn st s r ↔ a ∈ st.ackPool ∧ ∃ i, a.decode? = some (s, i, r) := by
  unfold acksOn
  rw [List.mem_filter]
  cases h : a.decode? with
  | none => simp
  | some v =>
    rcases v with ⟨s', i, r'⟩
    simp only [Bool.and_eq_true, beq_iff_eq, Option.some.injEq, Prod.mk.injEq]
    aesop

end AvailableChain.PCSA
end

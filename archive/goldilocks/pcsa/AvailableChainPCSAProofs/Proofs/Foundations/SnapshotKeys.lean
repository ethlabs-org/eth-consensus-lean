module
public import AvailableChainPCSAProofs.Proofs.Foundations.Run

public section

/-! Freeze-label provenance (pcsa34-r4.3 §3.3). Only the clock adds labels. -/

namespace AvailableChain.PCSA
variable {n : Nat}

/-- Normalization changes no snapshot. -/
theorem normalizeS_snapshot (st : State n) : (normalizeS st).pcSnapshot = st.pcSnapshot := by
  unfold normalizeS
  split <;> rfl

/-- Reconciliation filters PC lists but keeps their freeze labels. -/
theorem reconcile_snapshot_keys (st : State n) :
    (reconcile st).pcSnapshot.map Prod.fst = st.pcSnapshot.map Prod.fst := by
  unfold reconcile
  rw [normalizeS_snapshot]
  simp only [List.map_map, Function.comp_def]

/-- Raw ack pooling changes no snapshot. -/
theorem poolAckRaw_snapshot (st : State n) (a : AckWire n) :
    (poolAckRaw st a).pcSnapshot = st.pcSnapshot := by
  delta poolAckRaw
  cases hdecode : a.decode? <;> dsimp only
  split <;> rfl


/-- A batch of raw acks changes no snapshot. -/
theorem fold_poolAckRaw_snapshot (st : State n) (as : List (AckWire n)) :
    (as.foldl poolAckRaw st).pcSnapshot = st.pcSnapshot := by
  induction as generalizing st with
  | nil => rfl
  | cons a as ih => rw [List.foldl_cons, ih, poolAckRaw_snapshot]

/-- Row admission changes no snapshot. -/
theorem admitRow_snapshot (p : Params) (st : State p.n) (a : RowWire p.n) :
    (admitRow p st a).pcSnapshot = st.pcSnapshot := by
  delta admitRow
  cases hdecode : a.decode? <;> dsimp only
  split <;> rfl


/-- A row batch changes no snapshot. -/
theorem fold_admitRow_snapshot (p : Params) (st : State p.n) (as : List (RowWire p.n)) :
    (as.foldl (admitRow p) st).pcSnapshot = st.pcSnapshot := by
  induction as generalizing st with
  | nil => rfl
  | cons a as ih => rw [List.foldl_cons, ih, admitRow_snapshot]

/-- Deliveries never add or remove freeze labels. -/
theorem process_snapshot_keys (p : Params) (st : State p.n) (o : Wire p.n) :
    (process p st o).pcSnapshot.map Prod.fst = st.pcSnapshot.map Prod.fst := by
  delta process
  cases hd : o.decode with
  | some msg => cases msg with
    | vote s i r =>
      dsimp only
      rfl
    | row i body =>
      dsimp only
      rw [admitRow_snapshot]
    | block s N =>
      dsimp only
      delta admitBlock
      split
      · rfl
      · cases hP : parentFG st N.erase
        · rfl
        · dsimp only
          split
          · rw [fold_admitRow_snapshot, (collectPCs_frame _).2.2.2.1, fold_poolAckRaw_snapshot]
            cases N.pc <;> dsimp only <;> split_ifs <;> simp only [reconcile_snapshot_keys] <;> rfl
          · rfl
    | ack s i r =>
      dsimp only
      unfold admitAck
      rw [(collectPCs_frame _).2.2.2.1]
      delta poolAck
      cases hdecode : AckWire.decode? (⟨o.auth, r⟩ : AckWire p.n) <;> dsimp only
      rename_i v
      rcases v with ⟨_, _, _⟩
      dsimp only
      split_ifs <;> rfl
    | pc d =>
      dsimp only
      unfold admitPC
      split
      · rw [(collectPCs_frame _).2.2.2.1, fold_poolAckRaw_snapshot]
      · rfl
  | none =>
    rfl

/-- A gate changes no snapshot. -/
theorem gateFrom_snapshot (p : Params) (a : Block) (cs : List (PC n)) (ρ : Option PCRank)
    (st : State n) (s : Slot) : (gateFrom p a cs ρ st s).pcSnapshot = st.pcSnapshot := by
  rw [gateFrom_def]
  dsimp only
  cases hc : SA.Root.confirmationFrom p.toParams a (actView st) s
  · rfl
  · dsimp only
    split
    · rfl
    · apply List.foldlRecOn (motive := fun a : State n => a.pcSnapshot = st.pcSnapshot)
      · rfl
      · intro acc ha b _
        apply List.foldlRecOn (motive := fun a : State n => a.pcSnapshot = st.pcSnapshot)
        · exact ha
        · intro acc' ha' g _
          exact ha'

/-- Gate completion changes no snapshot. -/
theorem gateStep_snapshot (p : Params) (st : State p.n) (s : Slot) :
    (gateStep p st s).pcSnapshot = st.pcSnapshot := by
  unfold gateStep
  rw [normalizeS_snapshot]
  split
  · rfl
  · exact gateFrom_snapshot _ _ _ _ _ _

/-- Only the freeze part of the pre-gate clock changes the snapshot list. -/
theorem clockPre_snapshot (p : Params) (st : State p.n) (t : Time) :
    (clockPre p st t).pcSnapshot =
      (let s := ((t - 3 * p.Δ) / (4 * p.Δ)).toNat
       if 0 ≤ t - 3 * p.Δ && t == SA.freezeTime p.toParams s then
         if (st.pcSnapshot.find? (fun row => row.1 == s)).isSome then st.pcSnapshot
         else st.pcSnapshot ++ [(s, st.pcs)]
       else st.pcSnapshot) := by
  unfold clockPre
  dsimp only
  split <;> split <;> split <;> rfl

/-- A clock adds a freeze label only at that label's freeze time. -/
theorem clock_snapshot_origin (p : Params) (st : State p.n) (t : Time) (s : Slot)
    (h : s ∈ (clock p st t).pcSnapshot.map Prod.fst) :
    s ∈ st.pcSnapshot.map Prod.fst ∨ t = SA.freezeTime p.toParams s := by
  have he : (clock p st t).pcSnapshot = (clockPre p st t).pcSnapshot := by
    unfold clock
    dsimp only
    split
    · exact gateStep_snapshot _ _ _
    · rfl
  rw [he, clockPre_snapshot] at h
  dsimp only at h
  split at h
  · rename_i hf
    split at h
    · exact Or.inl h
    · simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
        List.mem_singleton] at h
      rcases h with h | h
      · exact Or.inl h
      · subst s
        exact Or.inr (of_decide_eq_true (Bool.and_eq_true_iff.mp hf).2)
  · exact Or.inl h

end AvailableChain.PCSA
end

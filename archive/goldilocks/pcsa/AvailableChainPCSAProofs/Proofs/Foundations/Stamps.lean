module
public import AvailableChainPCSAProofs.Proofs.Foundations.SnapshotKeys
public import AvailableChainFGSARun.Proofs.Excludes

public section

/-! Held-PC stamps before a time bound (pcsa34-r4.3 §3.3, §3.6). -/

namespace AvailableChain.PCSA
variable {n : Nat}

/-- Every held PC has a stamp, and every stored stamp is below the bound. -/
def StampBound (t : Time) (st : State n) : Prop :=
  st.base.now < t ∧
    (∀ c ∈ st.pcs, ∃ row ∈ st.pcStamps, row.1 = c.slot ∧ row.2.1 = c.target.root) ∧
    ∀ row ∈ st.pcStamps, row.2.2 < t

theorem StampBound_def (t : Time) (st : State n) : StampBound t st =
    (st.base.now < t ∧
      (∀ c ∈ st.pcs, ∃ row ∈ st.pcStamps, row.1 = c.slot ∧ row.2.1 = c.target.root) ∧
      ∀ row ∈ st.pcStamps, row.2.2 < t) := by
  apply propext
  exact ⟨fun h => h, fun h => h⟩

/-- A stamp lookup on a held PC succeeds below the bound. -/
theorem held_pcStamp (t : Time) (st : State n) (h : StampBound t st)
    (c : PC n) (hc : c ∈ st.pcs) : ∃ a < t, pcStamp? st c = some a := by
  obtain ⟨row, hr, hs, hb⟩ := h.2.1 c hc
  cases he : st.pcStamps.find? (fun row => row.1 == c.slot && row.2.1 == c.target.root) with
  | none =>
    have hn := List.find?_eq_none.mp he row hr
    simp [hs, hb] at hn
  | some row =>
    exact ⟨row.2.2, h.2.2 row (List.mem_of_find?_eq_some he), by simp [pcStamp?_def, he]⟩

/-- Installation keeps the stamp bound, also when it replaces a stamp key. -/
theorem installPC_stampBound (t : Time) (st : State n) (c : PC n) (h : StampBound t st) :
    StampBound t (installPC st c) := by
  unfold installPC
  split
  · exact h
  · change st.base.now < t ∧ _ ∧ _
    refine ⟨h.1, ?_, ?_⟩
    · intro d hd
      change d ∈ st.pcs ++ [c] at hd
      by_cases hk : d.slot = c.slot ∧ d.target.root = c.target.root
      · exact ⟨(c.slot, c.target.root, st.base.now), List.mem_append_right _ (by simp),
          hk.1.symm, hk.2.symm⟩
      · have hd' : d ∈ st.pcs := by
          rcases List.mem_append.mp hd with hd | hd
          · exact hd
          · have he := List.mem_singleton.mp hd
            subst d
            exact (hk ⟨rfl, rfl⟩).elim
        obtain ⟨row, hr, hs, hb⟩ := h.2.1 d hd'
        refine ⟨row, List.mem_append_left _ (List.mem_filter.mpr ⟨hr, ?_⟩), hs, hb⟩
        simp only [Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne, hs, hb]
        exact not_and_or.mp hk
    · intro row hr
      rcases List.mem_append.mp hr with hr | hr
      · exact h.2.2 row (List.mem_filter.mp hr).1
      · have he := List.mem_singleton.mp hr
        subst row
        exact h.1

/-- Normalization keeps stamp bounds. -/
theorem normalizeS_stampBound (t : Time) (st : State n) (h : StampBound t st) :
    StampBound t (normalizeS st) := by
  unfold normalizeS
  split <;> exact h

/-- Reconciliation removes PCs but keeps the bound and stamps of those left. -/
theorem reconcile_stampBound (t : Time) (st : State n) (h : StampBound t st) :
    StampBound t (reconcile st) := by
  apply normalizeS_stampBound
  exact ⟨h.1, fun c hc => h.2.1 c (List.mem_filter.mp hc).1, h.2.2⟩

/-- Raw ack pooling keeps stamp bounds. -/
theorem poolAckRaw_stampBound (t : Time) (st : State n) (a : AckWire n)
    (h : StampBound t st) : StampBound t (poolAckRaw st a) := by
  delta poolAckRaw
  cases hdecode : a.decode? <;> dsimp only
  rotate_left
  · split <;> exact h
  · exact h

/-- Row admission keeps stamp bounds. -/
theorem admitRow_stampBound (p : Params) (t : Time) (st : State p.n) (a : RowWire p.n)
    (h : StampBound t st) : StampBound t (admitRow p st a) := by
  delta admitRow
  cases hdecode : a.decode? <;> dsimp only
  rotate_left
  · split <;> exact h
  · exact h

/-- Deliveries keep stamp bounds when the current clock is below the bound. -/
theorem process_stampBound (p : Params) (t : Time) (st : State p.n) (o : Wire p.n)
    (h : StampBound t st) : StampBound t (process p st o) := by
  have hc := collectPCs_invariant (n := p.n) (StampBound t)
    (fun st c h _ => installPC_stampBound t st c h)
  have ha (st : State p.n) (as : List (AckWire p.n)) (h : StampBound t st) :
      StampBound t (as.foldl poolAckRaw st) :=
    List.foldlRecOn as poolAckRaw h (fun acc ha a _ => poolAckRaw_stampBound t acc a ha)
  have hr (st : State p.n) (as : List (RowWire p.n)) (h : StampBound t st) :
      StampBound t (as.foldl (admitRow p) st) :=
    List.foldlRecOn as (admitRow p) h (fun acc ha a _ => admitRow_stampBound p t acc a ha)
  delta process
  cases hd : o.decode with
  | some msg => cases msg with
    | vote s i r =>
      dsimp only
      dsimp only [admitHead]
      simpa only [StampBound_def, FGSA.Run.Internal.grid_admitVote_now] using h
    | row i body =>
      dsimp only
      exact admitRow_stampBound p t st _ h
    | block s N =>
      dsimp only
      delta admitBlock
      split
      · exact h
      · cases hP : parentFG st N.erase
        · exact h
        · dsimp only
          split
          · apply hr
            apply hc
            apply ha
            cases N.pc <;> dsimp only <;> split_ifs <;>
              first
              | (apply reconcile_stampBound; simpa only [StampBound_def,
                  deleteConflictingLeases_def, FGSA.Run.Internal.grid_admitProposal_now] using h)
              | simpa only [StampBound_def, deleteConflictingLeases_def,
                  FGSA.Run.Internal.grid_admitProposal_now] using h
          · exact h
    | ack s i r =>
      dsimp only
      unfold admitAck
      apply hc
      delta poolAck
      cases hdecode : AckWire.decode? (⟨o.auth, r⟩ : AckWire p.n) <;> dsimp only
      rotate_left
      · rename_i v
        rcases v with ⟨_, _, _⟩
        split
        · exact h
        · split <;> exact h
      · exact h
    | pc d =>
      dsimp only
      unfold admitPC
      split
      · exact hc _ (ha _ _ h)
      · exact h
  | none =>
    exact h

/-- Gate steps keep stamp bounds. -/
theorem gateFrom_stampBound (p : Params) (t : Time) (a : Block) (cs : List (PC n))
    (ρ : Option PCRank) (st : State n) (s : Slot) (h : StampBound t st) :
    StampBound t (gateFrom p a cs ρ st s) := by
  rw [gateFrom_def]
  dsimp only
  cases hc : SA.Root.confirmationFrom p.toParams a (actView st) s
  · exact h
  · dsimp only
    split
    · exact h
    · apply List.foldlRecOn
      · exact h
      · intro acc ha b _
        apply List.foldlRecOn
        · exact ha
        · intro acc' ha' g _
          exact ha'

/-- A clock below the bound keeps all held-PC stamps below the bound. -/
theorem clock_stampBound (p : Params) (t u : Time) (st : State p.n)
    (hu : u < t) (h : StampBound t st) : StampBound t (clock p st u) := by
  have hc : StampBound t (clockPre p st u) := by
    unfold clockPre
    dsimp only
    split <;> split <;> split <;> exact ⟨hu, h.2⟩
  unfold clock
  dsimp only
  split
  · unfold gateStep
    apply normalizeS_stampBound
    split
    · exact hc
    · exact gateFrom_stampBound p t _ _ _ _ _ hc
  · exact hc

end AvailableChain.PCSA
end

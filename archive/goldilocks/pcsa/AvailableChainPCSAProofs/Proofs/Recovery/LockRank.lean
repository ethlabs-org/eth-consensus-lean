module
public import AvailableChainPCSAProofs.Proofs.Recovery.LockWindow

public section

/-! The local rank invariant for surviving locks. -/

namespace AvailableChain.PCSA

private def RecoveryRankSafe {n : Nat} (st : State n) : Prop :=
  ∀ row ∈ st.base.obligations, ∀ pc ∈ st.pcs,
    rankAtLeast pc (leaseRank st row.1) = true → Block.Compatible pc.target row.1

private theorem recovery_rank_rank_other {n : Nat} (st : State n) (b B : Block) (g : Nat)
    (d : Time) (rank : Option PCRank) (hne : B ≠ b) :
    leaseRank (writeLease st b g d rank) B = leaseRank st B := by
  simp only [leaseRank_def, writeLease_def, List.find?_append, List.find?_filter]
  have he : (fun row : Block × Option PCRank =>
      decide ((row.1 != b) = true ∧ (row.1 == B) = true)) =
      (fun row => row.1 == B) := by
    funext row
    by_cases h : row.1 = B
    · simp [h, hne]
    · simp [h]
  rw [he]
  simp [Ne.symm hne]

private theorem recovery_rank_write_safe {n : Nat} (st : State n) (b : Block) (g : Nat)
    (d : Time) (rank : Option PCRank) (h : RecoveryRankSafe st)
    (hok : leaseWriteOK st.pcs rank b = true) : RecoveryRankSafe (writeLease st b g d rank) := by
  intro row hr pc hp hk
  have hpcs : pc ∈ st.pcs := hp
  by_cases hb : row.1 = b
  · rw [hb, writeLease_rank] at hk
    exact hb ▸ (leaseWriteOK_iff st.pcs rank b).mp hok pc hpcs hk
  · rw [recovery_rank_rank_other st b row.1 g d rank hb] at hk
    apply h row ?_ pc hpcs hk
    change row ∈ (GridCO.writeObligation st.base b g d).obligations at hr
    delta GridCO.writeObligation at hr
    rcases List.mem_append.mp hr with hr | hr
    · exact (List.mem_filter.mp hr).1
    · have he := List.mem_singleton.mp hr
      exact (hb (congrArg Prod.fst he)).elim

private theorem recovery_rank_delete_safe {n : Nat} (st : State n) (pc : PC n)
    (h : RecoveryRankSafe st) :
    RecoveryRankSafe (deleteConflictingLeases st pc) := by
  intro row hr c hc hk
  exact h row (deleteConflictingLeases_subset st pc hr) c hc hk

private theorem recovery_rank_install_safe {n : Nat} (st : State n) (pc : PC n)
    (h : RecoveryRankSafe st) :
    RecoveryRankSafe (installPC st pc) := by
  rw [installPC_def]
  split
  · exact h
  · intro row hr c hc hk
    have hm := (mem_deleteConflictingLeases _ pc row).mp hr
    rcases List.mem_append.mp hc with hc | hc
    · exact h row hm.1 c hc hk
    · cases List.mem_singleton.mp hc
      rcases hm.2 with hn | hy
      · change rankAtLeast pc (leaseRank st row.1) = false at hn
        change rankAtLeast pc (leaseRank st row.1) = true at hk
        rw [hk] at hn
        cases hn
      · exact hy

private theorem recovery_rank_normalize_safe {n : Nat} (st : State n) (h : RecoveryRankSafe st) :
    RecoveryRankSafe (normalizeS st) := by
  delta normalizeS
  split <;> exact h

private theorem recovery_rank_reconcile_safe {n : Nat} (st : State n) (h : RecoveryRankSafe st) :
    RecoveryRankSafe (reconcile st) := by
  apply recovery_rank_normalize_safe
  intro row hr pc hp hk
  exact h row (List.mem_filter.mp hr).1 pc (List.mem_filter.mp hp).1 hk

private theorem recovery_rank_row_safe (p : Params) (st : State p.n) (a : RowWire p.n)
    (h : RecoveryRankSafe st) : RecoveryRankSafe (admitRow p st a) := by
  delta admitRow
  cases a.decode? <;> dsimp only
  · exact h
  · split <;> exact h

private theorem recovery_rank_raw_safe {n : Nat} (st : State n) (a : AckWire n)
    (h : RecoveryRankSafe st) : RecoveryRankSafe (poolAckRaw st a) := by
  delta poolAckRaw
  cases a.decode? <;> dsimp only
  · exact h
  · split <;> exact h

private theorem recovery_rank_process_safe (p : Params) (st : State p.n) (o : Wire p.n)
    (h : RecoveryRankSafe st) : RecoveryRankSafe (process p st o) := by
  have hc := collectPCs_invariant (n := p.n) RecoveryRankSafe
    (fun st pc h _ => recovery_rank_install_safe st pc h)
  have ha (st : State p.n) (as : List (AckWire p.n)) (h : RecoveryRankSafe st) :
      RecoveryRankSafe (as.foldl poolAckRaw st) :=
    List.foldlRecOn as poolAckRaw h (fun acc hh a _ => recovery_rank_raw_safe acc a hh)
  delta process
  cases hd : o.decode with
  | none => exact h
  | some msg => cases msg with
    | vote s i r =>
      intro row hr pc hp hk
      apply h row ?_ pc hp hk
      change row ∈ (GridCO.admitVote _ _ _).obligations at hr
      simpa only [GridCO.admitVote_obligations] using hr
    | row i body => exact recovery_rank_row_safe p st _ h
    | block s N =>
      dsimp only
      delta admitBlock
      split
      · exact h
      · cases hp : parentFG st N.erase
        · exact h
        · dsimp only
          split
          · apply List.foldlRecOn
            · apply hc
              apply ha
              have hb : RecoveryRankSafe { st with base := (GridCO.admitProposal
                  p.toParams.engine st.base (baseProposal s N.erase N.raw N.support)
                  N.erase (N.raw.map baseHead)) } := by
                intro row hr pc hp hk
                exact h row (by simpa only [GridCO.admitProposal_obligations] using hr)
                  pc hp hk
              cases N.pc <;> dsimp only <;> split_ifs <;> first
                | (apply recovery_rank_reconcile_safe; exact hb)
                | (apply recovery_rank_reconcile_safe; exact recovery_rank_delete_safe _ _ hb)
                | exact hb
                | exact recovery_rank_delete_safe _ _ hb
            · intro acc hh a _
              exact recovery_rank_row_safe p acc a hh
          · exact h
    | ack s i r =>
      dsimp only
      delta admitAck
      apply hc
      delta poolAck
      cases hd : AckWire.decode? (⟨o.auth, r⟩ : AckWire p.n) <;> dsimp only
      · exact h
      · rename_i v
        rcases v with ⟨_, _, _⟩
        split
        · exact h
        · split <;> exact h
    | pc pc =>
      dsimp only
      delta admitPC
      split
      · exact hc _ (ha _ _ h)
      · exact h

private theorem recovery_rank_gate_safe (p : Params) (st : State p.n) (a : Block)
    (rank : Option PCRank) (s : Slot) (h : RecoveryRankSafe st) :
    RecoveryRankSafe (gateFrom p a st.pcs rank st s) := by
  have hg : RecoveryRankSafe (gateFrom p a st.pcs rank st s) ∧
      (gateFrom p a st.pcs rank st s).pcs = st.pcs := by
    rw [gateFrom_def]
    dsimp only
    cases hc : SA.Root.confirmationFrom p.toParams a (actView st) s
    · exact ⟨h, rfl⟩
    · dsimp only
      split
      · exact ⟨h, rfl⟩
      · apply List.foldlRecOn (motive := fun acc : State p.n =>
          RecoveryRankSafe acc ∧ acc.pcs = st.pcs)
        · exact ⟨h, rfl⟩
        · intro acc hh b hb
          have hok : leaseWriteOK st.pcs rank b = true :=
            (Bool.and_eq_true_iff.mp (List.mem_filter.mp hb).2).2
          apply List.foldlRecOn (motive := fun acc' : State p.n =>
            RecoveryRankSafe acc' ∧ acc'.pcs = st.pcs)
          · exact hh
          · intro acc' hh' g _
            exact ⟨recovery_rank_write_safe acc' b g _ rank hh'.1 (by rw [hh'.2]; exact hok), hh'.2⟩
  exact hg.1

private theorem recovery_rank_clock_safe (p : Params) (st : State p.n) (t : Time)
    (h : RecoveryRankSafe st) : RecoveryRankSafe (clock p st t) := by
  have hc : RecoveryRankSafe (clockPre p st t) := by
    delta clockPre
    dsimp only
    split <;> split <;> split <;>
      try dsimp only [onView, actView, SA.Root.release]
    all_goals
      intro row hr pc hp hk
      apply h row ?_ pc hp hk
      try delta GridCO.release at hr
      try delta GridCO.freeze at hr
      try delta GridCO.expire at hr
      simp only [List.mem_filter] at hr
      tauto
  delta clock
  dsimp only
  split
  · rw [gateStep_def]
    dsimp only
    apply recovery_rank_normalize_safe
    split
    · exact hc
    · exact recovery_rank_gate_safe p _ _ _ _ hc
  · exact hc

/-- Every held PC at or above a live lock's rank has a compatible target. -/
theorem recovery_live_lock_rank_compatible (p : Params) (st : State p.n)
    (h : Reachable p st) (B : Block) (hB : LiveLease st B)
    (pc : PC p.n) (hpc : pc ∈ st.pcs)
    (hrank : rankAtLeast pc (leaseRank st B) = true) : Block.Compatible pc.target B := by
  have allSafe : ∀ st : State p.n, Reachable p st → RecoveryRankSafe st := by
    intro st hs
    induction hs with
    | init => intro row hr; exact (List.not_mem_nil hr).elim
    | tick t _ ih => exact recovery_rank_clock_safe p _ t ih
    | deliver o _ ih => exact recovery_rank_process_safe p _ o ih
  obtain ⟨row, hr, he, _⟩ := hB
  subst B
  exact allSafe st h row hr pc hpc hrank

/-- The rank invariant also applies to an exact stored row before expiry runs. -/
theorem recovery_stored_lock_rank_compatible (p : Params) (st : State p.n)
    (h : Reachable p st) (row : Block × Nat × Time)
    (hr : row ∈ st.base.obligations) (pc : PC p.n) (hpc : pc ∈ st.pcs)
    (hrank : rankAtLeast pc (leaseRank st row.1) = true) :
    Block.Compatible pc.target row.1 := by
  have allSafe : ∀ st : State p.n, Reachable p st → RecoveryRankSafe st := by
    intro st hs
    induction hs with
    | init => intro row hr; exact (List.not_mem_nil hr).elim
    | tick t _ ih => exact recovery_rank_clock_safe p _ t ih
    | deliver o _ ih => exact recovery_rank_process_safe p _ o ih
  exact allSafe st h row hr pc hpc hrank

/-- A nonempty gate rank has an active held-PC witness with an early stamp. -/
theorem recovery_gate_rank_witness (p : Params) (st : State p.n) (s : Slot)
    (rank : PCRank) (hr : gateRank p st s = some rank) :
    ∃ pc ∈ st.pcs, pc.rank = rank ∧ frameActive p st pc = true ∧
      ∃ t, t < SA.earlyTime p.toParams s ∧ pcStamp? st pc = some t := by
  rw [gateRank_def] at hr
  obtain ⟨pc, hp, he⟩ := Option.map_eq_some_iff.mp hr
  obtain ⟨hm, hf⟩ := List.mem_filter.mp (bestPC_mem _ pc hp)
  obtain ⟨ha, ht⟩ := Bool.and_eq_true_iff.mp hf
  refine ⟨pc, hm, he, ha, ?_⟩
  cases hs : pcStamp? st pc with
  | none => simp [hs] at ht
  | some t => exact ⟨t, by simpa only [hs, Option.any_some, decide_eq_true_eq] using ht, rfl⟩

end AvailableChain.PCSA
end

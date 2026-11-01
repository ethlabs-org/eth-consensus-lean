module
public import AvailableChainPCSAProofs.Proofs.Foundations.AckPool
public import AvailableChainPCSAProofs.Proofs.Foundations.Run

public section

/-! C3 store facts (pcsa34-r4.3 §3.6, §5.2.3). Ack pools are cumulative.
Admission still needs the run's slot, root, and honest-seat facts. -/

namespace AvailableChain.PCSA

/-- A decoded ack passes admission when its slot and root pass and its seat
has fewer than two roots. An ack already in the pool stays there. -/
theorem pcsa_poolAck_mem (p : Params) (st : State p.n) (a : AckWire p.n)
    (s : Slot) (i : Fin p.n) (r : BlockId) (hd : a.decode? = some (s, i, r))
    (hs : s ≤ st.slot p) (hr : ackSlotOK st s r = true)
    (hc : (seatAcks st s i).length < 2) : a ∈ (poolAck p st a).ackPool := by
  delta poolAck
  rw [hd]
  simp only [show ¬st.slot p < s from Nat.not_lt.mpr hs, decide_false, hr,
    Bool.not_true, Bool.false_or, Bool.or_false,
    show ¬2 ≤ (seatAcks st s i).length from Nat.not_le.mpr hc]
  split
  · exact of_decide_eq_true ‹_›
  · simp

/-- Collection after admission keeps the admitted ack. -/
theorem pcsa_admitAck_mem (p : Params) (st : State p.n) (a : AckWire p.n)
    (s : Slot) (i : Fin p.n) (r : BlockId) (hd : a.decode? = some (s, i, r))
    (hs : s ≤ st.slot p) (hr : ackSlotOK st s r = true)
    (hc : (seatAcks st s i).length < 2) : a ∈ (admitAck p st a).ackPool := by
  change a ∈ (collectPCs (poolAck p st a)).ackPool
  rw [(collectPCs_frame _).2.2.1]
  exact pcsa_poolAck_mem p st a s i r hd hs hr hc

/-- Raw ack folds preserve every old ack. -/
theorem pcsa_fold_poolAckRaw_mono (st : State n) (as : List (AckWire n)) :
    st.ackPool ⊆ (as.foldl poolAckRaw st).ackPool := by
  apply List.foldlRecOn (motive := fun acc : State n => st.ackPool ⊆ acc.ackPool)
  · exact List.Subset.refl _
  · intro acc h a _
    exact List.Subset.trans h (poolAckRaw_mono acc a)

private theorem row_pool (p : Params) (st : State p.n) (a : RowWire p.n) :
    (admitRow p st a).ackPool = st.ackPool := by
  delta admitRow
  cases a.decode? <;> dsimp only
  split <;> rfl

private theorem normalize_pool (st : State n) : (normalizeS st).ackPool = st.ackPool := by
  delta normalizeS
  split <;> rfl

private theorem reconcile_pool (st : State n) : (reconcile st).ackPool = st.ackPool := by
  delta reconcile
  rw [normalize_pool]

/-- No delivery handler removes an ack, including carried-PC admission
and frame reconciliation. -/
theorem pcsa_process_ackPool_mono (p : Params) (st : State p.n) (o : Wire p.n) :
    st.ackPool ⊆ (process p st o).ackPool := by
  delta process
  cases hd : o.decode with
  | none => exact List.Subset.refl _
  | some msg => cases msg with
    | vote s i r => exact List.Subset.refl _
    | row i body => exact (row_pool p st ⟨o.auth, body⟩) ▸ List.Subset.refl _
    | block s N =>
      dsimp only
      delta admitBlock
      split
      · exact List.Subset.refl _
      · cases parentFG st N.erase with
        | none => exact List.Subset.refl _
        | some P =>
          dsimp only
          split
          · apply List.foldlRecOn (motive := fun acc : State p.n => st.ackPool ⊆ acc.ackPool)
            · rw [(collectPCs_frame _).2.2.1]
              refine List.Subset.trans ?_ (pcsa_fold_poolAckRaw_mono _ _)
              cases N.pc <;> dsimp only
              all_goals repeat first
              | exact List.Subset.refl _
              | rw [reconcile_pool]
              | split
            · intro acc h a _
              rw [row_pool]
              exact h
          · exact List.Subset.refl _
    | ack s i r =>
      change st.ackPool ⊆ (collectPCs (poolAck p st _)).ackPool
      rw [(collectPCs_frame _).2.2.1]
      exact poolAck_mono p st _
    | pc C =>
      dsimp only
      delta admitPC
      split
      · rw [(collectPCs_frame _).2.2.1]
        exact pcsa_fold_poolAckRaw_mono st _
      · exact List.Subset.refl _

/-- Gates preserve the ack pool, including every lock write. -/
theorem pcsa_gateFrom_ackPool (p : Params) (a : Block) (cs : List (PC n))
    (rank : Option PCRank) (st : State n) (s : Slot) :
    (gateFrom p a cs rank st s).ackPool = st.ackPool := by
  rw [gateFrom_def]
  dsimp only
  cases SA.Root.confirmationFrom p.toParams a (actView st) s <;> dsimp only
  split
  · rfl
  · apply List.foldlRecOn (motive := fun acc : State n => acc.ackPool = st.ackPool)
    · rfl
    · intro acc h b _
      apply List.foldlRecOn (motive := fun acc : State n => acc.ackPool = st.ackPool)
      · exact h
      · intro acc' h' g _
        exact h'

/-- Clock operations preserve the ack pool. -/
theorem pcsa_clock_ackPool (p : Params) (st : State p.n) (t : Time) :
    (clock p st t).ackPool = st.ackPool := by
  have hpre : (clockPre p st t).ackPool = st.ackPool := by
    delta clockPre
    dsimp only
    split <;> split <;> split <;> rfl
  delta clock
  dsimp only
  split
  · rw [gateStep_def, normalize_pool]
    split
    · exact hpre
    · rw [pcsa_gateFrom_ackPool]
      exact hpre
  · exact hpre

end AvailableChain.PCSA
end

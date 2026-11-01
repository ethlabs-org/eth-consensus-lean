module
public import AvailableChainPCSAProofs.Proofs.Clean.AckDecisions
public import AvailableChainPCSAProofs.Proofs.Foundations.SnapshotKeys

public section

/-! C6 SnapshotContents: concrete receipt and count support. -/
namespace AvailableChain.PCSA
variable {n : Nat}
private def SnapshotPred (Q : Slot → PC n → Prop) (st : State n) : Prop :=
  ∀ row ∈ st.pcSnapshot, ∀ C ∈ row.2, Q row.1 C
private theorem snap_reconcile (Q : Slot → PC n → Prop) (st : State n)
    (h : SnapshotPred Q st) : SnapshotPred Q (reconcile st) := by
  change ∀ row ∈ (reconcile st).pcSnapshot, ∀ C ∈ row.2, Q row.1 C
  delta reconcile
  rw [normalizeS_snapshot]
  intro row hr C hC
  obtain ⟨old, hold, he⟩ := List.mem_map.mp hr
  subst row
  exact h old hold C (List.mem_filter.mp hC).1
private theorem snap_pool (p : Params) (st : State p.n) (a : AckWire p.n) :
    (poolAck p st a).pcSnapshot = st.pcSnapshot := by
  delta poolAck
  cases a.decode? with
  | none => rfl
  | some v =>
    rcases v with ⟨_, _, _⟩
    dsimp only
    split
    · rfl
    · split <;> rfl
private theorem snap_process (p : Params) (Q : Slot → PC p.n → Prop)
    (st : State p.n) (o : Wire p.n) (h : SnapshotPred Q st) :
    SnapshotPred Q (process p st o) := by
  change ∀ row ∈ (process p st o).pcSnapshot, ∀ C ∈ row.2, Q row.1 C
  delta process
  cases o.decode with
  | none => exact h
  | some msg => cases msg with
    | vote s i r => exact h
    | row i body => rw [admitRow_snapshot]; exact h
    | ack s i r =>
      change ∀ row ∈ (collectPCs (poolAck p st _)).pcSnapshot, ∀ C ∈ row.2, Q row.1 C
      rw [(collectPCs_frame _).2.2.2.1, snap_pool]
      exact h
    | pc C =>
      dsimp only
      delta admitPC
      split
      · rw [(collectPCs_frame _).2.2.2.1, fold_poolAckRaw_snapshot]
        exact h
      · exact h
    | block s N =>
      dsimp only
      delta admitBlock
      split
      · exact h
      · cases parentFG st N.erase with
        | none => exact h
        | some P =>
          dsimp only
          split
          · rw [fold_admitRow_snapshot, (collectPCs_frame _).2.2.2.1,
              fold_poolAckRaw_snapshot]
            cases N.pc <;> dsimp only
            all_goals split_ifs <;> first | exact h | (apply snap_reconcile; exact h)
          · exact h
private theorem snap_clock (p : Params) (Q : Slot → PC p.n → Prop)
    (st : State p.n) (t : Time) (h : SnapshotPred Q st)
    (hnew : ∀ s, t = SA.freezeTime p.toParams s → ∀ C ∈ st.pcs, Q s C) :
    SnapshotPred Q (clock p st t) := by
  have he : (clock p st t).pcSnapshot = (clockPre p st t).pcSnapshot := by
    delta clock
    dsimp only
    split
    · exact gateStep_snapshot _ _ _
    · rfl
  change ∀ row ∈ (clock p st t).pcSnapshot, ∀ C ∈ row.2, Q row.1 C
  rw [he, clockPre_snapshot]
  dsimp only
  split
  · rename_i hf
    split
    · exact h
    · intro row hr C hC
      rcases List.mem_append.mp hr with hr | hr
      · exact h row hr C hC
      · obtain rfl := List.mem_singleton.mp hr
        exact hnew _ (beq_iff_eq.mp (Bool.and_eq_true_iff.mp hf).2) C hC
  · exact h
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- Each snapshot entry came from the PC pool before its exact earlier freeze tick. -/
theorem pcsa_snapshot_row_origin (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (k : Nat) (x : V) :
    ∀ row ∈ (V2.D.Run.stateBefore E rho k x).st.pcSnapshot, ∀ C ∈ row.2,
      ∃ j < k, rho.events[j]? = some (.tick x (SA.freezeTime p.toParams row.1)) ∧
        C ∈ (V2.D.Run.stateBefore E rho j x).st.pcs := by
  let Q := fun s C => ∃ j < k, rho.events[j]? = some (.tick x (SA.freezeTime p.toParams s)) ∧
    C ∈ (V2.D.Run.stateBefore E rho j x).st.pcs
  have hz : SnapshotPred Q (initial p.n) := by
    intro row hr
    exact (List.not_mem_nil hr).elim
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => SnapshotPred Q nd.st) (Nat.zero_le k) x ?_ hz
  intro j e _ hjk he hy ih
  cases e with
  | restart y t =>
    change y = x at hy
    subst y
    change SnapshotPred Q (Function.update (V2.D.Run.stateBefore E rho j) x _ x).st
    rw [Function.update_self]
    exact hz
  | tick y t =>
    change y = x at hy
    subst y
    change SnapshotPred Q (Function.update (V2.D.Run.stateBefore E rho j) x _ x).st
    rw [Function.update_self]
    have ht := pcsa_tick_st E rho (V2.D.Run.stateBefore E rho j x) x t
    rw [ht]
    apply snap_clock p Q _ t ih
    intro s hs C hC
    exact ⟨j, hjk, hs ▸ he, hC⟩
  | deliver y o t =>
    change y = x at hy
    subst y
    change SnapshotPred Q (Function.update (V2.D.Run.stateBefore E rho j) x _ x).st
    rw [Function.update_self]
    exact snap_process p Q _ (toWire p o) ih
/-- A selected freeze snapshot has the same earlier PC-pool origin. -/
theorem pcsa_snapshot_pc_origin (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (k : Nat) (x : V) (s : Slot) (C : PC p.n)
    (hm : C ∈ pcSnapshotAt (V2.D.Run.stateBefore E rho k x).st s) :
    ∃ j < k, rho.events[j]? = some (.tick x (SA.freezeTime p.toParams s)) ∧
      C ∈ (V2.D.Run.stateBefore E rho j x).st.pcs := by
  delta pcSnapshotAt at hm
  cases hf : (V2.D.Run.stateBefore E rho k x).st.pcSnapshot.find? (fun row => row.1 == s) with
  | none => rw [hf] at hm; exact (List.not_mem_nil hm).elim
  | some row =>
    rw [hf] at hm
    have hs : row.1 = s := beq_iff_eq.mp
      (List.find?_some (p := fun row : Slot × List (PC p.n) => row.1 == s) hf)
    have hrow := List.mem_of_find?_eq_some hf
    have ho := pcsa_snapshot_row_origin E rho k x row hrow C hm
    rwa [hs] at ho
/-- Every snapshot is empty before the first possible PC ack duty. -/
theorem pcsa_snapshots_before_first_gate_empty [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hFault : FaultsBelowQA p c rho) (k : Nat) (x : V)
    (hk : k ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams 0)) (s : Slot) :
    pcSnapshotAt (V2.D.Run.stateBefore E rho k x).st s = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro C hC
  obtain ⟨j, hj, _, hC⟩ := pcsa_snapshot_pc_origin E rho k x s C hC
  have he := pcsa_pcs_before_first_gate_empty E rho h hFault j x
    ((Nat.le_of_lt hj).trans hk)
  rw [he] at hC
  exact List.not_mem_nil hC
end AvailableChain.PCSA.Run

end

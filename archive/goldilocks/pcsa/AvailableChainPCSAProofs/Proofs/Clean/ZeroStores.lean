module
public import AvailableChainPCSAProofs.Proofs.Clean.StoreOrigins
public import AvailableChainPCSAProofs.Proofs.Clean.LockOrigins
public import AvailableChainPCSAProofs.Proofs.Clean.AckDecisions

public section

/-! C6 ZeroStores: concrete receipt and count support. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- Before the first gate, every honest store has genesis S and no lock rows. -/
theorem pcsa_zero_store_before_gate (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (k : Nat) (x : V) (hx : x ∈ rho.honest)
    (hk : k ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams 0)) :
    (V2.D.Run.stateBefore E rho k x).st.base.stableRecord = .genesis ∧
      (V2.D.Run.stateBefore E rho k x).st.base.obligations = [] := by
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => nd.st.base.stableRecord = .genesis ∧ nd.st.base.obligations = [])
    (Nat.zero_le k) x ?_ ⟨rfl, rfl⟩
  intro j e _ hjk he hy ih
  cases e with
  | restart y t => exact (h.noRestart j y t he).elim
  | tick y t =>
    change y = x at hy
    subst y
    change (Function.update (V2.D.Run.stateBefore E rho j) x _ x).st.base.stableRecord = _ ∧
      (Function.update (V2.D.Run.stateBefore E rho j) x _ x).st.base.obligations = []
    rw [Function.update_self]
    have htime : t < SA.gateTime p.toParams 0 :=
      (Gen.V2.Duty.index_lt_idxBefore_iff h.valid.toScheduleWellFormed he _).mp
        (lt_of_lt_of_le hjk hk)
    have ht := pcsa_tick_st E rho (V2.D.Run.stateBefore E rho j x) x t
    rw [ht]
    constructor
    · rw [pcsa_clock_record_before_first_gate p _ t htime]
      exact ih.1
    · have hs := pcsa_clock_locks_before_first_gate p
        (V2.D.Run.stateBefore E rho j x).st t htime
      rw [ih.2] at hs
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro row hr
      exact (List.not_mem_nil (hs hr)).elim
  | deliver y o t =>
    change y = x at hy
    subst y
    change (Function.update (V2.D.Run.stateBefore E rho j) x _ x).st.base.stableRecord = _ ∧
      (Function.update (V2.D.Run.stateBefore E rho j) x _ x).st.base.obligations = []
    rw [Function.update_self]
    have hf := (hF x hx (j + 1)).1
    rw [V2.D.Run.stateBefore_succ E rho he] at hf
    change (Function.update (V2.D.Run.stateBefore E rho j) x _ x).st.fg.F = .genesis at hf
    rw [Function.update_self] at hf
    constructor
    · exact (pcsa_process_record_of_genesis p _ (toWire p o) hf).trans ih.1
    · have hs := pcsa_process_locks_subset p (V2.D.Run.stateBefore E rho j x).st (toWire p o)
      rw [ih.2] at hs
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro row hr
      exact (List.not_mem_nil (hs hr)).elim
/-- The label-zero store components hold at every inclusive read before the first gate. -/
theorem pcsa_zero_storeAt_before_gate [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (hFault : FaultsBelowQA p c rho)
    (x : V) (hx : x ∈ rho.honest) (t : Time) (ht : t < SA.gateTime p.toParams 0) :
    (storeAt p c E rho x t).base.stableRecord = .genesis ∧
      (storeAt p c E rho x t).base.obligations = [] ∧ (storeAt p c E rho x t).pcs = [] := by
  rw [storeAt_def, V2.D.Engine.readAt_eq_stateBefore h.valid.toScheduleWellFormed]
  have hk := pcsa_readAt_index_before_cut rho t (SA.gateTime p.toParams 0) ht
  have hs := pcsa_zero_store_before_gate E rho h hF _ x hx hk
  exact ⟨hs.1, hs.2, pcsa_pcs_before_first_gate_empty E rho h hFault _ x hk⟩
end AvailableChain.PCSA.Run

end

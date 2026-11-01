module
public import AvailableChainPCSAProofs.Proofs.Clean.VoteTransport
public import AvailableChainPCSAProofs.Proofs.Clean.ZeroStores
public import AvailableChainPCSAProofs.Proofs.Clean.SnapshotContents
public import AvailableChainPCSAProofs.Proofs.Clean.CarriedPCs
public import AvailableChainPCSAProofs.Proofs.Clean.ZeroResult

public section

/-! C6 ZeroViews: concrete receipt and count support. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- The slot-zero proposal duty emits no object. -/
theorem pcsa_no_honest_proposal_zero (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (B : Block) :
    ¬ Gen.V2.Duty.HonestProposalAt E (pcsaInterface p c (m := m)).toInterface rho 0 B := by
  rintro ⟨_, payload, _, k, hk, ho⟩
  rw [(V2.D.Run.step_tick_eq E rho hk).2] at ho
  obtain ⟨_, _, d, hd, _, hact⟩ := (V2.D.Engine.mem_tick_seat_iff E rho _ _ _
    (.prop 0) _ payload).mp ho
  have hD : d = .propAction 0 := by
    change d.signLabel = .prop 0 at hd
    cases d <;> cases hd
    rfl
  subst d
  cases m <;> change (none : Option (Msg p.n)) = some payload at hact
  all_goals cases hact
/-- A gate input exposes its exact earlier event-indexed store. -/
theorem pcsa_gateInAt_source (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (x : V) (s : Slot) (st : State p.n)
    (hi : gateInAt p c E rho x s = some st) :
    ∃ k, rho.events[k]? = some (.tick x (SA.gateTime p.toParams s)) ∧
      st = clockPre p (V2.D.Run.stateBefore E rho k x).st (SA.gateTime p.toParams s) := by
  rw [pcsa_gateInAt_def] at hi
  obtain ⟨nd, hnd, hs⟩ := Option.map_eq_some_iff.mp hi
  rw [pcsa_preTick_def] at hnd
  obtain ⟨k, hk, hnd⟩ := Option.map_eq_some_iff.mp hnd
  subst nd
  exact ⟨k, V2.D.Run.tickIdx?_spec hk, hs.symm⟩
/-- The label-zero gate input has no PC. -/
theorem pcsa_zero_gate_pcs [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hFault : FaultsBelowQA p c rho) (x : V) (st : State p.n)
    (hi : gateInAt p c E rho x 0 = some st) : st.pcs = [] := by
  obtain ⟨k, hk, hst⟩ := pcsa_gateInAt_source E rho x 0 st hi
  have he := V2.D.Engine.stateBefore_tick_eq_stateBeforeTime
    h.valid.toScheduleWellFormed h.noRestart hk
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ h.valid.toScheduleWellFormed] at he
  rw [hst, clockPre_pcs, he]
  exact pcsa_pcs_before_first_gate_empty E rho h hFault _ x (le_refl _)
/-- The first next-label root is genesis: its PC view and live lock list are empty. -/
theorem pcsa_zero_next_root [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (hFault : FaultsBelowQA p c rho)
    (x : V) (hx : x ∈ rho.honest) (R : Block)
    (hR : liveRootAt p c E rho x 1 = some R) : R = .genesis := by
  rw [pcsa_liveRootAt_def] at hR
  obtain ⟨nd, hnd, hR⟩ := Option.map_eq_some_iff.mp hR
  obtain ⟨k, hk, hst⟩ := pcsa_postClock_source E rho x _ nd hnd
  have ht : SA.voteTime p.toParams 1 < SA.gateTime p.toParams 0 := by
    have hp := p.deltaPos
    change 4 * p.Δ * (1 : Int) + p.Δ < 4 * p.Δ * (0 : Int) + 6 * p.Δ
    nlinarith
  have hki : k + 1 ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams 0) :=
    Nat.succ_le_of_lt ((Gen.V2.Duty.index_lt_idxBefore_iff h.valid.toScheduleWellFormed hk _).mpr
      ht)
  have hafter : nd.st = (V2.D.Run.stateBefore E rho (k + 1) x).st := by
    rw [hst, V2.D.Run.stateBefore_succ E rho hk]
    change clock p _ _ = (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st
    rw [Function.update_self]
    exact (pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k x) x _).symm
  rw [hafter] at hR
  let st := (V2.D.Run.stateBefore E rho (k + 1) x).st
  have hlocks : st.base.obligations = [] :=
    (pcsa_zero_store_before_gate E rho h hF (k + 1) x hx hki).2
  have hsnap : pcSnapshotAt st 0 = [] :=
    pcsa_snapshots_before_first_gate_empty E rho h hFault (k + 1) x hki 0
  have hcar : carriedPCs st 1 = [] :=
    pcsa_carriedPCs_before_first_gate_empty E rho h hFault (k + 1) x 1 hki
  have hview : voterPC p st 1 = none := by
    delta voterPC
    change bestPC ((pcSnapshotAt st 0 ++ carriedPCs st 1).filter _) = none
    rw [hsnap, hcar]
    rfl
  have hz := (hF x hx (k + 1)).2.1
  have hroot : liveRoot p st (voterPC p st 1) = .genesis := by
    rw [hview]
    delta liveRoot
    rw [hlocks]
    change eraseFG (controls p st).Z = .genesis
    rw [hz]
    rfl
  exact hR.symm.trans hroot
end AvailableChain.PCSA.Run

end

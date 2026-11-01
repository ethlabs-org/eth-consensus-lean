module
public import AvailableChainPCSAProofs.Proofs.Clean.InputTransport

public section

/-! C6 CommonInputs: concrete receipt and count support. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
private theorem common_input_shape (o : GridCO.Wire p.n .root) (s : Slot)
    (hl : GridCO.headLabel? o = some s) : ∃ i r, o = ⟨.seat s i, .head r⟩ := by
  rcases o with ⟨auth, payload⟩
  cases auth <;> cases payload <;> (delta GridCO.headLabel? at hl; cases hl)
  exact ⟨_, _, rfl⟩
/-- At the proposer tick, every preceding-label pooled HEAD is in the late denominator. -/
theorem pcsa_proposer_late_eq (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (k : Nat) (x : V) (s : Slot)
    (hk : rho.events[k]? = some (.tick x (GridCO.proposalTime p.toParams.engine (s + 1)))) :
    GridCO.lateVotes p.toParams.engine
      (actView (clock p (V2.D.Run.stateBefore E rho k x).st
        (GridCO.proposalTime p.toParams.engine (s + 1)))) s =
      proposerVotes (clock p (V2.D.Run.stateBefore E rho k x).st
        (GridCO.proposalTime p.toParams.engine (s + 1))) (s + 1) := by
  have he := V2.D.Engine.stateBefore_tick_eq_stateBeforeTime
    h.valid.toScheduleWellFormed h.noRestart hk
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ h.valid.toScheduleWellFormed] at he
  rw [he]
  change (GridCO.votesAt _ s).filter _ = GridCO.votesAt _ (s + 1 - 1)
  rw [Nat.add_sub_cancel]
  apply List.filter_eq_self.mpr
  intro o ho
  have hl : GridCO.headLabel? o = some s := beq_iff_eq.mp (List.mem_filter.mp ho).2
  obtain ⟨i, r, rfl⟩ := common_input_shape o s hl
  apply decide_eq_true
  have ht := pcsa_head_stamp_lt_at_clocked_read E rho h.valid.toScheduleWellFormed h.noRestart
    (V2.D.Run.idxBefore rho (GridCO.proposalTime p.toParams.engine (s + 1))) x s i r
    (GridCO.proposalTime p.toParams.engine (s + 1))
    (GridCO.proposalTime p.toParams.engine (s + 1)) (le_refl _) (List.mem_filter.mp ho).1
  have hb : GridCO.proposalTime p.toParams.engine (s + 1) ≤ SA.gateTime p.toParams s := by
    change 4 * p.Δ * ((s + 1 : Nat) : Int) ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    push_cast
    have hp := p.deltaPos
    nlinarith
  exact lt_of_lt_of_le ht hb
/-- In the delivery window: Every frozen voter input reaches the honest proposer pool, or that pool
caps its seat. -/
theorem pcsa_frozen_input_in_proposer_win (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (i : Fin p.n) (r : BlockId) (v : Time)
    (hT : T₀ ≤ SA.freezeTime p.toParams s) (hc : SA.gateTime p.toParams s ≤ cut)
    (hk : rho.events[k]? = some (.tick y (GridCO.proposalTime p.toParams.engine (s + 1))))
    (hm : (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
      (clock p (V2.D.Run.stateBefore E rho a x).st v).base.votes)
    (hs : GridCO.stampVote (clock p (V2.D.Run.stateBefore E rho a x).st v).base
      ⟨.seat s i, .head r⟩ < SA.freezeTime p.toParams s) :
    (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
      proposerVotes (clock p (V2.D.Run.stateBefore E rho k y).st
        (GridCO.proposalTime p.toParams.engine (s + 1))) (s + 1) ∨
    GridCO.equivocates (proposerVotes (clock p (V2.D.Run.stateBefore E rho k y).st
      (GridCO.proposalTime p.toParams.engine (s + 1))) (s + 1)) i = true := by
  have he : SA.freezeTime p.toParams s + E.Δ =
      GridCO.proposalTime p.toParams.engine (s + 1) := by
    rw [h.delta]
    change 4 * p.Δ * (s : Int) + 3 * p.Δ + p.Δ = 4 * p.Δ * ((s + 1 : Nat) : Int)
    push_cast
    ring
  have hi : V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s + E.Δ) ≤ k := by
    rw [he]
    apply Nat.le_of_not_gt
    intro hlt
    exact lt_irrefl _ ((Gen.V2.Duty.index_lt_idxBefore_iff h.valid.toScheduleWellFormed hk _).mp
      hlt)
  have ht := pcsa_frozen_input_relay_late_win E rho h hD (hT := hT) a k x y hx hy s i r v
    (GridCO.proposalTime p.toParams.engine (s + 1)) hc hi hm hs
  rwa [pcsa_proposer_late_eq E rho h k y s hk] at ht
/-- Every frozen voter input reaches the honest proposer pool, or that pool caps its seat. -/
theorem pcsa_frozen_input_in_proposer (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (i : Fin p.n) (r : BlockId) (v : Time)
    (hc : SA.gateTime p.toParams s ≤ cut)
    (hk : rho.events[k]? = some (.tick y (GridCO.proposalTime p.toParams.engine (s + 1))))
    (hm : (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
      (clock p (V2.D.Run.stateBefore E rho a x).st v).base.votes)
    (hs : GridCO.stampVote (clock p (V2.D.Run.stateBefore E rho a x).st v).base
      ⟨.seat s i, .head r⟩ < SA.freezeTime p.toParams s) :
    (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
      proposerVotes (clock p (V2.D.Run.stateBefore E rho k y).st
        (GridCO.proposalTime p.toParams.engine (s + 1))) (s + 1) ∨
    GridCO.equivocates (proposerVotes (clock p (V2.D.Run.stateBefore E rho k y).st
      (GridCO.proposalTime p.toParams.engine (s + 1))) (s + 1)) i = true :=
  pcsa_frozen_input_in_proposer_win E rho h (pcsa_strictFrom_of_healthy E rho hD 0) a k x y hx hy
    s i r v (pcsa_floor_freeze (pcsa_zero_le_proposal s)) hc hk hm hs
end AvailableChain.PCSA.Run

end

module
public import AvailableChainSAPC.Proofs.CleanConsequences
public import AvailableChainSAPC.Proofs.CertificateValidity

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

theorem clock_at_gate (p : Params) {n : Nat} (st : State n) (r : Slot) :
    clock p st (gateTime p r) = gate p (clockPreGate p st (gateTime p r)) r := by
  rw [clock_eq_gate_prestate]
  have ht : gateTime p r - 6 * p.Δ = 4 * p.Δ * (r : Time) := by
    change 4 * p.Δ * (r : Time) + 6 * p.Δ - 6 * p.Δ = _
    ring
  have hd : 4 * p.Δ ≠ 0 := ne_of_gt (by linarith [p.deltaPos])
  simp [ht, hd, mul_nonneg (show 0 ≤ 4 * p.Δ by linarith [p.deltaPos])
    (Int.natCast_nonneg r)]

theorem clockPreGate_pcData (p : Params) {n : Nat} (st : State n) (t : Time) :
    (clockPreGate p st t).bestPC = st.bestPC ∧
      capBroken p (clockPreGate p st t) = capBroken p st := by
  unfold clockPreGate
  dsimp only
  split_ifs <;> simp only [saveTimely]
  all_goals (try split_ifs) <;> constructor <;> first | rfl | trivial

/-- The run-level gate includes its raw result once the joint invariant
holds. The statement covers active and disabled mode with no cap. -/
theorem gate_includes_of_joint {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (last index : Nat)
    {path : Block → Prop} (h : CleanPathFacts p E rho last path)
    (hi : index < last) (v : V) (hv : v ∈ rho.honest) (r : Slot) (b : Block)
    (htick : rho.events[index]? = some (.tick v (gateTime p r)))
    (hraw : SA.confirmation p (Run.stateBefore (sapc p) rho index v).base r = some b) :
    Block.Preceq b (stable (Run.stateBefore (sapc p) rho (index + 1) v)) := by
  set_option backward.isDefEq.respectTransparency false in
  let st := Run.stateBefore (sapc p) rho index v
  have hs := h.states index hi.le v hv
  have hp := clockPreGate_clean p st (gateTime p r) hs
  have hb := h.genuine index hi v hv r b htick hraw
  have hpre : SA.confirmation p (clockPreGate p st (gateTime p r)).base r = some b := by
    rw [clockPreGate_base]
    exact (@GridCO.confirmation_eq_of_receiptData GridCO.slowLeasePolicy p.engine p.n
      _ st.base (GridCO.clockPreGate_receiptData p.engine st.base (gateTime p r))
      (base_receiptStamped_at_fold p _ v) r).trans hraw
  have hgate := gate_clean_includes p (clockPreGate p st (gateTime p r)) r h.chain
    hp.1 b hpre hb (by
      intro c hm hc
      rw [(clockPreGate_pcData p st (gateTime p r)).1] at hc
      rw [(clockPreGate_pcData p st (gateTime p r)).2] at hm
      exact h.gateAuthorities index hi v hv r c htick hm hc)
  rw [stateBefore_succ_event htick]
  simpa only [World.step, sapc, Function.update_self, clock_at_gate] using! hgate

/-- This reduction isolates the missing honest-proposal service proof.
Its service premise concerns raw gate results, before either guard.
The joint invariant then supplies all guards and preserves the result
through the remainder of the deadline's event prefix. -/
theorem clean_inclusion_of_joint_and_service {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (hs : ScheduleWellFormed E rho) {path : Block → Prop}
    (h : CleanPathFacts p E rho rho.events.length path) (t₀ : Time)
    (service : ∀ r, t₀ < proposalTime p r → HonestAwakeProposer E rho r →
      gateTime p r ≤ rho.horizon → ∃ b,
        HonestProposalAt E (sapcInterface p).toInterface rho r b ∧
        ∀ v ∈ rho.honest,
          SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some b) :
    IncludedFrom (sapc p) E (sapcInterface p).toInterface rho (sapcInterface p).stable
      t₀ (6 * p.Δ) ∧
    IncludedFrom (sapc p) E (sapcInterface p).toInterface rho (sapcInterface p).confirmed
      t₀ (6 * p.Δ) := by
  have hincluded : IncludedFrom (sapc p) E (sapcInterface p).toInterface rho
      (sapcInterface p).stable t₀ (6 * p.Δ) := by
    intro r hr hprop hh
    obtain ⟨b, hb, hraw⟩ := service r hr hprop hh
    refine ⟨b, hb, ?_⟩
    intro v hv
    have hpub : PublicTime E (gateTime p r) := by
      refine ⟨4 * r + 6, ?_⟩
      change 4 * p.Δ * (r : Time) + 6 * p.Δ = _
      rw [hΔ]
      push_cast
      ring
    have hnonneg : 0 ≤ gateTime p r := by
      change 0 ≤ 4 * p.Δ * (r : Time) + 6 * p.Δ
      nlinarith [p.deltaPos, Int.natCast_nonneg r]
    obtain ⟨index, hi⟩ := List.mem_iff_getElem?.mp (hs.tick_total v hv _ hpub hnonneg hh)
    have hlen := (List.getElem?_eq_some_iff.mp hi).1
    have hb' := gate_includes_of_joint p E rho rho.events.length index h hlen v hv r b hi
      (by rw [stateBefore_tick_eq_stateBeforeTime hs hi]; exact hraw v hv)
    change Block.Preceq b (stable (Run.readAt (sapc p) rho (gateTime p r) v))
    rw [readAt_eq_stateBefore hs]
    apply GridCO.prefix_trans _ _ _ hb'
    apply record_prefix_of_joint p E rho _ h _ _ _ (List.length_filter_le _ _) v hv
    exact Nat.succ_le_of_lt ((index_lt_read_length_iff hs (gateTime p r) hi).mpr (le_refl _))
  exact ⟨hincluded, hincluded⟩

end AvailableChain.SAPC
end

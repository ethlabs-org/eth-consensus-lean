module
public import AvailableChainPCSAProofs.Proofs.Clean.ZeroViews
public import AvailableChainPCSAProofs.Proofs.Clean.PCChain

public section

/-! C6 StorePCInputs: concrete receipt and count support. -/
namespace AvailableChain.PCSA
/-- An ack strictly before a gate has at most that gate's label. -/
theorem pcsa_early_label_before_gate (p : Params) (i j : Slot)
    (ht : SA.earlyTime p.toParams i < SA.gateTime p.toParams j) : i ≤ j := by
  by_contra hn
  have hi : (j : Int) + 1 ≤ (i : Int) := by exact_mod_cast Nat.lt_of_not_ge hn
  change 4 * p.Δ * (i : Int) + 2 * p.Δ < 4 * p.Δ * (j : Int) + 6 * p.Δ at ht
  have hp : (0 : Int) < p.Δ := p.deltaPos
  nlinarith
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}
/-- An indexed held PC before the next vote has a bounded honest ack. -/
theorem pcsa_pc_index_ack_slot (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hFault : FaultsBelowQA p c rho) (j k : Nat) (x : V) (hx : x ∈ rho.honest)
    (hk : k ≤ V2.D.Run.idxBefore rho (SA.voteTime p.toParams (j + 1)))
    (C : PC p.n) (hC : C ∈ (V2.D.Run.stateBefore E rho k x).st.pcs) :
    C.slot ≤ j ∧ ∃ y, HonestAckAt p c E rho y C.slot C.target := by
  obtain ⟨_, y, ha, ht⟩ := pcsa_pc_honest_ack_before E rho h hFault k x hx _ hk C hC
  exact ⟨pcsa_early_label_before_vote p C.slot j ht, y, ha⟩
/-- An indexed carried PC before the next vote has a bounded honest ack. -/
theorem pcsa_carriedPC_index_ack_slot (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hFault : FaultsBelowQA p c rho) (j k : Nat) (x : V) (hx : x ∈ rho.honest)
    (hk : k ≤ V2.D.Run.idxBefore rho (SA.voteTime p.toParams (j + 1)))
    (s : Slot) (C : PC p.n) (hC : C ∈ carriedPCs (V2.D.Run.stateBefore E rho k x).st s) :
    C.slot ≤ j ∧ ∃ y, HonestAckAt p c E rho y C.slot C.target := by
  obtain ⟨y, ha, ht⟩ := pcsa_carriedPC_honest_ack_before E rho h hFault k x hx s _ hk C hC
  exact ⟨pcsa_early_label_before_vote p C.slot j ht, y, ha⟩
/-- Each PC in an exact gate input has an honest ack of at most that gate's label. -/
theorem pcsa_gate_pc_ack_slot (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hFault : FaultsBelowQA p c rho) (x : V) (hx : x ∈ rho.honest) (s : Slot)
    (st : State p.n) (hst : gateInAt p c E rho x s = some st) (C : PC p.n) (hC : C ∈ st.pcs) :
    C.slot ≤ s ∧ ∃ y, HonestAckAt p c E rho y C.slot C.target := by
  obtain ⟨k, hk, he⟩ := pcsa_gateInAt_source E rho x s st hst
  rw [he, clockPre_pcs] at hC
  have hpre := V2.D.Engine.stateBefore_tick_eq_stateBeforeTime h.valid.toScheduleWellFormed
    h.noRestart hk
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ h.valid.toScheduleWellFormed] at hpre
  rw [hpre] at hC
  obtain ⟨_, y, ha, ht⟩ := pcsa_pc_honest_ack_before E rho h hFault _ x hx _ (le_refl _) C hC
  exact ⟨pcsa_early_label_before_gate p C.slot s ht, y, ha⟩
end AvailableChain.PCSA.Run

end

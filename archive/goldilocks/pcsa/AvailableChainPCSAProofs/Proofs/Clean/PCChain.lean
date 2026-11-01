module
public import AvailableChainPCSAProofs.Proofs.Clean.NRoot
public import AvailableChainPCSAProofs.Proofs.Clean.NCounts
public import AvailableChainPCSAProofs.Proofs.Clean.AckDecisions

public section

/-! C6 PCChain: concrete receipt and count support. -/
namespace AvailableChain.PCSA
/-- An ack before the next vote has no later label. -/
theorem pcsa_early_label_before_vote (p : Params) (i j : Slot)
    (ht : SA.earlyTime p.toParams i < SA.voteTime p.toParams (j + 1)) : i ≤ j := by
  by_contra hn
  have hi : (j : Int) + 1 ≤ (i : Int) := by exact_mod_cast Nat.lt_of_not_ge hn
  change 4 * p.Δ * (i : Int) + 2 * p.Δ <
    4 * p.Δ * ((j + 1 : Nat) : Int) + p.Δ at ht
  push_cast at ht
  have hp := p.deltaPos
  nlinarith
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}
/-- A bounded held PC has an exact honest ack and a bounded slot. -/
theorem pcsa_pc_storeAt_ack_slot (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hFault : FaultsBelowQA p c rho) (j : Slot) (x : V) (hx : x ∈ rho.honest)
    (t : Time) (ht : t < SA.voteTime p.toParams (j + 1))
    (C : PC p.n) (hC : C ∈ (storeAt p c E rho x t).pcs) :
    C.slot ≤ j ∧ ∃ y, HonestAckAt p c E rho y C.slot C.target := by
  obtain ⟨_, y, ha, htime⟩ := pcsa_pc_honest_ack_storeAt E rho h hFault x hx t _ ht C hC
  exact ⟨pcsa_early_label_before_vote p C.slot j htime, y, ha⟩
/-- Earlier ack dissemination orders all bounded held PC targets by slot. -/
theorem pcsa_pc_storeAt_chain (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (hFault : FaultsBelowQA p c rho) (j : Slot)
    (hdis : ∀ i i', i < i' → i' ≤ j → ∀ y A, HonestAckAt p c E rho y i A →
      ∀ z H, HonestHeadAt p c E rho z i' H → Block.Preceq A H)
    (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest) (t t' : Time)
    (ht : t < SA.voteTime p.toParams (j + 1))
    (ht' : t' < SA.voteTime p.toParams (j + 1)) (C D : PC p.n)
    (hC : C ∈ (storeAt p c E rho x t).pcs) (hD : D ∈ (storeAt p c E rho y t').pcs) :
    Block.Compatible C.target D.target ∧ (C.slot < D.slot → Block.Preceq C.target D.target) := by
  obtain ⟨hcj, u, hu⟩ := pcsa_pc_storeAt_ack_slot E rho h hFault j x hx t ht C hC
  obtain ⟨hdj, v, hv⟩ := pcsa_pc_storeAt_ack_slot E rho h hFault j y hy t' ht' D hD
  have forward (hlt : C.slot < D.slot) : Block.Preceq C.target D.target := by
    obtain ⟨z, hz⟩ := pcsa_ack_has_honest_head E rho h hF hFault v D.slot D.target hv
    exact hdis C.slot D.slot hlt hdj u C.target hu z D.target hz
  refine ⟨?_, forward⟩
  rcases lt_trichotomy C.slot D.slot with hlt | heq | hgt
  · exact Bool.or_eq_true_iff.mpr (Or.inl (forward hlt))
  · have hh := pcsa_ack_targets_unique E rho h hF hFault u v C.slot C.target D.target
      hu (heq.symm ▸ hv)
    rw [hh]
    exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl _)
      (Gen.Pure.block_preceq_refl _)
  · obtain ⟨z, hz⟩ := pcsa_ack_has_honest_head E rho h hF hFault u C.slot C.target hu
    exact Bool.or_eq_true_iff.mpr (Or.inr
      (hdis D.slot C.slot hgt hcj v D.target hv z C.target hz))
/-- Earlier, equal, and later label arguments make every bounded PC/result pair compatible. -/
theorem pcsa_pc_storeAt_result (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {cut ΔF : Time}
    (h : Clean₂ p c E rho cut ΔF) (hF : StageOneFrame p c E rho)
    (hFault : FaultsBelowQA p c rho) (j : Slot) (hc : SA.gateTime p.toParams j ≤ cut)
    (hpast : ∀ k, k ≤ j → ∀ z H, HonestHeadAt p c E rho z k H →
      ∀ y ∈ rho.honest, ∀ i X, i < k →
        gateResultAt p c E rho y i = some (some X) → Block.Preceq X H)
    (hdis : ∀ k i, k < i → i ≤ j → ∀ z B, HonestAckAt p c E rho z k B →
      ∀ y ∈ rho.honest, ∀ X,
        gateResultAt p c E rho y i = some (some X) → Block.Preceq B X)
    (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest) (t : Time)
    (ht : t < SA.voteTime p.toParams (j + 1)) (C : PC p.n)
    (hC : C ∈ (storeAt p c E rho x t).pcs) (i : Slot) (hi : i ≤ j) (X : Block)
    (hX : gateResultAt p c E rho y i = some (some X)) : Block.Compatible C.target X := by
  obtain ⟨hcj, z, hz⟩ := pcsa_pc_storeAt_ack_slot E rho h.base hFault j x hx t ht C hC
  rcases lt_trichotomy C.slot i with hlt | heq | hgt
  · exact Bool.or_eq_true_iff.mpr (Or.inl (hdis C.slot i hlt hi z C.target hz y hy X hX))
  · have hcut : SA.gateTime p.toParams i ≤ cut := by
      apply le_trans _ hc
      change 4 * p.Δ * (i : Int) + 6 * p.Δ ≤ 4 * p.Δ * (j : Int) + 6 * p.Δ
      have hle := Int.ofNat_le.mpr hi
      have hp := p.deltaPos
      nlinarith
    exact pcsa_honestAck_same_label_result E rho h hF hFault z y hy
      i C.target X hcut (heq ▸ hz) hX
  · obtain ⟨u, hu⟩ := pcsa_ack_has_honest_head E rho h.base hF hFault z C.slot C.target hz
    exact Bool.or_eq_true_iff.mpr (Or.inr (hpast C.slot hcj u C.target hu y hy i X hgt hX))
end AvailableChain.PCSA.Run

end

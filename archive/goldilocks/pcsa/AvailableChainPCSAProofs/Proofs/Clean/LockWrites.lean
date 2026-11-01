module
public import AvailableChainPCSAProofs.Proofs.Clean.StorePCInputs
public import AvailableChainPCSAProofs.Proofs.Foundations.Locks

public section

/-! C6 LockWrites: concrete receipt and count support. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}
/-- Ack/result compatibility prevents every veto of a lock write below an honest result. -/
theorem pcsa_lock_write_all_of_ack_results (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hFault : FaultsBelowQA p c rho) (j : Slot)
    (hcompat : ∀ s, s ≤ j → ∀ z B, HonestAckAt p c E rho z s B →
      ∀ i, i ≤ j → ∀ y ∈ rho.honest, ∀ X,
        gateResultAt p c E rho y i = some (some X) → Block.Compatible B X)
    (x : V) (hx : x ∈ rho.honest) (i : Slot) (hi : i ≤ j) (st : State p.n) (X b : Block)
    (hst : gateInAt p c E rho x i = some st) (hX : gateResultAt p c E rho x i = some (some X))
    (hb : Block.Preceq b X) : leaseWriteOK st.pcs (gateRank p st i) b = true := by
  apply (leaseWriteOK_iff st.pcs (gateRank p st i) b).mpr
  intro C hC _
  obtain ⟨hs, z, ha⟩ := pcsa_gate_pc_ack_slot E rho h hFault x hx i st hst C hC
  have hc := hcompat C.slot (hs.trans hi) z C.target ha i hi x hx X hX
  rcases Bool.or_eq_true_iff.mp hc with hCX | hXC
  · exact Gen.Pure.block_compatible_of_common hCX hb
  · exact Bool.or_eq_true_iff.mpr (Or.inr (Gen.Pure.block_preceq_trans hb hXC))
end AvailableChain.PCSA.Run

end

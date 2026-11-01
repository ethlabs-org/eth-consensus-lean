module
public import AvailableChainPCSAProofs.Proofs.Clean.NRoot
public import AvailableChainPCSAProofs.Proofs.Clean.GateBatch
public import AvailableChainPCSAProofs.Proofs.Clean.StepVote
public import AvailableChainPCSAProofs.Proofs.Clean.RecordOrder
public import AvailableChainPCSAProofs.Proofs.Clean.PCChain
public import AvailableChainPCSAProofs.Proofs.Clean.RunLockKeep
public import AvailableChainPCSAProofs.Proofs.Clean.LockWrites
public import AvailableChainPCSAProofs.Proofs.Clean.AckResults
public import AvailableChainPCSAProofs.Proofs.Clean.HonestProposal
public import AvailableChainPCSAProofs.Proofs.Clean.ZeroViews
public import AvailableChainPCSAProofs.Proofs.Clean.NDissemination

public section

/-! C6 JointAux: concrete receipt and count support. -/
namespace AvailableChain.PCSA
/-- Gate times preserve label order. -/
theorem pcsa_gate_time_mono (p : Params) {i j : Slot} (h : i ≤ j) :
    SA.gateTime p.toParams i ≤ SA.gateTime p.toParams j := by
  change 4 * p.Δ * (i : Int) + 6 * p.Δ ≤ 4 * p.Δ * (j : Int) + 6 * p.Δ
  have hp : (0 : Int) ≤ 4 * p.Δ := le_of_lt (mul_pos (by norm_num) p.deltaPos)
  exact Int.add_le_add (mul_le_mul_of_nonneg_left (Int.ofNat_le.mpr h) hp) (Int.le_refl _)
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    {m : FGMode} (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
/-- The joint induction retains coverage of earlier ack targets at later reads. -/
structure CleanAckCoverageAt (j : Slot) : Prop where
  heads : ∀ i k, i < k → k ≤ j + 1 → ∀ y B, HonestAckAt p c E rho y i B →
    ∀ x H, HonestHeadAt p c E rho x k H → Block.Preceq B H
  results : ∀ i k, i < k → k ≤ j → ∀ y B, HonestAckAt p c E rho y i B →
    ∀ x ∈ rho.honest, ∀ X, gateResultAt p c E rho x k = some (some X) → Block.Preceq B X
end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}
/-- At label zero, every relevant ack target is genesis and later-result coverage is empty. -/
theorem pcsa_ack_coverage_zero (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (hFault : FaultsBelowQA p c rho) :
    CleanAckCoverageAt p c E rho 0 := by
  constructor
  · intro i k hik hk y B hB x H _
    have hi0 : i = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (hik.trans_le hk))
    subst i
    obtain ⟨z, hz⟩ := pcsa_ack_has_honest_head E rho h hF hFault y 0 B hB
    rw [pcsa_honestHead_zero E rho z B hz]
    exact Gen.Pure.block_genesis_preceq H
  · intro i k hik hk
    have hk0 := Nat.eq_zero_of_le_zero hk
    subst k
    exact (Nat.not_lt_zero i hik).elim
/-- Adjacent HEAD coverage and ordered results give coverage of every earlier result. -/
theorem pcsa_heads_cover_past_results (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {cut ΔF : Time}
    (h : Clean₂ p c E rho cut ΔF) (hF : StageOneFrame p c E rho)
    (j : Slot) (hc : SA.gateTime p.toParams j ≤ cut)
    (hchain : ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ i i' X Y, i ≤ i' → i' ≤ j →
      gateResultAt p c E rho x i = some (some X) → gateResultAt p c E rho y i' = some (some Y) →
      (i < i' → Block.Preceq X Y) ∧ (i = i' → Block.Compatible X Y))
    (hheads : ∀ i x y H X, 0 < i → i ≤ j → HonestHeadAt p c E rho x i H → y ∈ rho.honest →
      gateResultAt p c E rho y (i - 1) = some (some X) → Block.Preceq X H)
    (k : Slot) (hk : k ≤ j) (z : V) (H : Block) (hH : HonestHeadAt p c E rho z k H)
    (y : V) (hy : y ∈ rho.honest) (i : Slot) (X : Block) (hi : i < k)
    (hX : gateResultAt p c E rho y i = some (some X)) : Block.Preceq X H := by
  have hprev : k - 1 ≤ j := (Nat.sub_le k 1).trans hk
  obtain ⟨D, hD⟩ := pcsa_clean_result_exists E rho h hF y hy (k - 1)
    ((pcsa_gate_time_mono p hprev).trans hc)
  have hiPrev : i ≤ k - 1 := Nat.le_pred_of_lt hi
  have hXD : Block.Preceq X D := by
    rcases hiPrev.lt_or_eq with hlt | heq
    · exact (hchain y hy y hy i (k - 1) X D hiPrev hprev hX hD).1 hlt
    · subst i
      have he : X = D := Option.some.inj (Option.some.inj (hX.symm.trans hD))
      rw [he]
      exact Gen.Pure.block_preceq_refl _
  exact Gen.Pure.block_preceq_trans hXD
    (hheads k z y H D (Nat.lt_of_le_of_lt (Nat.zero_le i) hi) hk hH hy hD)
end AvailableChain.PCSA.Run

end

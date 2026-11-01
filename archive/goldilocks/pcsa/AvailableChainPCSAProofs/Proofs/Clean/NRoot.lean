module
public import AvailableChainPCSAProofs.Proofs.Clean.RootSources
public import AvailableChainPCSAProofs.Proofs.Clean.NHeads

public section

/-! C6 NRoot: concrete receipt and count support. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}
/-- Every honest ack target is an exact honest HEAD of its label. -/
theorem pcsa_ack_has_honest_head (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (hFault : FaultsBelowQA p c rho)
    (x : V) (s : Slot) (B : Block) (ha : HonestAckAt p c E rho x s B) :
    ∃ y, HonestHeadAt p c E rho y s B := by
  obtain ⟨nd, hnd, _, _, hN, _⟩ := pcsa_honestAck_N_source E rho x s B ha
  obtain ⟨a, _, hst⟩ := pcsa_postClock_source E rho x _ nd hnd
  rw [hst] at hN
  exact pcsa_N_has_honest_head E rho h hF hFault a x ha.1 _ s B hN
/-- Honest ack targets of the same label are equal as full scoped blocks. -/
theorem pcsa_ack_targets_unique (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (hFault : FaultsBelowQA p c rho)
    (x y : V) (s : Slot) (B C : Block)
    (hB : HonestAckAt p c E rho x s B) (hC : HonestAckAt p c E rho y s C) : B = C := by
  obtain ⟨nx, hx, _, _, hnB, _⟩ := pcsa_honestAck_N_source E rho x s B hB
  obtain ⟨ny, hy, _, _, hnC, _⟩ := pcsa_honestAck_N_source E rho y s C hC
  obtain ⟨a, _, hsa⟩ := pcsa_postClock_source E rho x _ nx hx
  obtain ⟨b, _, hsb⟩ := pcsa_postClock_source E rho y _ ny hy
  rw [hsa] at hnB
  rw [hsb] at hnC
  exact pcsa_N_targets_unique E rho h hF hFault a b x y hB.1 hC.1 _ _ s B C hnB hnC
/-- Prior dissemination and prior-result coverage place the next root below an N target. -/
theorem pcsa_ack_next_root_below (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (hFault : FaultsBelowQA p c rho)
    (s : Slot)
    (hpast : ∀ y H, HonestHeadAt p c E rho y s H →
      ∀ x ∈ rho.honest, ∀ i X, i < s →
        gateResultAt p c E rho x i = some (some X) → Block.Preceq X H)
    (hdis : ∀ i, i < s → ∀ y A, HonestAckAt p c E rho y i A →
      ∀ z H, HonestHeadAt p c E rho z s H → Block.Preceq A H)
    (x y : V) (hx : x ∈ rho.honest) (B R : Block)
    (hB : HonestAckAt p c E rho y s B)
    (hR : liveRootAt p c E rho x (s + 1) = some R) : Block.Preceq R B := by
  obtain ⟨z, hz⟩ := pcsa_ack_has_honest_head E rho h hF hFault y s B hB
  rcases pcsa_next_root_source E rho h hF hFault x hx s R hR with
    hgen | ⟨u, i, ha, ht⟩ | ⟨i, X, hi, hX, hrX⟩
  · rw [hgen]
    exact Gen.Pure.block_genesis_preceq _
  · have his : i ≤ s := by
      by_contra hn
      have hi : (s : Int) + 1 ≤ (i : Int) := by exact_mod_cast Nat.lt_of_not_ge hn
      change 4 * p.Δ * (i : Int) + 2 * p.Δ <
        4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ at ht
      push_cast at ht
      have hp := p.deltaPos
      nlinarith
    rcases his.lt_or_eq with hi | hi
    · exact hdis i hi u R ha z B hz
    · subst i
      rw [pcsa_ack_targets_unique E rho h hF hFault u y s R B ha hB]
      exact Gen.Pure.block_preceq_refl _
  · exact Gen.Pure.block_preceq_trans hrX (hpast z B hz x hx i X hi hX)
end AvailableChain.PCSA.Run

end

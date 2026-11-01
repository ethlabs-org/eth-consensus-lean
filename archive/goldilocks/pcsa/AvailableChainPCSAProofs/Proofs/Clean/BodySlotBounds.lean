module
public import AvailableChainPCSAProofs.Proofs.Clean.BodyRelayTime

public section

/-! C6 BodySlotBounds: concrete receipt and count support. -/
namespace AvailableChain.PCSA
/-- An admitted body has a past-or-current slot and a strictly earlier parent slot. -/
theorem pcsa_admission_slot_bounds (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) (P : SimplexFG.FGBlock (Fin p.n))
    (ha : blockAccepted p st s N P = true) :
    N.erase.slot ≤ st.slot p ∧ N.erase.parent.slot < N.erase.slot := by
  change (_ && decide (N.erase.slot ≤ st.slot p) && _ && _ &&
    decide (N.erase.parent.slot < N.erase.slot) && _ && _ && _ && _) = true at ha
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ha
  exact ⟨ha.1.1.1.1.1.1.1.2, ha.1.1.1.1.2⟩
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- Every stored non-genesis body has a strictly earlier parent slot. -/
theorem pcsa_body_parent_slot_lt (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (k : Nat) (x : V) (B : Block) (hg : B ≠ .genesis)
    (hm : B ∈ (V2.D.Run.stateBefore E rho k x).st.base.blocks) : B.parent.slot < B.slot := by
  obtain ⟨_, _, _, _, _, N, P, _, _, he, _, ha, _⟩ :=
    pcsa_body_receipt_origin E rho h.valid k x B hg hm
  rw [← he]
  exact (pcsa_admission_slot_bounds p _ _ N P ha).2
/-- A read before the next proposal contains no later-slot body. -/
theorem pcsa_body_slot_before_next_proposal (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (k : Nat) (x : V) (s : Slot)
    (hk : k ≤ V2.D.Run.idxBefore rho (SA.proposalTime p.toParams (s + 1)))
    (B : Block) (hm : B ∈ (V2.D.Run.stateBefore E rho k x).st.base.blocks) : B.slot ≤ s := by
  by_cases hg : B = .genesis
  · rw [hg]
    exact Nat.zero_le _
  · obtain ⟨j, hj, t, o, r, N, P, he, _, hB, _, hacc, _⟩ :=
      pcsa_body_receipt_origin E rho h.valid k x B hg hm
    have hslot := (pcsa_admission_slot_bounds p _ r N P hacc).1
    rw [hB] at hslot
    apply hslot.trans
    have ht := (Gen.V2.Duty.index_lt_idxBefore_iff h.valid.toScheduleWellFormed he _).mp
      (hj.trans_le hk)
    have hnow := V2.D.Engine.stateBefore_now_le_event_noRestart (pcsaClock p c) E rho
      h.valid.toScheduleWellFormed h.noRestart he x
    rw [pcsa_clock_read p c (m := m) (V2.D.Run.stateBefore E rho j x)] at hnow
    have htime : (V2.D.Run.stateBefore E rho j x).st.base.now ≤
        4 * p.Δ * (s : Int) + (4 * p.Δ - 1) := by
      change t < 4 * p.Δ * ((s + 1 : Nat) : Int) at ht
      push_cast at ht
      change (V2.D.Run.stateBefore E rho j x).st.base.now ≤ t at hnow
      have hti : (t : Int) < (4 : Int) * p.Δ * ((s : Int) + 1) := ht
      have hni : ((V2.D.Run.stateBefore E rho j x).st.base.now : Int) ≤ (t : Int) := hnow
      have ht' : (t : Int) ≤ (4 : Int) * p.Δ * ((s : Int) + 1) - 1 :=
        Int.le_sub_one_of_lt hti
      nlinarith only [ht', hni]
    have hp : (0 : Int) < p.Δ := p.deltaPos
    have hfloor := pcsa_slotOf_offset p s (4 * p.Δ - 1) (by omega) (by omega)
    change p.slotOf (V2.D.Run.stateBefore E rho j x).st.base.now ≤ s
    rw [← hfloor]
    have hden : (0 : Int) < 4 * p.Δ := mul_pos (by norm_num) hp
    exact Int.toNat_le_toNat (Int.ediv_le_ediv hden htime)
end AvailableChain.PCSA.Run

end

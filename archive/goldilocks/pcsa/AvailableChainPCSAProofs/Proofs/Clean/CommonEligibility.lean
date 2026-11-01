module
public import AvailableChainPCSAProofs.Proofs.Shared.Clock
public import AvailableChainPCSAProofs.Proofs.Clean.Saturation

public section

/-! C6 CommonEligibility: concrete receipt and count support. -/
namespace AvailableChain.PCSA
/-- At a zero band floor, eligibility depends only on the majority and current-slot tests. -/
theorem pcsa_eligible_zero_floor (p : Params) (st : State p.n)
    (raw sup : List (GridCO.Wire p.n .root)) (B : Block)
    (hlo : (controls p st).lo = 0) :
    eligible p st raw sup B =
      (decide (GridCO.voterCount raw < 2 * GridCO.goldfishScore st.base.blocks raw sup B) ||
        B.slot == st.slot p) := by
  delta eligible
  rw [hlo]
  simp only [Nat.not_lt_zero, and_false, exists_false, decide_false, Bool.false_or]
/-- Equal counts and clock slots give equal eligibility in stage one. -/
theorem pcsa_eligible_equal_counts (p : Params) (src dst : State p.n)
    (raw sup raw' sup' : List (GridCO.Wire p.n .root))
    (hsrc : (controls p src).lo = 0) (hdst : (controls p dst).lo = 0)
    (hslot : src.slot p = dst.slot p) (hcount : GridCO.voterCount raw = GridCO.voterCount raw')
    (hscore : ∀ B, GridCO.goldfishScore src.base.blocks raw sup B =
      GridCO.goldfishScore dst.base.blocks raw' sup' B) :
    ∀ B, eligible p src raw sup B = eligible p dst raw' sup' B := by
  intro B
  rw [pcsa_eligible_zero_floor p src raw sup B hsrc,
    pcsa_eligible_zero_floor p dst raw' sup' B hdst, hcount, hscore B, hslot]
/-- A proposal-slot body is eligible at a read of that slot. -/
theorem pcsa_eligible_current_slot (p : Params) (st : State p.n)
    (raw sup : List (GridCO.Wire p.n .root)) (B : Block) (hs : B.slot = st.slot p) :
    eligible p st raw sup B = true := by
  delta eligible
  rw [hs, beq_self_eq_true, Bool.or_true]
/-- The actual proposer clock reads its duty slot. -/
theorem pcsa_proposal_clock_slot (p : Params) (st : State p.n) (s : Slot) :
    (clock p st (SA.proposalTime p.toParams s)).slot p = s := by
  change p.slotOf (clock p st (SA.proposalTime p.toParams s)).base.now = s
  rw [pcsa_clock_now]
  change p.slotOf (4 * p.Δ * (s : Int)) = s
  simpa only [add_zero] using Run.pcsa_slotOf_offset p s 0 le_rfl
    (mul_pos (by norm_num) p.deltaPos)
/-- The actual voter clock reads its duty slot. -/
theorem pcsa_vote_clock_slot (p : Params) (st : State p.n) (s : Slot) :
    (clock p st (SA.voteTime p.toParams s)).slot p = s := by
  change p.slotOf (clock p st (SA.voteTime p.toParams s)).base.now = s
  rw [pcsa_clock_now]
  change p.slotOf (4 * p.Δ * (s : Int) + p.Δ) = s
  have hp : (0 : Int) < p.Δ := p.deltaPos
  exact Run.pcsa_slotOf_offset p s p.Δ hp.le (by omega)
end AvailableChain.PCSA

end

module
-- shake keep reason: source declarations
public import AvailableChainFGSAProofs.Proofs.Healing.SupportRelease -- shake: keep

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params}

private theorem releaseScope_vote_release (s : Slot) :
    SA.voteTime p.toParams (s + 1) = SA.releaseTime p.toParams s := by
  change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ = 4 * p.Δ * (s : Int) + 5 * p.Δ
  push_cast
  ring

private theorem releaseScope_vote_clock (st : State p.n) (s : Slot) :
    FGSA.clock p st (SA.voteTime p.toParams (s + 1)) =
      clockPre p st (SA.voteTime p.toParams (s + 1)) := by
  have hn : isGateTime p (SA.voteTime p.toParams (s + 1)) ≠ true := by
    intro hh
    obtain ⟨r, hr⟩ := (isGateTime_iff p _).mp hh
    symm at hr
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ =
      4 * p.Δ * (r : Int) + 6 * p.Δ at hr
    push_cast at hr
    have hd := p.deltaPos
    rcases Nat.lt_or_ge r s with hrs | hsr
    · have hi : (r : Int) + 1 ≤ (s : Int) := by exact_mod_cast hrs
      nlinarith
    · have hi : (s : Int) ≤ (r : Int) := by exact_mod_cast hsr
      nlinarith
  change (if isGateTime p _ then _ else _) = _
  rw [ite_eq_right hn]

/-- At release, each surviving lease passed expiry in both join branches.
Expiry membership does not require the strict release count. -/
theorem healing_release_rows_expiry (st : State p.n) (s : Slot)
    (row : Block × Nat × Time)
    (hrow : row ∈ (FGSA.clock p st (SA.voteTime p.toParams (s + 1))).base.obligations) :
    row ∈ (GridCO.expire { st.base with now := SA.releaseTime p.toParams s }
      (SA.releaseTime p.toParams s)).obligations := by
  rw [releaseScope_vote_clock, releaseScope_vote_release] at hrow
  have hsub : (clockPre p st (SA.releaseTime p.toParams s)).base.obligations ⊆
      (GridCO.expire { st.base with now := SA.releaseTime p.toParams s }
        (SA.releaseTime p.toParams s)).obligations := by
    unfold clockPre
    dsimp only
    split_ifs <;>
      first
      | exact List.Subset.refl _
      | exact List.filter_sublist.subset
  exact hsub hrow

end AvailableChain.FGSA.Run
end

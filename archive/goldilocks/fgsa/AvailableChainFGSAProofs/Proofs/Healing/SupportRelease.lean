module
public import AvailableChainFGSAProofs.Proofs.Shared.Reads

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params}

private theorem transfer_vote_release (s : Slot) :
    SA.voteTime p.toParams (s + 1) = SA.releaseTime p.toParams s := by
  change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ = 4 * p.Δ * (s : Int) + 5 * p.Δ
  push_cast
  ring

private theorem transfer_vote_clock' (st : State p.n) (s : Slot) :
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

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:689–692 (H.1 release); plan H-SUPPORT §4 step 5 (G5).
DC: SAME the HEAD tick at q_s = v_(s+1) runs only expiry and the label-s release
on the active view, so every surviving lease passed the release count test. -/
theorem healing_support_release_rows (st : State p.n) (s : Slot)
    (hj : joinedAtTime p st.restartTime (SA.releaseTime p.toParams s) = true)
    (row : Block × Nat × Time)
    (hrow : row ∈ (FGSA.clock p st (SA.voteTime p.toParams (s + 1))).base.obligations) :
    let st1 : State p.n := { st with
      base := GridCO.expire { st.base with now := SA.releaseTime p.toParams s }
        (SA.releaseTime p.toParams s) }
    row ∈ (actView st1).obligations ∧
      GridCO.releaseCount p.toParams.engine (actView st1) s row.1 < row.2.1 := by
  intro st1
  rw [transfer_vote_clock', transfer_vote_release, fgsa_release_clockPre st s hj] at hrow
  change row ∈ (actView st1).obligations.filter
    (fun (b, g, _) => GridCO.releaseCount p.toParams.engine (actView st1) s b < g) at hrow
  obtain ⟨hm, hc⟩ := List.mem_filter.mp hrow
  exact ⟨hm, of_decide_eq_true hc⟩

end AvailableChain.FGSA.Run
end

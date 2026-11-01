module
public import AvailableChainPCSAProofs.Proofs.Clean.ViewOrigins
public import AvailableChainPCSAProofs.Proofs.Clean.LockEvents
public import AvailableChainPCSAProofs.Proofs.Clean.VoteTransport

public section

/-! C6 RootSources: concrete receipt and count support. -/
namespace AvailableChain.PCSA
/-- A vote tick cannot also be a gate tick. -/
theorem pcsa_vote_ne_gate (p : Params) (s r : Slot) :
    SA.voteTime p.toParams s ≠ SA.gateTime p.toParams r := by
  intro he
  change 4 * p.Δ * (s : Int) + p.Δ = 4 * p.Δ * (r : Int) + 6 * p.Δ at he
  have hp := p.deltaPos
  by_cases h : s ≤ r + 1
  · have hh : (s : Int) ≤ (r : Int) + 1 := by exact_mod_cast h
    nlinarith
  · have hh : (r : Int) + 2 ≤ (s : Int) := by exact_mod_cast Nat.lt_of_not_ge h
    nlinarith
/-- A vote tick can only retain lock rows. -/
theorem pcsa_vote_locks_subset (p : Params) (st : State p.n) (s : Slot) :
    (clock p st (SA.voteTime p.toParams s)).base.obligations ⊆ st.base.obligations := by
  intro row hr
  rcases pcsa_clock_lock_origin p st _ row hr with hold | ⟨r, X, ht, _⟩
  · exact hold
  · exact (pcsa_vote_ne_gate p s r ht).elim
/-- Every gate before the next vote has a strictly earlier label. -/
theorem pcsa_gate_label_lt_next_vote (p : Params) (i j : Slot)
    (ht : SA.gateTime p.toParams i < SA.voteTime p.toParams (j + 1)) : i < j := by
  by_contra hn
  have hi : (j : Int) ≤ (i : Int) := Int.ofNat_le.mpr (Nat.le_of_not_gt hn)
  change 4 * p.Δ * (i : Int) + 6 * p.Δ <
    4 * p.Δ * ((j + 1 : Nat) : Int) + p.Δ at ht
  push_cast at ht
  have hp := p.deltaPos
  nlinarith
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}
/-- Each next-vote root is genesis, an earlier ack target, or below an earlier result. -/
theorem pcsa_next_root_source (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (hFault : FaultsBelowQA p c rho)
    (x : V) (hx : x ∈ rho.honest) (s : Slot) (R : Block)
    (hR : liveRootAt p c E rho x (s + 1) = some R) :
    R = .genesis ∨
      (∃ y i, HonestAckAt p c E rho y i R ∧
        SA.earlyTime p.toParams i < SA.voteTime p.toParams (s + 1)) ∨
      (∃ i X, i < s ∧ gateResultAt p c E rho x i = some (some X) ∧ Block.Preceq R X) := by
  rw [pcsa_liveRootAt_def] at hR
  obtain ⟨nd, hnd, hr⟩ := Option.map_eq_some_iff.mp hR
  obtain ⟨k, hk, hst⟩ := pcsa_postClock_source E rho x _ nd hnd
  have hpre := V2.D.Engine.stateBefore_tick_eq_stateBeforeTime
    h.valid.toScheduleWellFormed h.noRestart hk
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ h.valid.toScheduleWellFormed] at hpre
  rw [hpre] at hst
  let a := V2.D.Run.idxBefore rho (SA.voteTime p.toParams (s + 1))
  let st := clock p (V2.D.Run.stateBefore E rho a x).st (SA.voteTime p.toParams (s + 1))
  have hroot : liveRoot p st (voterPC p st (s + 1)) = R := by
    rw [hst] at hr
    exact hr
  have hz : (controls p st).Z = .genesis := by
    change (KitFG.storeControlsView (FGSA.heightView p) (clock p _ _).fg).Z = .genesis
    rw [pcsa_body_clock_fg]
    exact (hF x hx a).2.1
  rcases pcsa_liveRoot_origin p st (voterPC p st (s + 1)) with hb | hl
  · rw [hroot] at hb
    cases hv : voterPC p st (s + 1) with
    | none =>
      left
      rw [hv] at hb
      change R = eraseFG (controls p st).Z at hb
      rw [hz] at hb
      exact hb
    | some C =>
      rw [hv] at hb
      change R = (if frameActive p st C then C.target else eraseFG (controls p st).Z) at hb
      split at hb
      · right; left
        obtain ⟨y, ha, ht⟩ := pcsa_voterPC_honest_ack_before E rho h hFault a x hx
          (s + 1) (le_refl _) C hv
        exact ⟨y, C.slot, hb ▸ ha, ht⟩
      · left
        rw [hz] at hb
        exact hb
  · rw [hroot] at hl
    obtain ⟨row, hrow, he, _, _⟩ := (pcsa_walkLocks_mem p st _ R).mp hl
    have hm := pcsa_vote_locks_subset p (V2.D.Run.stateBefore E rho a x).st (s + 1) hrow
    obtain ⟨b, hba, i, X, hevent, hX, hprefix, _⟩ := pcsa_lock_stateBefore_origin E rho h a x row hm
    have ht := (Gen.V2.Duty.index_lt_idxBefore_iff h.valid.toScheduleWellFormed hevent _).mp hba
    exact Or.inr (Or.inr ⟨i, X, pcsa_gate_label_lt_next_vote p i s ht, hX, he ▸ hprefix⟩)
end AvailableChain.PCSA.Run

end

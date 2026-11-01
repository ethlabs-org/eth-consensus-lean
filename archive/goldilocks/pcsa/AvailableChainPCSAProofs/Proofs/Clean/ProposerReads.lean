module
public import AvailableChainPCSAProofs.Proofs.Clean.LockEvents
public import AvailableChainPCSAProofs.Proofs.Clean.RootSources

public section

/-! C6 ProposerReads: concrete receipt and count support. -/
namespace AvailableChain.PCSA
/-- A proposal tick cannot also be a gate tick. -/
theorem pcsa_proposal_ne_gate (p : Params) (s r : Slot) :
    SA.proposalTime p.toParams s ≠ SA.gateTime p.toParams r := by
  intro he
  change 4 * p.Δ * (s : Int) = 4 * p.Δ * (r : Int) + 6 * p.Δ at he
  have hp : (0 : Int) < p.Δ := p.deltaPos
  by_cases h : s ≤ r + 1
  · have hh : (s : Int) ≤ (r : Int) + 1 := by exact_mod_cast h
    nlinarith
  · have hh : (r : Int) + 2 ≤ (s : Int) := by exact_mod_cast Nat.lt_of_not_ge h
    nlinarith
/-- A proposal tick can only retain existing lock rows. -/
theorem pcsa_proposal_locks_subset (p : Params) (st : State p.n) (s : Slot) :
    (clock p st (SA.proposalTime p.toParams s)).base.obligations ⊆ st.base.obligations := by
  intro row hr
  rcases pcsa_clock_lock_origin p st _ row hr with hold | ⟨r, X, ht, _⟩
  · exact hold
  · exact (pcsa_proposal_ne_gate p s r ht).elim
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- A strict read equals the inclusive read at the preceding integer time. -/
theorem pcsa_strict_read_eq_previous (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (t : Time) :
    V2.D.Run.stateBeforeTime E rho t = V2.D.Run.readAt E rho (t - 1) := by
  delta V2.D.Run.stateBeforeTime V2.D.Run.readAt
  congr 2
  funext e
  simp only [decide_eq_decide]
  exact Int.le_sub_one_iff.symm
/-- An actual tick's pre-state is the claim's preceding inclusive store read. -/
theorem pcsa_pre_tick_storeAt (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (k : Nat) (x : V) (t : Time) (hk : rho.events[k]? = some (.tick x t)) :
    (V2.D.Run.stateBefore E rho k x).st = storeAt p c E rho x (t - 1) := by
  rw [V2.D.Engine.stateBefore_tick_eq_stateBeforeTime h.valid.toScheduleWellFormed h.noRestart hk,
    pcsa_strict_read_eq_previous, storeAt_def]
end AvailableChain.PCSA.Run

end

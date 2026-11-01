module
-- shake keep reason: source declarations
public import AvailableChainFGSAProofs.Proofs.Outage.ScopedPaths -- shake: keep
-- shake keep reason: source declarations
public import AvailableChainFGSAProofs.Proofs.Outage.ContinuationPaths -- shake: keep

/-! ScopedPaths supplies actual joined read paths, source witnesses and marker receipt.
The superseded no-restart helpers have no current production callers. Their exact
source remains in Git at de637290 and in the Round 13 evidence. -/

public section
namespace AvailableChain.FGSA.Run
/-- OUTPUT-DIRECT §6. DC: INTENTIONAL; a horizon before the relay deadline
also excludes the next HEAD and the gate that consumes regressed HEADs. -/
theorem outageV_short_horizon (p : Params) (s : Slot) (horizon : Time)
    (h : horizon < SA.voteTime p.toParams s + p.Δ) :
    horizon < SA.voteTime p.toParams (s + 1) ∧ horizon < SA.gateTime p.toParams s := by
  rw [arming_vote_eq] at h
  rw [arming_vote_eq, arming_gate_eq]
  push_cast
  have := p.deltaPos
  constructor <;> nlinarith
/-- OUTPUT-DIRECT §6. DC: INTENTIONAL; every gate through the relay
cut uses an earlier label. No regressed HEAD can justify its own receipt. -/
theorem outageV_gate_through_relay (p : Params) (s q : Slot)
    (h : SA.gateTime p.toParams q ≤ SA.voteTime p.toParams s + p.Δ) : q < s := by
  rw [arming_gate_eq, arming_vote_eq] at h
  by_contra hn
  have hsq : (s : Int) ≤ (q : Int) := by exact_mod_cast (Nat.le_of_not_gt hn)
  have := p.deltaPos
  nlinarith

/-- OUTPUT-DIRECT §3. DC: INTENTIONAL; any source gate no later than
this HEAD lies at or before the previous label's early boundary. The
endpoint is inclusive, as required for the old-source relay witness. -/
theorem outageV_source_gate_cutoff (p : Params) (s q : Slot)
    (h : SA.gateTime p.toParams q ≤ SA.voteTime p.toParams (s + 1)) :
    SA.gateTime p.toParams q ≤ SA.earlyTime p.toParams s := by
  rw [arming_gate_eq, arming_vote_eq] at h
  rw [arming_gate_eq, arming_early_eq]
  push_cast at h
  have hd := p.deltaPos
  have hqs : q < s := by
    by_contra hn
    have hsq : (s : Int) ≤ (q : Int) := by exact_mod_cast (Nat.le_of_not_gt hn)
    nlinarith
  have hcast : (q : Int) + 1 ≤ (s : Int) := by exact_mod_cast (Nat.succ_le_of_lt hqs)
  nlinarith


end AvailableChain.FGSA.Run
end

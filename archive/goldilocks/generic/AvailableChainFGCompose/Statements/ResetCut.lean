module
public import AvailableChainFGCompose.Statements.ResetHistory
import Mathlib.Tactic.Linarith -- shake: keep (exposed proof tactic)

@[expose] public section

namespace AvailableChain.FGCompose

/-- The action period uses the supplied timing, independently of a service seed. -/
def period (T : FGTiming) : Time := 4 * (T.roundSlots : Time) * T.delta

/-- The first mathematical action round at or after the supplied recovery start. -/
noncomputable def resetFirstRound (T : FGTiming) (L : FGTimingLaws T)
    (Jst : Time) : Nat := Nat.find (show ∃ r, Jst ≤ T.action r from by
  refine ⟨Jst.toNat + 1, ?_⟩
  have hR : (2 : Time) ≤ T.roundSlots := by exact_mod_cast L.rounds
  have hd : 1 ≤ T.delta := L.delta_pos
  have hp : 1 ≤ period T := by unfold period; nlinarith
  rw [L.action_eq, L.gate_eq, L.proposal_eq]
  have hn := Int.natCast_nonneg Jst.toNat
  have ht := Int.self_le_toNat Jst
  push_cast
  unfold period at hp
  nlinarith)

/-- All events at this time belong to the reset cut. -/
noncomputable def resetCutTime (T : FGTiming) (L : FGTimingLaws T)
    (Jst : Time) : Time := T.action (resetFirstRound T L Jst + 2)

variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}

/-- The cumulative store frontier at an event-prefix index. -/
def frontierAtIdx (R : FGCoreReads P n Base Proposal Wire)
    (E : Generic.Env V) (rho : V2.D.Run V P) (i : Nat) : Nat :=
  rho.honest.sup (fun x => (R.core (V2.D.Run.stateBefore E rho i x)).fg.h_max)

/-- The honest frontier uses the inclusive time read, not a service-start read. -/
noncomputable def resetCutFrontier (R : FGCoreReads P n Base Proposal Wire)
    (E : Generic.Env V) (rho : V2.D.Run V P) (T : FGTiming) (L : FGTimingLaws T)
    (Jst : Time) : Nat := honestFrontier R E rho (resetCutTime T L Jst)

end AvailableChain.FGCompose
end

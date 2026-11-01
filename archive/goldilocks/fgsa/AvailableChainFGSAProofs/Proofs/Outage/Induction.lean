module
-- shake keep reason: source declarations
public import AvailableChainFGSAProofs.Proofs.Outage.ScopedInduction -- shake: keep

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- The pending gate emits no HEAD or proposal at the all-ticks seed.
The active sleep induction and its produced seeds are in ScopedInduction.
Protection and later duties are scoped to covered receivers there. -/
theorem outage_arming_duties (hvalid : V2.D.ExecutionValid E rho) (j : Slot) (B : Block) :
    OutageDutyHistory p c E rho B j (afterTicksIdx rho (SA.gateTime p.toParams j)) := by
  constructor
  intro k y t o hk hy hdt htick ho
  have htd : t ≤ SA.gateTime p.toParams j :=
    arming_tick_le hvalid.toScheduleWellFormed htick
      (hk.trans_le (preIdx_le_afterTicksIdx E rho hvalid.toScheduleWellFormed _).2)
  have hte : t = SA.gateTime p.toParams j := le_antisymm htd hdt
  constructor
  · intro H hH
    obtain ⟨s, _, _, _, he, _, _⟩ := arming_emit_head hvalid hy ⟨k, htick, ho⟩ hH
    exact (arming_gate_ne_vote p j s (hte.symm.trans he)).elim
  · intro N hX
    obtain ⟨s, _, _, he, _, _⟩ := arming_emit_proposal hvalid hy ⟨k, htick, ho⟩ hX
    exact (arming_gate_ne_proposal p j s (hte.symm.trans he)).elim

end AvailableChain.FGSA.Run
end

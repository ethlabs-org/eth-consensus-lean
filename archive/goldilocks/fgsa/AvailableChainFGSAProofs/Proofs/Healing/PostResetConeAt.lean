module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetJoint2

public section

/-! Blueprint 21 H.17:2946–3040; plan RE-BIND D1; DC: SAME cone at the cut.
The cut projection is separate from PostResetRead to keep the import order. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- Blueprint 21 H.17:2946–3040; plan RE-BIND D1; DC: SAME bounded label. -/
theorem postResetConeAt_of_cut (w : HealingWitness) {i : Nat} {s : Slot}
    (hcone : PostResetRetainedConeP p c E rho w i)
    (hcut : timeIdx rho (SA.voteTime p.toParams s) ≤ i) :
    PostResetConeAt p c E rho w s := by
  rw [PostResetConeAt_def]
  rw [PostResetRetainedConeP_def] at hcone
  intro hs hh
  exact hcone s hs hh hcut

end AvailableChain.FGSA.Run
end

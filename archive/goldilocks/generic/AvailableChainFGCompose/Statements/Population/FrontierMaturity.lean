module
public import AvailableChainFGCompose.Statements.Promotion

@[expose] public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {Prot : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire Body : Type}
variable (R : FGCoreReads Prot n Base Proposal Wire) (S : FGSafetyReads Prot n Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V Prot)
variable (O : FGObservationReads R) (T : FGTiming) (I : V2.D.Interface Prot)
variable (D : FGHistoryWireReads S)

/-- Fixed source rows over covered FG seats; the other eight fields are unchanged. -/
structure PromotionSourceAtFG (A : Finset (Fin n)) (ΔF : Time) (r height : Nat)
    (U : FGBlock (Fin n))
    (s : Slot) (X : FGBlock (Fin n)) : Prop where
  entry : EntryAt O.height U height
  parentPath : FGBlock.Preceq U X.parent
  proposal : HonestProposal E rho I s (R.erase X)
  slot : X.slot = s
  sync : E.t_GST ≤ T.action r
  carrier : carrierTimeW T ΔF r ≤ T.proposal s
  age : T.proposal U.slot + 2 * FGCompose.P T ≤ T.proposal s
  horizon : T.proposal s ≤ rho.horizon
  rows : ∀ i ∈ A, ∃ j rSent a, rSent ≤ r ∧
    HonestRowAt S E rho T j (safetyHolder S rho i) rSent a ∧
    NamesEntry D.heightPair .progress a height U

end AvailableChain.FGCompose
end

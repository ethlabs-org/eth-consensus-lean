module
public import AvailableChainFGCompose.Statements.CoreReads
public import AvailableChainKitFG.TreeFrameDef
public import AvailableChainKitFG.CertificateCoreDef

@[expose] public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {P : V2.ProtocolSpecD In}
variable [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads P n Base Proposal Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V P)

structure FGObservationReads
    (R : FGCoreReads P n Base Proposal Wire) where
  height : FGHeightView (Fin n)
  finality : FGFinalityView (Fin n)
  controls : P.State → Controls (Fin n)
  viable : P.State → Finset (FGBlock (Fin n)) → Finset (FGBlock (Fin n))

structure FGObservationLaws (O : FGObservationReads R) : Prop where
  controls_eq : ∀ nd,
    O.controls nd = treeStoreControlsView O.height (R.core nd).fg
  viable_eq : ∀ nd X,
    O.viable nd X = treeStoreFrameView O.height (R.core nd).fg X

structure FGRunOrderLaws (E : Generic.Env V) (rho : V2.D.Run V P)
    (R : FGCoreReads P n Base Proposal Wire) : Prop where
  mono : ∀ i j x, x ∈ rho.honest → i ≤ j →
    let a := (R.core (V2.D.Run.stateBefore E rho i x)).fg
    let b := (R.core (V2.D.Run.stateBefore E rho j x)).fg
    FGBlock.Preceq a.F b.F ∧
      lexKey (a.h_j, a.J) ≤ lexKey (b.h_j, b.J) ∧ a.h_max ≤ b.h_max

end AvailableChain.FGCompose
end

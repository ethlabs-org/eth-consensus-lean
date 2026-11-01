module
public import AvailableChainFGSAClaims.Statements.Reads
public import AvailableChainFGSA.Statements.FinalityView
public import AvailableChainKitFG.StoreSafetyDef -- shake: keep (Claims policy for row evidence)

@[expose] public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
F-API, dc-align-full.md:78–129;
DC DecoupledConsensusStatements/Definitions/FinalitySafety.lean:20–53; class: INTENTIONAL.
Observe the selected window carrier certificate.
This definition makes no global root claim. Pure finality claims take collision freedom on the
compared FG ancestor chains. Run claims take NamedRootCollisionFree over full named proposals. -/
def FinalityFinalizedAt (K T : FGBlock (Fin p.n)) (h : Nat) : Prop :=
  (finalityView p K).F = T ∧ (finalityView p K).h_F = h

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
F-API, dc-align-full.md:78–129;
DC DecoupledConsensusStatements/Definitions/FinalitySafety.lean:20–53; class: INTENTIONAL.
This definition makes no global root claim. Pure finality claims take collision freedom on the
compared FG ancestor chains. Run claims take NamedRootCollisionFree over full named proposals. -/
theorem FinalityFinalizedAt_def (K T : FGBlock (Fin p.n)) (h : Nat) : FinalityFinalizedAt p K T h =
  ((finalityView p K).F = T ∧ (finalityView p K).h_F = h) := by rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
F-API, dc-align-full.md:78–129;
DC DecoupledConsensusStatements/Definitions/FinalitySafety.lean:20–53; class: INTENTIONAL.
This definition makes no global root claim. Pure finality claims take collision freedom on the
compared FG ancestor chains. Run claims take NamedRootCollisionFree over full named proposals. -/
def FinalityBlock (X : FGBlock (Fin p.n)) : Prop :=
  ∃ o N,
    o.payload = Msg.proposal N ∧
    ((∃ x t, V2.D.Run.emits E rho x o t) ∨
      (∃ x t, V2.Event.deliver x o t ∈ rho.events)) ∧
    Block.Preceq (eraseFG X) N.erase

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
F-API, dc-align-full.md:78–129;
DC DecoupledConsensusStatements/Definitions/FinalitySafety.lean:20–53; class: INTENTIONAL.
This definition makes no global root claim. Pure finality claims take collision freedom on the
compared FG ancestor chains. Run claims take NamedRootCollisionFree over full named proposals. -/
theorem FinalityBlock_def (X : FGBlock (Fin p.n)) : FinalityBlock p c E rho X =
  (∃ o N,
    o.payload = Msg.proposal N ∧
    ((∃ x t, V2.D.Run.emits E rho x o t) ∨
      (∃ x t, V2.Event.deliver x o t ∈ rho.events)) ∧
    Block.Preceq (eraseFG X) N.erase) := by rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
F-API, dc-align-full.md:78–129;
DC DecoupledConsensusStatements/Definitions/FinalitySafety.lean:20–53; class: INTENTIONAL.
This definition makes no global root claim. Pure finality claims take collision freedom on the
compared FG ancestor chains. Run claims take NamedRootCollisionFree over full named proposals. -/
def finalityRows (st : State p.n) : Finset (Row (Fin p.n)) :=
  st.fg.TF.biUnion chainRows

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
F-API, dc-align-full.md:78–129;
DC DecoupledConsensusStatements/Definitions/FinalitySafety.lean:20–53; class: INTENTIONAL.
This definition makes no global root claim. Pure finality claims take collision freedom on the
compared FG ancestor chains. Run claims take NamedRootCollisionFree over full named proposals. -/
theorem finalityRows_def (st : State p.n) : finalityRows p st =
  (st.fg.TF.biUnion chainRows) := by rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
F-API, dc-align-full.md:78–129;
DC DecoupledConsensusStatements/Definitions/FinalitySafety.lean:20–53; class: INTENTIONAL.
This definition makes no global root claim. Pure finality claims take collision freedom on the
compared FG ancestor chains. Run claims take NamedRootCollisionFree over full named proposals. -/
def FinalitySlashableBound : Prop :=
  ∀ K W, FinalityBlock p c E rho K → FinalityBlock p c E rho W →
    ¬ HasSlashableWeightBetween p.E (chainRows K) (chainRows W)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
F-API, dc-align-full.md:78–129;
DC DecoupledConsensusStatements/Definitions/FinalitySafety.lean:20–53; class: INTENTIONAL.
This definition makes no global root claim. Pure finality claims take collision freedom on the
compared FG ancestor chains. Run claims take NamedRootCollisionFree over full named proposals. -/
theorem FinalitySlashableBound_def : FinalitySlashableBound p c E rho =
  (∀ K W, FinalityBlock p c E rho K → FinalityBlock p c E rho W →
    ¬ HasSlashableWeightBetween p.E (chainRows K) (chainRows W)) := by rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
F-API, dc-align-full.md:89–92;
DC DecoupledConsensusStatements/Definitions/FinalitySafety.lean:20–53; class: INTENTIONAL.
Sorted events are retained. ROOT-DIGEST W1 uses the separate DC root premises. -/
def FinalityExecution : Prop :=
  rho.events.Pairwise (fun a b => a.key ≤ b.key)

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
F-API, dc-align-full.md:89–112;
DC DecoupledConsensusStatements/Definitions/FinalitySafety.lean:20–53;
class: INTENTIONAL. Home equation for the FG observation contract. -/
theorem FinalityExecution_def : FinalityExecution p c rho =
  (rho.events.Pairwise (fun a b => a.key ≤ b.key)) := by rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
F-API, dc-align-full.md:94–100;
DC DecoupledConsensusStatements/Definitions/FinalitySafety.lean:20–53; class: INTENTIONAL.
This definition makes no global root claim. Pure finality claims take collision freedom on the
compared FG ancestor chains. Run claims take NamedRootCollisionFree over full named proposals. -/
def WholeRunAccountable : Prop :=
  (∀ K W T₁ T₂ h₁ h₂,
    FinalityBlock p c E rho K → FinalityBlock p c E rho W →
    FinalityFinalizedAt p K T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
    HasSlashableWeightBetween p.E (chainRows K) (chainRows W) ∨
      FGBlock.compatible T₁ T₂ = true) ∧
  (∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ i j,
    HasSlashableWeightBetween p.E (finalityRows p (storeAt p c E rho i u))
      (finalityRows p (storeAt p c E rho j v)) ∨
      FGBlock.compatible (storeAt p c E rho i u).fg.F (storeAt p c E rho j v).fg.F = true) ∧
  (∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t t',
    HasSlashableWeightBetween p.E (finalityRows p (V2.D.Run.readAt E rho t u).st)
      (finalityRows p (V2.D.Run.readAt E rho t' v).st) ∨
      FGBlock.compatible (V2.D.Run.readAt E rho t u).st.fg.F
        (V2.D.Run.readAt E rho t' v).st.fg.F = true)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
F-API, dc-align-full.md:89–112;
DC DecoupledConsensusStatements/Definitions/FinalitySafety.lean:20–53;
class: INTENTIONAL. Home equation for the FG observation contract. -/
theorem WholeRunAccountable_def : WholeRunAccountable p c E rho =
  ((∀ K W T₁ T₂ h₁ h₂,
    FinalityBlock p c E rho K → FinalityBlock p c E rho W →
    FinalityFinalizedAt p K T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
    HasSlashableWeightBetween p.E (chainRows K) (chainRows W) ∨
      FGBlock.compatible T₁ T₂ = true) ∧
  (∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ i j,
    HasSlashableWeightBetween p.E (finalityRows p (storeAt p c E rho i u))
      (finalityRows p (storeAt p c E rho j v)) ∨
      FGBlock.compatible (storeAt p c E rho i u).fg.F (storeAt p c E rho j v).fg.F = true) ∧
  (∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t t',
    HasSlashableWeightBetween p.E (finalityRows p (V2.D.Run.readAt E rho t u).st)
      (finalityRows p (V2.D.Run.readAt E rho t' v).st) ∨
      FGBlock.compatible (V2.D.Run.readAt E rho t u).st.fg.F
        (V2.D.Run.readAt E rho t' v).st.fg.F = true)) := by rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
F-API, dc-align-full.md:104–112;
DC DecoupledConsensusStatements/Definitions/FinalitySafety.lean:20–53; class: INTENTIONAL.
This definition makes no global root claim. Pure finality claims take collision freedom on the
compared FG ancestor chains. Run claims take NamedRootCollisionFree over full named proposals. -/
def WholeRunAgreement : Prop :=
    (∀ K W T₁ T₂ h₁ h₂, FinalityBlock p c E rho K → FinalityBlock p c E rho W →
      FinalityFinalizedAt p K T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
      FGBlock.compatible T₁ T₂ = true) ∧
    (∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t t',
      FGBlock.compatible (V2.D.Run.readAt E rho t u).st.fg.F
        (V2.D.Run.readAt E rho t' v).st.fg.F = true)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
F-API, dc-align-full.md:89–112;
DC DecoupledConsensusStatements/Definitions/FinalitySafety.lean:20–53;
class: INTENTIONAL. Home equation for the FG observation contract. -/
theorem WholeRunAgreement_def : WholeRunAgreement p c E rho =
  ((∀ K W T₁ T₂ h₁ h₂, FinalityBlock p c E rho K → FinalityBlock p c E rho W →
      FinalityFinalizedAt p K T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
      FGBlock.compatible T₁ T₂ = true) ∧
    (∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t t',
      FGBlock.compatible (V2.D.Run.readAt E rho t u).st.fg.F
        (V2.D.Run.readAt E rho t' v).st.fg.F = true)) := by rfl

end AvailableChain.FGSA.Run
end

module
public import AvailableChainPCSAClaims.Statements.LaneReads
public import AvailableChainPCSA.Statements.FinalityView
public import AvailableChainKitFG.StoreSafetyDef

@[expose] public section

/-! [PC-SA claims, W0; FG-SA Statements/FinalityApi.lean, port over `pcsa`
runs] The FG observation reads of the finality safety claims: the selected
window carrier certificate (`pcsa_finalityView`), the run blocks of finality,
the row sets, the slashable bound, and the whole-run accountability and
agreement predicates. The reads are pure FG (pcsa34-r4 5.8.2: UNCHANGED rows);
they name no FG-SA object. -/

namespace AvailableChain.PCSA.Run

open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    {m : FGMode} (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))

/-- [PC-SA claims, W0; FG-SA FinalityFinalizedAt] The window carrier
certificate of `K` finalizes `T` at height `h`. -/
def PCFinalizedAt (K T : FGBlock (Fin p.n)) (h : Nat) : Prop :=
  (pcsa_finalityView p K).F = T ∧ (pcsa_finalityView p K).h_F = h

theorem pcsa_PCFinalizedAt_def (K T : FGBlock (Fin p.n)) (h : Nat) :
    PCFinalizedAt p K T h =
      ((pcsa_finalityView p K).F = T ∧ (pcsa_finalityView p K).h_F = h) := rfl

/-- [PC-SA claims, W0; FG-SA FinalityBlock] An FG block below the erasure of a
proposal that is emitted or delivered in the run. -/
def PCFinalityBlock (X : FGBlock (Fin p.n)) : Prop :=
  ∃ o N,
    o.payload = Msg.proposal N ∧
    ((∃ x t, V2.D.Run.emits E rho x o t) ∨
      (∃ x t, V2.Event.deliver x o t ∈ rho.events)) ∧
    Block.Preceq (eraseFG X) N.erase

theorem pcsa_PCFinalityBlock_def (X : FGBlock (Fin p.n)) :
    PCFinalityBlock p c E rho X =
      (∃ o N,
        o.payload = Msg.proposal N ∧
        ((∃ x t, V2.D.Run.emits E rho x o t) ∨
          (∃ x t, V2.Event.deliver x o t ∈ rho.events)) ∧
        Block.Preceq (eraseFG X) N.erase) := rfl

/-- [PC-SA claims, W0; FG-SA finalityRows] The rows carried by the FG chains
of a store. -/
def pcFinalityRows (st : State p.n) : Finset (Row (Fin p.n)) :=
  st.fg.TF.biUnion chainRows

theorem pcsa_pcFinalityRows_def (st : State p.n) :
    pcFinalityRows p st = st.fg.TF.biUnion chainRows := rfl

/-- [PC-SA claims, W0; FG-SA FinalitySlashableBound] No two finality blocks
of the run carry slashable weight between them. -/
def PCFinalitySlashableBound : Prop :=
  ∀ K W, PCFinalityBlock p c E rho K → PCFinalityBlock p c E rho W →
    ¬ HasSlashableWeightBetween p.E (chainRows K) (chainRows W)

theorem pcsa_PCFinalitySlashableBound_def : PCFinalitySlashableBound p c E rho =
    (∀ K W, PCFinalityBlock p c E rho K → PCFinalityBlock p c E rho W →
      ¬ HasSlashableWeightBetween p.E (chainRows K) (chainRows W)) := rfl

/-- [PC-SA claims, W0; FG-SA FinalityExecution] The events are sorted. -/
def PCFinalityExecution : Prop :=
  rho.events.Pairwise (fun a b => a.key ≤ b.key)

omit [DecidableEq V] in
theorem pcsa_PCFinalityExecution_def : PCFinalityExecution p c rho =
    (rho.events.Pairwise (fun a b => a.key ≤ b.key)) := rfl

/-- [PC-SA claims, W0; FG-SA WholeRunAccountable] Finalized blocks of any two
finality blocks, any two honest event states and any two honest time reads
are compatible, or slashable weight lies between the compared rows. -/
def PCWholeRunAccountable : Prop :=
  (∀ K W T₁ T₂ h₁ h₂,
    PCFinalityBlock p c E rho K → PCFinalityBlock p c E rho W →
    PCFinalizedAt p K T₁ h₁ → PCFinalizedAt p W T₂ h₂ →
    HasSlashableWeightBetween p.E (chainRows K) (chainRows W) ∨
      FGBlock.compatible T₁ T₂ = true) ∧
  (∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ i j,
    HasSlashableWeightBetween p.E (pcFinalityRows p (storeBefore p c E rho i u))
      (pcFinalityRows p (storeBefore p c E rho j v)) ∨
      FGBlock.compatible (storeBefore p c E rho i u).fg.F
        (storeBefore p c E rho j v).fg.F = true) ∧
  (∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t t',
    HasSlashableWeightBetween p.E (pcFinalityRows p (V2.D.Run.readAt E rho t u).st)
      (pcFinalityRows p (V2.D.Run.readAt E rho t' v).st) ∨
      FGBlock.compatible (V2.D.Run.readAt E rho t u).st.fg.F
        (V2.D.Run.readAt E rho t' v).st.fg.F = true)

theorem pcsa_PCWholeRunAccountable_def : PCWholeRunAccountable p c E rho =
    ((∀ K W T₁ T₂ h₁ h₂,
      PCFinalityBlock p c E rho K → PCFinalityBlock p c E rho W →
      PCFinalizedAt p K T₁ h₁ → PCFinalizedAt p W T₂ h₂ →
      HasSlashableWeightBetween p.E (chainRows K) (chainRows W) ∨
        FGBlock.compatible T₁ T₂ = true) ∧
    (∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ i j,
      HasSlashableWeightBetween p.E (pcFinalityRows p (storeBefore p c E rho i u))
        (pcFinalityRows p (storeBefore p c E rho j v)) ∨
        FGBlock.compatible (storeBefore p c E rho i u).fg.F
          (storeBefore p c E rho j v).fg.F = true) ∧
    (∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t t',
      HasSlashableWeightBetween p.E (pcFinalityRows p (V2.D.Run.readAt E rho t u).st)
        (pcFinalityRows p (V2.D.Run.readAt E rho t' v).st) ∨
        FGBlock.compatible (V2.D.Run.readAt E rho t u).st.fg.F
          (V2.D.Run.readAt E rho t' v).st.fg.F = true)) := rfl

/-- [PC-SA claims, W0; FG-SA WholeRunAgreement] Finalized blocks of any two
finality blocks and any two honest time reads are compatible. -/
def PCWholeRunAgreement : Prop :=
  (∀ K W T₁ T₂ h₁ h₂, PCFinalityBlock p c E rho K → PCFinalityBlock p c E rho W →
    PCFinalizedAt p K T₁ h₁ → PCFinalizedAt p W T₂ h₂ →
    FGBlock.compatible T₁ T₂ = true) ∧
  (∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t t',
    FGBlock.compatible (V2.D.Run.readAt E rho t u).st.fg.F
      (V2.D.Run.readAt E rho t' v).st.fg.F = true)

theorem pcsa_PCWholeRunAgreement_def : PCWholeRunAgreement p c E rho =
    ((∀ K W T₁ T₂ h₁ h₂, PCFinalityBlock p c E rho K → PCFinalityBlock p c E rho W →
      PCFinalizedAt p K T₁ h₁ → PCFinalizedAt p W T₂ h₂ →
      FGBlock.compatible T₁ T₂ = true) ∧
    (∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t t',
      FGBlock.compatible (V2.D.Run.readAt E rho t u).st.fg.F
        (V2.D.Run.readAt E rho t' v).st.fg.F = true)) := rfl

end AvailableChain.PCSA.Run

end

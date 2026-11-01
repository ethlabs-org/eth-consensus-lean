module
public import AvailableChainFGSAClaims.Statements.Packages.Healing
public import AvailableChainFGSAClaims.Statements.Packages.FinalityGST
public import AvailableChainFGSAClaims.Statements.LiveDC

@[expose] public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure

/-! W kernel and FF5–FF7 contracts. Full run proofs belong to stage 5.
A contract definition is not a proved LAW instance. Best/search is deferred. -/

variable (p : Params)

/-- Blueprint 22:1171–1180. DC: INTENTIONAL split W kernel contract. -/
def FinalityKernelClaim_W : Prop :=
  ∀ (G ΔF : Time) (_hδ : p.δt = 2 * p.R)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : KernelPt),
    KernelPrem_W p c G ΔF E rho pt → KernelConclusion_W p c E rho ΔF pt.r

/-- Blueprint 01:126–129, plan item 18. DC: INTENTIONAL AC service contract.
Recovery and the same input witness supply the composition services. -/
def KernelACSideClaim_W : Prop :=
  ∀ (G ΔF : Time) (_hδ : p.δt = 2 * p.R)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (w : HealingWitness),
    RecoverySleep₂ p c E rho G ΔF → LivenessBoundW p ΔF →
    HealingInput p c E rho w ΔF → CoreServices p c E rho w

/-- Blueprint 22:1171–1180. DC: INTENTIONAL joined W kernel contract. -/
def FinalityKernelJoinedClaim_W : Prop :=
  ∀ (G ΔF : Time) (_hδ : p.δt = 2 * p.R)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : PtR),
    KernelJoinedPrem p c G ΔF E rho pt → KernelConclusion_W p c E rho ΔF pt.r

/-- Blueprint 22:1985–2009. DC: INTENTIONAL local Tail kernel, retained by decision 6.
The fixed timeout is explicit; capacity is a Params fact. -/
def TailKernelClaim_W : Prop :=
  ∀ (G ΔF : Time) (_hδ : p.δt = 2 * p.R)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : TailKernelPt p),
    TailKernelPrem_W p c G ΔF E rho pt →
    ∀ x ∈ rho.honest,
      AcceptsFinalBefore p c E rho x pt.U (kernelDeadlineW p ΔF (pt.r + 1))

/-- Blueprint 22:1371–1380. DC: INTENTIONAL strict extension and carrier certificate height.
Compare each accepted carrier K of the current F with H(U), not with H(F). -/
def FinalityLivenessConcl_W {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (t deadline : Time) : Prop :=
  ∃ U : FGBlock (Fin p.n),
    (∀ x, confirmedReader p c E rho x t →
      Block.Prec (V2.D.Run.readAt E rho t x).st.base.stableRecord (eraseFG U)) ∧
    (∀ x ∈ rho.honest, ∀ K ∈ (V2.D.Run.readAt E rho t x).st.fg.TF,
      (finalityView p K).F = (V2.D.Run.readAt E rho t x).st.fg.F →
      (finalityView p K).h_F < (heightView p U).h) ∧
    ∀ x ∈ rho.honest, AcceptsFinalBefore p c E rho x U deadline

/-- Blueprint 22:1382–1384. DC: INTENTIONAL GST composition with an output healing witness. -/
def FirstFinalityConcl_W {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time) (G : Time)
    (deadline : Time) : Prop :=
  ∃ w, HealingInput p c E rho w ΔF ∧ tstar p w < recoveryStart p E + B_HF p ΔF G ∧
    FinalityLivenessConcl_W p c E rho (tstar p w) deadline

/-- Blueprint 22:1421–1430. DC: INTENTIONAL specified proposal prefix coverage. -/
def ProposalFinalConcl_W {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (X : Block) (deadline : Time) : Prop :=
  ∃ Xfg : FGBlock (Fin p.n), eraseFG Xfg = X ∧
    ∀ x ∈ rho.honest, AcceptsFinalBefore p c E rho x Xfg deadline

/-- Blueprint 22:1434–1451. DC: INTENTIONAL archival frontier and two windows. -/
def AboveFrontierConcl_W {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (t deadline : Time) : Prop :=
  ∃ U : FGBlock (Fin p.n), honestFrontier p c E rho t < (heightView p U).h ∧
    ∀ x ∈ rho.honest, AcceptsFinalBefore p c E rho x U deadline

/-- Blueprint 22:1382–1384. DC: INTENTIONAL FirstFinality W contract; full finite horizon.
The conclusion supplies a HealingInput witness from H-time. -/
def FirstFinalityRecFEClaim_W : Prop :=
  ∀ (G ΔF : Time) (g : Nat) (_hδ : p.δt = 2 * p.R)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
    FirstFinalityPrem_W p c G ΔF .recFE g E rho pt →
    FirstFinalityConcl_W p c E rho ΔF G (recoveryStart p E + B_HF p ΔF G + W_W p ΔF g)

/-- Blueprint 22:1382–1384. DC: INTENTIONAL FirstFinality W contract; full finite horizon.
The conclusion supplies a HealingInput witness from H-time. -/
def FirstFinalityRecF4Claim_W : Prop :=
  ∀ (G ΔF : Time) (g : Nat) (_hδ : p.δt = 2 * p.R)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
    FirstFinalityPrem_W p c G ΔF .recF4 g E rho pt →
    FirstFinalityConcl_W p c E rho ΔF G (recoveryStart p E + B_HF p ΔF G + W_W p ΔF g)

/-- Blueprint 22:1371–1380. DC: INTENTIONAL FinalityLiveness W contract; full finite horizon.
The package supplies one common HealingInput witness. -/
def FinalityLivenessRecFEClaim_W : Prop :=
  ∀ (G ΔF : Time) (g : Nat) (w : HealingWitness) (_hδ : p.δt = 2 * p.R)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : PtT),
    FinalityLivenessPrem_W p c G ΔF .recFE g w E rho pt →
    FinalityLivenessConcl_W p c E rho pt.t (pt.t + W_W p ΔF g)

/-- Blueprint 22:1371–1380. DC: INTENTIONAL FinalityLiveness W contract; full finite horizon.
The package supplies one common HealingInput witness. -/
def FinalityLivenessRecF4Claim_W : Prop :=
  ∀ (G ΔF : Time) (g : Nat) (w : HealingWitness) (_hδ : p.δt = 2 * p.R)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : PtT),
    FinalityLivenessPrem_W p c G ΔF .recF4 g w E rho pt →
    FinalityLivenessConcl_W p c E rho pt.t (pt.t + W_W p ΔF g)

/-- Blueprint 22:1421–1430. DC: INTENTIONAL ProposalFinal W contract; full finite horizon.
The package supplies one common HealingInput witness. -/
def ProposalFinalRecFEClaim_W : Prop :=
  ∀ (G ΔF : Time) (g : Nat) (w : HealingWitness) (_hδ : p.δt = 2 * p.R)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : PtSX),
    ProposalFinalPrem_W p c G ΔF .recFE g w E rho pt →
    ProposalFinalConcl_W p c E rho pt.X
      (V2.D.proposalTime (fgsaInterface p c) pt.s + W_W p ΔF g)

/-- Blueprint 22:1421–1430. DC: INTENTIONAL ProposalFinal W contract; full finite horizon.
The package supplies one common HealingInput witness. -/
def ProposalFinalRecF4Claim_W : Prop :=
  ∀ (G ΔF : Time) (g : Nat) (w : HealingWitness) (_hδ : p.δt = 2 * p.R)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : PtSX),
    ProposalFinalPrem_W p c G ΔF .recF4 g w E rho pt →
    ProposalFinalConcl_W p c E rho pt.X
      (V2.D.proposalTime (fgsaInterface p c) pt.s + W_W p ΔF g)

/-- Blueprint 22:1434–1451. DC: INTENTIONAL AboveFrontier W contract; full finite horizon.
The package supplies one common HealingInput witness. -/
def AboveFrontierRecFEClaim_W : Prop :=
  ∀ (G ΔF : Time) (g : Nat) (w : HealingWitness) (_hδ : p.δt = 2 * p.R)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : PtT),
    AboveFrontierPrem_W p c G ΔF .recFE g w E rho pt →
    AboveFrontierConcl_W p c E rho pt.t (pt.t + 2 * W_W p ΔF g)

/-- Blueprint 22:1434–1451. DC: INTENTIONAL AboveFrontier W contract; full finite horizon.
The package supplies one common HealingInput witness. -/
def AboveFrontierRecF4Claim_W : Prop :=
  ∀ (G ΔF : Time) (g : Nat) (w : HealingWitness) (_hδ : p.δt = 2 * p.R)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : PtT),
    AboveFrontierPrem_W p c G ΔF .recF4 g w E rho pt →
    AboveFrontierConcl_W p c E rho pt.t (pt.t + 2 * W_W p ΔF g)

/-- Blueprint 22:1371–1380. DC: INTENTIONAL GST form; no healing output as premise;
DC finalized (Generic/Claims.lean:39–44). The conclusion returns the common input witness.
LIVE-DC: add Generic/Properties.lean:105 at the guarded deadline 2 * W_W + G. -/
def FinalityLivenessGSTClaim_W (form : FinFormW) : Prop :=
  ∀ (G ΔF : Time) (g : Nat) (_hδ : p.δt = 2 * p.R)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type}
    (c : AppCodec In) (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (pt : PtT),
    FinalityLivenessGSTPrem_W p c G ΔF form g E rho pt →
    ∃ w, HealingInput p c E rho w ΔF ∧ tstar p w < recoveryStart p E + B_HF p ΔF G ∧
      FinalityLivenessConcl_W p c E rho pt.t
        (pt.t + W_W p ΔF g) ∧
      (pt.t + liveDCDeadline_W p ΔF G g ≤ rho.horizon →
        LiveDCConcl_W p c E rho pt.t (pt.t + liveDCDeadline_W p ΔF G g))

/-- Blueprint 22:1421–1430. DC: INTENTIONAL GST form; no healing output as premise;
DC finalized (Generic/Claims.lean:39–44). The conclusion returns the common input witness. -/
def ProposalFinalGSTClaim_W (form : FinFormW) : Prop :=
  ∀ (G ΔF : Time) (g : Nat) (_hδ : p.δt = 2 * p.R)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type}
    (c : AppCodec In) (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (pt : PtSX),
    ProposalFinalGSTPrem_W p c G ΔF form g E rho pt →
    ∃ w, HealingInput p c E rho w ΔF ∧ tstar p w < recoveryStart p E + B_HF p ΔF G ∧
      ProposalFinalConcl_W p c E rho pt.X
        (V2.D.proposalTime (fgsaInterface p c) pt.s +
          W_W p ΔF g)

/-- Blueprint 22:1434–1451. DC: INTENTIONAL GST form; no healing output as premise;
DC finalized (Generic/Claims.lean:39–44). The conclusion returns the common input witness. -/
def AboveFrontierGSTClaim_W (form : FinFormW) : Prop :=
  ∀ (G ΔF : Time) (g : Nat) (_hδ : p.δt = 2 * p.R)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type}
    (c : AppCodec In) (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (pt : PtT),
    AboveFrontierGSTPrem_W p c G ΔF form g E rho pt →
    ∃ w, HealingInput p c E rho w ΔF ∧ tstar p w < recoveryStart p E + B_HF p ΔF G ∧
      AboveFrontierConcl_W p c E rho pt.t
        (pt.t + 2 * W_W p ΔF g)

end AvailableChain.FGSA.Run
end

#print axioms AvailableChain.FGSA.Run.KernelACSideClaim_W
#print axioms AvailableChain.FGSA.Run.FinalityLivenessConcl_W
#print axioms AvailableChain.FGSA.Run.FirstFinalityConcl_W
#print axioms AvailableChain.FGSA.Run.FirstFinalityRecFEClaim_W
#print axioms AvailableChain.FGSA.Run.FirstFinalityRecF4Claim_W
#print axioms AvailableChain.FGSA.Run.FinalityLivenessGSTClaim_W
#print axioms AvailableChain.FGSA.Run.ProposalFinalGSTClaim_W
#print axioms AvailableChain.FGSA.Run.AboveFrontierGSTClaim_W

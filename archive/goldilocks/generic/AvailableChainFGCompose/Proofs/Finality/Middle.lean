module
public import AvailableChainFGCompose.Proofs.Finality.MiddleSupport

public import AvailableChainFGCompose.Proofs.Population.Middle

public import AvailableChainFGCompose.Proofs.Population.HolderBaseMiddleWitness

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire Body : Type}
variable (R : FGCoreReads P n Base Proposal Wire) (S : FGSafetyReads P n Wire)
variable (O : FGObservationReads R) (T : FGTiming) (L : FGTimingLaws T)
variable (E : Generic.Env V) (rho : V2.D.Run V P) (I : V2.D.Interface P)
variable (D : FGHistoryWireReads S) (Ef : Electorate (Fin n))

include L in
/-- The actual reset source transfers before the opening, even before service starts. -/
theorem middle_reset_opening_height (sp : FGServicePoint) (horizon Jst : Time)
    (reset : H0Reset R S E rho O T (fun a => namedEntry (D.heightPair a)) Jst sp.reset)
    (history : FGHistoricalHighTransfer R O T E rho I sp horizon)
    (height : FGHeightLaws Ef O.height)
    (reflect : ∀ A B, Block.Preceq (R.erase A) (R.erase B) → FGBlock.Preceq A B)
    (parent : ∀ B, R.erase B.parent = (R.erase B).parent)
    (q : Nat) (A₀ : FGBlock (Fin n))
    (hA : HonestProposal E rho I (q * T.roundSlots) (R.erase A₀))
    (hprop : T.proposal (q * T.roundSlots) ≤ horizon)
    (hgap : sp.reset.sStar + 2 ≤ q * T.roundSlots) :
    sp.reset.M + 1 ≤ (O.height A₀).h := by
  exact middle_reset_opening_height_core R S O T L E rho I D Ef sp horizon Jst reset history height
    reflect parent q A₀ hA hprop hgap

variable (decodeProposal : P.Object → Option (Slot × Body))
variable (bodyErase : Body → Block) (bodyRows : Body → List Wire)
variable (blockWireRows : P.State → List Wire)
variable (parentFG : P.State → Block → Option (FGBlock (Fin n)))
variable (parentHeight : P.State → Slot → FGBlock (Fin n) → Height × BlockId)
variable (validFor : P.State → Slot → FGBlock (Fin n) → Wire → Bool)
variable (makeFG : FGBlock (Fin n) → Block → List Wire → FGBlock (Fin n))
variable (valid : Wire → Bool) (ac : FGACServiceReads V)
variable (cfg : FGConfig) (K : Nat) (ΔF : Time) (sp : FGServicePoint) (pt : KernelPt) (A : Block)
variable {Jst : Time}

include L in
/-- Construct the middle from the same service point and actual signed history. -/
theorem kernel_opening_and_middle
    (CL : FGCoreLaws R) (HL : FGHeadLaws R E rho)
    (keep : FGTreeKeepLaws R) (restore : FGTreeRestoreLaws R)
    (hs : V2.D.ScheduleWellFormed E rho)
    (hc : FGCertificateLaws Ef O.height O.finality)
    (heightBridge : HeightBridge Ef cfg O.height)
    (height_eq : O.height = KitFG.Window.certificateHeight Ef cfg K)
    (finality_eq : O.finality = KitFG.Window.certificateFinality Ef cfg K)
    (hne : ¬ Ef.IsQuorum ∅)
    (target : TargetJustification Ef O.height)
    (foldTarget : ∀ y U X, X ≠ .genesis → EntryAt O.height U y →
      FGBlock.Preceq U X.parent →
      ((O.height X.parent).h = y → TargetCoveredByChild Ef O.height X U y) →
      y + 1 ≤ (O.height X).h)
    (noMixed : ∀ y U X, SlotChain X → EntryAt O.height U y →
      FGBlock.Preceq U X.parent → X.slot < U.slot + cfg.timeoutDelay + 1 →
      NoMixedOnPath O.height X y)
    (honestSlot : Slot → Prop)
    (hK : KernelPrem_W T ΔF rho.horizon sp pt honestSlot Ef.q
      (Ef.weightOf (Finset.univ \ historyFaulty S rho)) cfg.timeoutDelay K)
    (hF0 : 0 ≤ ΔF) (deltaF : E.Δ ≤ ΔF)
    (hreset : T.proposal (sp.reset.sStar + 2) ≤ sp.serviceStart)
    (hGSTstart : E.t_GST ≤ sp.serviceStart)
    (reset : H0Reset R S E rho O T (fun a => namedEntry (D.heightPair a)) Jst sp.reset)
    (history : FGHistoricalHighTransfer R O T E rho I sp rho.horizon)
    (reflect : ∀ A B, Block.Preceq (R.erase A) (R.erase B) → FGBlock.Preceq A B)
    (parent : ∀ B, R.erase B.parent = (R.erase B).parent)
    (hNames : HighRecordNames R S O T E rho D)
    (hOrigin : RawHistoryOrigin R S E rho T D)
    (emission : HighRecordEmission S T E rho Ef cfg)
    (decoded : ∀ j x r a, HonestRowAt S E rho T j x r a → ∃ u, S.decode a = some u)
    (hweight : Ef.weightOf (historyFaulty S rho) < Ef.q)
    (linked : Function.Injective (safetyHolder S rho))
    (receipt : TRowsReceipt R S E rho T blockWireRows ΔF)
    (awake : ∀ x ∈ rho.honest, ∀ t, E.t_GST ≤ t → t ≤ rho.horizon → E.awake x t = true)
    (honest_slot : ∀ s, honestSlot s → ∃ x, x ∈ rho.honest)
    (proposal : ∀ s, honestSlot s → pt.r * T.roundSlots ≤ s →
      s ≤ (pt.r + 2) * T.roundSlots → ∃ Q, HonestProposal E rho I s Q)
    (carrier : ∀ s Q, HonestProposal E rho I s Q →
      ∃ X : FGBlock (Fin n), R.erase X = Q ∧
        OpeningCarrier_W decodeProposal bodyErase bodyRows (fun nd Q => parentFG nd Q.parent)
          makeFG E rho I s Q X ∧ X.slot = s ∧
        (∃ rows, HonestCarrier E rho I (kernelCarrier decodeProposal bodyErase bodyRows)
          s Q rows ∧ X.rows = rows.filterMap S.decode) ∧
        ∃ nd, proposalStateAt E rho I s = some nd ∧
          parentFG nd Q.parent = some X.parent ∧ X.parent ∈ (R.core nd).fg.TF)
    (exactService : ∀ s Q, HonestProposal E rho I s Q → pt.r * T.roundSlots ≤ s →
      KernelExactService ac rho.horizon s Q)
    (source_read : ∀ s Q r x, KernelExactService ac rho.horizon s Q →
      T.gate s ≤ rho.horizon → s = r * T.roundSlots → x ∈ rho.honest →
      pt.r * T.roundSlots ≤ s → ac.source x r = some (some Q))
    (source_eq : ∀ x r, ac.source x r =
      (actionSourceFG R E rho T x r).map (Option.map R.erase))
    (head_read : ∀ s Q x, KernelExactService ac rho.horizon s Q →
      pt.r * T.roundSlots ≤ s → s ≤ (pt.r + 2) * T.roundSlots → x ∈ rho.honest →
      headAtLabel R E rho T x s = some Q)
    (head_held : ∀ s X x, headAtLabel R E rho T x s = some (R.erase X) →
      ∃ i, rho.events[i]? = some (.tick x (T.vote s)) ∧
        X ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF)
    (slot_chain : ∀ i x X, X ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF → SlotChain X)
    (closed : ∀ s nd, proposalStateAt E rho I s = some nd →
      ∀ X ∈ (R.core nd).fg.TF, X.parent ∈ (R.core nd).fg.TF)
    (roots : ∀ s nd, proposalStateAt E rho I s = some nd → ViewRootInj (R.core nd).fg.TF)
    (validRows : ∀ s nd, proposalStateAt E rho I s = some nd →
      ∀ X ∈ (R.core nd).fg.TF, ∀ row ∈ X.rows,
        SimplexFG.Window.r6w (SimplexFG.Window.derive Ef cfg K X.parent) row = true)
    (parentEq : ∀ nd s X, parentHeight nd s X = ((O.height X).h, (O.height X).T_h.root))
    (matchValid : ∀ nd s X a, valid a = true →
      namedEntry (D.heightPair a) = some (parentHeight nd s X) → validFor nd s X a = true)
    (hBatch : ∀ q y U X,
      BatchPrem R S O T E rho I D Ef decodeProposal bodyErase bodyRows blockWireRows
        parentFG parentHeight validFor ΔF .target q y U X →
      (O.height X.parent).h = y → TargetCoveredByChild Ef O.height X U y)
    (hSOCOVTarget : ∀ x ∈ rho.honest, ∀ r C,
      actionSourceFG R E rho T x r = some (some C) → sp.reset.M + 1 ≤ (O.height C).h →
      E.awake x (T.action r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt S E rho T j x rSent a ∧
        RowComplete S rho D.signer valid x a ∧
        D.heightPair a = .vote (O.height C).h (O.height C).T_h.root false)
    (hA : HonestProposal E rho I (pt.r * T.roundSlots) A) :
    Nonempty (KernelMiddleWitness_W R S O T E rho I D Ef decodeProposal bodyErase bodyRows
      blockWireRows parentFG parentHeight validFor makeFG valid ac cfg K ΔF sp pt A) := by
  obtain ⟨m⟩ := kernel_opening_and_middle_holder R S O T L E rho I D Ef decodeProposal bodyErase
    bodyRows blockWireRows parentFG parentHeight validFor makeFG valid ac cfg K ΔF sp pt A CL HL
    keep restore hs hc heightBridge height_eq finality_eq hne target foldTarget noMixed honestSlot
    hK hF0 deltaF hreset hGSTstart reset history reflect parent hNames hOrigin emission decoded
    hweight linked receipt awake honest_slot proposal carrier exactService source_read source_eq
    head_read head_held slot_chain closed roots validRows parentEq matchValid hBatch (fun i hi =>
    hSOCOVTarget _ hi) hA
  obtain ⟨_, _, _, _, _, hGST, _⟩ :=
    kmid_kernel_bounds T L hK.bound hK.start hK.hhor hF0 hreset hGSTstart
  have hAwake : ∀ x ∈ rho.honest, E.awake x (T.action (pt.r + 1)) = true := by
    intro x hx
    exact awake x hx _
      (hGST.trans (kmid_proposal_le_action T L (Nat.mul_le_mul_right _ (by omega))))
      (le_trans ((kmid_action_strictMono T L).monotone (by omega)) m.actionsInRun)
  exact ⟨kernel_middle_to_node_core m
    (kernel_middle_targets_of_service_core m L hSOCOVTarget hAwake)⟩

variable (m : KernelMiddleWitness_W R S O T E rho I D Ef decodeProposal bodyErase bodyRows
  blockWireRows parentFG parentHeight validFor makeFG valid ac cfg K ΔF sp pt A)

/-- The witness retains the same fresh entry; this does not make a new selection. -/
theorem kernel_middle_fresh_U :
    FGBlock.Preceq m.A₀ m.U ∧ m.A₀ ≠ m.U ∧
    (O.height m.U).h = (O.height m.A₀).h + 1 ∧ FGBlock.Preceq m.U m.B := by
  obtain ⟨hA, hB, hU, hX, _, hd⟩ := kernel_middle_to_holder_selected_core m
  simpa only [hA, hB, hU, hX, hd] using kernel_middle_fresh_U_holder R S O T E rho I D Ef
    decodeProposal bodyErase bodyRows blockWireRows parentFG parentHeight validFor makeFG valid ac
    cfg K ΔF sp pt A (kernel_middle_to_holder_core m)

/-- The selected early carrier retains the same pending justification. -/
theorem kernel_middle_early_justification :
    (O.height m.X_D).h = m.d + 2 ∧ (O.height m.X_D).J = m.U ∧
    (O.height m.X_D).h_j = m.d + 1 ∧
    (SimplexFG.Window.derive Ef cfg K m.X_D).h_F < m.d + 1 ∧
    KitFG.Window.RetainedW Ef cfg K m.X_D (m.d + 1) m.U := by
  obtain ⟨hA, hB, hU, hX, _, hd⟩ := kernel_middle_to_holder_selected_core m
  simpa only [hA, hB, hU, hX, hd] using kernel_middle_early_justification_holder R S O T E rho I D
    Ef decodeProposal bodyErase bodyRows blockWireRows parentFG parentHeight validFor makeFG valid
    ac cfg K ΔF sp pt A (kernel_middle_to_holder_core m)

/-- The cap includes the actual source read at the final action. -/
theorem kernel_middle_source_cap (CL : FGCoreLaws R) (hs : V2.D.ScheduleWellFormed E rho)
    {x : V} {C : FGBlock (Fin n)} (hx : x ∈ rho.honest)
    (hsrc : actionSourceFG R E rho T x (pt.r + 2) = some (some C)) :
    (O.height C).h ≤ m.d + 2 := by
  obtain ⟨hA, hB, hU, hX, _, hd⟩ := kernel_middle_to_holder_selected_core m
  simpa only [hA, hB, hU, hX, hd] using kernel_middle_source_cap_holder R S O T E rho I D Ef
    decodeProposal bodyErase bodyRows blockWireRows parentFG parentHeight validFor makeFG valid ac
    cfg K ΔF sp pt A (kernel_middle_to_holder_core m) CL hs hx hsrc

end AvailableChain.FGCompose
end

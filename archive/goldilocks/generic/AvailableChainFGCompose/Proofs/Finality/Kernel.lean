module

public import AvailableChainFGCompose.Proofs.Population.Kernel

public import AvailableChainFGCompose.Proofs.Population.HolderBaseMiddleWitness

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

/-- Paper 22:1265–1289: the terminal carrier slot is after row delivery, its read plus one
delay is the kernel deadline, and it precedes the next action.
DC: INTENTIONAL: the W deadline bounds the actual terminal read. -/
theorem kernel_terminal_bounds_W (T : FGTiming) (L : FGTimingLaws T) {ΔF gst : Time}
    (q : Nat) (bound : LivenessBoundW T ΔF) (hF : 0 ≤ ΔF) (hG : gst ≤ T.action q) :
    max (T.action q) gst + ΔF ≤ T.proposal (q * T.roundSlots + kappaF T ΔF) ∧
      T.proposal (q * T.roundSlots + kappaF T ΔF) + T.delta = kernelDeadlineW T ΔF q ∧
      T.proposal (q * T.roundSlots + kappaF T ΔF) < T.action (q + 1) := by
  exact kernel_terminal_bounds_W_core T L q bound hF hG

variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire Body : Type}
variable (R : FGCoreReads P n Base Proposal Wire) (S : FGSafetyReads P n Wire)
variable (O : FGObservationReads R) (T : FGTiming) (L : FGTimingLaws T)
variable (E : Generic.Env V) (rho : V2.D.Run V P) (I : V2.D.Interface P)
variable (D : FGHistoryWireReads S) (Ef : Electorate (Fin n))

variable (decodeProposal : P.Object → Option (Slot × Body))
variable (bodyErase : Body → Block) (bodyRows : Body → List Wire)
variable (blockWireRows : P.State → List Wire)
variable (chainWireRows : P.State → Block → List Wire)
variable (parentFG : P.State → Block → Option (FGBlock (Fin n)))
variable (parentHeight : P.State → Slot → FGBlock (Fin n) → Height × BlockId)
variable (validFor : P.State → Slot → FGBlock (Fin n) → Wire → Bool)
variable (makeFG : FGBlock (Fin n) → Block → List Wire → FGBlock (Fin n))
variable (valid : Wire → Bool) (ac : FGACServiceReads V)
variable (cfg : FGConfig) (K : Nat) (ΔF : Time) (sp : FGServicePoint) (pt : KernelPt)
variable {Jst : Time}

include L in
/-- Paper 22:1171–1305 (F1–F9): the forward W kernel gives a strict fresh extension accepted
by every honest node before the kernel deadline. One service point `sp` indexes the reset,
historical transfer, middle, action rows and receipt guards. `run` replaces the FG-SA
aggregates `BaseSet`/`Recovery₂` (R7); `action` and `delivery` are the selected action and
terminal-receipt suppliers. DC-CS/W4FKChainSecondCheckpoint.lean:43: INTENTIONAL: W
retention, exact signed rows, the actual receipt and its guards replace the DC pin. -/
theorem finality_kernel_W_of
    (CL : FGCoreLaws R) (HL : FGHeadLaws R E rho)
    (keep : FGTreeKeepLaws R) (restore : FGTreeRestoreLaws R)
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
    (run : KernelRunFacts S E rho Ef ΔF)
    (hreset : T.proposal (sp.reset.sStar + 2) ≤ sp.serviceStart)
    (hGSTstart : E.t_GST ≤ sp.serviceStart)
    (reset : H0Reset R S E rho O T (fun a => namedEntry (D.heightPair a)) Jst sp.reset)
    (history : FGHistoricalHighTransfer R O T E rho I sp rho.horizon)
    (chain : ∀ horizon, FGHistoricalHighChain R O T E rho sp horizon)
    (reflect : ∀ A B, Block.Preceq (R.erase A) (R.erase B) → FGBlock.Preceq A B)
    (parent : ∀ B, R.erase B.parent = (R.erase B).parent)
    (hOrigin : RawHistoryOrigin R S E rho T D)
    (emission : HighRecordEmission S T E rho Ef cfg)
    (decoded : ∀ j x r a, HonestRowAt S E rho T j x r a → ∃ u, S.decode a = some u)
    (receipt : TRowsReceipt R S E rho T blockWireRows ΔF)
    (honest_slot : ∀ s, honestSlot s → ∃ x, x ∈ rho.honest)
    (proposal : ∀ s, honestSlot s → pt.r * T.roundSlots ≤ s →
      s ≤ (pt.r + 2) * T.roundSlots → ∃ Q, HonestProposal E rho I s Q)
    (terminalProposal : honestSlot ((pt.r + 2) * T.roundSlots + kappaF T ΔF) →
      ∃ Q, HonestProposal E rho I ((pt.r + 2) * T.roundSlots + kappaF T ΔF) Q)
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
    (action : ∀ A (m : KernelMiddleWitness_W R S O T E rho I D Ef decodeProposal bodyErase
      bodyRows blockWireRows parentFG parentHeight validFor makeFG valid ac cfg K ΔF sp pt A),
      KernelActionSupply_W R S O T E rho I D Ef m)
    (makeWire : Row (Fin n) → Wire)
    (wireDecode : ∀ row, S.decode (makeWire row) = some row)
    (wireValid : ∀ i y U B,
      valid (makeWire ⟨i, .vote (y + 1) B false, some ⟨y, U⟩⟩) = true)
    (client : ∀ nd, (S.inputs nd).1 = R.source nd)
    (release : ∀ i q nd row,
      postClock E rho (safetyHolder S rho i) (T.action q) = some nd →
      E.awake (safetyHolder S rho i) (T.action q) = true →
      (createRowOnce Ef cfg (S.record nd) i (S.inputs nd).1 (S.inputs nd).2).1 = some row →
      ∃ j, rho.events[j]? = some (.tick (safetyHolder S rho i) (T.action q)) ∧
        S.encode (makeWire row) ∈ V2.D.Run.emitsAt E rho j)
    (fields : ∀ nd H, R.finalityHead nd = some H →
      (S.inputs nd).2 = certificateHeadFields O.height O.finality H)
    {storedCarrier : P.State → FGBlock (Fin n) → Wire → Prop}
    {SourceService : V → Nat → FGBlock (Fin n) → Prop}
    (hQC : RQCOrigin R S E rho O T storedCarrier SourceService Ef)
    (recordHead : HighRecordHead R S O E rho) (clientLaws : FGSafetyClientLaws S Ef cfg)
    (own : HighRecordOwnOrigin S T E rho)
    (hsel : TRowsSelect R S E rho T I (kernelCarrier decodeProposal bodyErase bodyRows)
      chainWireRows blockWireRows parentFG validFor)
    (decode : ∀ a i, D.signer a = some i → ∃ u, S.decode a = some u)
    (occurrence : ∀ s (Q : Block) H nd a u,
      proposalStateAt E rho I s = some nd → parentFG nd Q.parent = some H →
      a ∈ chainWireRows nd Q.parent → S.decode a = some u →
      ∃ W, FGBlock.Preceq W H ∧ u ∈ W.rows)
    (validFor_eq : ∀ nd s B a, validFor nd s B a =
      ((S.decode a).isSome && ((S.decode a).map
        (SimplexFG.Window.r6w (KitFG.Window.parentState Ef cfg K B s))).getD false))
    (pathValid : ∀ s nd, proposalStateAt E rho I s = some nd → ∀ H ∈ (R.core nd).fg.TF,
      ∀ B s' root body rs, FGBlock.Preceq (.node B s' root body rs) H → ∀ a ∈ rs,
      (match a.height_pair with
        | .empty => false
        | .vote h _ _ => decide (1 ≤ h) &&
            (a.finality_pair.map (fun fp => decide (fp.height < h))).getD true) = true ∧
        SimplexFG.Window.r6w (SimplexFG.Window.derive Ef cfg K B) a = true)
    (dutyTime : ∀ s, T.proposal s = V2.D.proposalTime I s)
    (rowDurable : ∀ i j x a, i ≤ j →
      rowHeld R blockWireRows (V2.D.Run.stateBefore E rho i x) a →
      rowHeld R blockWireRows (V2.D.Run.stateBefore E rho j x) a)
    (rowClock : ∀ nd t a, rowHeld R blockWireRows nd a →
      rowHeld R blockWireRows (P.clock nd t) a)
    (ready : Nat → V → FGBlock (Fin n) → Time → Prop)
    (step : AcceptStep_W R E rho Ef cfg K ready) (durable : FGFinalityDurableLaws R)
    (inv : ∀ i x, x ∈ rho.honest → KitFG.FGStoreInvariant O.height O.finality
      (R.core (V2.D.Run.stateBefore E rho i x)).fg)
    (finBlock : FGBlock (Fin n) → Prop)
    (hI3 : ∀ C W, finBlock C → finBlock W →
      FGBlock.compatible (O.finality C).F (O.finality W).F = true)
    (readyBlock : ∀ i x X t, ready i x X t → finBlock X)
    (stored : ∀ i x, ∀ C ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF,
      C ≠ .genesis → finBlock C)
    (rootScope : ∀ i x, x ∈ rho.honest → ∀ C k u r a B,
      C ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF →
      HonestRowAt S E rho T k u r a → actionSourceFG R E rho T u r = some (some B) →
      (O.height C).J.root = (O.height B).T_h.root → (O.height C).J = (O.height B).T_h)
    (hStrat : ∀ j z W, z ∈ rho.honest →
      W ∈ (R.core (V2.D.Run.stateBefore E rho j z)).fg.TF →
      ∀ J ∈ certified R O W, J ≠ .genesis → ∃ u r a,
        HonestRowBefore S E rho T j u r a ∧
        namedEntry (D.heightPair a) = some ((O.height J).h, J.root))
    (hEmittedSource : ∀ j z r a e, HonestRowAt S E rho T j z r a →
      namedEntry (D.heightPair a) = some e → ∃ C,
        actionSourceFG R E rho T z r = some (some C) ∧
        e = ((O.height C).h, (O.height C).T_h.root) ∧
        FGBlock.Preceq (O.height C).T_h C)
    (hcapBefore : ∀ (cut : Time) (b j : Nat) (z : V) (W : FGBlock (Fin n)),
      j ≤ V2.D.Run.idxBefore rho cut → HeldAt R E rho j z W →
      (∀ k u r a row h B timeout, HonestRowAt S E rho T k u r a →
        S.decode a = some row → row.height_pair = .vote h B timeout →
        T.action r < cut → h < b + 1) → (O.height W).h < b + 2)
    (delivery : ∀ (X U : FGBlock (Fin n)) rows,
      HonestCarrier E rho I (kernelCarrier decodeProposal bodyErase bodyRows)
        X.slot (R.erase X) rows →
      E.t_GST ≤ T.proposal X.slot → T.proposal X.slot + T.delta ≤ rho.horizon →
      FGBlock.Preceq U (SimplexFG.Window.derive Ef cfg K X).F →
      Nonempty (BlockDelivery_W R E rho ready X U (T.proposal X.slot)
        (T.proposal X.slot + T.delta))) :
    KernelConclusion_W R E rho O T I decodeProposal bodyErase bodyRows
      (fun nd Q => parentFG nd Q.parent) makeFG ΔF pt.r := by
  have hF0 : 0 ≤ ΔF := le_trans (le_of_lt E.Δ_pos) run.deltaF
  obtain ⟨_, _, _, _, _, hGST, hhorA⟩ :=
    kmid_kernel_bounds T L hK.bound hK.start hK.hhor hF0 hreset hGSTstart
  have hAwake : ∀ x ∈ rho.honest, E.awake x (T.action (pt.r + 1)) = true := by
    intro x hx
    exact run.awake x hx _
      (hGST.trans (kmid_proposal_le_action T L (Nat.mul_le_mul_right _ (by omega))))
      (le_trans ((kmid_action_strictMono T L).monotone (by omega)) hhorA)
  have holderAction : ∀ A (m : KernelMiddleWitnessFG_W R S O T E rho I D Ef decodeProposal
      bodyErase bodyRows blockWireRows parentFG parentHeight validFor makeFG valid ac cfg K
      ΔF sp pt A), KernelActionSupplyFG_W R S O T E rho I D Ef m := by
    intro A m
    let targets := kernel_middle_targets_of_service_core m L hSOCOVTarget hAwake
    exact kernel_middle_action_to_holder_core m targets
      (action A (kernel_middle_to_node_core m targets))
  exact finality_kernel_W_of_holder R S O T L E rho I D Ef decodeProposal bodyErase bodyRows
    blockWireRows chainWireRows parentFG parentHeight validFor makeFG valid ac cfg K ΔF sp pt CL HL
    keep restore hc heightBridge height_eq finality_eq hne target foldTarget noMixed honestSlot hK
    run hreset hGSTstart reset history chain reflect parent hOrigin emission decoded receipt
    honest_slot proposal terminalProposal carrier exactService source_read source_eq head_read
    head_held slot_chain closed roots validRows parentEq matchValid hBatch (fun i hi =>
    hSOCOVTarget _ hi) holderAction makeWire wireDecode wireValid client release fields hQC
    recordHead clientLaws own hsel decode occurrence validFor_eq pathValid dutyTime rowDurable
    rowClock ready step durable inv finBlock hI3 readyBlock stored rootScope hStrat hEmittedSource
    hcapBefore delivery

end AvailableChain.FGCompose
end

module
public import AvailableChainFGCompose.Proofs.Finality.Receipt
public import AvailableChainFGCompose.Proofs.Finality.Accept
public import AvailableChainFGCompose.Proofs.Population.Middle
public import AvailableChainFGCompose.Proofs.Population.RowsPrem
public import AvailableChainFGCompose.Proofs.Population.RowsRecords
public import AvailableChainFGCompose.Proofs.Population.HolderBaseKernel

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

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
theorem finality_kernel_W_of_holder
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
    (hSOCOVTarget : ∀ i : Fin n, safetyHolder S rho i ∈ rho.honest → ∀ r C,
      actionSourceFG R E rho T (safetyHolder S rho i) r = some (some C) →
      sp.reset.M + 1 ≤ (O.height C).h →
      E.awake (safetyHolder S rho i) (T.action r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt S E rho T j (safetyHolder S rho i) rSent a ∧
        RowComplete S rho D.signer valid (safetyHolder S rho i) a ∧
        D.heightPair a = .vote (O.height C).h (O.height C).T_h.root false)
    (action : ∀ A (m : KernelMiddleWitnessFG_W R S O T E rho I D Ef decodeProposal bodyErase
      bodyRows blockWireRows parentFG parentHeight validFor makeFG valid ac cfg K ΔF sp pt A),
      KernelActionSupplyFG_W R S O T E rho I D Ef m)
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
  classical
  have hs := run.schedule
  have hK2 := hK.capacity_ge
  have height := hc.height
  have hF0 : 0 ≤ ΔF := le_trans (le_of_lt E.Δ_pos) run.deltaF
  have hNames : HighRecordNames R S O T E rho D := by
    intro j x r a e ha he
    obtain ⟨C, hsrc, hn, _⟩ := hEmittedSource j x r a e ha he
    exact ⟨C, hsrc, hn⟩
  obtain ⟨_, hκ2, _, _, _, hGST, hhorA⟩ :=
    kmid_kernel_bounds T L hK.bound hK.start hK.hhor hF0 hreset hGSTstart
  have hGSTq : E.t_GST ≤ T.action (pt.r + 2) :=
    hGST.trans (kmid_proposal_le_action T L (Nat.mul_le_mul_right _ (by omega)))
  obtain ⟨hTdel, hTdl, hTnext⟩ :=
    kernel_terminal_bounds_W_core T L (pt.r + 2) hK.bound hF0 hGSTq
  have hThor : T.proposal ((pt.r + 2) * T.roundSlots + kappaF T ΔF) ≤ rho.horizon := by
    have hd := L.delta_pos
    have := hK.hhor
    rw [← hTdl] at this
    linarith
  intro A hA
  obtain ⟨m⟩ := kernel_opening_and_middle_holder R S O T L E rho I D Ef decodeProposal bodyErase
    bodyRows blockWireRows parentFG parentHeight validFor makeFG valid ac cfg K ΔF sp pt A
    CL HL keep restore hs hc heightBridge height_eq finality_eq hne target foldTarget noMixed
    honestSlot hK hF0 run.deltaF hreset hGSTstart reset history reflect parent hNames hOrigin
    emission decoded run.fault_weight run.linked receipt run.awake honest_slot proposal carrier
    exactService source_read source_eq head_read head_held slot_chain closed roots validRows
    parentEq matchValid hBatch hSOCOVTarget hA
  have act := action A m
  -- The action sources, pending heads, records and fresh rows at action pt.r + 2.
  have sources := rowsPrem_action_source_holder m CL height act.read act.service
  have heads := rowsPrem_pending_head_holder m height heightBridge act.read act.head act.walk
    (fun nd A B _ _ h => reflect A B h)
  have records := rowsPrem_action_record_holder m chain hc reflect hQC recordHead clientLaws
    emission own hNames L hs
  have hawake : ∀ x ∈ rho.honest, E.awake x (T.action (pt.r + 2)) = true :=
    fun x hx => run.awake x hx _ hGSTq m.actionsInRun
  have hseats : ∀ i ∈ Finset.univ \ historyFaulty S rho,
      safetyHolder S rho i ∈ rho.honest := by
    intro i hi
    exact kmid_honest_seat (S := S) (rho := rho) ⟨i, .empty, none⟩
      (Finset.mem_sdiff.mp hi).2
  obtain ⟨rows, hfresh, hentry, _⟩ := rowsPrem_fresh_rows_holder m height heightBridge makeWire
    wireDecode wireValid client release sources heads fields records L _ hseats
    hK.honest_quorum hawake
  -- The terminal honest proposal and its carrier.
  have hwin := hK.window
  rw [Gen.Pure.FGoodE_W_def] at hwin
  obtain ⟨b, hb⟩ := terminalProposal hwin.2.2.2
  obtain ⟨X, heX, _, hXs, hcar, st, hst, hlook, hpar⟩ := carrier _ _ hb
  subst heX
  have hX : HonestProposal E rho I X.slot (R.erase X) := by rw [hXs]; exact hb
  have hstX : proposalStateAt E rho I X.slot = some st := by rw [hXs]; exact hst
  have hxh : V2.D.proposerOf rho I X.slot ∈ rho.honest := hX.1.2
  have hXne : X ≠ .genesis := by
    intro he
    have h0 := hXs
    rw [he] at h0
    change 0 = (pt.r + 2) * T.roundSlots + kappaF T ΔF at h0
    omega
  have hXhor : T.proposal X.slot ≤ rho.horizon := by rw [hXs]; exact hThor
  -- The terminal parent extends the middle carrier through the actual action source.
  have hpath : FGBlock.Preceq m.X_D X.parent := by
    obtain ⟨nd, C, hnd, hsrc, hDC, hCh, _⟩ := sources _ hxh
    have hsource : actionSourceFG R E rho T (V2.D.proposerOf rho I X.slot) (pt.r + 2) =
        some (some C) := by
      change (postClock E rho _ (T.action (pt.r + 2))).map R.source = some (some C)
      rw [hnd]
      exact congrArg some hsrc
    have hhigh : sp.reset.M + 1 ≤ (O.height C).h := by
      rw [hCh]
      have := m.highA
      omega
    have hp := history _ (pt.r + 2) C hxh hsource hhigh m.actionsInRun X.slot (R.erase X)
      hX hXhor (by rw [hXs]; exact Nat.add_le_add_left hκ2 _)
    rw [← parent] at hp
    exact KitFG.preceq_trans hDC (reflect _ _ hp)
  -- The anchor cap at the proposer's read, before the next action.
  have hcap : (O.height X.parent).h ≤ m.d + 3 := by
    have hlt : V2.D.proposalTime I X.slot < T.action (pt.r + 3) := by
      rw [← dutyTime, hXs]
      exact hTnext
    have held : ∃ j, j ≤ V2.D.Run.idxBefore rho (T.action (pt.r + 3)) ∧
        HeldAt R E rho j (V2.D.proposerOf rho I X.slot) X.parent := by
      unfold proposalStateAt postClock preTick at hstX
      cases hk : V2.D.Run.tickIdx? rho (V2.D.proposerOf rho I X.slot)
          (V2.D.proposalTime I X.slot) with
      | none => simp only [hk, Option.map_none] at hstX; contradiction
      | some k =>
        simp only [hk, Option.map_some, Option.some.injEq] at hstX
        have he := V2.D.Run.tickIdx?_spec hk
        refine ⟨k, Nat.le_of_lt ((Gen.V2.Duty.index_lt_idxBefore_iff hs he _).mpr hlt), hxh, ?_⟩
        rw [← hstX, CL.clock_fg] at hpar
        exact hpar
    obtain ⟨j, hj, hheld⟩ := held
    exact rowsPrem_anchor_cap_holder m CL L hs hNames hcapBefore j _ X.parent hj hheld
  have hret := rowsPrem_anchor_retained_or_covered_holder m (by rw [height_eq]; rfl) hne hK2
    X.parent hpath hcap
  -- Terminal carriage of the fixed fresh rows with their actual receipts.
  have hdel : max (T.action (pt.r + 2)) E.t_GST + ΔF ≤ T.proposal X.slot := by
    rw [hXs]; exact hTdel
  let carriage : TerminalCarriagePrem_W R S O T E rho I D Ef cfg K valid
      (kernelCarrier decodeProposal bodyErase bodyRows) blockWireRows parentFG ΔF
      (pt.r + 2) (m.d + 1) m.X_D m.U X := {
    schedule := hs
    fault_weight := run.fault_weight
    deltaF := run.deltaF
    carrier := by rw [hXs]; exact hcar
    parent := ⟨st, hstX, hlook⟩
    path := hpath
    freshHeight := m.heightD
    retainedOrCovered := hret
    horizon := ⟨hdel, hXhor⟩
    seats := Finset.univ \ historyFaulty S rho
    rows := rows
    fresh := hfresh
    heightEntry := hentry
    receipt := by
      intro i hi
      obtain ⟨_, _, hf⟩ := hfresh
      obtain ⟨j, _, ha, _⟩ := hf i hi
      have hh := receipt j _ _ (rows i) ha (hdel.trans hXhor) _ hxh
      refine ⟨hh, ?_⟩
      exact finality_heldBefore_at_proposal R E rho I blockWireRows hs rowDurable rowClock
        hstX hh (by rw [← dutyTime]; exact hdel) }
  have hfinal := receipt_finalized_of_carriage R S T E rho I D Ef cfg K
    (kernelCarrier decodeProposal bodyErase bodyRows) chainWireRows blockWireRows parentFG
    validFor hsel hne hK2 decode occurrence O height height_eq parentHeight parentEq validFor_eq
    valid ΔF (pt.r + 2) (m.d + 1) m.X_D m.U X hXne carriage
    (pathValid _ _ hstX X.parent hpar)
  -- The selected terminal receipts and their acceptance guards.
  have hgst : E.t_GST ≤ T.proposal X.slot :=
    (le_max_right _ _).trans (le_trans (le_add_of_nonneg_right hF0) hdel)
  have hdl : T.proposal X.slot + T.delta = kernelDeadlineW T ΔF (pt.r + 2) := by
    rw [hXs]; exact hTdl
  have hcarX := carriage.carrier
  obtain ⟨wires, hwires, _⟩ := hcarX
  obtain ⟨deliv⟩ := delivery X m.U wires hwires hgst (by rw [hdl]; exact hK.hhor) hfinal
  rw [hdl] at deliv
  have hM : 1 ≤ sp.reset.M := le_trans (le_max_left _ _) reset.mu_le
  have hheight : m.d + 1 + 1 ≤ (O.height X).h := by
    rw [← m.heightD]
    exact height.h_mono (KitFG.preceq_trans hpath (kmid_parent_preceq X))
  have hrows : ∀ j z r a row h B timeout, HonestRowAt S E rho T j z r a →
      S.decode a = some row → row.height_pair = .vote h B timeout →
      T.action r < T.action (pt.r + 2 + 1) → h ≤ m.d + 1 + 1 := by
    intro j z r a row h B timeout ha hd hp hr
    obtain ⟨C, hsrc, he⟩ := hNames j z r a (h, B) ha (by
      rw [D.decode_height a row hd, hp]; rfl)
    have hrq : r ≤ pt.r + 2 := by
      have := (kmid_action_strictMono T L).lt_iff_lt.mp hr
      omega
    have hh : h = (O.height C).h := congrArg Prod.fst he
    rw [hh]
    obtain ⟨i, hi, hilt, hheld⟩ := kmid_source_held_at_tick R T E rho CL hs ha.1 hsrc
    have hcut := kmid_tick_lt_afterTicks E rho hs hi ((kmid_action_strictMono T L).monotone hrq)
    exact m.capThroughFinalAction i z C (List.getElem?_eq_some_iff.mp hi).1.le hcut.le hheld
  obtain ⟨accept⟩ := receipt_acceptPrem_W R S T E rho I Ef cfg K O height_eq finality_eq hne
    hK2 L hs (fun a => namedEntry (D.heightPair a)) reflect parent ready finBlock hI3
    readyBlock stored inv ΔF (pt.r + 2) (m.d + 1) m.X_D m.U X run.deltaF hpath hX hXhor sp hM
    history hK.bound (by rw [hXs]) m.justifiedHeightD (by have := m.highA; omega) hStrat
    hEmittedSource rootScope hheight hcapBefore hrows hfinal _ deliv hK.hhor
  have hinv : ∀ i x, x ∈ rho.honest → KitFG.FGStoreInvariant
      (KitFG.Window.certificateHeight Ef cfg K) (KitFG.Window.certificateFinality Ef cfg K)
      (R.core (V2.D.Run.stateBefore E rho i x)).fg := by
    intro i x hx
    rw [← height_eq, ← finality_eq]
    exact inv i x hx
  have ha := acceptBefore_W R E rho Ef cfg K hne hK2 durable ready step hinv X m.U _ _ accept
  refine ⟨m.A₀, m.eraseA, m.carrierA, m.heldAAtEnd, m.U, m.strictAU.1, m.strictAU.2, ?_, ha⟩
  rw [m.freshEntry.1, m.heightA]

end AvailableChain.FGCompose
end

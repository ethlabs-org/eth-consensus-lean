module
-- shake keep reason: source declarations
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingSleep -- shake: keep
public import AvailableChainFGSAProofs.Proofs.Shared.AnchorService

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- Gate-path proposal service uses v(s) and e(s). The joint invariant
supplies compatibility at e(s); the enabled gate supplies the local epoch.
Proposal history is durable across earlier receiver restarts. -/
theorem outage_gate_path_proposal_service {ΔF : Time}
    (hBase : Base₂ p c E rho)
    (hSync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    {j k : Nat} {x v : V} {s r : Slot} {o : Obj p} {N : NamedProposal p.n} {t : Time}
    (hx : x ∈ rho.honest) (hv : v ∈ rho.honest)
    (hG : enabledGateAt p c E rho j x s)
    (hd : (toWire p o).decode = some (.block r N))
    (hacc : V2.D.Run.acceptsAt E rho k v o t) (ht : t < SA.voteTime p.toParams s)
    (hGST : E.t_GST ≤ SA.voteTime p.toParams s)
    (hF : Block.Compatible N.erase
      (eraseFG (V2.D.Run.stateBeforeTime E rho (SA.earlyTime p.toParams s) x).st.fg.F)) :
    Nonempty (ReceiverService E rho o t (SA.earlyTime p.toParams s) x) := by
  obtain ⟨hReady, hHistory, hRF, hHandlers⟩ := fgsa_gate_path_anchor_service
    hBase.valid hBase.delta hBase.restartsAtWakes hx hv hG hd hacc ht
  have hdle : max (SA.voteTime p.toParams s) E.t_GST + p.Δ =
      SA.earlyTime p.toParams s := by
    rw [max_eq_left hGST]
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ = 4 * p.Δ * (s : Int) + 2 * p.Δ
    ring
  have h0 : 0 ≤ SA.voteTime p.toParams s := by
    change 0 ≤ 4 * p.Δ * (s : Int) + p.Δ
    have hpos := p.deltaPos
    positivity
  have hve : SA.voteTime p.toParams s < SA.earlyTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + p.Δ < 4 * p.Δ * (s : Int) + 2 * p.Δ
    linarith [p.deltaPos]
  have heh : SA.earlyTime p.toParams s ≤ rho.horizon := by
    apply le_trans _ (hBase.valid.in_horizon _ (List.mem_of_getElem? hG.1)).2
    change 4 * p.Δ * (s : Int) + 2 * p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  change Block.compatible N.erase
    (eraseFG (V2.D.Run.stateBeforeTime E rho (SA.earlyTime p.toParams s) x).st.fg.F) = true at hF
  have hNX : (fgsa p c).excludes
      (V2.D.Run.stateBeforeTime E rho (SA.earlyTime p.toParams s) x) o = false := by
    change excludesS p _ o = false
    dsimp only [excludesS]
    rw [hd]
    simp only [blockExcluded, activeCompatible, hF, Bool.not_true, Bool.false_or]
    exact fgsa_trigger_invalid_false E rho o t r N (Or.inr ⟨v, hv, k, hacc⟩) hd _
  refine ⟨⟨fun a => max a E.t_GST + p.Δ, rho.horizon, SA.voteTime p.toParams s,
    ?_, ?_, ht.le, h0, ?_, ?_, ?_, ?_, hHistory, hRF, ?_, ?_⟩⟩
  · simpa only [hBase.delta] using Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy
      E rho hSync (fun o => ¬ isRowObject o) E.Δ (fgsaDelay_nonrow E.Δ ΔF)
  · simpa only [hdle] using hReady
  · simpa only [hdle] using hve
  · simpa only [hdle] using heh
  · simpa only [hdle] using heh
  · exact hdle.le
  · simpa only [hdle] using hHandlers
  · simpa only [hdle] using hNX

/-- Frozen transfer service uses e(s) and f(s). Joinedness at v(s+1)
supplies receiver readiness and survival through the freeze. -/
theorem outage_transfer_path_proposal_service {ΔF : Time}
    (hBase : Base₂ p c E rho)
    (hSync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    {k : Nat} {x v : V} {s r : Slot} {o : Obj p} {N : NamedProposal p.n} {t : Time}
    (hx : x ∈ rho.honest) (hv : v ∈ rho.honest)
    (hJ : joinedAt p E rho x (s + 1) (SA.voteTime p.toParams (s + 1)))
    (hhor : SA.voteTime p.toParams (s + 1) ≤ rho.horizon)
    (hd : (toWire p o).decode = some (.block r N))
    (hacc : V2.D.Run.acceptsAt E rho k v o t) (ht : t < SA.earlyTime p.toParams s)
    (hGST : E.t_GST ≤ SA.earlyTime p.toParams s)
    (hF : Block.Compatible N.erase
      (eraseFG (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) x).st.fg.F)) :
    Nonempty (ReceiverService E rho o t (SA.freezeTime p.toParams s) x) := by
  obtain ⟨hReady, hHistory, hRF, hHandlers⟩ := fgsa_transfer_path_anchor_service
    hBase.valid hBase.delta hx hv hJ hhor hd hacc ht
  have hdle : max (SA.earlyTime p.toParams s) E.t_GST + p.Δ =
      SA.freezeTime p.toParams s := by
    rw [max_eq_left hGST]
    change 4 * p.Δ * (s : Int) + 2 * p.Δ + p.Δ = 4 * p.Δ * (s : Int) + 3 * p.Δ
    ring
  have h0 : 0 ≤ SA.earlyTime p.toParams s := by
    change 0 ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ
    have hpos := p.deltaPos
    positivity
  have hef : SA.earlyTime p.toParams s < SA.freezeTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + 2 * p.Δ < 4 * p.Δ * (s : Int) + 3 * p.Δ
    linarith [p.deltaPos]
  have hfv : SA.freezeTime p.toParams s ≤ SA.voteTime p.toParams (s + 1) := by
    change 4 * p.Δ * (s : Int) + 3 * p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith [p.deltaPos]
  change Block.compatible N.erase
    (eraseFG (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) x).st.fg.F) = true at hF
  have hNX : (fgsa p c).excludes
      (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) x) o = false := by
    change excludesS p _ o = false
    dsimp only [excludesS]
    rw [hd]
    simp only [blockExcluded, activeCompatible, hF, Bool.not_true, Bool.false_or]
    exact fgsa_trigger_invalid_false E rho o t r N (Or.inr ⟨v, hv, k, hacc⟩) hd _
  refine ⟨⟨fun a => max a E.t_GST + p.Δ, rho.horizon, SA.earlyTime p.toParams s,
    ?_, ?_, ht.le, h0, ?_, ?_, ?_, ?_, hHistory,
    hRF.mono le_rfl (fgsa_idxBefore_mono rho hfv), ?_, ?_⟩⟩
  · simpa only [hBase.delta] using Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy
      E rho hSync (fun o => ¬ isRowObject o) E.Δ (fgsaDelay_nonrow E.Δ ΔF)
  · simpa only [hdle] using hReady
  · simpa only [hdle] using hef
  · simpa only [hdle] using hfv.trans hhor
  · simpa only [hdle] using hfv.trans hhor
  · exact hdle.le
  · simpa only [hdle] using hHandlers
  · simpa only [hdle] using hNX

/-- P15 local service. The anchor is max(send,wake). Finality compatibility
is checked at the receiver's deadline; survival uses event indices. -/
theorem outage_restored_service {o : Obj p} {send wake C : Time} {x : V}
    (hDelta : E.Δ = p.Δ) {ΔF : Time}
    (hSync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hSend : 0 ≤ send)
    (hReady : Gen.V2.Duty.ReadyTrigger E rho o send x (max send wake)
      (max (max send wake) E.t_GST + p.Δ))
    (hHor : max (max send wake) E.t_GST + p.Δ ≤ rho.horizon)
    (hRead : max (max send wake) E.t_GST + p.Δ ≤ C)
    (hHistory : Gen.V2.Duty.HistorySafeAt E rho x o (max send wake))
    (hEpoch : V2.D.restartFree rho x (V2.D.Run.actionCut rho (max send wake))
      (V2.D.Run.idxBefore rho C))
    (hHandlers : ∀ j t, max send wake ≤ t →
      t < max (max send wake) E.t_GST + p.Δ → V2.D.Run.handlesAt E rho j x o t →
      (fgsa p c).wellFormed o = true ∧
      (fgsa p c).depsPresent (V2.D.Run.stateBefore E rho j x) o = true ∧
      fgsaTimely p (V2.D.Run.stateBefore E rho j x) o)
    (hFinality : (fgsa p c).excludes (V2.D.Run.stateBeforeTime E rho
      (max (max send wake) E.t_GST + p.Δ) x) o = false) :
    Nonempty (ReceiverService E rho o send C x) := by
  refine ⟨⟨fun t => max t E.t_GST + p.Δ, rho.horizon, max send wake, ?_, hReady,
    le_max_left _ _, hSend.trans (le_max_left _ _), ?_, hHor, hHor, hRead,
    hHistory, hEpoch, hHandlers, hFinality⟩⟩
  · simpa only [hDelta] using
      Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy E rho hSync
        (fun o => ¬ isRowObject o) E.Δ (fgsaDelay_nonrow E.Δ ΔF)
  · exact (le_max_left _ _).trans_lt (lt_add_of_pos_right _ p.deltaPos)

/-- P15 local proposal receipt. Each ancestor has a strict stamp at the read.
The service retains the visible finality and dependency inputs. -/
theorem outage_restored_proposal_receipt {x : V} {s : Slot} {N : NamedProposal p.n}
    {send C : Time} (hS : V2.D.ScheduleWellFormed E rho)
    (hRoots : NamedReceiptRootCollisionFree p c E rho) (hx : x ∈ rho.honest)
    (hC : 0 < C)
    (h : ReceiverService E rho (ofWire p ⟨.proposer s, .proposal N⟩) send C x) :
    ReceiptObjectAt p c E rho x (ofWire p ⟨.proposer s, .proposal N⟩) C :=
  arming_proposal_receipt_on hS hRoots hx hC h

/-- P15 local batch receipt. It applies to every honest receiver, including W.
The service supplies the finality alternative for each authentic HEAD target. -/
theorem outage_restored_batch_receipt_on {x : V} {q : Slot} {C : Time}
    (hE : V2.D.ExecutionValid E rho)
    (hRoots : NamedReceiptRootCollisionFree p c E rho) (hx : x ∈ rho.honest)
    (hC : 0 < C) (h : ArmingBatchReceiptService E rho x q C) :
    BatchReceiptAt p c E rho x q C :=
  arming_batch_receipt_on hE hRoots hx hC h

omit [DecidableEq V] in
/-- A joined gate reader was awake throughout the label's receipt window. -/
theorem outage_restored_reader_awake {x : V} {q : Slot} {C : Time}
    (hJ : joinedAt p E rho x (q + 1) C)
    {t : Time} (ht : 0 ≤ t) (hStart : slotStartZ p (q : Int) ≤ t) (hEnd : t ≤ C) :
    E.awake x t = true := by
  classical
  by_contra hn
  obtain ⟨w, htw, hwC, hw⟩ := V2.D.Engine.wake_between hEnd
    (Bool.eq_false_iff.mpr hn) hJ.1
  have hBound := hJ.2.1 w (ht.trans_lt htw) hwC hw
  have he : slotStartZ p (((q + 1 : Nat) : Int) - 1) = slotStartZ p (q : Int) := by
    congr 1
    omega
  rw [he] at hBound
  exact (not_lt.mpr hBound) (hStart.trans_lt htw)

omit [DecidableEq V] in
/-- The joined reader supplies its exact current epoch after the label's start.
A restart at the start is before actionCut and is allowed. -/
theorem outage_restored_reader_epoch (hS : V2.D.ScheduleWellFormed E rho)
    {x : V} {q : Slot} {C a : Time} (hJ : joinedAt p E rho x (q + 1) C)
    (hStart : slotStartZ p (q : Int) ≤ a) (haC : a < C) :
    V2.D.restartFree rho x (V2.D.Run.actionCut rho a) (V2.D.Run.idxBefore rho C) := by
  classical
  apply Gen.V2.Duty.restartFree_actionCut_idxBefore hS haC
  intro k w he haw hwC
  have hw0 := (hS.in_horizon _ (List.mem_of_getElem? he)).1
  have hBound := hJ.2.2 w hw0 hwC.le (List.mem_of_getElem? he)
  have hEq : slotStartZ p (((q + 1 : Nat) : Int) - 1) = slotStartZ p (q : Int) := by
    congr 1
    omega
  rw [hEq] at hBound
  exact (not_lt.mpr hBound) (hStart.trans_lt haw)

/-- P15-CUT: a protected non-genesis block's origin gate gives the cut
bound. The origin producer must supply the actual gate; no regime field or
receipt at an early cut is assumed. -/
theorem outage_prefix_cut_of_origin {b₀ : Time}
    (hOrigin : ∃ s, SA.gateTime p.toParams s ≤ b₀) : 6 * p.Δ ≤ b₀ := by
  obtain ⟨s, hs⟩ := hOrigin
  rw [arming_gate_eq] at hs
  have hn : 0 ≤ 4 * p.Δ * (s : Time) :=
    mul_nonneg (mul_nonneg (by decide) p.deltaPos.le) (Int.natCast_nonneg s)
  linarith

/-- P15-CUT: every selected label lies in the healthy prefix once an origin
has given 6Δ ≤ b₀. Equality at the early cut is allowed. -/
theorem outage_prefix_label_cut {b₀ : Time} (hCut : 6 * p.Δ ≤ b₀)
    {q : Slot} (hq : q ≤ coverLabel p b₀) : SA.earlyTime p.toParams q ≤ b₀ := by
  have hlast := (arming_label p b₀ hCut).1
  rw [← arming_early_next] at hlast
  have hq' : (q : Time) ≤ (coverLabel p b₀ : Time) := by exact_mod_cast hq
  change 4 * p.Δ * (q : Time) + 2 * p.Δ ≤ b₀
  change 4 * p.Δ * (coverLabel p b₀ : Time) + 2 * p.Δ ≤ b₀ at hlast
  nlinarith [p.deltaPos]

/-- The protected-block consumer uses the corrected prefix predicate.
For genesis, inclusion follows from block_genesis_preceq and needs no batch. -/
theorem outage_prefix_receipt_of_origin {fast : Bool} {T b₀ : Time}
    (hPrefix : OutagePrefixReceipt p c E rho fast T b₀)
    (hOrigin : ∃ s, SA.gateTime p.toParams s ≤ b₀)
    {x : V} (hx : x ∈ coveredNodes p E rho fast b₀) {q : Slot}
    (hq : if fast then q = coverLabel p b₀
      else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ (q : Int) ∧
        q ≤ coverLabel p b₀) (hT : T ≤ SA.gateTime p.toParams q) :
    BatchReceiptAt p c E rho x q (SA.earlyTime p.toParams q) := by
  have hle : q ≤ coverLabel p b₀ := by
    cases fast with
    | false => exact hq.2
    | true => exact hq.le
  exact hPrefix x hx q hq hT
    (outage_prefix_label_cut (outage_prefix_cut_of_origin hOrigin) hle)

/-- Compose the three approved restored read cuts. The public regime theorem
must derive these services and the P-Ar prefix; they are local proof inputs. -/
theorem outage_restored_receipt_with_service {fast : Bool} {T b₀ b₁ : Time}
    (hE : V2.D.ExecutionValid E rho)
    (hRoots : NamedReceiptRootCollisionFree p c E rho)
    (hPrefix : OutagePrefixReceipt p c E rho fast T b₀)
    (hEarly : ∀ x q, restoredLabel p b₁ ≤ q →
      SA.earlyTime p.toParams q ≤ rho.horizon →
      headReader p E rho x (q + 1) (SA.gateTime p.toParams q) →
      ArmingBatchReceiptService E rho x q (SA.earlyTime p.toParams q))
    (hFreeze : ∀ x s, 0 < s → restoredLabel p b₁ ≤ s - 1 →
      SA.voteTime p.toParams s ≤ rho.horizon →
      headReader p E rho x s (SA.voteTime p.toParams s) →
      ArmingBatchReceiptService E rho x (s - 1) (SA.freezeTime p.toParams (s - 1)))
    (hProposal : ∀ m, 0 < m → restoredLabel p b₁ ≤ m - 1 →
      V2.D.proposalTime (fgsaInterface p c) m ≤ rho.horizon →
      let x := V2.D.proposerOf rho (fgsaInterface p c) m
      headReader p E rho x m (V2.D.proposalTime (fgsaInterface p c) m) →
      ArmingBatchReceiptService E rho x (m - 1)
        (V2.D.proposalTime (fgsaInterface p c) m)) :
    OutageContinuationReceipt p c E rho fast T b₀ b₁ := by
  refine ⟨hPrefix, ?_, ?_, ?_⟩
  · intro x q hr hHor hx
    apply outage_restored_batch_receipt_on hE hRoots hx.1
    · change 0 < 4 * p.Δ * (q : Int) + 2 * p.Δ
      have hd := p.deltaPos
      positivity
    · exact hEarly x q hr hHor hx
  · intro x s hs hr hHor hx
    apply outage_restored_batch_receipt_on hE hRoots hx.1
    · change 0 < 4 * p.Δ * ((s - 1 : Nat) : Int) + 3 * p.Δ
      have hd := p.deltaPos
      positivity
    · exact hFreeze x s hs hr hHor hx
  · intro m hm hr hHor x hx
    apply outage_restored_batch_receipt_on hE hRoots hx.1
    · change 0 < 4 * p.Δ * (m : Int)
      have hd := p.deltaPos
      have hm' : (0 : Int) < (m : Int) := by exact_mod_cast hm
      positivity
    · exact hProposal m hm hr hHor hx

/-- The restored services have the three approved read cuts. The prefix field
comes from P-Ar's public theorem, not from these restored services. -/
structure OutageRestoredServices (fast : Bool) (T b₀ b₁ : Time) : Prop where
  early : ∀ x q, restoredLabel p b₁ ≤ q →
    SA.earlyTime p.toParams q ≤ rho.horizon →
    headReader p E rho x (q + 1) (SA.gateTime p.toParams q) →
    ArmingBatchReceiptService E rho x q (SA.earlyTime p.toParams q)
  freeze : ∀ x s, 0 < s → restoredLabel p b₁ ≤ s - 1 →
    SA.voteTime p.toParams s ≤ rho.horizon →
    headReader p E rho x s (SA.voteTime p.toParams s) →
    ArmingBatchReceiptService E rho x (s - 1) (SA.freezeTime p.toParams (s - 1))
  proposal : ∀ m, 0 < m → restoredLabel p b₁ ≤ m - 1 →
    V2.D.proposalTime (fgsaInterface p c) m ≤ rho.horizon →
    let x := V2.D.proposerOf rho (fgsaInterface p c) m
    headReader p E rho x m (V2.D.proposalTime (fgsaInterface p c) m) →
    ArmingBatchReceiptService E rho x (m - 1)
      (V2.D.proposalTime (fgsaInterface p c) m)

/-- P-Ar supplies the corrected public prefix; P-Ou supplies only restored service. -/
theorem outage_restored_receipt_on [Fintype V] {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c fast E rho T b₀ b₁ ΔF)
    (hServices : OutageRestoredServices (p := p) (c := c) (E := E) (rho := rho)
      fast T b₀ b₁) : OutageContinuationReceipt p c E rho fast T b₀ b₁ := by
  exact outage_restored_receipt_with_service h.pre.base.valid h.pre.base.receiptIdealization
    (arming_prefix_batch_receipt p c E rho fast T b₀ b₁ ΔF h)
    hServices.early hServices.freeze hServices.proposal

/-- A protected non-genesis read supplies the actual origin and the P15-CUT bound. -/
theorem outage_prefix_receipt_of_protected_read [Fintype V]
    {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c fast E rho T b₀ b₁ ΔF)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hHist : CleanHist p c E rho (timeIdx rho b₀)) {z : V} {B : Block}
    (hread : Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable z T))
    (hne : B ≠ .genesis) {x : V} (hx : x ∈ coveredNodes p E rho fast b₀) {q : Slot}
    (hq : if fast then q = coverLabel p b₀
      else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ (q : Int) ∧
        q ≤ coverLabel p b₀) (hT : T ≤ SA.gateTime p.toParams q) :
    BatchReceiptAt p c E rho x q (SA.earlyTime p.toParams q) := by
  obtain ⟨r, C, _, _, hr, _⟩ := arming_protected_origin_on
    h.pre.base.valid.toScheduleWellFormed h.order.2.1 hState hHist hread hne
  exact outage_prefix_receipt_of_origin
    (arming_prefix_batch_receipt p c E rho fast T b₀ b₁ ΔF h)
    ⟨r, hr.trans h.order.2.1⟩ hx hq hT

end AvailableChain.FGSA.Run
end

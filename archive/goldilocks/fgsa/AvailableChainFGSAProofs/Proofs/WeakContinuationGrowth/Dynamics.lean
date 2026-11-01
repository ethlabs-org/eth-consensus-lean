module
-- shake keep reason: facade coverage
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.FinalBelow -- shake: keep
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.StepOutput
-- shake keep reason: facade coverage
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.StepReconcile -- shake: keep
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.StepTransferReceipts
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.StepFacts
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.StepRestart
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Epoch
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.StepInit
public import AvailableChainFGSAProofs.Proofs.Shared.Roots
public import AvailableChainFGSAProofs.Proofs.Shared.Reads
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.HeadRelay
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.ReceiptOrigins
public import AvailableChainFGSA.Proofs.Head.Transfer -- shake: keep (fgsa_headInTree_covers_of_transfer proof reference)

namespace AvailableChain.GridCO

private def growth_advance (old candidate : Block) : Block :=
  if Block.preceq candidate old then old else candidate
private theorem growth_advance_eq : @advance = @growth_advance := rfl

private def growth_stampBlock {n : Nat} {mode : HeadMode} (st : State n mode) (b : Block) : Time :=
  ((st.blockStamp.find? (fun row => row.1 == b)).map Prod.snd).getD st.now
private theorem growth_stampBlock_eq : @stampBlock = @growth_stampBlock := rfl

private def growth_stampVote {n : Nat} {mode : HeadMode} (st : State n mode) (o : Wire n mode)
  : Time :=
  ((st.voteStamp.find? (fun row => row.1 == o)).map Prod.snd).getD st.now
private theorem growth_stampVote_eq : @stampVote = @growth_stampVote := rfl

private def growth_admitProposal (p : Params) {n : Nat} {mode : HeadMode} (st : State n mode)
  (o : Wire n mode)
    (b : Block) (raw : List (HeadWire n mode)) : State n mode :=
  let current := (st.now / (4 * p.Δ)).toNat
  let correctProposer := match o.auth with
    | .proposer s => s == b.slot
    | _ => false
  if b.slot > current || !blockKnown st b.parent || b ∈ st.blocks ||
      !(b.parent.slot < b.slot) || !correctProposer then st else
    let st' := { st with
      blocks := st.blocks ++ [b]
      blockStamp := st.blockStamp ++ [(b, st.now)]
      proposals := st.proposals ++ [o] }
    raw.foldl (fun acc row => admitVote p acc (fromHead row)) st'
private theorem growth_admitProposal_eq : @admitProposal = @growth_admitProposal := rfl

private def growth_resolvedBefore {n : Nat} {mode : HeadMode}
    (st : State n mode) (o : Wire n mode) (cutoff : Time) : Bool :=
  match resolvedHead? st o with
  | none => false
  | some B => decide (B.slot ≤ (headLabel? o).getD 0) &&
      decide (stampVote st o < cutoff) && decide (stampBlock st B < cutoff)
private theorem growth_resolvedBefore_eq : @resolvedBefore = @growth_resolvedBefore := rfl

end AvailableChain.GridCO

namespace AvailableChain.FGSA

private def growth_gateStep (p : Params) (st : State p.n) (s : Slot) : State p.n :=
  let a := eraseFG st.fg.F
  let st := if (GridCO.savedGenuine st.base s).isSome then st else
    if !joinedNow p st then
      { onView (fun v => { v with genuine := v.genuine ++ [(s, none)] }) st with
        fastWrite := st.fastWrite ++ [(s, [])] }
    else
      { onView (fun v => SA.Root.gateFrom p.toParams a v s) st with
        fastWrite := st.fastWrite ++ [(s, fastSet p a (actView st) s)] }
  normalizeS st
private theorem growth_gateStep_eq : @gateStep = @growth_gateStep := rfl

end AvailableChain.FGSA

namespace AvailableChain.FGSA.Run
private def growth_headAtIdx (p : Params) {In : Type} (c : AppCodec In) {V : Type} [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (k : Nat) (s : Slot) : Block :=
  match rho.events[k]? with
  | some (.tick y t) => FGSA.headVote p ((fgsa p c).clock (V2.D.Run.stateBefore E rho k y) t).st s
  | _ => .genesis
private theorem growth_headAtIdx_eq : @headAtIdx = @growth_headAtIdx := rfl

private def growth_blockOf (p : Params) (o : Obj p) : Option Block :=
  match (toWire p o).decode with
  | some (.block _ N) => some N.erase
  | _ => none
private theorem growth_blockOf_eq : @blockOf? = @growth_blockOf := rfl
end AvailableChain.FGSA.Run




public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {w : HealingWitness} {iStar : Nat}

/-- WC plan §6.7; DC completed result evidence persists in a longer history. -/
private theorem result_mono {i k j : Nat} {x : V} {s : Slot} {B : Block}
    (h : WCResult p c E rho w iStar i j x s B) (hik : i ≤ k) :
    WCResult p c E rho w iStar k j x s B :=
  { h with completed := h.completed.trans_le hik }

/-- WC plan §6.7; DC prefix origins persist in a longer history. -/
private theorem history_mono {i k : Nat} {B : Block}
    (h : WCBelowHistory p c E rho w iStar i B) (hik : i ≤ k) :
    WCBelowHistory p c E rho w iStar k B := by
  rcases h.origin with h | ⟨j, x, s, C, hr, hb⟩
  · exact ⟨Or.inl h⟩
  · exact ⟨Or.inr ⟨j, x, s, C, result_mono hr hik, hb⟩⟩

end AvailableChain.FGSA.Run


/-! Companion event induction. The source WC modules stay unchanged.
One-quorum causality and invariant-to-safety use the existing lane Export.
Low finality uses whole-run accountability in place of FaultX. -/






/-! WC plan §6.6; DC finite service follows the proved joint history. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {w : HealingWitness} {iStar : Nat}

end AvailableChain.FGSA.Run



/-! WC plan §6.5; DC old results cover the current honest HEAD inputs. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

omit [DecidableEq V] [Fintype V] in
/-- WC plan §6.5; DC every event strictly after the cut has a later key. -/
private theorem growthStepInputs_time_before_cut (hsch : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {e : V2.Event V (fgsa p c).Object} {t : Time}
    (he : rho.events[i]? = some e) (hi : i < afterTicksIdx rho t) : e.time ≤ t := by
  have hm : e ∈ rho.events.filter (cutPred t) := by
    rw [V2.D.Engine.filter_eq_take hsch (cutPred t) (by
      intro e f hk hf
      exact decide_eq_true (hk.trans (of_decide_eq_true hf)))]
    apply List.mem_of_getElem? (i := i)
    change (rho.events.take (afterTicksIdx rho t))[i]? = some e
    rw [List.getElem?_take_of_lt hi]
    exact he
  have hk := of_decide_eq_true (List.mem_filter.mp hm).2
  rcases Prod.Lex.toLex_le_toLex.mp hk with h | ⟨h, _⟩
  · exact h.le
  · exact h.le

end AvailableChain.FGSA.Run



/-! WC plan §6.5; DC the honest batch retains its original receipt deadlines. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG Gen.Pure

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)} {ΔF : Time}

end AvailableChain.FGSA.Run



/-! WC plan §6.5; DC gate order and the guard precede retrospective transfer. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG Gen.Pure

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V] [Fintype V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

end AvailableChain.FGSA.Run



/-! WC plan §6.5; DC a received finalization was served before its acceptance. -/





/-! WC plan §6.5; DC the ordered handler cases preserve and identify the output. -/





/-! WC plan §6.5; DC retrospective frame bounds use only earlier result labels. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG Gen.Pure

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V] [Fintype V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

end AvailableChain.FGSA.Run



/-! WC plan §6.5; DC retrospective paths retain the original per-body receipt times. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG Gen.Pure

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time}

end AvailableChain.FGSA.Run



/-! WC plan §6.5; DC retrospective HEAD transfer precedes exact proposal adoption. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG Gen.Pure

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V] [Fintype V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {ΔF : Time} {w : HealingWitness} {iStar : Nat}

/-- WC plan §6.5; DC raw pools, carried support and original receipts give the earlier HEAD. -/
theorem wcg_retrospective (hcausal : WCFinalityTargetEarlierStatement p c E rho) :
  WCGRetrospectiveStatement p c E rho ΔF w iStar := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i hi hilen inv x s B hx ht hslabel hB y hy hJ
  obtain ⟨C, hC, _, hQC, hord, _, _⟩ := (wcg_gateResult hcausal) ΔF w iStar hvalid hlinked
    hcstar hnr
    hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead
    hs i x s hi hilen inv (wcg_gate_enabled_of_result hvalid.toScheduleWellFormed ht hB) hslabel
  have he : C = B := Option.some.inj (Option.some.inj (hC.symm.trans hB))
  subst C
  have hsch := hvalid.toScheduleWellFormed
  have htime : SA.voteTime p.toParams (s + 1) < SA.gateTime p.toParams s := by
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ
    push_cast
    linarith [p.deltaPos]
  have hclock : ((4 * (s + 1) + 1 : Nat) : Time) * p.Δ =
      SA.voteTime p.toParams (s + 1) := by
    change ((4 * (s + 1) + 1 : Nat) : Int) * p.Δ =
      4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast
    ring
  obtain ⟨k, hk, _⟩ := fgsa_tick_total E rho hsch hdelta y hy (4 * (s + 1) + 1)
    (hclock ▸ htime.le.trans (hvalid.in_horizon _ (List.mem_of_getElem? ht)).2)
    (hclock ▸ hJ.1)
  rw [hclock] at hk
  have hki := V2.D.Engine.eventIndex_lt_of_time_lt hsch hk ht htime
  let src := actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))
  let dst := FGSA.clock p (storeAt p c E rho k y) (SA.voteTime p.toParams (s + 1))
  obtain ⟨Bfg, he, hframe, hpathB, hpaths⟩ := wcg_retrospectivePaths p c E rho ΔF w iStar
    hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i k x y s B hi hilen inv ht hslabel hki hk hJ hB hQC hord
  have hGST : E.t_GST ≤ SA.voteTime p.toParams s := by
    apply hs.firstVoteAfterGST.trans
    have hh : ((w.u + 1 : Nat) : Int) ≤ s := Int.ofNat_le.mpr (Nat.succ_le_of_lt hslabel)
    change 4 * p.Δ * ((w.u + 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + p.Δ
    nlinarith [p.deltaPos]
  have hsyncLabel := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho
    (fun o => ¬ isRowObject o) (SA.voteTime p.toParams s) (SA.gateTime p.toParams s)
    hsync (fgsaDelay_nonrow E.Δ _) hGST (by
      rw [hdelta]
      change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
      linarith [p.deltaPos]) (hvalid.in_horizon _ (List.mem_of_getElem? ht)).2
  have hFB : Block.Preceq (eraseFG dst.fg.F) B :=
    he ▸ block_preceq_trans hframe.frame.finalRoot hframe.frame.rootBelow
  have hforward : ∀ o ∈ GridCO.cleanSupport p.toParams.engine src s, ∀ seat,
      GridCO.headSeat? o = some seat → Gen.AC.Root.voteSupports src.blocks B o = true →
      (o ∈ headSupport p dst (s + 1) ∧ Gen.AC.Root.voteSupports dst.base.blocks B o = true) ∨
        GridCO.equivocates (headVotes p dst (s + 1)) seat = true := by
    intro o ho seat hseat hsupp
    obtain ⟨K, hlookup, hKm, _, hBK⟩ := (Gen.AC.Root.vote_support_body _ _ _).mp hsupp
    have hhead := actView_resolve_target p
      (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))
      (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho i x) _)
      (by rw [clockPre_headDomain]; exact base_headDomain_none p (reachable_stateBefore E rho i x))
      o hKm (resolvedTarget_root _ o hlookup)
    obtain ⟨Kfg, heK, hpath⟩ := hpaths o ho K hhead hBK
    exact fgsa_cleanSupport_forward_relay_on E rho hvalid s
      (ix := i) (iy := k) hx hy ht hk o ho seat hseat (by
        intro b heq
        subst o
        exact wcg_relay_transfer_head_scope hvalid hnr hdelta hsync hx hy
          (wcg_gate_enabled_of_result hsch ht hB) hk hJ
          (hvalid.in_horizon _ (List.mem_of_getElem? ht)).2 hGST seat b ho)
      Kfg (heK ▸ hhead) B
      (heK ▸ hBK) hpath hFB
  have hraw : SA.Root.confirmationFrom p.toParams
      (eraseFG (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)).fg.F)
      src s = some B := by
    have hh : gateResultAt p c E rho i = some (SA.Root.confirmationFrom p.toParams
        (eraseFG (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)).fg.F)
        src s) := by
      rw [gateResultAt_eq_gateResult p c E rho hsch ht,
        gateResult_eq_saved p c E rho hsch ht, clockPre_fg]
      exact fgsa_gate_saved_result E rho hsch ht
        (fgsa_gate_joined_of_enabled E rho (wcg_gate_enabled_of_result hsch ht hB))
    exact Option.some.inj (hh.symm.trans hB)
  let P := GridCO.cleanSupport p.toParams.engine src s
  let L := GridCO.lateVotes p.toParams.engine src s
  have hscore (D : Block) := actView_score p
    (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))
    (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho i x) _)
    (by rw [clockPre_headDomain]; exact base_headDomain_none p (reachable_stateBefore E rho i x))
    P P D
  have hmajority : GridCO.voterCount L < 2 * GridCO.goldfishScore src.blocks P P B := by
    rw [← hscore B]
    change (if _ then some _ else none) = some B at hraw
    split at hraw
    · have hwalk := Option.some.inj hraw
      rw [← hwalk]
      exact ‹_ < 2 * _›
    · contradiction
  have hcounts := Gen.AC.Root.transfer src.blocks dst.base.blocks P L
    (headVotes p dst (s + 1)) (headSupport p dst (s + 1)) B
    (fun _ ho => fgsa_early_subset_late p src s (List.mem_filter.mp ho).1)
    (fgsa_cleanSupport_seat_clean_late p src s) hforward
    (wcg_relay_headVotes_backward hvalid hnr hdelta hsync hx hy
      (wcg_gate_enabled_of_result hsch ht hB) hk hJ
      (hvalid.in_horizon _ (List.mem_of_getElem? ht)).2 hGST)
    (fgsa_headSupport_subset_headVotes E rho hvalid k y s) hmajority
  rw [Gen.AC.Root.TransferBounds_def] at hcounts
  have hinv : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho k y) _
  have hv : ∀ A, FGBlock.Preceq dst.fg.F A → FGBlock.Preceq A Bfg →
      A ∈ voterBlocks p dst (s + 1) := by
    intro A hFA hA
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨(hpathB A hA).1, hFA⟩,
      Bool.or_eq_true_iff.mpr (Or.inl ?_)⟩
    apply decide_eq_true
    simpa only [Nat.add_sub_cancel] using (hpathB A hA).2
  obtain ⟨D, hD, hfloor⟩ := hframe.frame.floor
  have hDB : D = Bfg := eraseFG_injective hD
  subst D
  have hpath : ∀ A, Block.Prec (liveRoot p dst) A → Block.Preceq A B →
      A ∈ erasedList dst
        (filteredFrom p.E p.cfg (frameR p dst) (voterBlocks p dst (s + 1))) := by
    intro A hr hAB
    have hroot : Block.Preceq (liveRoot p dst) A := (Bool.and_eq_true_iff.mp hr).2
    obtain ⟨Afg, hAfg, heA, hpre⟩ := eraseFG_ancestor_preceq hinv.fg.closed
      (hpathB Bfg (preceq_refl _)).1 (he ▸ hAB)
    apply List.mem_filter.mpr
    refine ⟨(hinv.baseTree A).mpr ⟨Afg, hAfg, heA⟩, decide_eq_true ⟨Afg, ?_, heA⟩⟩
    rw [filteredFrom_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)]
    apply (mem_filteredFromView (heightView p) (frameR p dst) _ Afg).mpr
    have hZA := block_preceq_trans hframe.startAbove hroot
    have hFA := eraseFG_preceq_iff.mp
      (heA ▸ block_preceq_trans hframe.frame.finalRoot hZA)
    exact ⟨hv Afg hFA hpre, hFA, eraseFG_preceq_iff.mp (heA ▸ hZA),
      Bfg, hv Bfg (eraseFG_preceq_iff.mp (he ▸ hFB)) (preceq_refl _), hpre, hfloor⟩
  have hhead : Block.Preceq B (headVote p dst (s + 1)) := by
    rw [fgsa_headVote_eq_filtered, ite_eq_right (Nat.succ_ne_zero s)]
    exact fgsa_headInTree_covers_of_transfer p dst _ _ _ B
      (block_compatible_of_common (he ▸ hframe.startBelow) (block_preceq_refl B))
      hpath hcounts.2.2.2.2.2.1 hcounts.2.2.2.2.2.2
  refine ⟨k, hki, hk, ?_, ?_, ?_⟩
  · rw [growth_headAtIdx_eq]
    unfold growth_headAtIdx
    rw [hk]
    exact hhead
  · intro A hAB
    obtain ⟨Afg, hAfg, heA⟩ := eraseFG_ancestor_mem hinv.fg.closed
      (hpathB Bfg (preceq_refl _)).1 (he ▸ hAB)
    exact (hinv.baseTree A).mpr ⟨Afg, hAfg, heA⟩
  · have hr : WCReceiptOrigins p c E rho k y (storeAt p c E rho k y) :=
      wcg_receiptOrigins E rho k y
    constructor
    · simpa only [(clock_cumulative p _ _).2.2.1] using hr.blocks
    · simpa only [(clock_cumulative p _ _).2.2.2.1] using hr.votes

end AvailableChain.FGSA.Run



/-! WC plan §6.5; DC the joint event step preserves all bounded history and state fields. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG Gen.Pure

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {w : HealingWitness} {iStar : Nat}

/-- WC plan §6.5; DC a completed result remains completed in an extended prefix. -/
private theorem growthStep_extend_result {i n j : Nat} {x : V} {s : Slot} {B : Block}
    (h : WCResult p c E rho w iStar i j x s B) (hin : i ≤ n) :
    WCResult p c E rho w iStar n j x s B :=
  { h with completed := h.completed.trans_le hin }

/-- WC plan §6.5; DC prefix origins remain valid in an extended history. -/
private theorem growthStep_extend_history {i n : Nat} {B : Block}
    (h : WCBelowHistory p c E rho w iStar i B) (hin : i ≤ n) :
    WCBelowHistory p c E rho w iStar n B := by
  rcases h.origin with h | ⟨j, x, s, C, hr, hb⟩
  · exact ⟨Or.inl h⟩
  · exact ⟨Or.inr ⟨j, x, s, C, growthStep_extend_result hr hin, hb⟩⟩

/-- WC plan §6.5; DC an ancestor uses the same seed or result origin. -/
private theorem growthStep_prefix_history {i : Nat} {A B : Block} (hab : Block.Preceq A B)
    (h : WCBelowHistory p c E rho w iStar i B) :
    WCBelowHistory p c E rho w iStar i A := by
  rcases h.origin with h | ⟨j, x, s, C, hr, hb⟩
  · exact ⟨Or.inl (block_preceq_trans hab h)⟩
  · exact ⟨Or.inr ⟨j, x, s, C, hr, block_preceq_trans hab hb⟩⟩

omit [DecidableEq V] in
/-- WC plan §6.5; DC the schedule orders completed gate labels. -/
private theorem growthStep_gate_label_le (hsch : V2.D.ScheduleWellFormed E rho)
    {i j : Nat} {x y : V} {s r : Slot} (hij : i ≤ j)
    (hi : IsGateTick p c rho i x s) (hj : IsGateTick p c rho j y r) : s ≤ r := by
  have ht : SA.gateTime p.toParams s ≤ SA.gateTime p.toParams r := by
    rcases hij.lt_or_eq with hij | rfl
    · obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
      obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
      have hk := (List.pairwise_iff_getElem.mp hsch.sorted) i j hil hjl hij
      rw [hie, hje] at hk
      exact V2.D.Engine.time_le_of_key_le _ _ hk
    · exact (V2.Event.tick.inj (Option.some.inj (hi.symm.trans hj))).2.le
  change 4 * p.Δ * (s : Int) + 6 * p.Δ ≤ 4 * p.Δ * (r : Int) + 6 * p.Δ at ht
  have hc : (s : Int) ≤ r := by nlinarith [p.deltaPos]
  exact Int.ofNat_le.mp hc

variable [Fintype V] {ΔF : Time}

/-- WC plan §6.5; DC join the proved handler, origin, gate and retrospective conclusions. -/
private theorem growthStep_step_core (hcausal : WCFinalityTargetEarlierStatement p c E rho) :
  WCGStepStatement p c E rho ΔF w iStar := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF hfaultQ haccountable hpart
    hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert hsrc hlabel hqc hstrat
    hnoslash hemitted htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead
    hs i hi hilen inv e he
  have hsch := hvalid.toScheduleWellFormed
  have hnext : i + 1 ≤ rho.events.length := Nat.succ_le_of_lt hilen
  have hfinite := wcg_finiteStep ΔF w iStar hvalid hlinked hcstar hnr hdelta hroots hsync
    hdeltaF hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo
    hcert hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines
    hheldRows hscopeRows hfinalHead hs i hi hilen inv e he
  have gate : ∀ x s, x ∈ rho.honest → enabledGateAt p c E rho i x s → w.u < s →
      ∃ B, gateResultAt p c E rho i = some (some B) ∧ Block.Preceq w.QStar B ∧
        gatePassedAt p c E rho i ∧
        (∀ j y r C, WCResult p c E rho w iStar i j y r C → r < s → Block.Preceq C B) ∧
        (∀ j y r C, WCResult p c E rho w iStar i j y r C → Block.Compatible C B) ∧
        ∀ y ∈ rho.honest,
          joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
          ∃ k < i, WCHeadRead p c E rho k y (s + 1) B := by
    intro x s hx ht hslabel
    obtain ⟨B, hB, hp, hQB, ho, hc, _⟩ := (wcg_gateResult hcausal) ΔF w iStar hvalid hlinked hcstar
      hnr hdelta hroots hsync hdeltaF hfaultQ haccountable hpart hstore hcumul hmono
      hactive hframe hmeta hrec hgeo hcert hsrc hlabel hqc hstrat hnoslash hemitted
      htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead hs i x s hi hilen
      inv ht hslabel
    exact ⟨B, hB, hQB, hp, ho, hc, (wcg_retrospective hcausal) hvalid hlinked hcstar hnr hdelta
      hroots
      hsync hdeltaF hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta
      hrec hgeo hcert hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast
      hdeadlines hheldRows hscopeRows hfinalHead hs i hi hilen inv x s B hx ht.1 hslabel hB⟩
  have nonempty : ∀ j x s, iStar ≤ j → j < i + 1 → x ∈ rho.honest →
      enabledGateAt p c E rho j x s → w.u < s →
      ∃ B, gateResultAt p c E rho j = some (some B) ∧
        Block.Preceq w.QStar B ∧ gatePassedAt p c E rho j := by
    intro j x s hj hji hx ht hl
    rcases (Nat.le_of_lt_succ hji).lt_or_eq with hlt | rfl
    · exact inv.nonempty j x s hj hlt hx ht hl
    · obtain ⟨B, hB, hQ, hp, _⟩ := gate x s hx ht hl
      exact ⟨B, hB, hQ, hp⟩
  have ordered : ∀ j k x y s r B C, WCResult p c E rho w iStar (i + 1) j x s B →
      WCResult p c E rho w iStar (i + 1) k y r C → s < r → Block.Preceq B C := by
    intro j k x y s r B C hb hc hsr
    by_cases hk : k < i
    · by_cases hj : j < i
      · exact inv.ordered j k x y s r B C { hb with completed := hj }
          { hc with completed := hk } hsr
      · have heq : j = i := by have := hb.completed; omega
        subst j
        exact (not_lt.mpr (growthStep_gate_label_le hsch hk.le hc.event hb.event) hsr).elim
    · have heq : k = i := by have := hc.completed; omega
      subst k
      have hj : j < i := by
        by_contra hn
        have heq : j = i := by have := hb.completed; omega
        subst j
        exact (not_lt.mpr (growthStep_gate_label_le hsch le_rfl hc.event hb.event)) hsr
      obtain ⟨D, hD, _, _, ho, _⟩ := gate y r hc.honest (wcg_gate_enabled_of_result hsch
        hc.event hc.value) hc.label
      have heq : C = D := Option.some.inj (Option.some.inj (hc.value.symm.trans hD))
      exact heq ▸ ho j x s B { hb with completed := hj } hsr
  have sameLabel : ∀ j k x y s B C, WCResult p c E rho w iStar (i + 1) j x s B →
      WCResult p c E rho w iStar (i + 1) k y s C → Block.Compatible B C := by
    intro j k x y s B C hb hc
    by_cases hj : j < i
    · by_cases hk : k < i
      · exact inv.sameLabel j k x y s B C { hb with completed := hj }
          { hc with completed := hk }
      · have heq : k = i := by have := hc.completed; omega
        subst k
        obtain ⟨D, hD, _, _, _, hcompat, _⟩ := gate y s hc.honest (wcg_gate_enabled_of_result
        hsch hc.event hc.value) hc.label
        have heq : C = D := Option.some.inj (Option.some.inj (hc.value.symm.trans hD))
        exact heq ▸ hcompat j x s B { hb with completed := hj }
    · have heq : j = i := by have := hb.completed; omega
      subst j
      by_cases hk : k < i
      · obtain ⟨D, hD, _, _, _, hcompat, _⟩ := gate x s hb.honest (wcg_gate_enabled_of_result
        hsch hb.event hb.value) hb.label
        have heq : B = D := Option.some.inj (Option.some.inj (hb.value.symm.trans hD))
        change Block.compatible B C = true
        rw [block_compatible_comm, heq]
        exact hcompat k y s C { hc with completed := hk }
      · have heq : k = i := by have := hc.completed; omega
        subst k
        have heq : B = C := Option.some.inj (Option.some.inj (hb.value.symm.trans hc.value))
        exact block_compatible_of_common (heq ▸ block_preceq_refl C) (block_preceq_refl C)
  have resultCompat : ∀ j k x y s r B C,
      WCResult p c E rho w iStar (i + 1) j x s B →
      WCResult p c E rho w iStar (i + 1) k y r C → Block.Compatible B C := by
    intro j k x y s r B C hb hc
    rcases lt_trichotomy s r with h | h | h
    · exact block_compatible_of_common (ordered j k x y s r B C hb hc h)
        (block_preceq_refl C)
    · subst r
      exact sameLabel j k x y s B C hb hc
    · exact block_compatible_of_common (block_preceq_refl B)
        (ordered k j y x r s C B hc hb h)
  have historyCompat : ∀ A j x s B, WCBelowHistory p c E rho w iStar (i + 1) A →
      WCResult p c E rho w iStar (i + 1) j x s B → Block.Compatible A B := by
    intro A j x s B ha hr
    rcases ha.origin with ha | ⟨k, y, r, C, hc, hAC⟩
    · obtain ⟨C, hC, hQC, _⟩ := nonempty j x s hr.afterCut hr.completed hr.honest
        (wcg_gate_enabled_of_result hsch hr.event hr.value) hr.label
      have heq : C = B := Option.some.inj (Option.some.inj (hC.symm.trans hr.value))
      exact block_compatible_of_common (block_preceq_trans ha (heq ▸ hQC))
        (block_preceq_refl B)
    · exact block_compatible_of_preceq_compatible hAC (resultCompat k j y x r s C B hc hr)
  have sources : ∀ j x r K, iStar ≤ j → j < i + 1 → x ∈ rho.honest →
      rho.events[j]? = some (.tick x (p.actionTime r)) →
      actionSourceFG p c E rho x r = some (some K) →
      ∃ B, WCResult p c E rho w iStar (i + 1) j x (r * p.R) B ∧
        Block.Preceq (eraseFG K) B := by
    intro j x r K hj hji hx ht hK
    have hread : actionSource p c E rho x r = some (some (eraseFG K)) := by
      change (actionSourceFG p c E rho x r).map (Option.map eraseFG) = _
      rw [hK]
      rfl
    obtain ⟨targets, B, _, hmem, hB, hbelow, _⟩ := hsrc x r _ hx hread
    have hgate : IsGateTick p c rho j x (r * p.R) := ht
    exact ⟨B, ⟨hx, hj, hji, (wcg_gate_cut_iff hsch hs hgate).mp hj, hgate,
      (gateResultAt_eq_gateResult p c E rho hsch hgate).trans hB⟩, hbelow _ hmem⟩
  have finite : ∀ k, iStar ≤ k → k ≤ i + 1 → WCFiniteFacts p c E rho k := by
    intro k hk hkn
    by_cases hki : k ≤ i
    · exact inv.finite k hk hki
    · have heq : k = i + 1 := by omega
      exact heq ▸ hfinite
  have finalHistory : ∀ x ∈ rho.honest,
      WCBelowHistory p c E rho w iStar i (F_at p c E rho (i + 1) x) := by
    intro x hx
    obtain ⟨D, hD, hF⟩ := (hstore (i + 1) x hx).1.fg.Fcar
    by_cases hlo : (finalityView p D).h_F ≤ w.M
    · have hbelow := (wcg_lowFinalized (hroots.toNamedRootCollisionFree E rho) haccountable hs
        D _ _ (wcg_finalizedOccurrence hscopeRows hnoslash D _ _
          (rootScope_store hx hD) hF rfl) hlo).2
      exact ⟨Or.inl hbelow⟩
    have hpos : 0 < (finalityView p D).h_F := by simp only [Height] at hlo ⊢; omega
    have hhigh : w.M + 1 ≤ (finalityView p D).h_F := by simp only [Height] at hlo ⊢; omega
    obtain ⟨jf, z, rf, af, uf, H, jt, q, rt, aT, ut, K, B, hjf, haf, _, _, _, _,
      _, _, _, _, hjt, haT, hdecode, _, htarget, hK, hXK, _hgate, _hKB, hgap⟩ :=
      (hcausal hvalid hlinked hfaultQ
        (hroots.toNamedRootCollisionFree E rho) hheldRows hfinalHead hqc
        hemitted (i + 1) x D _ _ ⟨hx, hD⟩ hpos hF rfl).finalityRow
    have hfields : aT.payload.height_pair = ut.height_pair := by
      rcases aT with ⟨auth, body⟩
      cases auth with
      | none => cases hdecode
      | proposer s => cases hdecode
      | seat label k =>
        cases label with
        | head s => cases hdecode
        | fg => exact congrArg Row.height_pair (Option.some.inj hdecode)
    have hname : namedEntry aT.payload.height_pair =
        some ((finalityView p D).h_F, (storeAt p c E rho (i + 1) x).fg.F.root) := by
      rw [hfields, htarget]
      rfl
    by_cases hbefore : jt < iStar
    · obtain ⟨K', B', hK', _, _, _, _, hbelow⟩ :=
        hs.highSources jt q rt aT _ hbefore haT hname hhigh
      have heq : K = K' := Option.some.inj (Option.some.inj (hK.symm.trans hK'))
      exact ⟨Or.inl (block_preceq_trans (eraseFG_preceq hXK) (heq ▸ hbelow))⟩
    obtain ⟨C, hr, hKC⟩ := inv.suffixSources jt q rt K (Nat.le_of_not_gt hbefore)
      (hjt.trans_le (Nat.le_of_lt_succ hjf)) haT.1 haT.2.1 hK
    exact ⟨Or.inr ⟨jt, q, rt * p.R, C, hr,
      block_preceq_trans (eraseFG_preceq hXK) hKC⟩⟩
  have historyCompatOld : ∀ A C, WCBelowHistory p c E rho w iStar i A →
      WCBelowHistory p c E rho w iStar i C → Block.Compatible A C := by
    have seedResult : ∀ j x s B, WCResult p c E rho w iStar i j x s B →
        Block.Preceq w.QStar B := by
      intro j x s B hr
      obtain ⟨C, hC, hQ, _⟩ := inv.nonempty j x s hr.afterCut hr.completed hr.honest
        (wcg_gate_enabled_of_result hsch hr.event hr.value) hr.label
      have heq : C = B := Option.some.inj (Option.some.inj (hC.symm.trans hr.value))
      exact heq ▸ hQ
    intro A C ha hc
    rcases ha.origin with ha | ⟨j, x, r, B, hb, hAB⟩
    · rcases hc.origin with hc | ⟨k, y, s, D, hd, hCD⟩
      · exact block_compatible_of_common ha hc
      · exact block_compatible_of_common
          (block_preceq_trans ha (seedResult k y s D hd)) hCD
    · rcases hc.origin with hc | ⟨k, y, s, D, hd, hCD⟩
      · exact block_compatible_of_common hAB
          (block_preceq_trans hc (seedResult j x r B hb))
      · have hBD := resultCompat j k x y r s B D
          (growthStep_extend_result hb (Nat.le_succ i))
          (growthStep_extend_result hd (Nat.le_succ i))
        apply block_compatible_of_preceq_compatible hAB
        change Block.compatible _ _ = true
        rw [block_compatible_comm]
        apply block_compatible_of_preceq_compatible hCD
        change Block.compatible _ _ = true
        rw [block_compatible_comm]
        exact hBD
  have hout := wcg_outputStep hsch
    (fun x hx => historyCompatOld _ _
      (wcg_outputHistoryAt hs inv hi le_rfl hx) (finalHistory x hx)) (by
      intro x s hx hG
      obtain ⟨B, hB, hQ, hp, _, _, _⟩ := gate x s hx hG
        ((wcg_gate_cut_iff hsch hs hG.1).mp hi)
      have hcompat := historyCompat _ i x s B
        (growthStep_extend_history (wcg_outputHistoryAt hs inv hi le_rfl hx) (Nat.le_succ i))
        ⟨hx, hi, Nat.lt_succ_self i, ((wcg_gate_cut_iff hsch hs hG.1).mp hi), hG.1, hB⟩
      exact ⟨B, hB, hp, ((wcg_gate_cut_iff hsch hs hG.1).mp hi), hcompat⟩)
  have outputHistory : ∀ x ∈ rho.honest,
      WCBelowHistory p c E rho w iStar (i + 1) (S_at p c E rho (i + 1) x) := by
    intro x hx
    rcases (hout x hx).2 with hkeep | ⟨s, ht, hl, hraw⟩ | hfinal
    · rw [hkeep]
      exact growthStep_extend_history (wcg_outputHistoryAt hs inv hi le_rfl hx) (Nat.le_succ i)
    · exact ⟨Or.inr ⟨i, x, s, _,
        ⟨hx, hi, Nat.lt_succ_self i, hl, ht, hraw⟩, block_preceq_refl _⟩⟩
    · rw [hfinal]
      exact growthStep_extend_history (finalHistory x hx) (Nat.le_succ i)
  have oldOrigin : ∀ k x, iStar ≤ k → k ≤ i → x ∈ rho.honest →
      S_at p c E rho k x = w.QStar ∨
      (∃ j y s, WCResult p c E rho w iStar k j y s (S_at p c E rho k x)) ∨
      (∃ l, iStar ≤ l ∧ l ≤ k ∧ S_at p c E rho k x = F_at p c E rho l x ∧
        ∀ j y s B, WCResult p c E rho w iStar (i + 1) j y s B →
          Block.Compatible (F_at p c E rho l x) B) := by
    intro k x hlo hki hx
    rcases inv.outputOrigin k x hlo hki hx with hq | hr | ⟨l, hl, hlk, heq, _⟩
    · exact Or.inl hq
    · exact Or.inr (Or.inl hr)
    · refine Or.inr (Or.inr ⟨l, hl, hlk, heq, ?_⟩)
      intro j y s B hr
      exact historyCompat _ j y s B
        (growthStep_extend_history (wcg_finalHistoryAt hs inv hl (hlk.trans hki) hx)
          (hlk.trans (hki.trans (Nat.le_succ i)))) hr
  refine {
    interval := ⟨hi.trans (Nat.le_succ i), hnext⟩
    nonempty := nonempty
    ordered := ordered
    sameLabel := sameLabel
    retrospective := ?_
    preCutHigh := inv.preCutHigh
    suffixSources := sources
    highCertificates := ?_
    lowFinalized := ?_
    liveTargets := ?_
    oldLiveTargets := ?_
    suffixSaved := ?_
    suffixFast := ?_
    outputOrigin := ?_
    served := ?_
    transitions := ?_
    finite := finite
    carrier := ?_ }
  · intro j x s B hr y hy hJ
    by_cases hj : j < i
    · exact inv.retrospective j x s B { hr with completed := hj } y hy hJ
    · have heq : j = i := by have := hr.completed; omega
      subst j
      obtain ⟨C, hC, _, _, _, _, hhead⟩ := gate x s hr.honest
        (wcg_gate_enabled_of_result hsch hr.event hr.value) hr.label
      have heq : B = C := Option.some.inj (Option.some.inj (hr.value.symm.trans hC))
      exact heq ▸ hhead y hy hJ
  · intro k x W X hlo hkn hx hW hX hn hh
    by_cases hki : k ≤ i
    · exact inv.highCertificates k x W X hlo hki hx hW hX hn hh
    · have heq : k = i + 1 := by omega
      subst k
      have ho := hfinite.certified x hx W hW X hX hn
      refine ⟨ho, ?_⟩
      obtain ⟨j, y, r, wire, K, B, hj, hrow, hname, hK, hXK, _⟩ := ho.origin
      by_cases hjcut : j < iStar
      · obtain ⟨K', B', hK', _, _, _, _, hbelow⟩ :=
          hs.highSources j y r wire _ hjcut hrow hname hh
        have heq : K = K' := Option.some.inj (Option.some.inj (hK.symm.trans hK'))
        exact ⟨Or.inl (block_preceq_trans (eraseFG_preceq hXK) (heq ▸ hbelow))⟩
      · obtain ⟨C, hr, hKC⟩ := sources j y r K (Nat.le_of_not_gt hjcut) hj hrow.1 hrow.2.1 hK
        exact ⟨Or.inr ⟨j, y, r * p.R, C, hr, block_preceq_trans (eraseFG_preceq hXK) hKC⟩⟩
  · intro k x D X h _ _ hD hF hh hlo
    exact (wcg_lowFinalized (hroots.toNamedRootCollisionFree E rho) haccountable hs D X h
      (wcg_finalizedOccurrence hscopeRows hnoslash D X h
        (rootScope_store hD.1 hD.2) hF hh) hlo).1
  · intro k x row hlo hkn hx hr ht
    by_cases hki : k ≤ i
    · exact inv.liveTargets k x row hlo hki hx hr ht
    · have heq : k = i + 1 := by omega
      subst k
      exact growthStep_prefix_history (htargets (i + 1) x row hr) (outputHistory x hx)
  · intro k x row hlo _ hx hr _ ht
    have hnow := V2.D.Engine.stateBefore_now_mono_atRestart (fgsaClock p c)
      (fgsaRestoreTimeLaw p c) E rho hsch
      hlo x
    rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho iStar x),
      fgsa_clock_now p c (V2.D.Run.stateBefore E rho k x)] at hnow
    exact hs.liveTargets x hx row hr (hnow.trans_lt ht)
  · intro k x s B hlo hkn hx hslabel hB
    obtain ⟨j, hj, hRF, ht, hraw⟩ := (finite k hlo hkn).saved x hx s B hB
    exact ⟨j, hRF, hx, (wcg_gate_cut_iff hsch hs ht.1).mpr hslabel, hj, hslabel, ht.1, hraw⟩
  · intro k x s X hlo hkn hx hslabel hX
    obtain ⟨j, hj, hRF, ht, _, B, hB, hXB, _⟩ := (finite k hlo hkn).fastWrites x hx s X hX
    exact ⟨j, B, hRF, ⟨hx, (wcg_gate_cut_iff hsch hs ht.1).mpr hslabel, hj, hslabel, ht.1, hB⟩, hXB⟩
  · intro k x hlo hkn hx
    by_cases hki : k ≤ i
    · exact oldOrigin k x hlo hki hx
    · have heq : k = i + 1 := by omega
      subst k
      rcases (hout x hx).2 with hkeep | ⟨s, ht, hl, hB⟩ | hfinal
      · rcases oldOrigin i x hi le_rfl hx with hq | ⟨j, y, s, hr⟩ | ⟨l, hl, hli, hF, hc⟩
        · exact Or.inl (hkeep.trans hq)
        · right; left
          refine ⟨j, y, s, ?_⟩
          rw [hkeep]
          exact growthStep_extend_result hr (Nat.le_succ i)
        · exact Or.inr (Or.inr ⟨l, hl, hli.trans (Nat.le_succ i), hkeep.trans hF, hc⟩)
      · exact Or.inr (Or.inl ⟨i, x, s, hx, hi, Nat.lt_succ_self i, hl, ht, hB⟩)
      · exact Or.inr (Or.inr ⟨i + 1, hi.trans (Nat.le_succ i), le_rfl, hfinal,
          fun j y s B hr => historyCompat _ j y s B
            (growthStep_extend_history (finalHistory x hx) (Nat.le_succ i)) hr⟩)
  · intro k x hlo hkn hx
    by_cases hki : k ≤ i
    · exact inv.served k x hlo hki hx
    · have heq : k = i + 1 := by omega
      subst k
      apply block_preceq_trans _ (hout x hx.1.1).1
      rw [← hs.refreshed x hx.1.1]
      exact wcg_output_mono_of_inv hsch hs inv iStar i x ⟨le_rfl, hi⟩
        ⟨hi, le_rfl⟩ hi hx.1.1
  · intro k x hlo hkn hx hxnext
    rcases (Nat.le_of_lt_succ hkn).lt_or_eq with hki | rfl
    · exact inv.transitions k x hlo hki hx hxnext
    · exact (hout x hx.1.1).1
  · obtain ⟨W, hW, hh, _, hmem⟩ := hs.carrier
    refine ⟨W, hW, hh, ?_⟩
    intro k x hlo hkn hx
    exact (hcumul.1 iStar k x hx hlo (hkn.trans hnext)).1 (hmem x hx)

/-- WC plan §6.5; DC delivery preserves the joint invariant after immediate reconciliation. -/
theorem wcg_stepDelivery (hcausal : WCFinalityTargetEarlierStatement p c E rho) :
  WCGStepDeliveryStatement p c E rho ΔF w iStar := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i hi hilen inv x o t he
  exact (growthStep_step_core hcausal) hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i hi hilen inv (.deliver x o t) he

/-- WC plan §6.5; DC a tick without a gate preserves the joint invariant in handler order. -/
theorem wcg_stepNoGateTick (hcausal : WCFinalityTargetEarlierStatement p c E rho) :
  WCGStepNoGateTickStatement p c E rho ΔF w iStar := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i hi hilen inv x t he _hgate
  exact (growthStep_step_core hcausal) hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i hi hilen inv (.tick x t) he

/-- WC plan §6.5; DC a suffix gate adds its ordered result and retrospective HEAD evidence. -/
theorem wcg_stepGateTick (hcausal : WCFinalityTargetEarlierStatement p c E rho) :
  WCGStepGateTickStatement p c E rho ΔF w iStar := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i hi hilen inv x s he _hlabel
  exact (growthStep_step_core hcausal) hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i hi hilen inv (.tick x (SA.gateTime p.toParams s)) he

/-- WC plan §6.5; DC split the actual event into the proved delivery, tick and restart cases. -/
theorem wcg_step (hcausal : WCFinalityTargetEarlierStatement p c E rho) : WCGStepStatement p c
  E rho ΔF w iStar := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i hi hilen inv e he
  cases e with
  | deliver x o t =>
    exact (wcg_stepDelivery hcausal) hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
        hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
        hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
        hscopeRows hfinalHead hs i hi hilen inv x o t he
  | restart x t =>
    exact (wcg_stepRestart hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
        hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
        hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
        hscopeRows hfinalHead hs i hi hilen inv x t he)
  | tick x t =>
    by_cases hg : isGateTime p t = true
    · obtain ⟨s, rfl⟩ := (isGateTime_iff p t).mp hg
      exact (wcg_stepGateTick hcausal) hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
        hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
        hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
        hscopeRows hfinalHead hs i hi hilen inv x s he
        ((wcg_gate_cut_iff hvalid.toScheduleWellFormed hs he).mp hi)
    · exact (wcg_stepNoGateTick hcausal) hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
        hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
        hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
        hscopeRows hfinalHead hs i hi hilen inv x t he (Bool.eq_false_iff.mpr hg)

end AvailableChain.FGSA.Run



/-! WC plan §6.8; DC finality remains below every honest output. -/





/-! WC plan §§6.6–6.8; DC joint event induction and the five seeded safety fields. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V] [Fintype V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {ΔF : Time} {w : HealingWitness} {iStar : Nat}

/-- WC plan §6.6; DC initialization and actual event steps prove the complete suffix invariant. -/
theorem wcg_seededInduction (hcausal : WCFinalityTargetEarlierStatement p c E rho) :
  WCGSeededInductionStatement p c E rho ΔF w iStar := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs
  have initial := wcg_init hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs hs.within
  have step := (wcg_step hcausal) hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs
  have all : ∀ i, iStar ≤ i → i ≤ rho.events.length → WCInv p c E rho w iStar i := by
    intro i hi
    induction i, hi using Nat.le_induction with
    | base => intro _; exact initial
    | succ i hi ih =>
      intro hbound
      have hlt : i < rho.events.length := by omega
      exact step i hi hlt (ih (Nat.le_of_lt hlt)) rho.events[i]
        (List.getElem?_eq_getElem hlt)
  intro i hi
  exact all i hi.1 hi.2

end AvailableChain.FGSA.Run

end

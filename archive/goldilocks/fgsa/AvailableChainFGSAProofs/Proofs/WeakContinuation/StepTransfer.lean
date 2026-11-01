module
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.Epoch
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.StepGateHistory
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.StepTransferReceipts
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.HeadRelay
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.ReceiptOrigins
public import AvailableChainFGSA.Proofs.Head.Transfer -- shake: keep (fgsa_headInTree_covers_of_transfer proof reference)

public section

/-! WC plan §6.5; DC retrospective HEAD transfer precedes exact proposal adoption. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG Gen.Pure

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V] [Fintype V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {ΔF : Time} {w : HealingWitness} {iStar : Nat}

/-- WC plan §6.5; DC raw pools, carried support and original receipts give the earlier HEAD. -/
theorem wc_retrospective : WCRetrospectiveStatement p c E rho ΔF w iStar := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfault hfaultQ hfaultX hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i hi hilen inv x s B hx ht hslabel hB y hy hJ
  obtain ⟨C, hC, _, hQC, hord, _, _⟩ := wc_gateResult ΔF w iStar hvalid hlinked hcstar hnr
    hdelta hroots hsync hdeltaF
    hfault hfaultQ hfaultX hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead
    hs i x s hi hilen inv (wc_gate_enabled_of_result hvalid.toScheduleWellFormed ht hB) hslabel
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
  obtain ⟨Bfg, he, hframe, hpathB, hpaths⟩ := wc_retrospectivePaths p c E rho ΔF w iStar
    hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfault hfaultQ hfaultX hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
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
        exact wc_relay_transfer_head_scope hvalid hnr hdelta hsync hx hy
          (wc_gate_enabled_of_result hsch ht hB) hk hJ
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
        (fgsa_gate_joined_of_enabled E rho (wc_gate_enabled_of_result hsch ht hB))
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
    (wc_relay_headVotes_backward hvalid hnr hdelta hsync hx hy
      (wc_gate_enabled_of_result hsch ht hB) hk hJ
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
  · unfold headAtIdx
    rw [hk]
    exact hhead
  · intro A hAB
    obtain ⟨Afg, hAfg, heA⟩ := eraseFG_ancestor_mem hinv.fg.closed
      (hpathB Bfg (preceq_refl _)).1 (he ▸ hAB)
    exact (hinv.baseTree A).mpr ⟨Afg, hAfg, heA⟩
  · have hr : WCReceiptOrigins p c E rho k y (storeAt p c E rho k y) :=
      wc_receiptOrigins E rho k y
    constructor
    · simpa only [(clock_cumulative p _ _).2.2.1] using hr.blocks
    · simpa only [(clock_cumulative p _ _).2.2.2.1] using hr.votes

end AvailableChain.FGSA.Run
end

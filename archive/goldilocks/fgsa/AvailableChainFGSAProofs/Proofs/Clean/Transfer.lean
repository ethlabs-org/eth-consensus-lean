module
public import AvailableChainFGSAProofs.Proofs.Shared.Channels
public import AvailableChainFGSAProofs.Proofs.Clean.TransferFrame
public import AvailableChainFGSAProofs.Proofs.Clean.Service
public import AvailableChainFGSA.Proofs.Head.Transfer -- shake: keep (fgsa_headInTree_covers_of_transfer proof reference)

public section

namespace AvailableChain.FGSA.Run

variable {ΔF : Time}
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} (c : AppCodec In)
    [DecidableEq V] [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

set_option linter.unusedVariables false in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F2.3:5496–5503; bp02 §4.2, G24. Class B, private run instance.
DC: Goldfish/Adoption.lean:53–67,158–170; AdoptionTransport.lean:346.
INTENTIONAL: the actual F-anchored optional gate result supplies the majority
(spec:2506–2513). The named forward hypothesis is private, as required by the
F2.3 split ruling; like G24 and DC it covers only source supporters of B.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
private theorem clean_transfer_counts_of_forward (b₀ : Time) :
  CleanCutSet p c E rho b₀ ΔF → Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card →
  FGFoundation p c E rho → SrcFrameAboveStmt p c E rho →
  ∀ i k x y s B, i < timeIdx rho b₀ → k < i →
    IsGateTick p c rho i x s →
    rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1))) →
    joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
    CleanHist p c E rho i → (∀ j, j ≤ i → CleanState p c E rho j) →
    gateResultAt p c E rho i = some (some B) →
    (∀ r C, (r, C) ∈ cleanResults p c E rho i → r < s → Block.Preceq C B) →
    let src := FGSA.actView (FGSA.clockPre p (storeAt p c E rho i x)
      (SA.gateTime p.toParams s))
    let dst := ((fgsa p c).clock (V2.D.Run.stateBefore E rho k y)
      (SA.voteTime p.toParams (s + 1))).st
    let P := GridCO.cleanSupport p.toParams.engine src s
    let L := GridCO.lateVotes p.toParams.engine src s
    let U := FGSA.headVotes p dst (s + 1)
    let Vsup := FGSA.headSupport p dst (s + 1)
    ∀ (hC5 : ∀ o ∈ P, ∀ seat, GridCO.headSeat? o = some seat →
      Gen.AC.Root.voteSupports src.blocks B o = true →
      (o ∈ Vsup ∧ Gen.AC.Root.voteSupports dst.base.blocks B o = true) ∨
        GridCO.equivocates U seat = true),
    Gen.AC.Root.TransferBounds (Gen.AC.Root.plainSupporters src.blocks P P B)
      L dst.base.blocks U Vsup B := by
  intro h _ _ _ i k x y s B hi _ ht hk hJ _ _ hB _ src dst P L U Vsup hC5
  have hsch := h.base.valid.toScheduleWellFormed
  have hx := hsch.honest_only _ (List.mem_of_getElem? ht)
  have hy := hsch.honest_only _ (List.mem_of_getElem? hk)
  have hcut := (V2.D.Engine.index_lt_read_length_iff hsch b₀ ht).mp hi
  have hraw := (clean_gate_nonempty_raw hsch ht hB).2
  have hscore (C : Block) := actView_score p
    (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))
    (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho i x) _)
    (by rw [clockPre_headDomain]; exact base_headDomain_none p (reachable_stateBefore E rho i x))
    P P C
  have hmajority : GridCO.voterCount L < 2 * GridCO.goldfishScore src.blocks P P B := by
    rw [← hscore B]
    change (if _ then some _ else none) = some B at hraw
    split at hraw
    · have he := Option.some.inj hraw
      subst B
      exact ‹_ < 2 * _›
    · contradiction
  exact Gen.AC.Root.transfer src.blocks dst.base.blocks P L U Vsup B
    (fun _ ho => fgsa_early_subset_late p src s (List.mem_filter.mp ho).1)
    (fgsa_cleanSupport_seat_clean_late p src s)
    hC5
    (clean_headVotes_backward h hx hy (clean_gate_enabled_of_result hsch ht hB) hk hJ hcut)
    (fgsa_headSupport_subset_headVotes E rho h.base.valid k y s) hmajority

set_option linter.unusedVariables false in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F2.3:5496–5503; bp02 §4.2; blueprint claim bp.cleanTransfer.v1
(00:756–765): internal lane theorem, public statement candidate for a later freeze.
Class B. DC: AdoptionTransport.lean:346 and Goldfish/Adoption.lean:441–461.
INTENTIONAL: FG-SA uses an F-anchored optional result, a lease liveRoot and
an FJ voter domain (spec:2506–2525,2557–2565). Current Ordered is explicit
(review-00-02:234–236). The split ruling keeps the named C5 premise private;
this conditional lemma does not export the later public cleanTransfer.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
private theorem cleanTransfer_of_forward (b₀ : Time) :
  CleanCutSet p c E rho b₀ ΔF → Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card →
  FGFoundation p c E rho → SrcFrameAboveStmt p c E rho →
  ∀ i k x y s B, i < timeIdx rho b₀ → k < i →
    IsGateTick p c rho i x s →
    rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1))) →
    joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
    CleanHist p c E rho i → (∀ j, j ≤ i → CleanState p c E rho j) →
    gateResultAt p c E rho i = some (some B) →
    (∀ r C, (r, C) ∈ cleanResults p c E rho i → r < s → Block.Preceq C B) →
    let src := FGSA.actView (FGSA.clockPre p (storeAt p c E rho i x)
      (SA.gateTime p.toParams s))
    let dst := ((fgsa p c).clock (V2.D.Run.stateBefore E rho k y)
      (SA.voteTime p.toParams (s + 1))).st
    let P := GridCO.cleanSupport p.toParams.engine src s
    let L := GridCO.lateVotes p.toParams.engine src s
    let U := FGSA.headVotes p dst (s + 1)
    let Vsup := FGSA.headSupport p dst (s + 1)
    ∀ (hC5 : ∀ o ∈ P, ∀ seat, GridCO.headSeat? o = some seat →
      Gen.AC.Root.voteSupports src.blocks B o = true →
      (o ∈ Vsup ∧ Gen.AC.Root.voteSupports dst.base.blocks B o = true) ∨
        GridCO.equivocates U seat = true),
    Block.Preceq B (headAtIdx p c E rho k (s + 1)) := by
  intro h hq hf hsrc i k x y s B hi hki ht hk hJ hh hall hB hord src dst P L U Vsup hC5
  have hc := clean_transfer_counts_of_forward p c E rho b₀ h hq hf hsrc
    i k x y s B hi hki ht hk hJ hh hall hB hord hC5
  rw [Gen.AC.Root.TransferBounds_def] at hc
  obtain ⟨Bfg, he, _, _, _, _, _, hroot, hV, hdom⟩ :=
    clean_transfer_frame p c E rho b₀ h hq hf hsrc
      i k x y s B hi hki ht hk hJ hh hall hB hord
  have hinv : CStoreInv p dst :=
    cstoreInv_clock p _ (cstoreInv_stateBefore E rho k y) _
  have hstored : Bfg ∈ dst.fg.TF := by
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hV).1).1
  have hpath : ∀ C, Block.Prec (liveRoot p dst) C → Block.Preceq C B →
      C ∈ erasedList dst
        (filteredFrom p.E p.cfg (controls p dst) (voterBlocks p dst (s + 1))) := by
    intro C hr hCB
    have hr' : liveRoot p dst ≠ C ∧ Block.Preceq (liveRoot p dst) C := by
      change ((!decide (liveRoot p dst = C)) && Block.preceq (liveRoot p dst) C) = true at hr
      simpa only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        Block.Preceq] using hr
    obtain ⟨A, hA, heA, hAB⟩ := eraseFG_ancestor_preceq hinv.fg.closed hstored (he ▸ hCB)
    apply List.mem_filter.mpr
    refine ⟨(hinv.baseTree C).mpr ⟨A, hA, heA⟩, decide_eq_true ⟨A, ?_, heA⟩⟩
    simpa only [fgsa_domainR_eq_filtered] using
      hdom A (heA ▸ hr'.2) hAB (by simpa only [heA] using Ne.symm hr'.1)
  have hhead : Block.Preceq B (headVote p dst (s + 1)) := by
    rw [fgsa_headVote_eq_filtered, ite_eq_right (Nat.succ_ne_zero s)]
    exact fgsa_headInTree_covers_of_transfer p dst _ _ _ B
      (Bool.or_eq_true_iff.mpr (Or.inl hroot)) hpath hc.2.2.2.2.2.1 hc.2.2.2.2.2.2
  have hread : headAtIdx p c E rho k (s + 1) = headVote p dst (s + 1) := by
    delta headAtIdx
    rw [hk]
  exact hread ▸ hhead

set_option linter.unusedVariables false in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F2.3:5496–5503; bp02 §4.2 C5, G24 item 4. Class B.
DC: Goldfish/Adoption.lean:53–62; AdoptionTransport.lean:346.
INTENTIONAL: the FG-SA head path and current-F frame come from the clean
history at the source gate, with strict freeze stamps at the target read.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
private theorem clean_transfer_forward (b₀ : Time) :
  CleanCutSet p c E rho b₀ ΔF → Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card →
  FGFoundation p c E rho → SrcFrameAboveStmt p c E rho →
  ∀ i k x y s B, i < timeIdx rho b₀ → k < i →
    IsGateTick p c rho i x s →
    rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1))) →
    joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
    CleanHist p c E rho i → (∀ j, j ≤ i → CleanState p c E rho j) →
    gateResultAt p c E rho i = some (some B) →
    (∀ r C, (r, C) ∈ cleanResults p c E rho i → r < s → Block.Preceq C B) →
    let src := FGSA.actView (FGSA.clockPre p (storeAt p c E rho i x)
      (SA.gateTime p.toParams s))
    let dst := ((fgsa p c).clock (V2.D.Run.stateBefore E rho k y)
      (SA.voteTime p.toParams (s + 1))).st
    let P := GridCO.cleanSupport p.toParams.engine src s
    let L := GridCO.lateVotes p.toParams.engine src s
    let U := FGSA.headVotes p dst (s + 1)
    let Vsup := FGSA.headSupport p dst (s + 1)
    ∀ o ∈ P, ∀ seat, GridCO.headSeat? o = some seat →
      Gen.AC.Root.voteSupports src.blocks B o = true →
      (o ∈ Vsup ∧ Gen.AC.Root.voteSupports dst.base.blocks B o = true) ∨
        GridCO.equivocates U seat = true := by
  intro h hq hf hsrc i k x y s B hi hki ht hk hJ hh hall hB hord src dst P L U Vsup
    o ho seat hs hsupp
  have hsch := h.base.valid.toScheduleWellFormed
  have hx := hsch.honest_only _ (List.mem_of_getElem? ht)
  have hy := hsch.honest_only _ (List.mem_of_getElem? hk)
  have hcut := (V2.D.Engine.index_lt_read_length_iff hsch b₀ ht).mp hi
  obtain ⟨K, hlookup, hKm, _, hBK⟩ := (Gen.AC.Root.vote_support_body _ _ _).mp hsupp
  have hhead := actView_resolve_target p
    (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))
    (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho i x) _)
    (by rw [clockPre_headDomain]; exact base_headDomain_none p (reachable_stateBefore E rho i x))
    o hKm (resolvedTarget_root _ o hlookup)
  obtain ⟨Kfg, he, hpath⟩ := clean_transfer_prefreeze_path_of_head p c E rho b₀ h hq hf hsrc
    i k x y s B K o hi hki ht hk hJ hh hall hB hord ho hhead hBK
  obtain ⟨Bfg', he', hF, _⟩ := clean_transfer_frame p c E rho b₀ h hq hf hsrc
    i k x y s B hi hki ht hk hJ hh hall hB hord
  exact fgsa_cleanSupport_forward_relay_on E rho h.base.valid
    s (ix := i) (iy := k) hx hy ht hk o ho seat hs (by
      intro b he
      subst o
      exact clean_transfer_head_scope h hx hy (clean_gate_enabled_of_result hsch ht hB)
        hk hJ hcut seat b ho) Kfg (he ▸ hhead) B
    (he ▸ hBK) hpath (he' ▸ eraseFG_preceq hF)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint claim bp.cleanTransfer.v1 (00:756–765):
internal lane theorem, public statement candidate for a later freeze.
P3 F2.3:5496–5503; bp02 §4.2. Class B, FG-SA run instance.
DC: AdoptionTransport.lean:346; Goldfish/Adoption.lean:53–67,415–461.
INTENTIONAL: the F-anchored optional result replaces SG grades and the lease
sets liveRoot (spec:2500–2525); the FJ voter domain restricts the walked tree
(spec:2557–2571). Current Ordered stays explicit because the consumer supplies
OSN (review-00-02:234–236; lead Q2). No UNMOTIVATED or UNCLEAR divergence.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem cleanTransfer (b₀ : Time) :
  CleanCutSet p c E rho b₀ ΔF → Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card →
  FGFoundation p c E rho → SrcFrameAboveStmt p c E rho →
  ∀ i k x y s B, i < timeIdx rho b₀ → k < i →
    IsGateTick p c rho i x s →
    rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1))) →
    joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
    CleanHist p c E rho i → (∀ j, j ≤ i → CleanState p c E rho j) →
    gateResultAt p c E rho i = some (some B) →
    (∀ r C, (r, C) ∈ cleanResults p c E rho i → r < s → Block.Preceq C B) →
    Block.Preceq B (headAtIdx p c E rho k (s + 1)) := by
  intro h hq hf hsrc i k x y s B hi hki ht hk hJ hh hall hB hord
  exact cleanTransfer_of_forward p c E rho b₀ h hq hf hsrc
    i k x y s B hi hki ht hk hJ hh hall hB hord
    (clean_transfer_forward p c E rho b₀ h hq hf hsrc
      i k x y s B hi hki ht hk hJ hh hall hB hord)

end AvailableChain.FGSA.Run

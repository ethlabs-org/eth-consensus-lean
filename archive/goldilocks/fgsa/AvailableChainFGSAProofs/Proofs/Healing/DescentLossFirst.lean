module
public import AvailableChainFGSAProofs.Proofs.Healing.DescentLoss

public section

/-! H-DESCENT D2 (H.13): the first transfer at label sB + 1 in the moving frame.
The H.1 count and transport step of `healing_first_transfer_core` with the
kept path and the live root from a domain witness of the HEAD view, not from
PhaseInterval. The lease bound is the release lower bound of the source. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

omit [DecidableEq V] in
private theorem first_lift {A B : FGBlock (Fin p.n)}
    (h : Block.Preceq (eraseFG A) (eraseFG B)) : FGBlock.Preceq A B :=
  eraseFG_preceq_iff.mp h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Plan fgsa-s5-m5-d2d4 B `cause` (first release l = sB + 1; H.1 re-proved
without PhaseInterval); blueprint 21:673–699, 2777–2798.
DC: INTENTIONAL moving frame. Let B be a high source of label sB, and X an
ancestor-closed part of the frozen HEAD view of an honest node x at v_(sB+1).
If B is in the domain of X at that read, the HEAD of x covers B. The domain
gives the kept path and F, Z ⪯ B; the release of the source support gives the
live leases; the genuine source result gives the majority (H.1). -/
theorem healing_first_transfer_domain [Fintype V] {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF)
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    {B : FGBlock (Fin p.n)} {sB : Slot} (hB : HighSrcN p c E rho B sB)
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (sB + 1))))
    (hScopes : ∀ ix xs, xs ∈ rho.honest → IsGateTick p c rho ix xs sB →
      (∃ C, gateResultAt p c E rho ix = some (some C) ∧ Block.Preceq (eraseFG B) C) →
      FirstTransferScope E rho ix iy xs y sB)
    {X : Finset (FGBlock (Fin p.n))}
    (hXv : X ⊆ voterBlocks p (FGSA.clock p (storeAt p c E rho iy y)
      (SA.voteTime p.toParams (sB + 1))) (sB + 1))
    (hXc : ∀ W ∈ X, ∀ A, FGBlock.Preceq (storeAt p c E rho iy y).fg.F A →
      FGBlock.Preceq A W → A ∈ X)
    (hD : B ∈ D_at p c E rho iy y X) :
    Block.Preceq (eraseFG B) (headAtIdx p c E rho iy (sB + 1)) := by
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hDelta := hrec.base.delta
  rw [HighSrcN_def, SrcN_def] at hB
  obtain ⟨hsrc, hc⟩ := hB
  have hSync := healing_high_source_labelSync p c E rho hrec emittedNonempty emittedName hsrc hc
  obtain ⟨j, xs, r, a, -, ha, hBs, hsB⟩ := hsrc
  subst hsB
  have hx := ha.1
  let s := r * p.R
  obtain ⟨-, Gr, -, hG, hBG, st, hst, hτ⟩ :=
    healing_source_decode p c E rho emittedNonempty emittedName ha hBs
  rw [gateIn_def, preTick_def] at hst
  cases hix' : V2.D.Run.tickIdx? rho xs (SA.gateTime p.toParams s) with
  | none => rw [hix'] at hst; cases hst
  | some ix =>
  rw [hix'] at hst
  have hix := V2.D.Run.tickIdx?_spec hix'
  have hst' := Option.some.inj hst
  subst hst'
  let src := actView (clockPre p (storeAt p c E rho ix xs) (SA.gateTime p.toParams s))
  let dst := FGSA.clock p (storeAt p c E rho iy y) (SA.voteTime p.toParams (s + 1))
  -- The genuine result Gr ⪰ B gives the majority for B.
  have hScope := hScopes ix xs hx hix
    ⟨Gr, (gateResultAt_eq_gateResult p c E rho hS hix).trans hG, hBG⟩
  have hconf := (fgsa_gate_raw_of_nonempty p c E rho hS hix hG).2
  have hmaj : GridCO.voterCount (GridCO.lateVotes p.toParams.engine src s) <
      2 * GridCO.goldfishScore src.blocks (GridCO.cleanSupport p.toParams.engine src s)
        (GridCO.cleanSupport p.toParams.engine src s) (eraseFG B) := by
    have hh : GridCO.voterCount (GridCO.lateVotes p.toParams.engine src s) <
        2 * GridCO.goldfishScore src.blocks (GridCO.cleanSupport p.toParams.engine src s)
          (GridCO.cleanSupport p.toParams.engine src s) Gr := by
      change (if _ then some _ else none) = some Gr at hconf
      split at hconf
      · have he := Option.some.inj hconf
        subst Gr
        have heq (C : Block) :
            GridCO.goldfishScoreOn (GridCO.resolutionTree src) src.blocks
              (GridCO.cleanSupport p.toParams.engine src s)
              (GridCO.cleanSupport p.toParams.engine src s) C =
            GridCO.goldfishScore src.blocks (GridCO.cleanSupport p.toParams.engine src s)
              (GridCO.cleanSupport p.toParams.engine src s) C :=
          actView_score p (clockPre p (storeAt p c E rho ix xs) (SA.gateTime p.toParams s))
            (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho ix xs) _)
            (by rw [clockPre_headDomain];
                exact base_headDomain_none p (reachable_stateBefore E rho ix xs)) _ _ C
        rw [← heq _]
        assumption
      · contradiction
    have hanti := Gen.AC.Root.goldfishScore_antitone src.blocks
      (GridCO.cleanSupport p.toParams.engine src s)
      (GridCO.cleanSupport p.toParams.engine src s) (eraseFG B) Gr hBG
    omega
  -- The domain witness of B at the receiver read.
  have hinv : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho iy y) _
  have hdfg : dst.fg = (storeAt p c E rho iy y).fg := clock_fg p _ _
  have hRd : FGSA.controls p dst = R_at p c E rho iy y := by
    change KitFG.treeStoreControlsView (heightView p) dst.fg =
      KitFG.treeStoreControlsView (heightView p) (storeAt p c E rho iy y).fg
    rw [hdfg]
  obtain ⟨hBX, hFB, hZB, W, hWX, hBW, hloW⟩ :=
    (KitFG.mem_filteredFromView (heightView p) (R_at p c E rho iy y) X B).mp hD
  have hvW : W ∈ voterBlocks p dst (s + 1) := hXv hWX
  have hWdst : W ∈ dst.fg.TF :=
    Next.tree_subset_TF p dst (Finset.mem_filter.mp hvW).1
  have hFB0 : Block.Preceq (eraseFG (storeAt p c E rho iy y).fg.F) (eraseFG B) :=
    eraseFG_preceq hFB
  have hFB' : Block.Preceq (eraseFG dst.fg.F) (eraseFG B) := hdfg ▸ hFB0
  -- The kept path: every block between the live root and B is in the frozen domain.
  have hpath : ∀ C, Block.Prec (liveRoot p dst) C → Block.Preceq C (eraseFG B) →
      C ∈ erasedList dst (filteredFrom p.E p.cfg (FGSA.controls p dst)
        (voterBlocks p dst (s + 1))) := by
    intro C hr hCB
    have hr' : liveRoot p dst ≠ C ∧ Block.Preceq (liveRoot p dst) C := by
      change ((!decide (liveRoot p dst = C)) && Block.preceq (liveRoot p dst) C) = true at hr
      simpa only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        Block.Preceq] using hr
    obtain ⟨A, hA, heA, hAW⟩ := eraseFG_ancestor_preceq hinv.fg.closed hWdst
      (Gen.Pure.block_preceq_trans hCB (eraseFG_preceq hBW))
    have hFA : FGBlock.Preceq dst.fg.F A := first_lift p
      (Gen.Pure.block_preceq_trans (F_preceq_liveRoot p dst hinv) (heA ▸ hr'.2))
    have hZA : FGBlock.Preceq (FGSA.controls p dst).Z A := first_lift p
      (Gen.Pure.block_preceq_trans (fgsa_Z_preceq_liveRoot p dst) (heA ▸ hr'.2))
    apply List.mem_filter.mpr
    refine ⟨(hinv.baseTree C).mpr ⟨A, hA, heA⟩, decide_eq_true ⟨A, ?_, heA⟩⟩
    rw [KitFG.filteredFrom_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)]
    exact (KitFG.mem_filteredFromView (heightView p) (FGSA.controls p dst) _ A).mpr
      ⟨hXv (hXc W hWX A (hdfg ▸ hFA) hAW), hFA, hZA, W, hvW, hAW, hRd ▸ hloW⟩
  -- The live root is compatible with B: every surviving lease passed the release.
  have hrows := healing_support_release_compat (hroots := hrec.base.receiptIdealization)
    E rho hE hDelta s hSync hx hy hix hiy hScope hτ hFB0
  have hanchor : Block.Compatible (liveRoot p dst) (eraseFG B) := by
    have hselect := Gen.Pure.foldl_select_mem (fun (best b : Block) =>
      best.depth < b.depth || (best.depth == b.depth && best.root < b.root))
      (dst.base.obligations.filterMap (fun row =>
        if dst.base.now < row.2.2 && decide (∃ X ∈ FGSA.fullTree p dst, eraseFG X = row.1)
        then some row.1 else none)) (eraseFG (FGSA.controls p dst).Z)
    change FGSA.liveRoot p dst = _ ∨ FGSA.liveRoot p dst ∈ _ at hselect
    rcases hselect with he | hm
    · rw [he, hRd]
      exact Gen.Pure.block_compatible_of_common (eraseFG_preceq hZB)
        (Gen.Pure.block_preceq_refl _)
    · obtain ⟨row, hr, hrow⟩ := List.mem_filterMap.mp hm
      split at hrow
      · rw [← Option.some.inj hrow]
        exact hrows row hr
      · contradiction
  -- Majority and rival dominance at the receiver (forward and reverse relay).
  have hforward : ∀ o ∈ GridCO.cleanSupport p.toParams.engine src s, ∀ seat,
      GridCO.headSeat? o = some seat → Gen.AC.Root.voteSupports src.blocks (eraseFG B) o = true →
      (o ∈ FGSA.headSupport p dst (s + 1) ∧
        Gen.AC.Root.voteSupports dst.base.blocks (eraseFG B) o = true) ∨
        GridCO.equivocates (FGSA.headVotes p dst (s + 1)) seat = true := by
    intro o' ho' seat hs' hsup'
    obtain ⟨K', hK', hKm', hKst', _, _, _⟩ := healing_support_clean_target E rho o' ho'
    have hBK' : Block.Preceq (eraseFG B) K' := by
      have hlookup : Gen.AC.Root.resolvedTarget? src.blocks o' = some K' :=
        actView_target_of_resolvedHead p _
          (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho ix xs) _) o' hK'
      rw [Gen.AC.Root.voteSupports_def, hlookup] at hsup'
      exact (Bool.and_eq_true_iff.mp hsup').2
    obtain ⟨Kfg', hKe', hpath'⟩ := healing_support_target_path_on
      (hroots := hrec.base.receiptIdealization) E rho hS hy hiy
      (hScope.epoch.mono (fgsa_idxBefore_mono rho (by
        change 4 * p.Δ * (s : Int) + 2 * p.Δ ≤ 4 * p.Δ * (s : Int) + 3 * p.Δ
        linarith [p.deltaPos])) le_rfl) K'
      (hScope.targets K' hKm' hKst' (Gen.Pure.block_preceq_trans hFB0 hBK'))
    exact fgsa_cleanSupport_forward_relay_on_receipt E rho hE s hx hy hix hiy o' ho'
      seat hs' (fun b he => hScope.forward seat b (he ▸ ho')) Kfg' (hKe' ▸ hK')
      (eraseFG B) (hKe' ▸ hBK') hpath' hFB'
  have htr := Gen.AC.Root.transfer src.blocks dst.base.blocks
    (GridCO.cleanSupport p.toParams.engine src s) (GridCO.lateVotes p.toParams.engine src s)
    (FGSA.headVotes p dst (s + 1)) (FGSA.headSupport p dst (s + 1)) (eraseFG B)
    (fun _ ho' => fgsa_early_subset_late p src s (List.mem_filter.mp ho').1)
    (fgsa_cleanSupport_seat_clean_late p src s) hforward
    (fgsa_headVotes_backward_relay_on_receipt E rho hE s ix iy xs y hx
      (fun q b hb => hScope.backward q b (Or.inr hb)))
    (fgsa_headSupport_subset_headVotes E rho hE iy y s) hmaj
  rw [Gen.AC.Root.TransferBounds_def] at htr
  rw [healing_headAtIdx_tick p c E rho hiy]
  rw [fgsa_headVote_eq_filtered, ite_eq_right (Nat.succ_ne_zero s)]
  exact fgsa_headInTree_covers_of_transfer p dst _ _ _ (eraseFG B) hanchor hpath
    htr.2.2.2.2.2.1 htr.2.2.2.2.2.2

end AvailableChain.FGSA.Run
end

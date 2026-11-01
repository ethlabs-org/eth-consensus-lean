module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetLease -- shake: keep (J4-A input)
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetKeep -- shake: keep (J4-A input)
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetCompat -- shake: keep (J4-A input)

public import AvailableChainFGSAProofs.Proofs.Healing.DescentLossNext
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetLeaseMove

public section

/-! Blueprint 21 H.15:2885–2923, H.1:663–708; plan J4-A;
B1/B13/B17/B18. First transfer for an arbitrary written prefix.
DC: SAME majority transport; INTENTIONAL moving domain and slow window.
The gate result supplies the majority. No emitted source of B is needed. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

omit [DecidableEq V] in
private theorem written_lift {A B : FGBlock (Fin p.n)}
    (h : Block.Preceq (eraseFG A) (eraseFG B)) : FGBlock.Preceq A B :=
  eraseFG_preceq_iff.mp h

omit [DecidableEq V] in
private theorem written_walk_extends (anchor : Block) (tree : List Block)
    (score : Block → Nat) (eligible : Block → Bool) :
    Block.Preceq anchor (GridCO.ghost anchor tree score eligible) := by
  apply Gen.Pure.walk_covers_of_dominated_suffix
  · exact Gen.Pure.block_compatible_of_common
      (Gen.Pure.block_preceq_refl anchor) (Gen.Pure.block_preceq_refl anchor)
  · rw [Gen.Pure.DominatedSuffix_def]
    intro A hA hAF
    change ((!decide (anchor = A)) && Block.preceq anchor A) = true at hA
    obtain ⟨hne, hpre⟩ := Bool.and_eq_true_iff.mp hA
    have he := Gen.Pure.block_preceq_antisymm hpre hAF
    simp only [he, decide_true, Bool.not_true, Bool.false_eq_true] at hne

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.15:2894–2900; plan J4-A A1 synchrony;
B1/B13/B17/B18. DC: SAME causal frontier cut. A stored prefix above C*
cannot be held at u₀. Its gate is after u₀, so its HEAD label is after GST.
This uses the actual stored prefix, without an emitted-source premise. -/
theorem postReset_written_ready [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {w : HealingWitness}
    (h0r : H0Reset p c E rho w) {i : Nat} {y : V} {s : Slot} {B : Block}
    (hy : y ∈ rho.honest) (ht : IsGateTick p c rho i y s)
    (hCB : Block.Preceq w.CStar B)
    (hB : B ∈ (actView (clockPre p (storeAt p c E rho i y)
      (SA.gateTime p.toParams s))).blocks) :
    recoveryStart p E < SA.voteTime p.toParams s := by
  have hs := hrec.base.valid.toScheduleWellFormed
  have hb := (actView_blocks _ _).mp hB |>.1
  rw [(clockPre_fields p _ _).2.1] at hb
  obtain ⟨Bfg, hBfg, heB⟩ := (cstoreInv_stateBefore E rho i y).baseTree B |>.mp hb
  obtain ⟨_, _, _, Cfg, _, _, _, heC, hhC⟩ := h0r.fresh
  have hCBfg : FGBlock.Preceq Cfg Bfg := written_lift p (by rwa [heC, heB])
  have hhB : w.M + 1 ≤ (heightView p Bfg).h :=
    hhC ▸ (fgCertificateLaws p).height.h_mono hCBfg
  have hcut : w.u₀ < SA.gateTime p.toParams s := by
    by_contra hn
    have hi : i ≤ timeIdx rho w.u₀ :=
      ((V2.D.Engine.index_lt_read_length_iff hs w.u₀ ht).mpr (le_of_not_gt hn)).le
    have hBcut := (fgsa_store_durable p c E rho hi y).1 hBfg
    have hheight := healing_phase_height_le p c E rho hBcut
    have hfront : (storeAt p c E rho (timeIdx rho w.u₀) y).fg.h_max ≤ w.M := by
      rw [h0r.frontier]
      unfold honestFrontier
      rw [V2.D.Engine.readAt_eq_stateBefore hs w.u₀]
      exact Finset.le_sup (f := fun z => (storeAt p c E rho (timeIdx rho w.u₀) z).fg.h_max) hy
    exact (Nat.not_succ_le_self w.M) (hhB.trans (hheight.trans hfront))
  have hP : 8 * p.Δ ≤ P p := by
    have hR : (2 : Int) ≤ p.R := by exact_mod_cast p.RLarge
    change 8 * p.Δ ≤ 4 * (p.R : Int) * p.Δ
    nlinarith [p.deltaPos]
  have hlow := h0r.cut_lower
  change w.u₀ < 4 * p.Δ * (s : Int) + 6 * p.Δ at hcut
  change recoveryStart p E < 4 * p.Δ * (s : Int) + p.Δ
  linarith [p.deltaPos]

/-- The stored reset extension starts after the complete recovery batch cut. -/
theorem postReset_written_sync [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {w : HealingWitness}
    (h0r : H0Reset p c E rho w) {i : Nat} {y : V} {s : Slot} {B : Block}
    (hy : y ∈ rho.honest) (ht : IsGateTick p c rho i y s)
    (hCB : Block.Preceq w.CStar B)
    (hB : B ∈ (actView (clockPre p (storeAt p c E rho i y)
      (SA.gateTime p.toParams s))).blocks) :
    E.t_GST < SA.voteTime p.toParams s :=
  lt_of_le_of_lt (healing_recoveryStart_ge p E)
    (postReset_written_ready p c E rho hrec h0r hy ht hCB hB)

theorem postReset_written_window [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {w : HealingWitness}
    (h0r : H0Reset p c E rho w) {i : Nat} {y : V} {s : Slot} {B : Block}
    (hy : y ∈ rho.honest) (ht : IsGateTick p c rho i y s)
    (hCB : Block.Preceq w.CStar B)
    (hB : B ∈ (actView (clockPre p (storeAt p c E rho i y)
      (SA.gateTime p.toParams s))).blocks) : HealingWindow p E 1 s :=
  healing_window_of_cut E (healing_ready_vote_cutoff E
    (postReset_written_ready p c E rho hrec h0r hy ht hCB hB).le)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.15:2902–2914, H.1:673–699; plan J4-A A1;
B1/B13/B17/B18. DC: SAME count and relay with a kept domain path.
The fast arm uses release. The slow arm uses the last-write window.
Assembly supplies fgsa_rMono and fgsa_leaseOrigins_lastWrite. The domain
and label synchrony are explicit read guards for the H.15 producer. -/
theorem healing_first_transfer_written [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    {ix : Nat} {x : V} {s : Slot} {C : Block} (hx : x ∈ rho.honest)
    (hix : IsGateTick p c rho ix x s)
    (hres : gateResultAt p c E rho ix = some (some C))
    {B : FGBlock (Fin p.n)} (hBC : Block.Preceq (eraseFG B) C)
    (hgst : E.t_GST ≤ SA.voteTime p.toParams s)
    (hCut : HealingWindow p E 1 s)
    (harm : SA.releaseThreshold p.toParams ≤ SA.Root.prefixSupport p.toParams
        (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s
        (eraseFG B) ∨
      (E.t_GST ≤ SA.voteTime p.toParams (s + 1 - p.k) ∧
        GridCO.slowEligible p.toParams.engine
          (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s
          (eraseFG B) = true))
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hGuard : enabledGateAt p c E rho ix x s)
    (hJoin : joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)))
    {X : Finset (FGBlock (Fin p.n))}
    (hXv : X ⊆ voterBlocks p (FGSA.clock p (storeAt p c E rho iy y)
      (SA.voteTime p.toParams (s + 1))) (s + 1))
    (hXc : ∀ W ∈ X, ∀ A, FGBlock.Preceq (storeAt p c E rho iy y).fg.F A →
      FGBlock.Preceq A W → A ∈ X)
    (hD : B ∈ D_at p c E rho iy y X) :
    Block.Preceq (eraseFG B) (headAtIdx p c E rho iy (s + 1)) := by
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hDelta := hrec.base.delta
  have hScope := healing_first_transfer_scope_recovery E rho hrec mono hgst hx hy
    hix hiy hGuard hJoin
  have hhor : SA.gateTime p.toParams s ≤ rho.horizon :=
    (hS.in_horizon _ (List.mem_of_getElem? hix)).2
  have hvd : SA.voteTime p.toParams s + E.Δ ≤ SA.gateTime p.toParams s := by
    rw [hDelta]
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hSync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _
    hrec.sync (fgsaDelay_nonrow E.Δ _) hgst hvd hhor
  have hres' : gateResult p c E rho x s = some (some C) :=
    (gateResultAt_eq_gateResult p c E rho hS hix).symm.trans hres
  let src := actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))
  have hmaj := healing_slow_majority E rho hS hix hres' hBC
  let dst := FGSA.clock p (storeAt p c E rho iy y) (SA.voteTime p.toParams (s + 1))
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
    have hFA : FGBlock.Preceq dst.fg.F A := written_lift p
      (Gen.Pure.block_preceq_trans (F_preceq_liveRoot p dst hinv) (heA ▸ hr'.2))
    have hZA : FGBlock.Preceq (FGSA.controls p dst).Z A := written_lift p
      (Gen.Pure.block_preceq_trans (fgsa_Z_preceq_liveRoot p dst) (heA ▸ hr'.2))
    apply List.mem_filter.mpr
    refine ⟨(hinv.baseTree C).mpr ⟨A, hA, heA⟩, decide_eq_true ⟨A, ?_, heA⟩⟩
    rw [KitFG.filteredFrom_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)]
    exact (KitFG.mem_filteredFromView (heightView p) (FGSA.controls p dst) _ A).mpr
      ⟨hXv (hXc W hWX A (hdfg ▸ hFA) hAW), hFA, hZA, W, hvW, hAW, hRd ▸ hloW⟩
  -- Both admission arms remove conflicting leases at this HEAD read.
  have hrows : ∀ row ∈ dst.base.obligations, Block.Compatible row.1 (eraseFG B) := by
    rcases harm with hτ | ⟨hgw, hel⟩
    · exact healing_support_release_compat (hroots := hrec.base.receiptIdealization)
        E rho hE hDelta s
        hSync hx hy hix hiy hScope hτ hFB0
    · have hst : gateIn p c E rho x s =
          some (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s)) := by
        rw [gateIn_def, preTick_def, fgsa_tickIdx_of_event p c E rho hS hix]
        rfl
      exact healing_slow_lease E rho hrec mono writes hgst hhor hx hgw hst hres' hBC hel
        le_rfl (hS.in_horizon _ (List.mem_of_getElem? hiy)).2
        (healing_slow_support_scope_recovery E rho hrec mono hCut hgw hx)
        (fun w hw1 hw2 => absurd (hw1.trans hw2) (Nat.not_succ_le_self s)) hy hiy hFB0
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
          (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho ix x) _) o' hK'
      rw [Gen.AC.Root.voteSupports_def, hlookup] at hsup'
      exact (Bool.and_eq_true_iff.mp hsup').2
    obtain ⟨Kfg', hKe', hpath'⟩ :=
      healing_support_target_path_on (hroots := hrec.base.receiptIdealization)
      E rho hS hy hiy
      (healing_recovery_epoch_after_vote E rho hrec hy hgst (by
        change 4 * p.Δ * (s : Int) + p.Δ < 4 * p.Δ * (s : Int) + 3 * p.Δ
        linarith [p.deltaPos]) _ ) K'
      (hScope.targets K' hKm' hKst' (Gen.Pure.block_preceq_trans hFB0 hBK'))
    exact fgsa_cleanSupport_forward_relay_on_receipt E rho hE s hx hy hix hiy o' ho'
      seat hs' (fun b hb => hScope.forward seat b (hb ▸ ho'))
      Kfg' (hKe' ▸ hK') (eraseFG B) (hKe' ▸ hBK') hpath' hFB'
  have htr := Gen.AC.Root.transfer src.blocks dst.base.blocks
    (GridCO.cleanSupport p.toParams.engine src s) (GridCO.lateVotes p.toParams.engine src s)
    (FGSA.headVotes p dst (s + 1)) (FGSA.headSupport p dst (s + 1)) (eraseFG B)
    (fun _ ho' => fgsa_early_subset_late p src s (List.mem_filter.mp ho').1)
    (fgsa_cleanSupport_seat_clean_late p src s) hforward
    (fgsa_headVotes_backward_relay_on_receipt E rho hE s ix iy x y hx
      (fun q b hb => hScope.backward q b (Or.inr hb)))
    (fgsa_headSupport_subset_headVotes E rho hE iy y s) hmaj
  rw [Gen.AC.Root.TransferBounds_def] at htr
  rw [healing_headAtIdx_tick p c E rho hiy]
  rw [fgsa_headVote_eq_filtered, ite_eq_right (Nat.succ_ne_zero s)]
  exact fgsa_headInTree_covers_of_transfer p dst _ _ _ (eraseFG B) hanchor hpath
    htr.2.2.2.2.2.1 htr.2.2.2.2.2.2


section WrittenDomain
variable [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    (source : TSrc p c E rho)
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    {w : HealingWitness} (h0r : H0Reset p c E rho w)

include hrec mono source emittedNonempty emittedName writes xing origin h0r

omit mono source emittedNonempty emittedName writes xing origin h0r in
private theorem written_source_label {iy : Nat} {y : V} {s : Slot}
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    {K : FGBlock (Fin p.n)} {r : Slot} (hK : SourceBefore p c E rho iy K r) :
    r + 1 ≤ s := by
  have ht := healing_source_gate p c E rho hrec.base.valid.toScheduleWellFormed hK hiy
  change 4 * p.Δ * (r : Int) + 6 * p.Δ ≤
    4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ at ht
  push_cast at ht
  have hrs : (r : Int) < s := by
    by_contra hn
    have hsr : (s : Int) ≤ r := le_of_not_gt hn
    nlinarith [p.deltaPos]
  exact_mod_cast hrs

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.15:2908–2914; plan J4-A2 route steps 1–7;
B1/B13/B17/B18. DC: SAME common honest HEAD from emitted-source no-loss.
The written prefix needs no emitted row. The shared supporter producer is
J5-A healing_gate_result_supporter, with its exact statement. Synchrony
comes from postReset_written_sync. The inherited engine has m = p.k. -/
theorem postReset_written_source_compatible
    {ix : Nat} {x : V} {s : Slot} {C : Block} {B : FGBlock (Fin p.n)}
    (hx : x ∈ rho.honest) (hix : IsGateTick p c rho ix x s)
    (hres : gateResultAt p c E rho ix = some (some C))
    (hCB : Block.Preceq w.CStar (eraseFG B))
    (hmem : eraseFG B ∈ (actView (clockPre p (storeAt p c E rho ix x)
      (SA.gateTime p.toParams s))).blocks)
    (hBC : Block.Preceq (eraseFG B) C)
    {iy : Nat} {y : V}
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1)))) :
    ∀ K r, SourceBefore p c E rho iy K r → high p w K →
      Block.Compatible (eraseFG B) (eraseFG K) := by
  have noLoss := (healing_high_source_compat p c E rho hrec
    (healing_loss_service_scope_recovery E rho hrec mono source emittedNonempty emittedName)
    mono emittedNonempty
    emittedName writes xing origin).1
  have hgst := postReset_written_sync p c E rho hrec h0r hx hix hCB hmem
  obtain ⟨jh, z, hz, hjh, hCH, -⟩ :=
    healing_gate_result_supporter p c E rho hrec
      (healing_raw_service_scope_recovery E rho hrec mono) hgst.le
      (postReset_written_window p c E rho hrec h0r hx hix hCB hmem).2 hx hix hres
  intro K r hK hhK
  have hrs := written_source_label p c E rho hrec hiy hK
  have hKn : HighSrcN p c E rho K r := by
    rw [HighSrcN_def]
    rw [high_def] at hhK
    exact ⟨healing_srcN_of_source p c E rho hK,
      (Nat.succ_le_succ h0r.mu_le).trans hhK⟩
  have hKH : Block.Preceq (eraseFG K) (headAtIdx p c E rho jh s) := by
    by_contra hn
    apply noLoss jh K r
    rw [Lost_def]
    exact ⟨hKn, z, s, hz, hrs, hjh, hn⟩
  exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_trans hBC hCH) hKH

omit hrec mono source emittedNonempty emittedName writes xing origin h0r in
omit [Fintype V] in
private theorem written_stored {ix : Nat} {x : V} {s : Slot} {B : FGBlock (Fin p.n)}
    (hmem : eraseFG B ∈ (actView (clockPre p (storeAt p c E rho ix x)
      (SA.gateTime p.toParams s))).blocks) : B ∈ (storeAt p c E rho ix x).fg.TF := by
  have hb := (actView_blocks _ _).mp hmem |>.1
  rw [(clockPre_fields p _ _).2.1] at hb
  obtain ⟨A, hA, he⟩ := (cstoreInv_stateBefore E rho ix x).baseTree (eraseFG B) |>.mp hb
  exact (eraseFG_injective he) ▸ hA

omit hrec mono source emittedNonempty emittedName writes xing origin h0r in
omit [Fintype V] in
private theorem written_source_mono {j i : Nat} {K : FGBlock (Fin p.n)} {r : Slot}
    (h : SourceBefore p c E rho j K r) (hji : j ≤ i) : SourceBefore p c E rho i K r := by
  obtain ⟨a, z, q, row, haj, hrow, hsrc, he⟩ := h
  exact ⟨a, z, q, row, haj.trans_le hji, hrow, hsrc, he⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.15:2904–2914; plan J4-A2, frozen domain;
B1/B13/B17/B18. DC: INTENTIONAL moving-frame descent at the first HEAD.
The root and finality coverage cases are excluded by the branch guards.
The proof supplies receipt and restricted view coverage, then excludes
both descent causes. It applies before and after q_(s*), without a phase
or a reset-copy availability premise. Only high_compatible at i is read.
The inherited engine has m = p.k; the label-s supporter is synchronous. -/
theorem postReset_written_domain
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    {ix : Nat} {x : V} {s : Slot} {C : Block} {B : FGBlock (Fin p.n)}
    (hx : x ∈ rho.honest) (hix : IsGateTick p c rho ix x s)
    (hres : gateResultAt p c E rho ix = some (some C))
    (hCB : Block.Preceq w.CStar (eraseFG B))
    (hmem : eraseFG B ∈ (actView (clockPre p (storeAt p c E rho ix x)
      (SA.gateTime p.toParams s))).blocks)
    (hBC : Block.Preceq (eraseFG B) C)
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hyi : iy ≤ i)
    (hnZ : ¬ FGBlock.Preceq B (R_at p c E rho iy y).Z)
    (hnF : ¬ FGBlock.Preceq B (storeAt p c E rho iy y).fg.F) :
    B ∈ D_at p c E rho iy y
      (storeAt p c E rho (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s)) y).fg.TF := by
  have hs := hrec.base.valid.toScheduleWellFormed
  have hBK := postReset_written_source_compatible p c E rho hrec mono source emittedNonempty
    emittedName writes xing origin h0r hx hix hres hCB hmem hBC hiy
  obtain ⟨-, -, -, Cfg, -, -, -, heC, hhC⟩ := h0r.fresh
  have hCBfg : FGBlock.Preceq Cfg B := written_lift p (by rwa [heC])
  have hhB : high p w B := by
    rw [high_def]
    exact hhC ▸ (fgCertificateLaws p).height.h_mono hCBfg
  have hBstore := written_stored p c E rho hmem
  have hFB : FGBlock.Preceq (storeAt p c E rho iy y).fg.F B := by
    by_cases hFg : (storeAt p c E rho iy y).fg.F = .genesis
    · rw [hFg]; exact KitFG.genesis_preceq B
    obtain ⟨D, hD, hDF, K, r, hK, hhK, hKF, -⟩ :=
      healing_finality_source (hroots := hrec.base.idealization) p c E rho hs origin hy hFg
    by_cases hl : (finalityView p D).h_F < (heightView p B).h
    · exact xing iy (iy + ix) y x D B hy (Nat.le_add_right iy ix) hD hDF
        ⟨hx, (fgsa_store_durable p c E rho (Nat.le_add_left ix iy) x).1 hBstore⟩ hl
    · have hhighK : high p w K := by
        rw [high_def, hhK]
        rw [high_def] at hhB
        exact hhB.trans (Nat.le_of_not_lt hl)
      have hcompat := hBK K r hK hhighK
      change (Block.preceq (eraseFG B) (eraseFG K) ||
        Block.preceq (eraseFG K) (eraseFG B)) = true at hcompat
      have hFK : FGBlock.Preceq (storeAt p c E rho iy y).fg.F K := by
        have hp := (fgCertificateLaws p).height.entry_preceq K
        rwa [hKF] at hp
      rcases Bool.or_eq_true_iff.mp hcompat with h | h
      · exact (KitFG.preceq_total_of_common hFK (written_lift p h)).resolve_right hnF
      · exact KitFG.preceq_trans hFK (written_lift p h)
  have hgst := postReset_written_sync p c E rho hrec h0r hx hix hCB hmem
  have hres' := (gateResultAt_eq_gateResult p c E rho hs hix).symm.trans hres
  have hmaj := healing_slow_majority E rho hs hix hres' hBC
  have hhor := (hs.in_horizon _ (List.mem_of_getElem? hix)).2
  obtain ⟨-, o, -, ho, -, hsup⟩ := healing_slow_honest_seat E rho hrec hgst.le hhor hx hix
    ((healing_raw_service_scope_recovery E rho hrec mono).late s ix x
      (postReset_written_window p c E rho hrec h0r hx hix hCB hmem) hx hix
      (healing_gate_enabled_of_result E rho hs hix hres))
    (healing_gate_enabled_of_result E rho hs hix hres) hmaj
  obtain ⟨K, hKt, hKm, hstamp, -, -, -⟩ := healing_support_clean_target E rho o ho
  have hBKt : Block.Preceq (eraseFG B) K := by
    have hlookup : Gen.AC.Root.resolvedTarget?
        (actView (clockPre p (storeAt p c E rho ix x)
          (SA.gateTime p.toParams s))).blocks o = some K :=
      actView_target_of_resolvedHead p _
        (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho ix x) _) o hKt
    rw [Gen.AC.Root.voteSupports_def, hlookup] at hsup
    exact (Bool.and_eq_true_iff.mp hsup).2
  have hvh := (hs.in_horizon _ (List.mem_of_getElem? hiy)).2
  have hvu : SA.voteTime p.toParams s + E.Δ ≤ SA.voteTime p.toParams (s + 1) := by
    rw [hrec.base.delta]
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith [p.deltaPos]
  have hSync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _
    hrec.sync (fgsaDelay_nonrow E.Δ _) hgst.le hvu hvh
  have hFK : Block.Preceq (eraseFG (FGSA.clock p (storeAt p c E rho iy y)
      (SA.voteTime p.toParams (s + 1))).fg.F) K := by
    rw [clock_fg]
    exact Gen.Pure.block_preceq_trans (eraseFG_preceq hFB) hBKt
  have service := healing_first_target_receipt_recovery E rho hrec mono hgst.le hx hy hiy
    hKm hstamp (by simpa only [clock_fg] using hFK)
  have hb := fgsa_target_receipt_on E rho hs hrec.base.receiptIdealization K
    (SA.freezeTime p.toParams s) y hy service
  obtain ⟨Y, hY, heY⟩ := ((storeBundle_stateBeforeTime E rho _ y).cstore.baseTree _).mp hb
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs] at hY
  let X := (storeAt p c E rho (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s)) y).fg.TF
  have hBX : B ∈ X := by
    obtain ⟨A, hA, heA⟩ := (cstoreInv_stateBefore E rho _ y).fg.closed |>
      fun hc => eraseFG_ancestor_mem hc hY (heY ▸ hBKt)
    exact (eraseFG_injective heA) ▸ hA
  have hcut : V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s) ≤ iy :=
    healing_support_idxBefore_le p c E rho hs hiy (by
      change 4 * p.Δ * (s : Int) + 3 * p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
      push_cast
      linarith [p.deltaPos])
  have hX : X ⊆ (storeAt p c E rho iy y).fg.TF :=
    (fgsa_store_durable p c E rho hcut y).1
  have hcover : ∀ K r, SourceBefore p c E rho iy K r →
      FGBlock.Preceq (storeAt p c E rho iy y).fg.F K → FGBlock.Preceq B K →
      (heightView p B).h < (heightView p K).h →
      K ∈ X ∨ FGBlock.Preceq K (storeAt p c E rho iy y).fg.F := by
    intro K r hK hFK _hBK _hhK
    exact Or.inl (healing_source_receipt p c E rho hrec
      (healing_loss_service_scope_recovery E rho hrec mono source emittedNonempty emittedName)
      emittedNonempty emittedName hK
      (Nat.le_of_succ_le (written_source_label p c E rho hrec hiy hK)) hgst.le hy hiy
      (healing_recovery_joined E rho hrec hy
        ((postReset_written_window p c E rho hrec h0r hx hix hCB hmem).cut_mono (Nat.le_succ s)).2
        (by apply hgst.le.trans
            change 4 * p.Δ * (s : Int) + p.Δ ≤
              4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
            push_cast; linarith [p.deltaPos])
        (hs.in_horizon _ (List.mem_of_getElem? hiy)).2) hFK)
  have hhigh := hinv.high_compatible
  rw [PostResetHighCompatible_def] at hhigh
  rcases healing_descent (hroots := hrec.base.idealization) p c E rho xing origin hy hX hBX hcover
    with
    hk | ⟨K, r, hK, hn, hhK⟩ | ⟨K, K', r, r', hK, hK', heh, hlt, hr⟩
  · exact (hk.resolve_left hnZ).resolve_right hnF
  · exact False.elim (hn (hBK K r hK (by
      rw [high_def] at hhB ⊢
      exact hhB.trans hhK)))
  · have hhK : high p w K := by
      rw [high_def] at hhB ⊢
      exact hhB.trans (Nat.le_of_lt hlt)
    have hhK' : high p w K' := by rw [high_def] at hhK ⊢; rwa [← heh]
    exact False.elim (healing_entry_pair_incompatible p heh hr
      (hhigh K K' r r' (written_source_mono p c E rho hK hyi)
        (written_source_mono p c E rho hK' hyi) hhK hhK'))


omit source emittedNonempty emittedName writes xing origin in
private theorem written_slow_boundary
    {ix : Nat} {x : V} {s : Slot} {B : FGBlock (Fin p.n)}
    (hx : x ∈ rho.honest) (hCB : Block.Preceq w.CStar (eraseFG B))
    (hel : GridCO.slowEligible p.toParams.engine
      (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s
      (eraseFG B) = true) : E.t_GST < SA.voteTime p.toParams (s + 1 - p.k) := by
  unfold GridCO.slowEligible at hel
  obtain ⟨hkw, hall⟩ := Bool.and_eq_true_iff.mp hel
  have hm : p.toParams.engine.m = p.k := rfl
  rw [hm] at hkw hall
  have hk : p.k ≤ s + 1 := of_decide_eq_true hkw
  have key0 : ∀ a k : Nat, 2 ≤ k → k ≤ a + 1 → a + 1 - k + 1 ≤ a := by
    intro a k h1 h2
    omega
  have hw := key0 s p.k p.kLarge hk
  have key1 : ∀ a b k : Nat, a + 1 - k ≤ b → b + 1 ≤ a → a - b - 1 < k - 1 := by
    intro a b k h1 h2
    omega
  have hj := key1 s (s + 1 - p.k) p.k le_rfl hw
  have h := List.all_eq_true.mp hall _ (List.mem_range.mpr hj)
  have key2 : ∀ a b : Nat, b + 1 ≤ a → a - (a - b - 1 + 1) = b := by
    intro a b h
    omega
  have he := key2 s (s + 1 - p.k) hw
  rw [he] at h
  have hsave : GridCO.savedGenuine
      (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s)))
      (s + 1 - p.k) = GridCO.savedGenuine (storeAt p c E rho ix x).base (s + 1 - p.k) :=
    savedGenuine_congr (clockPre_genuine p _ _) _
  rw [hsave] at h
  cases hsg : GridCO.savedGenuine (storeAt p c E rho ix x).base (s + 1 - p.k) with
  | none => rw [hsg] at h; cases h
  | some r =>
    cases r with
    | none => rw [hsg] at h; cases h
    | some C =>
      rw [hsg] at h
      exact postReset_slow_window_sync p c E rho hrec
        (healing_raw_service_scope_recovery E rho hrec mono) h0r hx hsg hCB h

omit mono source emittedNonempty emittedName writes xing origin h0r in
private theorem written_frozen_geometry
    {iy : Nat} {y : V} {s : Slot}
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hEpoch : V2.D.restartFree rho y
      (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s)) iy) :
    let X := (storeAt p c E rho
      (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s)) y).fg.TF.filter
        (fun A => FGBlock.Preceq (storeAt p c E rho iy y).fg.F A)
    X ⊆ voterBlocks p (FGSA.clock p (storeAt p c E rho iy y)
      (SA.voteTime p.toParams (s + 1))) (s + 1) ∧
    ∀ W ∈ X, ∀ A, FGBlock.Preceq (storeAt p c E rho iy y).fg.F A →
      FGBlock.Preceq A W → A ∈ X := by
  intro X
  have hs := hrec.base.valid.toScheduleWellFormed
  have hread : postClock E rho y (SA.voteTime p.toParams (s + 1)) =
      some ((fgsa p c).clock (V2.D.Run.stateBefore E rho iy y)
        (SA.voteTime p.toParams (s + 1))) := by
    rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hs hiy]
    rfl
  have hdpos : 0 < SA.freezeTime p.toParams s := by
    change 0 < 4 * p.Δ * (s : Int) + 3 * p.Δ
    have hd := p.deltaPos
    positivity
  have hdvote : SA.freezeTime p.toParams s ≤ SA.voteTime p.toParams (s + 1) := by
    change 4 * p.Δ * (s : Int) + 3 * p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith [p.deltaPos]
  constructor
  · intro W hW
    obtain ⟨hW, hFW⟩ := Finset.mem_filter.mp hW
    exact healing_frozen_path_on p c E rho hs hdpos hdvote
      (by rw [Nat.add_sub_cancel]) hW hread
      (fun j hj => (fgsa_tick_unique E rho hs hj hiy).symm ▸ hEpoch) W
      (by change FGBlock.Preceq (FGSA.clock p _ _).fg.F W; rw [clock_fg]; exact hFW)
      (KitFG.preceq_refl W)
  intro W hW A hFA hAW
  obtain ⟨hW, -⟩ := Finset.mem_filter.mp hW
  obtain ⟨A', hA', heA'⟩ := eraseFG_ancestor_mem
    (cstoreInv_stateBefore E rho _ y).fg.closed hW (eraseFG_preceq hAW)
  exact Finset.mem_filter.mpr ⟨(eraseFG_injective heA') ▸ hA', hFA⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.15:2902–2914, H.1:663–708; plan J4-A3;
B1/B13/B17/B18. DC: SAME first common HEAD for an actual written prefix.
A2 supplies the frozen domain; root and finality coverage are direct.
The actual key supplies the fast or slow arm. J5-A's exact named
postReset_slow_window_sync supplies synchrony at the first saved label.
The first HEAD precedes its write by time, hence by event index. -/
theorem postReset_written_first_head
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    {ix : Nat} {x : V} {s : Slot} {C : Block} {B : FGBlock (Fin p.n)} {g : Nat}
    (hx : x ∈ rho.honest) (hix : IsGateTick p c rho ix x s) (hxi : ix ≤ i)
    (hres : gateResultAt p c E rho ix = some (some C))
    (hCB : Block.Preceq w.CStar (eraseFG B))
    (hkey : (eraseFG B, g) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
        p.toParams.engine p.n
      (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s C)
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1)))) :
    Block.Preceq (eraseFG B) (headAtIdx p c E rho iy (s + 1)) := by
  by_cases hZ : FGBlock.Preceq B (R_at p c E rho iy y).Z
  · exact healing_head_covers_root p c E rho hiy (l := s + 1) (Nat.succ_ne_zero s) (Or.inl hZ)
  by_cases hF : FGBlock.Preceq B (storeAt p c E rho iy y).fg.F
  · exact healing_head_covers_root p c E rho hiy (l := s + 1) (Nat.succ_ne_zero s) (Or.inr hF)
  have hyx : iy < ix := healing_idx_lt_of_time_lt p c E rho
    hrec.base.valid.toScheduleWellFormed hiy hix (by
      change SA.voteTime p.toParams (s + 1) < SA.gateTime p.toParams s
      change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ
      push_cast
      linarith [p.deltaPos])
  obtain ⟨hmem, -, hBC, -, hcase⟩ := healing_support_key_cases p hkey
  have hD := postReset_written_domain p c E rho hrec mono source emittedNonempty emittedName
    writes xing origin h0r hinv hx hix hres hCB hmem hBC hy hiy
    (hyx.le.trans hxi) hZ hF
  have hgst := postReset_written_sync p c E rho hrec h0r hx hix hCB hmem
  have harm : SA.releaseThreshold p.toParams ≤ SA.Root.prefixSupport p.toParams
      (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s
      (eraseFG B) ∨
    (E.t_GST ≤ SA.voteTime p.toParams (s + 1 - p.k) ∧
      GridCO.slowEligible p.toParams.engine
        (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s
        (eraseFG B) = true) := hcase.imp_right (fun hel =>
    ⟨(written_slow_boundary p c E rho hrec mono h0r hx hCB hel).le, hel⟩)
  obtain ⟨hXv, hXc⟩ := written_frozen_geometry p c E rho hrec hiy
    (healing_recovery_epoch_after_vote E rho hrec hy hgst.le (by
      change 4 * p.Δ * (s : Int) + p.Δ < 4 * p.Δ * (s : Int) + 3 * p.Δ
      linarith [p.deltaPos]) _)
  exact healing_first_transfer_written p c E rho hrec mono writes hx hix hres hBC
    hgst.le (postReset_written_window p c E rho hrec h0r hx hix hCB hmem) harm hy hiy
    (healing_gate_enabled_of_result E rho hrec.base.valid.toScheduleWellFormed hix hres)
    (healing_recovery_joined E rho hrec hy
      ((postReset_written_window p c E rho hrec h0r hx hix hCB hmem).cut_mono (Nat.le_succ s)).2
      (by apply hgst.le.trans
          change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
          push_cast; linarith [p.deltaPos])
      (hrec.base.valid.in_horizon _ (List.mem_of_getElem? hiy)).2) hXv hXc (by
      dsimp only [D_at] at hD ⊢
      simpa only [healing_domain_filter_F] using hD)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.15 S1:2902–2914; plan J4-A3; B1/B13/B17/B18.
DC: SAME complete first-HEAD clause, expressed through headAtLabel.
No bounded induction range or first-proposal input is used. -/
theorem postReset_written_first_head_label
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    {ix : Nat} {x : V} {s : Slot} {C : Block} {B : FGBlock (Fin p.n)} {g : Nat}
    (hx : x ∈ rho.honest) (hix : IsGateTick p c rho ix x s) (hxi : ix ≤ i)
    (hres : gateResultAt p c E rho ix = some (some C))
    (hCB : Block.Preceq w.CStar (eraseFG B))
    (hkey : (eraseFG B, g) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
        p.toParams.engine p.n
      (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s C)
    {y : V} {H : Block} (hy : y ∈ rho.honest)
    (hhead : headAtLabel p c E rho y (s + 1) = some H) : Block.Preceq (eraseFG B) H := by
  delta headAtLabel at hhead
  rw [postClock_def, preTick_def] at hhead
  cases ht : V2.D.Run.tickIdx? rho y (SA.voteTime p.toParams (s + 1)) with
  | none => rw [ht] at hhead; cases hhead
  | some iy =>
    rw [ht] at hhead
    have hiy := V2.D.Run.tickIdx?_spec ht
    have hH : H = headAtIdx p c E rho iy (s + 1) := by
      rw [healing_headAtIdx_tick p c E rho hiy]
      exact (Option.some.inj hhead).symm
    rw [hH]
    exact postReset_written_first_head p c E rho hrec mono source emittedNonempty emittedName
      writes xing origin h0r hinv hx hix hxi hres hCB hkey hy hiy


/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.15 S1:2887–2914; plan J4-A5, new-write HEAD clause;
B1/B13/B17/B18. DC: SAME event-index cut. For every i : Nat, the only
label at or above s + 1 whose actual HEAD cut can be complete at i + 1
is s + 1. Later actual ticks contradict the cut. No induction or bound
by the run length is needed. This is the new-write case, not a successor
producer for old writes. -/
theorem postReset_written_heads_at_write_cut
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    {x : V} {s : Slot} {C : Block} {B : FGBlock (Fin p.n)} {g : Nat}
    (hx : x ∈ rho.honest) (hi : IsGateTick p c rho i x s)
    (hres : gateResultAt p c E rho i = some (some C))
    (hCB : Block.Preceq w.CStar (eraseFG B))
    (hkey : (eraseFG B, g) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
        p.toParams.engine p.n
      (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))) s C) :
    ∀ y j H, y ∈ rho.honest → s + 1 ≤ j →
      timeIdx rho (SA.voteTime p.toParams j) ≤ i + 1 →
      headAtLabel p c E rho y j = some H → Block.Preceq (eraseFG B) H := by
  intro y j H hy hsj hcut hhead
  rcases Nat.eq_or_lt_of_le hsj with rfl | hj
  · exact postReset_written_first_head_label p c E rho hrec mono source emittedNonempty emittedName
      writes xing origin h0r hinv hx hi le_rfl
      hres hCB hkey hy hhead
  · delta headAtLabel at hhead
    rw [postClock_def, preTick_def] at hhead
    cases ht : V2.D.Run.tickIdx? rho y (SA.voteTime p.toParams j) with
    | none => rw [ht] at hhead; cases hhead
    | some iy =>
      have hiy := V2.D.Run.tickIdx?_spec ht
      have hiycut : iy < timeIdx rho (SA.voteTime p.toParams j) :=
        (V2.D.Engine.index_lt_read_length_iff hrec.base.valid.toScheduleWellFormed _ hiy).mpr le_rfl
      have hil : i < iy := healing_idx_lt_of_time_lt p c E rho
        hrec.base.valid.toScheduleWellFormed hi hiy (by
          change SA.gateTime p.toParams s < SA.voteTime p.toParams j
          have hjs : (s : Int) + 2 ≤ j := by exact_mod_cast (show s + 2 ≤ j from hj)
          change 4 * p.Δ * (s : Int) + 6 * p.Δ < 4 * p.Δ * (j : Int) + p.Δ
          nlinarith [p.deltaPos])
      omega


omit mono source emittedNonempty emittedName writes xing origin h0r in
private theorem written_head_label {a : Nat} {z : V} {j : Slot}
    (ha : rho.events[a]? = some (.tick z (SA.voteTime p.toParams j))) :
    headAtLabel p c E rho z j = some (headAtIdx p c E rho a j) := by
  delta headAtLabel
  rw [postClock_def, preTick_def,
    fgsa_tickIdx_of_event p c E rho hrec.base.valid.toScheduleWellFormed ha]
  rw [healing_headAtIdx_tick p c E rho ha]
  rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.15:2916–2923, H.2:720–733; plan J4-A4, later result boundary;
B1/B13/B17/B18. DC: SAME finality coverage or a covering-batch confirmation.
The old write's S1 field at i covers the complete label-j batch before
this gate. Earlier sources use no-loss; a same-label emitted source uses
its genuine result's own honest supporter. No field at i + 1 is read. -/
theorem postReset_written_later_result
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    {k : Nat} (hki : k < i) {x : V} {s : Slot} {C : Block}
    {B : FGBlock (Fin p.n)} {g : Nat}
    (hx : x ∈ rho.honest) (hk : IsGateTick p c rho k x s)
    (hpass : gatePassedAt p c E rho k)
    (hres : gateResultAt p c E rho k = some (some C))
    (hCB : Block.Preceq w.CStar (eraseFG B)) (hne : eraseFG B ≠ w.CStar)
    (hkey : (eraseFG B, g) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
        p.toParams.engine p.n
      (actView (clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams s))) s C)
    {y : V} {j : Slot} {D : Block} (hy : y ∈ rho.honest) (hsj : s + 1 ≤ j)
    (hi : IsGateTick p c rho i y j)
    (hresult : gateResultAt p c E rho i = some (some D)) :
    Block.Preceq (eraseFG B) D ∨ Block.Preceq (eraseFG B) (F_at p c E rho i y) := by
  have hs := hrec.base.valid.toScheduleWellFormed
  obtain ⟨hmem, hgen, hBC, -, -⟩ := healing_support_key_cases p hkey
  have hadm : g ∈ @GridCO.admissionLevels GridCO.slowLeasePolicy p.toParams.engine p.n .root
      (actView (clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams s))) s (eraseFG B) := by
    have hkey' := hkey
    rw [@GridCO.gateWriteKeys_def GridCO.slowLeasePolicy] at hkey'
    obtain ⟨b, -, hbg⟩ := List.mem_flatMap.mp hkey'
    obtain ⟨g', hga, he⟩ := List.mem_map.mp hbg
    obtain ⟨heb, heg⟩ := Prod.mk.inj he
    simpa only [heb, heg] using hga
  have hsafe := hinv.lease_safe
  rw [PostResetLeaseSafe_def] at hsafe
  have hheads := (hsafe k hki x s (eraseFG B) g C hx hk hpass hres hCB hne
    hmem hgen hBC hadm).2.1
  have hcut : timeIdx rho (SA.voteTime p.toParams j) ≤ i := by
    by_contra hn
    have ht := (V2.D.Engine.index_lt_read_length_iff hs _ hi).mp (Nat.lt_of_not_ge hn)
    change SA.gateTime p.toParams j ≤ SA.voteTime p.toParams j at ht
    change 4 * p.Δ * (j : Int) + 6 * p.Δ ≤ 4 * p.Δ * (j : Int) + p.Δ at ht
    linarith [p.deltaPos]
  have hcov : ∀ z ∈ rho.honest, ∀ H, headAtLabel p c E rho z j = some H →
      Block.Preceq (eraseFG B) H := fun z hz H hh => hheads z j H hz hsj hcut hh
  have hgsts := postReset_written_sync p c E rho hrec h0r hx hk hCB hmem
  have hgst : E.t_GST ≤ SA.voteTime p.toParams j := by
    refine hgsts.le.trans ?_
    have hsj' : (s : Int) ≤ j := by exact_mod_cast (Nat.le_of_succ_le hsj)
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (j : Int) + p.Δ
    nlinarith [p.deltaPos]
  have noLoss := (healing_high_source_compat p c E rho hrec
    (healing_loss_service_scope_recovery E rho hrec mono source emittedNonempty emittedName)
    mono emittedNonempty
    emittedName writes xing origin).1
  obtain ⟨a, z, hz, ha, -, -⟩ :=
    healing_gate_result_supporter p c E rho hrec
      (healing_raw_service_scope_recovery E rho hrec mono) hgst
      ((postReset_written_window p c E rho hrec h0r hx hk hCB hmem).cut_mono
        (Nat.le_of_succ_le hsj)).2 hy hi hresult
  have hBH := hcov z hz _ (written_head_label p c E rho hrec ha)
  have hBK : ∀ K r, SourceBefore p c E rho i K r → high p w K →
      Block.Compatible (eraseFG B) (eraseFG K) := by
    intro K r hK hhK
    have hrj := (healing_source_read p c E rho hs hK hi).2.2 rfl
    rcases Nat.eq_or_lt_of_le hrj with he | hr
    · obtain ⟨b, zK, q, row, -, hrow, hsrc, hlabel⟩ := hK
      have hq : q * p.R = j := hlabel.symm.trans he
      obtain ⟨-, CK, -, hG, hKCK, st, hst, -⟩ :=
        healing_source_decode p c E rho emittedNonempty emittedName hrow hsrc
      rw [hq] at hG hst
      rw [gateIn_def, preTick_def] at hst
      cases hidx : V2.D.Run.tickIdx? rho zK (SA.gateTime p.toParams j) with
      | none => rw [hidx] at hst; cases hst
      | some ik =>
        have hik := V2.D.Run.tickIdx?_spec hidx
        have hraw := (gateResultAt_eq_gateResult p c E rho hs hik).trans hG
        obtain ⟨aK, zH, hzH, haK, hCKH, -⟩ :=
          healing_gate_result_supporter p c E rho hrec
            (healing_raw_service_scope_recovery E rho hrec mono) hgst
            ((postReset_written_window p c E rho hrec h0r hx hk hCB hmem).cut_mono
              (Nat.le_of_succ_le hsj)).2 hrow.1 hik hraw
        exact Gen.Pure.block_compatible_of_common
          (hcov zH hzH _ (written_head_label p c E rho hrec haK))
          (Gen.Pure.block_preceq_trans hKCK hCKH)
    · have hKn : HighSrcN p c E rho K r := by
        rw [HighSrcN_def]
        rw [high_def] at hhK
        exact ⟨healing_srcN_of_source p c E rho hK,
          (Nat.succ_le_succ h0r.mu_le).trans hhK⟩
      have hKH : Block.Preceq (eraseFG K) (headAtIdx p c E rho a j) := by
        by_contra hn
        apply noLoss a K r
        rw [Lost_def]
        exact ⟨hKn, z, j, hz, hr, ha, hn⟩
      exact Gen.Pure.block_compatible_of_common hBH hKH
  by_cases hBF : FGBlock.Preceq B (storeAt p c E rho i y).fg.F
  · right
    exact eraseFG_preceq hBF
  have hBstore := written_stored p c E rho hmem
  obtain ⟨-, -, -, Cfg, -, -, -, heC, hhC⟩ := h0r.fresh
  have hCBfg : FGBlock.Preceq Cfg B := written_lift p (by rwa [heC])
  have hhB : high p w B := by
    rw [high_def]
    exact hhC ▸ (fgCertificateLaws p).height.h_mono hCBfg
  have hFB : FGBlock.Preceq (storeAt p c E rho i y).fg.F B := by
    by_cases hFg : (storeAt p c E rho i y).fg.F = .genesis
    · rw [hFg]; exact KitFG.genesis_preceq B
    obtain ⟨DF, hDF, heF, K, r, hK, hhK, hKF, -⟩ :=
      healing_finality_source (hroots := hrec.base.idealization) p c E rho hs origin hy hFg
    by_cases hl : (finalityView p DF).h_F < (heightView p B).h
    · exact xing i (i + k) y x DF B hy (Nat.le_add_right i k) hDF heF
        ⟨hx, (fgsa_store_durable p c E rho
          (Nat.le_add_left k i) x).1 hBstore⟩ hl
    · have hhighK : high p w K := by
        rw [high_def, hhK]
        rw [high_def] at hhB
        exact hhB.trans (Nat.le_of_not_lt hl)
      have hcompat := hBK K r hK hhighK
      change (Block.preceq (eraseFG B) (eraseFG K) ||
        Block.preceq (eraseFG K) (eraseFG B)) = true at hcompat
      have hFK : FGBlock.Preceq (storeAt p c E rho i y).fg.F K := by
        have hp := (fgCertificateLaws p).height.entry_preceq K
        rwa [hKF] at hp
      rcases Bool.or_eq_true_iff.mp hcompat with h | h
      · exact (KitFG.preceq_total_of_common hFK (written_lift p h)).resolve_right hBF
      · exact KitFG.preceq_trans hFK (written_lift p h)
  have hhor := (hs.in_horizon _ (List.mem_of_getElem? hi)).2
  obtain ⟨D', hconf, hBD⟩ := healing_support_gate_cover E rho hrec hgst hhor hcov hi
    (healing_support_gate_scope_recovery E rho hrec mono
      ((postReset_written_window p c E rho hrec h0r hx hk hCB hmem).cut_mono
        (Nat.le_of_succ_le hsj)) hy
      (healing_gate_enabled_of_result E rho hs hi hresult)
      (healing_support_gate_geometry E rho hs hcov (by
        rw [clockPre_fg]; exact eraseFG_preceq hFB))) (by
    rw [clockPre_fg]
    exact eraseFG_preceq hFB)
  have hst : gateIn p c E rho y j =
      some (clockPre p (storeAt p c E rho i y) (SA.gateTime p.toParams j)) := by
    rw [gateIn_def, preTick_def, fgsa_tickIdx_of_event p c E rho hs hi]
    rfl
  have hG := (gateResultAt_eq_gateResult p c E rho hs hi).symm.trans hresult
  have hG' := (fgsa_gate_raw_of_nonempty p c E rho hs hi hG).2
  have heD : D' = D := Option.some.inj (hconf.symm.trans hG')
  exact Or.inl (heD ▸ hBD)


omit hrec mono source emittedNonempty emittedName writes xing origin h0r in
omit [Fintype V] in
private theorem written_key_of_guards {k : Nat} {x : V} {s : Slot} {B C : Block} {g : Nat}
    (hmem : B ∈ (actView (clockPre p (storeAt p c E rho k x)
      (SA.gateTime p.toParams s))).blocks) (hgen : B ≠ .genesis) (hBC : Block.Preceq B C)
    (hg : g ∈ @GridCO.admissionLevels GridCO.slowLeasePolicy p.toParams.engine p.n .root
        (actView (clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams s))) s B) :
    (B, g) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
      (actView (clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams s))) s C := by
  rw [@GridCO.gateWriteKeys_def GridCO.slowLeasePolicy]
  apply List.mem_flatMap.mpr
  refine ⟨B, List.mem_filter.mpr ⟨hmem, ?_⟩, List.mem_map.mpr ⟨g, hg, rfl⟩⟩
  simp only [Bool.and_eq_true, bne_iff_ne]
  exact ⟨hgen, hBC⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.15:2887–2892, 2916–2923; plan J4-A4, result clause at i + 1;
B1/B13/B17/B18. DC: SAME event-prefix result extension for every i : Nat.
Old writes use the prior result clause or the new gate boundary lemma.
A new write cannot have a later-label gate before this cut. This is the
full later-result clause; HEAD, proposal and output successors are separate. -/
theorem postReset_leaseSafe_results_succ {i : Nat} (hinv : PostResetInv p c E rho w i) :
    ∀ k, k < i + 1 → ∀ x s B g C, x ∈ rho.honest → IsGateTick p c rho k x s →
    gatePassedAt p c E rho k → gateResultAt p c E rho k = some (some C) →
    Block.Preceq w.CStar B → B ≠ w.CStar →
    let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams s)
    B ∈ (actView pre).blocks → B ≠ .genesis → Block.Preceq B C →
    g ∈ @GridCO.admissionLevels GridCO.slowLeasePolicy p.toParams.engine p.n .root (actView pre)
        s B →
    ∀ l, l < i + 1 → ∀ y j D, y ∈ rho.honest → s + 1 ≤ j →
      IsGateTick p c rho l y j → gateResultAt p c E rho l = some (some D) →
      Block.Preceq B D ∨ Block.Preceq B (F_at p c E rho l y) := by
  intro k hk x s B g C hx ht hp hr hCB hne pre hmem hgen hBC hg l hl y j D hy hsj hgate hresult
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hki | rfl
  · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hl) with hli | rfl
    · have hsafe := hinv.lease_safe
      rw [PostResetLeaseSafe_def] at hsafe
      exact (hsafe k hki x s B g C hx ht hp hr hCB hne hmem hgen hBC hg).1
        l hli y j D hy hsj hgate hresult
    · have hkey := written_key_of_guards p c E rho hmem hgen hBC hg
      have hb := (actView_blocks _ _).mp hmem |>.1
      rw [(clockPre_fields p _ _).2.1] at hb
      obtain ⟨Bfg, -, he⟩ := (cstoreInv_stateBefore E rho k x).baseTree B |>.mp hb
      have hresult' := postReset_written_later_result p c E rho hrec mono source emittedNonempty
        emittedName writes xing origin h0r hinv hki hx ht hp hr
        (B := Bfg) (by rwa [he]) (by rwa [he]) (by rwa [he]) hy hsj hgate hresult
      simpa only [he] using hresult'
  · have hkl : k < l := healing_idx_lt_of_time_lt p c E rho
      hrec.base.valid.toScheduleWellFormed ht hgate (by
        change SA.gateTime p.toParams s < SA.gateTime p.toParams j
        have hsj' : (s : Int) + 1 ≤ j := by exact_mod_cast hsj
        change 4 * p.Δ * (s : Int) + 6 * p.Δ < 4 * p.Δ * (j : Int) + 6 * p.Δ
        nlinarith [p.deltaPos])
    omega


/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.15:2916–2923, H.2:723–746; plan J4A2-3 G1;
B1/B13/B17/B18. DC: SAME last-write route at a moving reader.
The reader index iy is explicitly at most the prior cut i. The written
prefix has no emitted-source premise. Older writes use the first release
or the synchronous slow window; later writes use the prior RESULT clause.
No reset-release cut or successor reset-lease field is needed. -/
theorem postReset_moving_lease_compat
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    {ix : Nat} {x : V} {s : Slot} {C : Block} {B : FGBlock (Fin p.n)} {g : Nat}
    (hx : x ∈ rho.honest) (hix : IsGateTick p c rho ix x s) (hxi : ix ≤ i)
    (hpass : gatePassedAt p c E rho ix)
    (hres : gateResultAt p c E rho ix = some (some C))
    (hCB : Block.Preceq w.CStar (eraseFG B)) (hne : eraseFG B ≠ w.CStar)
    (hkey : (eraseFG B, g) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
        p.toParams.engine p.n
      (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s C)
    {l : Slot} (hsl : s + 1 ≤ l)
    (hbatch : ∀ z ∈ rho.honest, ∀ H, headAtLabel p c E rho z l = some H →
      Block.Preceq (eraseFG B) H)
    {iy : Nat} {y : V} {t : Time} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y t)) (hyi : iy ≤ i)
    (hafter : SA.freezeTime p.toParams l < t)
    (hupper : t ≤ SA.voteTime p.toParams (l + 1)) :
    ∀ row ∈ (FGSA.clock p (storeAt p c E rho iy y) t).base.obligations,
      Block.Compatible row.1 (eraseFG B) := by
  classical
  have hs := hrec.base.valid.toScheduleWellFormed
  have hhor := (hs.in_horizon _ (List.mem_of_getElem? hiy)).2
  obtain ⟨hmem, hgen, hBC, -, harm⟩ := healing_support_key_cases p hkey
  have hgsts := postReset_written_sync p c E rho hrec h0r hx hix hCB hmem
  have hgstl : E.t_GST ≤ SA.voteTime p.toParams l := by
    refine hgsts.le.trans ?_
    have h : (s : Int) ≤ l := by exact_mod_cast (Nat.le_of_succ_le hsl)
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (l : Int) + p.Δ
    nlinarith [p.deltaPos]
  have hst : SA.gateTime p.toParams s < t := by
    have h : (s : Int) + 1 ≤ l := by exact_mod_cast hsl
    change 4 * p.Δ * (s : Int) + 6 * p.Δ < t
    change 4 * p.Δ * (l : Int) + 3 * p.Δ < t at hafter
    nlinarith [p.deltaPos]
  have hxiy := healing_idx_lt_of_time_lt p c E rho hs hix hiy hst
  have hxcut : ix < i := lt_of_le_of_ne hxi (by omega)
  have hraw := (gateResultAt_eq_gateResult p c E rho hs hix).symm.trans hres
  have hgate := (healing_support_gate_reads p c E rho hs hix).1
  have hconf : SA.Root.confirmationFrom p.toParams
      (eraseFG (storeAt p c E rho ix x).fg.F)
      (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s = some C := by
    simpa only [clockPre_fg, storeAt] using
      (fgsa_gate_raw_of_nonempty p c E rho hs hix hraw).2
  have hadm : g ∈ @GridCO.admissionLevels GridCO.slowLeasePolicy p.toParams.engine p.n .root
      (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s
      (eraseFG B) := by
    have hk := hkey
    rw [@GridCO.gateWriteKeys_def GridCO.slowLeasePolicy] at hk
    obtain ⟨b, -, hm⟩ := List.mem_flatMap.mp hk
    obtain ⟨a, ha, he⟩ := List.mem_map.mp hm
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact ha
  have hsafe := hinv.lease_safe
  rw [PostResetLeaseSafe_def] at hsafe
  have hwritten := hsafe ix hxcut x s (eraseFG B) g C hx hix hpass hres hCB hne
    hmem hgen hBC hadm
  have hcov : ∀ q, s + 1 ≤ q → SA.gateTime p.toParams q ≤ t →
      ∀ z ∈ rho.honest, ∀ H, headAtLabel p c E rho z q = some H →
      Block.Preceq (eraseFG B) H := by
    intro q hsq hqt z hz H hH
    have hcut : timeIdx rho (SA.voteTime p.toParams q) ≤ iy := by
      by_contra hn
      have ht := (V2.D.Engine.index_lt_read_length_iff hs _ hiy).mp (Nat.lt_of_not_ge hn)
      change t ≤ 4 * p.Δ * (q : Int) + p.Δ at ht
      change 4 * p.Δ * (q : Int) + 6 * p.Δ ≤ t at hqt
      linarith [p.deltaPos]
    exact hwritten.2.1 z q H hz hsq (hcut.trans hyi) hH
  by_cases hBF : FGBlock.Preceq B (storeAt p c E rho iy y).fg.F
  · intro row hr
    have hc := (cstoreInv_clock p _ (cstoreInv_stateBefore E rho iy y) t).saCompat.1 row hr
    rw [clock_fg] at hc
    rcases Bool.or_eq_true_iff.mp hc with h | h
    · exact Gen.Pure.block_compatible_of_common h (eraseFG_preceq hBF)
    · exact Bool.or_eq_true_iff.mpr (Or.inr
        (Gen.Pure.block_preceq_trans (eraseFG_preceq hBF) h))
  have hFB : FGBlock.Preceq (storeAt p c E rho iy y).fg.F B := by
    by_cases hBZ : FGBlock.Preceq B (R_at p c E rho iy y).Z
    · have hFZ : FGBlock.Preceq (storeAt p c E rho iy y).fg.F
          (R_at p c E rho iy y).Z := by
        change FGBlock.Preceq (storeAt p c E rho iy y).fg.F
          (KitFG.treeStoreControlsView (heightView p) (storeAt p c E rho iy y).fg).Z
        unfold Controls.Z
        split
        · exact (cstoreInv_stateBefore E rho iy y).fg.FJ
        · exact KitFG.preceq_refl _
      exact (KitFG.preceq_total_of_common hFZ hBZ).resolve_right hBF
    have hc := healing_support_idxBefore_le p c E rho hs hiy hafter.le
    have hfrozen := (fgsa_store_durable p c E rho hc y).1
    have hD := postReset_moving_domain p c E rho hrec mono source emittedNonempty emittedName
      writes xing origin h0r hinv hgstl hCB hbatch hy hiy hyi hafter hupper le_rfl hfrozen hBZ hBF
    exact (KitFG.mem_filteredFromView (heightView p) (R_at p c E rho iy y) _ B).mp hD |>.2.1
  have hqt : SA.voteTime p.toParams (s + 1) < t := by
    have h : (s : Int) + 1 ≤ l := by exact_mod_cast hsl
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ < t
    push_cast
    change 4 * p.Δ * (l : Int) + 3 * p.Δ < t at hafter
    nlinarith [p.deltaPos]
  have hawake := hrec.awake y hy _ (by
    apply hgsts.le.trans
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast; linarith [p.deltaPos]) (hqt.le.trans hhor)
  obtain ⟨iq, hiq⟩ := healing_support_vote_tick E rho hs hrec.base.delta hy (s + 1)
    (hqt.le.trans hhor) hawake
  have hqa := healing_idx_lt_of_time_lt p c E rho hs hiq hiy hqt
  have hT : ∀ j u, j < iy → rho.events[j]? = some (.tick y u) → u ≤ t := by
    intro j u hj ht
    exact (fgsa_tick_time_strict E rho hs ht hiy hj).le
  have hnongate : ∀ q : Slot, t ≠ SA.gateTime p.toParams q := by
    intro q he
    rw [he] at hafter hupper
    change 4 * p.Δ * (l : Int) + 3 * p.Δ <
      4 * p.Δ * (q : Int) + 6 * p.Δ at hafter
    change 4 * p.Δ * (q : Int) + 6 * p.Δ ≤
      4 * p.Δ * ((l + 1 : Nat) : Int) + p.Δ at hupper
    push_cast at hupper
    have hq : (q : Int) ≤ l := by nlinarith [p.deltaPos]
    have hl : (l : Int) ≤ q := by
      by_contra hn
      have h : (q : Int) + 1 ≤ l := by omega
      nlinarith [p.deltaPos]
    nlinarith [p.deltaPos]
  intro row hr
  have hrow := healing_lease_clock_nongate _ _ hnongate row hr
  obtain ⟨j, hji, q, D, ht, -, hD, hrowD, -, -, -, -⟩ := writes iy y row hrow
  by_cases hsq : s < q
  · have hBD := hwritten.1 j (hji.trans_le hyi) y q D hy hsq ht hD
    have hFD : Block.Preceq (F_at p c E rho j y) D := by
      have hg := (healing_support_gate_reads p c E rho hs ht).1
      have hd := (gateResultAt_eq_gateResult p c E rho hs ht).symm.trans hD
      have hd' : SA.Root.confirmationFrom p.toParams (eraseFG (storeAt p c E rho j y).fg.F)
          (actView (clockPre p (storeAt p c E rho j y) (SA.gateTime p.toParams q))) q = some D := by
        simpa only [clockPre_fg, storeAt] using
          (fgsa_gate_raw_of_nonempty p c E rho hs ht hd).2
      unfold SA.Root.confirmationFrom GridCO.confirmationFrom at hd'
      dsimp only at hd'
      split at hd'
      · cases hd'
        exact written_walk_extends _ _ _ _
      · contradiction
    have hBD' := hBD.elim id (fun h => Gen.Pure.block_preceq_trans h hFD)
    exact Gen.Pure.block_compatible_of_common hrowD hBD'
  rcases harm with hfast | hslow
  · obtain ⟨-, hclock⟩ := healing_support_gate_reads p c E rho hs hix
    let nd := (fgsa p c).clock (V2.D.Run.stateBefore E rho ix x) (SA.gateTime p.toParams s)
    have hfastWrite : eraseFG B ∈ (fastWriteAt nd.st s).getD [] := by
      have hgr := (gateResultAt_eq_gateResult p c E rho hs hix).symm.trans hres
      have hjoined := (fgsa_gate_raw_of_nonempty p c E rho hs hix hgr).1
      rw [healing_support_fastWrite p c E rho hs hix hjoined]
      unfold fastSet
      rw [hconf]
      obtain ⟨x', s', hx', hsaved, R, hR, hguard⟩ := hpass
      have hev : V2.Event.tick x' (SA.gateTime p.toParams s') =
          V2.Event.tick x (SA.gateTime p.toParams s) := Option.some.inj (hx'.1.symm.trans hix)
      have he : x' = x ∧ s' = s := by
        have hv := V2.Event.tick.inj hev
        refine ⟨hv.1, ?_⟩
        have htime := hv.2
        change 4 * p.Δ * (s' : Int) + 6 * p.Δ =
          4 * p.Δ * (s : Int) + 6 * p.Δ at htime
        have h : (s' : Int) = s := by nlinarith [p.deltaPos]
        exact_mod_cast h
      obtain ⟨rfl, rfl⟩ := he
      rw [clockPre_fg, hconf] at hR
      cases hR
      simp only [hguard, Bool.false_eq_true, ite_false]
      change Block.preceq (eraseFG B) C = true at hBC
      exact List.mem_filter.mpr ⟨hmem, by simp [hgen, hBC, hfast]⟩
    exact healing_fast_lease_at E rho hrec mono writes hgsts.le (hst.le.trans hhor) hx
      hclock hfastWrite hhor
      (healing_fast_support_scope_recovery E rho hrec mono
        (postReset_written_window p c E rho hrec h0r hx hix hCB hmem) hx)
      (healing_gate_cut_of_batch_cut E s
        (postReset_written_window p c E rho hrec h0r hx hix hCB hmem).2)
      hcov hy hiq hqa hT (eraseFG_preceq hFB) row hrow
  · have hwindow := written_slow_boundary p c E rho hrec mono h0r hx hCB hslow
    exact healing_slow_lease_at E rho hrec mono writes hgsts.le (hst.le.trans hhor) hx
      hwindow.le hgate hraw hBC hslow hhor
      (healing_slow_support_scope_recovery E rho hrec mono
        (postReset_written_window p c E rho hrec h0r hx hix hCB hmem) hwindow.le hx)
      hcov hy hiq hqa hT
      (eraseFG_preceq hFB) row hrow

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.15:2916–2923, H.2:723–726; plan J4A2-3 G3;
B1/B13/B17/B18. DC: SAME one continuation step from the prior batch.
The complete preceding batch, G2 domain and G1 leases supply H.2.
The reader cut iy ≤ i is explicit, including the event at iy = i. -/
theorem postReset_written_next_head
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    {ix : Nat} {x : V} {s : Slot} {C : Block} {B : FGBlock (Fin p.n)} {g : Nat}
    (hx : x ∈ rho.honest) (hix : IsGateTick p c rho ix x s) (hxi : ix ≤ i)
    (hpass : gatePassedAt p c E rho ix)
    (hres : gateResultAt p c E rho ix = some (some C))
    (hCB : Block.Preceq w.CStar (eraseFG B)) (hne : eraseFG B ≠ w.CStar)
    (hkey : (eraseFG B, g) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
        p.toParams.engine p.n
      (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s C)
    {l : Slot} (hsl : s + 1 ≤ l)
    (hbatch : ∀ z ∈ rho.honest, ∀ H, headAtLabel p c E rho z l = some H →
      Block.Preceq (eraseFG B) H)
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (l + 1))))
    (hyi : iy ≤ i) :
    Block.Preceq (eraseFG B) (headAtIdx p c E rho iy (l + 1)) := by
  by_cases hZ : FGBlock.Preceq B (R_at p c E rho iy y).Z
  · exact healing_head_covers_root p c E rho hiy (l := l + 1) (Nat.succ_ne_zero l) (Or.inl hZ)
  by_cases hF : FGBlock.Preceq B (storeAt p c E rho iy y).fg.F
  · exact healing_head_covers_root p c E rho hiy (l := l + 1) (Nat.succ_ne_zero l) (Or.inr hF)
  obtain ⟨hmem, -, -, -, -⟩ := healing_support_key_cases p hkey
  have hgsts := postReset_written_sync p c E rho hrec h0r hx hix hCB hmem
  have hgst : E.t_GST ≤ SA.voteTime p.toParams l := by
    refine hgsts.le.trans ?_
    have h : (s : Int) ≤ l := by exact_mod_cast (Nat.le_of_succ_le hsl)
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (l : Int) + p.Δ
    nlinarith [p.deltaPos]
  have hafter : SA.freezeTime p.toParams l < SA.voteTime p.toParams (l + 1) := by
    change 4 * p.Δ * (l : Int) + 3 * p.Δ < 4 * p.Δ * ((l + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith [p.deltaPos]
  have hcut := healing_support_idxBefore_le p c E rho
    hrec.base.valid.toScheduleWellFormed hiy hafter.le
  have hX := (fgsa_store_durable p c E rho hcut y).1
  have hD := postReset_moving_domain p c E rho hrec mono source emittedNonempty emittedName
    writes xing origin h0r hinv hgst hCB hbatch hy hiy hyi hafter le_rfl hX le_rfl hZ hF
  have hlease := postReset_moving_lease_compat p c E rho hrec mono source emittedNonempty
    emittedName
    writes xing origin h0r hinv hx hix hxi hpass hres hCB hne hkey hsl
    hbatch hy hiy hyi hafter le_rfl
  obtain ⟨hXv, hXc⟩ := written_frozen_geometry p c E rho hrec hiy
    (healing_recovery_epoch_after_vote E rho hrec hy hgst (by
      change 4 * p.Δ * (l : Int) + p.Δ < 4 * p.Δ * (l : Int) + 3 * p.Δ
      linarith [p.deltaPos]) _)
  have hCut := (postReset_written_window p c E rho hrec h0r hx hix hCB hmem).cut_mono
    (Nat.le_of_succ_le hsl)
  have hJ := healing_recovery_joined E rho hrec hy (hCut.cut_mono (Nat.le_succ l)).2
    (by apply hgst.trans
        change 4 * p.Δ * (l : Int) + p.Δ ≤ 4 * p.Δ * ((l + 1 : Nat) : Int) + p.Δ
        push_cast; linarith [p.deltaPos])
    (hrec.base.valid.in_horizon _ (List.mem_of_getElem? hiy)).2
  exact healing_next_transfer_domain p c E rho hrec mono hgst hbatch hy hiy
    (healing_next_transfer_scope_recovery E rho hrec hCut hy hiy hJ) hCut hXv hXc (by
      dsimp only [D_at] at hD ⊢
      simpa only [healing_domain_filter_F] using hD) hlease

omit [Fintype V] hrec mono source emittedNonempty emittedName writes xing origin h0r in
private theorem written_proposal_read
    {s : Slot} {Q : Block}
    (hp : HonestProposal E rho (fgsaInterface p c) s Q) :
    ∃ j, rho.events[j]? = some (.tick (V2.D.proposerOf rho (fgsaInterface p c) s)
        (SA.proposalTime p.toParams s)) ∧
      Q.parent = proposerHead p (FGSA.clock p
        (storeAt p c E rho j (V2.D.proposerOf rho (fgsaInterface p c) s))
        (SA.proposalTime p.toParams s)) s := by
  obtain ⟨_, o, ⟨j, hj, hem⟩, hb⟩ := hp
  rw [proposalTime_fgsa p c s] at hj
  refine ⟨j, hj, ?_⟩
  obtain ⟨auth, m⟩ := o
  cases m with
  | head _ => cases hb
  | row _ => cases hb
  | proposal N =>
    have he : N.erase = Q := Option.some.inj hb
    subst Q
    rw [(V2.D.Run.step_tick_eq E rho hj).2] at hem
    change (⟨auth, .proposal N⟩ : Obj p) ∈
      (if E.awake _ (SA.proposalTime p.toParams s) then
        (duties p (SA.proposalTime p.toParams s)).flatMap (fun d =>
          (rho.ownSeats (RunDuty.signLabel d) _).filterMap (fun i =>
            (act p c ((fgsa p c).clock _ _) d (rho.input _ _)).map
              (fun m => (⟨.seat (RunDuty.signLabel d) i, m⟩ : Obj p)))) ++
                ([] : List (Obj p)) else []) at hem
    split at hem
    · rw [List.append_nil] at hem
      obtain ⟨d, hd, hem⟩ := List.mem_flatMap.mp hem
      obtain ⟨i, _, hm⟩ := List.mem_filterMap.mp hem
      obtain ⟨m, hm, ho⟩ := Option.map_eq_some_iff.mp hm
      have he : m = .proposal N := congrArg V2.Signed.payload ho
      subst m
      cases d with
      | headAction _ =>
        change (if joinedNow p _ then some (Msg.head _) else none) = some (.proposal N) at hm
        split_ifs at hm; cases hm
      | fgAction _ =>
        change (attest p _ _ _).1.map Msg.row = some (.proposal N) at hm
        obtain ⟨_, _, he⟩ := Option.map_eq_some_iff.mp hm
        cases he
      | propAction s' =>
        have ht := (duties_spec p _ _).mp hd
        have hss : s' = s := by
          change 4 * p.Δ * (s' : Int) = 4 * p.Δ * (s : Int) at ht
          have hΔ := p.deltaPos
          have he : (s' : Int) = s := by nlinarith
          exact_mod_cast he
        subst s'
        change (if joinedNow p _ then (propose p _ s).map (withApp p _) else none) =
          some (.proposal N) at hm
        split_ifs at hm
        exact (fgsa_walkRun_proposal_parent p _ s _ N hm).2.2
    · exact (List.not_mem_nil hem).elim


/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.15:2916–2923, H.2:736–746; plan J4A2-3 G4;
B1/B13/B17/B18. DC: SAME proposal continuation at the complete cut.
J5-A supplies the exact named moving-parent wrapper. G2 and G1 supply
its domain and lease guards. Root and finality coverage are direct. -/
theorem postReset_written_moving_parent
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    {ix : Nat} {x : V} {s : Slot} {C : Block} {B : FGBlock (Fin p.n)} {g : Nat}
    (hx : x ∈ rho.honest) (hix : IsGateTick p c rho ix x s) (hxi : ix ≤ i)
    (hpass : gatePassedAt p c E rho ix)
    (hres : gateResultAt p c E rho ix = some (some C))
    (hCB : Block.Preceq w.CStar (eraseFG B)) (hne : eraseFG B ≠ w.CStar)
    (hkey : (eraseFG B, g) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
        p.toParams.engine p.n
      (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s C)
    {l : Slot} (hsl : s + 1 ≤ l)
    (hbatch : ∀ z ∈ rho.honest, ∀ H, headAtLabel p c E rho z l = some H →
      Block.Preceq (eraseFG B) H)
    {Q : Block} (hp : HonestProposal E rho (fgsaInterface p c) (l + 1) Q)
    (hcut : timeIdx rho (SA.proposalTime p.toParams (l + 1)) ≤ i + 1) :
    Block.Preceq (eraseFG B) Q.parent := by
  classical
  have hs := hrec.base.valid.toScheduleWellFormed
  obtain ⟨ip, hip, hpar⟩ := written_proposal_read p c E rho hp
  have hpi : ip ≤ i := by
    have hlt := (V2.D.Engine.index_lt_read_length_iff hs _ hip).mpr le_rfl
    change ip < timeIdx rho (SA.proposalTime p.toParams (l + 1)) at hlt
    omega
  let y := V2.D.proposerOf rho (fgsaInterface p c) (l + 1)
  have hy : y ∈ rho.honest := hp.1.2
  let st := FGSA.clock p (storeAt p c E rho ip y) (SA.proposalTime p.toParams (l + 1))
  have hin : CStoreInv p st := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ip y) _
  have hfg : st.fg = (storeAt p c E rho ip y).fg := clock_fg p _ _
  have hR : FGSA.controls p st = R_at p c E rho ip y := by
    change KitFG.treeStoreControlsView (heightView p) st.fg =
      KitFG.treeStoreControlsView (heightView p) (storeAt p c E rho ip y).fg
    rw [hfg]
  by_cases hZ : FGBlock.Preceq B (R_at p c E rho ip y).Z
  · rw [hpar]
    have hBZ := eraseFG_preceq (hR ▸ hZ)
    exact Gen.Pure.block_preceq_trans hBZ (Gen.Pure.block_preceq_trans
      (fgsa_Z_preceq_liveRoot p st)
      (liveRoot_preceq_headInTree p st _ _ _))
  by_cases hF : FGBlock.Preceq B (storeAt p c E rho ip y).fg.F
  · rw [hpar]
    exact preceq_getHead_of_preceq_F p st hin (eraseFG_preceq (hfg ▸ hF)) _ _
  obtain ⟨hmem, -, -, -, -⟩ := healing_support_key_cases p hkey
  have hgsts := postReset_written_sync p c E rho hrec h0r hx hix hCB hmem
  have hgst : E.t_GST ≤ SA.voteTime p.toParams l := by
    refine hgsts.le.trans ?_
    have h : (s : Int) ≤ l := by exact_mod_cast (Nat.le_of_succ_le hsl)
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (l : Int) + p.Δ
    nlinarith [p.deltaPos]
  have hafter : SA.freezeTime p.toParams l < SA.proposalTime p.toParams (l + 1) := by
    change 4 * p.Δ * (l : Int) + 3 * p.Δ < 4 * p.Δ * ((l + 1 : Nat) : Int)
    push_cast
    linarith [p.deltaPos]
  have hupper : SA.proposalTime p.toParams (l + 1) ≤ SA.voteTime p.toParams (l + 1) := by
    change 4 * p.Δ * ((l + 1 : Nat) : Int) ≤ 4 * p.Δ * ((l + 1 : Nat) : Int) + p.Δ
    linarith [p.deltaPos]
  have hfroz := healing_support_idxBefore_le p c E rho hs hip hafter.le
  have hX := (fgsa_store_durable p c E rho hfroz y).1
  have hD := postReset_moving_domain p c E rho hrec mono source emittedNonempty emittedName writes
    xing origin h0r hinv hgst hCB hbatch hy hip hpi hafter hupper le_rfl hX hZ hF
  apply healing_proposal_moving_parent p c E rho hrec
    (healing_raw_service_scope_recovery E rho hrec mono) mono hgst
    ((postReset_written_window p c E rho hrec h0r hx hix hCB hmem).cut_mono
      (Nat.le_of_succ_le hsl)).2 hbatch hp
  · intro j hj
    have he : j = ip := fgsa_tick_unique E rho hs hj hip
    subst j
    refine ⟨(storeAt p c E rho ip y).fg.TF, le_rfl, ?_, hD⟩
    intro W hW A hAW
    obtain ⟨A', hA', heA⟩ := eraseFG_ancestor_mem hin.fg.closed
      (hfg.symm ▸ hW) (eraseFG_preceq hAW)
    exact hfg ▸ ((eraseFG_injective heA) ▸ hA')
  · intro j hj
    have he : j = ip := fgsa_tick_unique E rho hs hj hip
    subst j
    exact postReset_moving_lease_compat p c E rho hrec mono source emittedNonempty emittedName
      writes xing origin h0r hinv hx hix hxi hpass hres hCB hne hkey hsl
      hbatch hy hip hpi hafter hupper

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.15:2916–2923, H.2:723–726; plan J4A2-3 G6 HEAD;
B1/B13/B17/B18. DC: SAME inclusive cut at i + 1, for every i : Nat.
Old complete reads use the prior field. A new boundary read uses G3.
New writes use the proved first-HEAD clause at their write cut. -/
theorem postReset_written_heads_succ
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    {ix : Nat} {x : V} {s : Slot} {C : Block} {B : FGBlock (Fin p.n)} {g : Nat}
    (hx : x ∈ rho.honest) (hix : IsGateTick p c rho ix x s) (hxi : ix ≤ i)
    (hpass : gatePassedAt p c E rho ix)
    (hres : gateResultAt p c E rho ix = some (some C))
    (hCB : Block.Preceq w.CStar (eraseFG B)) (hne : eraseFG B ≠ w.CStar)
    (hkey : (eraseFG B, g) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
        p.toParams.engine p.n
      (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s C)
 :
    ∀ y j H, y ∈ rho.honest → s + 1 ≤ j →
      timeIdx rho (SA.voteTime p.toParams j) ≤ i + 1 →
      headAtLabel p c E rho y j = some H → Block.Preceq (eraseFG B) H := by
  rcases Nat.lt_or_eq_of_le hxi with hxi | rfl
  · obtain ⟨hmem, hgen, hBC, -, -⟩ := healing_support_key_cases p hkey
    have hadm : g ∈ @GridCO.admissionLevels GridCO.slowLeasePolicy p.toParams.engine p.n .root
        (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s
        (eraseFG B) := by
      have hk := hkey
      rw [@GridCO.gateWriteKeys_def GridCO.slowLeasePolicy] at hk
      obtain ⟨b, -, hm⟩ := List.mem_flatMap.mp hk
      obtain ⟨a, ha, he⟩ := List.mem_map.mp hm
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact ha
    have hsafe := hinv.lease_safe
    rw [PostResetLeaseSafe_def] at hsafe
    have hheads := (hsafe ix hxi x s (eraseFG B) g C hx hix hpass hres hCB hne
      hmem hgen hBC hadm).2.1
    intro y j H hy hsj hcut hhead
    by_cases hci : timeIdx rho (SA.voteTime p.toParams j) ≤ i
    · exact hheads y j H hy hsj hci hhead
    rcases Nat.eq_or_lt_of_le hsj with rfl | hsj
    · exact postReset_written_first_head_label p c E rho hrec mono source emittedNonempty
        emittedName
        writes xing origin h0r hinv hx hix hxi.le
        hres hCB hkey hy hhead
    obtain ⟨l, rfl⟩ : ∃ l : Slot, j = l + 1 := ⟨j - 1, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
    have hsl : s + 1 ≤ l := Nat.le_of_lt_succ hsj
    delta headAtLabel at hhead
    rw [postClock_def, preTick_def] at hhead
    cases ht : V2.D.Run.tickIdx? rho y (SA.voteTime p.toParams (l + 1)) with
    | none => rw [ht] at hhead; cases hhead
    | some iy =>
      have hiy := V2.D.Run.tickIdx?_spec ht
      have hiyle : iy ≤ i := by
        have hh := (V2.D.Engine.index_lt_read_length_iff
          hrec.base.valid.toScheduleWellFormed _ hiy).mpr le_rfl
        change iy < timeIdx rho (SA.voteTime p.toParams (l + 1)) at hh
        omega
      have hafter : SA.freezeTime p.toParams l < SA.voteTime p.toParams (l + 1) := by
        change 4 * p.Δ * (l : Int) + 3 * p.Δ < 4 * p.Δ * ((l + 1 : Nat) : Int) + p.Δ
        push_cast
        linarith [p.deltaPos]
      have hbcut := postReset_moving_head_cut p c E rho
        hrec.base.valid.toScheduleWellFormed hiy hafter
      have hbatch := fun z hz K hK => hheads z l K hz hsl (hbcut.trans hiyle) hK
      have hH := postReset_written_next_head p c E rho hrec mono source emittedNonempty emittedName
        writes xing origin h0r hinv hx hix hxi.le hpass hres hCB hne hkey
        hsl hbatch hy hiy hiyle
      rw [ht] at hhead
      have he : H = headAtIdx p c E rho iy (l + 1) := by
        rw [healing_headAtIdx_tick p c E rho hiy]
        exact (Option.some.inj hhead).symm
      exact he ▸ hH
  · exact postReset_written_heads_at_write_cut p c E rho hrec mono source emittedNonempty
      emittedName
      writes xing origin h0r hinv hx hix hres hCB hkey

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.15:2916–2923, H.2:736–746; plan J4A2-3 G6 proposal;
B1/B13/B17/B18. DC: SAME complete proposal cut at i + 1.
The preceding HEAD batch is complete at i. G4 supplies the parent.
A new write cannot precede a proposal with this completed cut. -/
theorem postReset_written_proposals_succ
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    {ix : Nat} {x : V} {s : Slot} {C : Block} {B : FGBlock (Fin p.n)} {g : Nat}
    (hx : x ∈ rho.honest) (hix : IsGateTick p c rho ix x s) (hxi : ix ≤ i)
    (hpass : gatePassedAt p c E rho ix)
    (hres : gateResultAt p c E rho ix = some (some C))
    (hCB : Block.Preceq w.CStar (eraseFG B)) (hne : eraseFG B ≠ w.CStar)
    (hkey : (eraseFG B, g) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
        p.toParams.engine p.n
      (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s C)
 :
    ∀ v Q, s + 2 ≤ v → timeIdx rho (SA.proposalTime p.toParams v) ≤ i + 1 →
      HonestProposal E rho (fgsaInterface p c) v Q → Block.Preceq (eraseFG B) Q.parent := by
  intro v Q hsv hcut hp
  have hs := hrec.base.valid.toScheduleWellFormed
  obtain ⟨ip, hip, -⟩ := written_proposal_read p c E rho hp
  have hpi : ip ≤ i := by
    have hh := (V2.D.Engine.index_lt_read_length_iff hs _ hip).mpr le_rfl
    change ip < timeIdx rho (SA.proposalTime p.toParams v) at hh
    omega
  have hxp := healing_idx_lt_of_time_lt p c E rho hs hix hip (by
    have hv : (s : Int) + 2 ≤ v := by exact_mod_cast hsv
    change 4 * p.Δ * (s : Int) + 6 * p.Δ < 4 * p.Δ * (v : Int)
    nlinarith [p.deltaPos])
  have hxcut : ix < i := hxp.trans_le hpi
  have hvpos : 0 < v := lt_of_lt_of_le (Nat.zero_lt_succ (s + 1)) hsv
  obtain ⟨l, rfl⟩ : ∃ l : Slot, v = l + 1 := ⟨v - 1, (Nat.succ_pred_eq_of_pos hvpos).symm⟩
  have hsl : s + 1 ≤ l := Nat.le_of_succ_le_succ hsv
  have hafter : SA.freezeTime p.toParams l < SA.proposalTime p.toParams (l + 1) := by
    change 4 * p.Δ * (l : Int) + 3 * p.Δ < 4 * p.Δ * ((l + 1 : Nat) : Int)
    push_cast
    linarith [p.deltaPos]
  have hbcut := postReset_moving_head_cut p c E rho hs hip hafter
  obtain ⟨hmem, hgen, hBC, -, -⟩ := healing_support_key_cases p hkey
  have hadm : g ∈ @GridCO.admissionLevels GridCO.slowLeasePolicy p.toParams.engine p.n .root
      (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s
      (eraseFG B) := by
    have hk := hkey
    rw [@GridCO.gateWriteKeys_def GridCO.slowLeasePolicy] at hk
    obtain ⟨b, -, hm⟩ := List.mem_flatMap.mp hk
    obtain ⟨a, ha, he⟩ := List.mem_map.mp hm
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact ha
  have hsafe := hinv.lease_safe
  rw [PostResetLeaseSafe_def] at hsafe
  have hheads := (hsafe ix hxcut x s (eraseFG B) g C hx hix hpass hres hCB hne
    hmem hgen hBC hadm).2.1
  have hbatch := fun z hz H hH => hheads z l H hz hsl (hbcut.trans hpi) hH
  exact postReset_written_moving_parent p c E rho hrec mono source emittedNonempty
    emittedName writes
    xing origin h0r hinv hx hix hxi hpass
    hres hCB hne hkey hsl hbatch hp hcut

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.15:2919–2923; plan J4A2-3 G5 finality;
B1/B13/B17/B18. DC: SAME provenance and complete honest HEAD history.
A low finality is below B by crossing. A higher source shares an actual
HEAD with B, either at s or at its own first transferred label.
No event witness is needed at the reader b, including the last state. -/
theorem postReset_written_finality_compatible
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    {ix : Nat} {x : V} {s : Slot} {C : Block} {B : FGBlock (Fin p.n)} {g : Nat}
    (hx : x ∈ rho.honest) (hix : IsGateTick p c rho ix x s) (hxi : ix ≤ i)
    (hpass : gatePassedAt p c E rho ix)
    (hres : gateResultAt p c E rho ix = some (some C))
    (hCB : Block.Preceq w.CStar (eraseFG B)) (hne : eraseFG B ≠ w.CStar)
    (hkey : (eraseFG B, g) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
        p.toParams.engine p.n
      (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s C)
    {b : Nat} {y : V} (hbi : b ≤ i) (hy : y ∈ rho.honest) :
    Block.Compatible (F_at p c E rho b y) (eraseFG B) := by
  have hs := hrec.base.valid.toScheduleWellFormed
  obtain ⟨hmem, -, -, -, -⟩ := healing_support_key_cases p hkey
  have hBstore := written_stored p c E rho hmem
  obtain ⟨-, -, -, Cfg, -, -, -, heC, hhC⟩ := h0r.fresh
  have hCBfg : FGBlock.Preceq Cfg B := written_lift p (by rwa [heC])
  have hhB : high p w B := by
    rw [high_def]
    exact hhC ▸ (fgCertificateLaws p).height.h_mono hCBfg
  by_cases hFg : (storeAt p c E rho b y).fg.F = .genesis
  · change Block.Compatible (eraseFG (storeAt p c E rho b y).fg.F) (eraseFG B)
    rw [hFg]
    exact Bool.or_eq_true_iff.mpr (Or.inl (Gen.Pure.block_genesis_preceq _))
  obtain ⟨DF, hDF, heF, K, r, hK, hhK, hKF, -⟩ :=
    healing_finality_source (hroots := hrec.base.idealization) p c E rho hs origin hy hFg
  by_cases hl : (finalityView p DF).h_F < (heightView p B).h
  · have hFB := xing b (b + ix) y x DF B hy (Nat.le_add_right b ix) hDF heF
      ⟨hx, (fgsa_store_durable p c E rho
        (Nat.le_add_left ix b) x).1 hBstore⟩ hl
    exact Bool.or_eq_true_iff.mpr (Or.inl (eraseFG_preceq hFB))
  have hhighK : high p w K := by
    rw [high_def, hhK]
    rw [high_def] at hhB
    exact hhB.trans (Nat.le_of_not_lt hl)
  have hKn : HighSrcN p c E rho K r := by
    rw [HighSrcN_def]
    rw [high_def] at hhighK
    exact ⟨healing_srcN_of_source p c E rho hK,
      (Nat.succ_le_succ h0r.mu_le).trans hhighK⟩
  have noLoss := (healing_high_source_compat p c E rho hrec
    (healing_loss_service_scope_recovery E rho hrec mono source emittedNonempty emittedName)
    mono emittedNonempty
    emittedName writes xing origin).1
  have hheads := postReset_written_heads_succ p c E rho hrec mono source emittedNonempty emittedName
    writes xing origin h0r hinv hx hix hxi hpass hres
    hCB hne hkey
  obtain ⟨a, z, hz, ha, hBH, hrs⟩ : ∃ a z, z ∈ rho.honest ∧
      rho.events[a]? = some (.tick z (SA.voteTime p.toParams (if r < s then s else r + 1))) ∧
      Block.Preceq (eraseFG B)
        (headAtIdx p c E rho a (if r < s then s else r + 1)) ∧
      r + 1 ≤ (if r < s then s else r + 1) := by
    by_cases hr : r < s
    · simp only [hr, ite_true]
      have hgst := postReset_written_sync p c E rho hrec h0r hx hix hCB hmem
      obtain ⟨a, z, hz, ha, hCH, -⟩ :=
        healing_gate_result_supporter p c E rho hrec
          (healing_raw_service_scope_recovery E rho hrec mono) hgst.le
          (postReset_written_window p c E rho hrec h0r hx hix hCB hmem).2 hx hix hres
      exact ⟨a, z, hz, ha, Gen.Pure.block_preceq_trans
        (healing_support_key_cases p hkey).2.2.1 hCH, hr⟩
    · simp only [hr, ite_false]
      obtain ⟨j, z, q, row, hjb, hrow, -, he⟩ := hK
      have hj : rho.events[j]? = some (.tick z (SA.gateTime p.toParams r)) := by
        simpa only [Params.actionTime, ← he] using hrow.2.1
      have htime : SA.voteTime p.toParams (r + 1) < SA.gateTime p.toParams r := by
        change 4 * p.Δ * ((r + 1 : Nat) : Int) + p.Δ < 4 * p.Δ * (r : Int) + 6 * p.Δ
        push_cast
        linarith [p.deltaPos]
      have hcut : timeIdx rho (SA.voteTime p.toParams (r + 1)) ≤ j := by
        by_contra hn
        have ht := (V2.D.Engine.index_lt_read_length_iff hs _ hj).mp (Nat.lt_of_not_ge hn)
        exact (not_lt_of_ge ht) htime
      have hawake := hrec.awake x hx _ (by
        apply (postReset_written_sync p c E rho hrec h0r hx hix hCB hmem).le.trans
        have hh : (s : Int) ≤ r := by exact_mod_cast Nat.le_of_not_lt hr
        change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Int) + p.Δ
        push_cast; nlinarith [p.deltaPos])
        (htime.le.trans ((hs.in_horizon _ (List.mem_of_getElem? hj)).2))
      obtain ⟨a, ha⟩ := healing_support_vote_tick E rho hs hrec.base.delta hx (r + 1)
        (htime.le.trans ((hs.in_horizon _ (List.mem_of_getElem? hj)).2)) hawake
      have hBH := hheads x (r + 1) _ hx (Nat.succ_le_succ (Nat.le_of_not_lt hr))
        (hcut.trans (hjb.le.trans (hbi.trans (Nat.le_succ i))))
        (written_head_label p c E rho hrec ha)
      exact ⟨a, x, hx, ha, hBH, le_rfl⟩
  have hKH : Block.Preceq (eraseFG K)
      (headAtIdx p c E rho a (if r < s then s else r + 1)) := by
    by_contra hn
    apply noLoss a K r
    rw [Lost_def]
    exact ⟨hKn, z, _, hz, hrs, ha, hn⟩
  have hFK : FGBlock.Preceq (storeAt p c E rho b y).fg.F K := by
    have hp := (fgCertificateLaws p).height.entry_preceq K
    rwa [hKF] at hp
  exact Gen.Pure.block_compatible_of_common
    (Gen.Pure.block_preceq_trans (eraseFG_preceq hFK) hKH) hBH

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.15:2916–2923, H.2:729–735; plan J4A2-3 G5 gate lease;
B1/B13/B17/B18. DC: SAME stored lease guard before the first output gate.
The fast release or slow last-write window applies before s + 1.
The finality-prefix input is the output wrapper's exact branch guard. -/
theorem postReset_written_gate_lease_compat
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    {ix : Nat} {x : V} {s : Slot} {C : Block} {B : FGBlock (Fin p.n)} {g : Nat}
    (hx : x ∈ rho.honest) (hix : IsGateTick p c rho ix x s) (hxi : ix ≤ i)
    (hpass : gatePassedAt p c E rho ix)
    (hres : gateResultAt p c E rho ix = some (some C))
    (hCB : Block.Preceq w.CStar (eraseFG B)) (hne : eraseFG B ≠ w.CStar)
    (hkey : (eraseFG B, g) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
        p.toParams.engine p.n
      (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s C)
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : IsGateTick p c rho iy y (s + 1)) (hyi : iy ≤ i)
    (hFB : Block.Preceq (F_at p c E rho iy y) (eraseFG B)) :
    ∀ row ∈ (storeAt p c E rho iy y).base.obligations,
      Block.Compatible row.1 (eraseFG B) := by
  have hs := hrec.base.valid.toScheduleWellFormed
  have hhor := (hs.in_horizon _ (List.mem_of_getElem? hiy)).2
  obtain ⟨hmem, hgen, hBC, -, harm⟩ := healing_support_key_cases p hkey
  have hgsts := postReset_written_sync p c E rho hrec h0r hx hix hCB hmem
  have hst : SA.gateTime p.toParams s ≤ SA.gateTime p.toParams (s + 1) := by
    change 4 * p.Δ * (s : Int) + 6 * p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + 6 * p.Δ
    push_cast
    linarith [p.deltaPos]
  have hraw := (gateResultAt_eq_gateResult p c E rho hs hix).symm.trans hres
  have hgate := (healing_support_gate_reads p c E rho hs hix).1
  have hconf : SA.Root.confirmationFrom p.toParams
      (eraseFG (storeAt p c E rho ix x).fg.F)
      (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s = some C := by
    simpa only [clockPre_fg, storeAt] using
      (fgsa_gate_raw_of_nonempty p c E rho hs hix hraw).2
  have hheads := postReset_written_heads_succ p c E rho hrec mono source emittedNonempty emittedName
    writes xing origin h0r hinv hx hix hxi hpass hres
    hCB hne hkey
  have hcov : ∀ q, s + 1 ≤ q → SA.gateTime p.toParams q ≤ SA.gateTime p.toParams (s + 1) →
      ∀ z ∈ rho.honest, ∀ H, headAtLabel p c E rho z q = some H →
      Block.Preceq (eraseFG B) H := by
    intro q hsq hqt z hz H hH
    have hcut : timeIdx rho (SA.voteTime p.toParams q) ≤ iy := by
      by_contra hn
      have ht := (V2.D.Engine.index_lt_read_length_iff hs _ hiy).mp (Nat.lt_of_not_ge hn)
      change SA.gateTime p.toParams (s + 1) ≤ 4 * p.Δ * (q : Int) + p.Δ at ht
      change 4 * p.Δ * (q : Int) + 6 * p.Δ ≤ SA.gateTime p.toParams (s + 1) at hqt
      linarith [p.deltaPos]
    exact hheads z q H hz hsq (hcut.trans (hyi.trans (Nat.le_succ i))) hH
  have hqt : SA.voteTime p.toParams (s + 1) < SA.gateTime p.toParams (s + 1) := by
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ <
      4 * p.Δ * ((s + 1 : Nat) : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hawake := hrec.awake y hy _ (by
    apply hgsts.le.trans
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast; linarith [p.deltaPos]) (hqt.le.trans hhor)
  obtain ⟨iq, hiq⟩ := healing_support_vote_tick E rho hs hrec.base.delta hy (s + 1)
    (hqt.le.trans hhor) hawake
  have hqa := healing_idx_lt_of_time_lt p c E rho hs hiq hiy hqt
  have hT : ∀ j t, j < iy → rho.events[j]? = some (.tick y t) →
      t ≤ SA.gateTime p.toParams (s + 1) := by
    intro j t hj ht
    exact (fgsa_tick_time_strict E rho hs ht hiy hj).le
  intro row hrow
  rcases harm with hfast | hslow
  · obtain ⟨-, hclock⟩ := healing_support_gate_reads p c E rho hs hix
    let nd := (fgsa p c).clock (V2.D.Run.stateBefore E rho ix x) (SA.gateTime p.toParams s)
    have hfastWrite : eraseFG B ∈ (fastWriteAt nd.st s).getD [] := by
      have hgr := (gateResultAt_eq_gateResult p c E rho hs hix).symm.trans hres
      have hjoined := (fgsa_gate_raw_of_nonempty p c E rho hs hix hgr).1
      rw [healing_support_fastWrite p c E rho hs hix hjoined]
      unfold fastSet
      rw [hconf]
      obtain ⟨x', s', hx', hsaved, R, hR, hguard⟩ := hpass
      have hev : V2.Event.tick x' (SA.gateTime p.toParams s') =
          V2.Event.tick x (SA.gateTime p.toParams s) := Option.some.inj (hx'.1.symm.trans hix)
      have he : x' = x ∧ s' = s := by
        have hv := V2.Event.tick.inj hev
        refine ⟨hv.1, ?_⟩
        have htime := hv.2
        change 4 * p.Δ * (s' : Int) + 6 * p.Δ =
          4 * p.Δ * (s : Int) + 6 * p.Δ at htime
        have h : (s' : Int) = s := by nlinarith [p.deltaPos]
        exact_mod_cast h
      obtain ⟨rfl, rfl⟩ := he
      rw [clockPre_fg, hconf] at hR
      cases hR
      simp only [hguard, Bool.false_eq_true, ite_false]
      change Block.preceq (eraseFG B) C = true at hBC
      exact List.mem_filter.mpr ⟨hmem, by simp [hgen, hBC, hfast]⟩
    exact healing_fast_lease_at E rho hrec mono writes hgsts.le (hst.trans hhor) hx
      hclock hfastWrite hhor
      (healing_fast_support_scope_recovery E rho hrec mono
        (postReset_written_window p c E rho hrec h0r hx hix hCB hmem) hx)
      (healing_gate_cut_of_batch_cut E s
        (postReset_written_window p c E rho hrec h0r hx hix hCB hmem).2)
      hcov hy hiq hqa hT hFB row hrow
  · have hwindow := written_slow_boundary p c E rho hrec mono h0r hx hCB hslow
    exact healing_slow_lease_at E rho hrec mono writes hgsts.le (hst.trans hhor) hx
      hwindow.le hgate hraw hBC hslow hhor
      (healing_slow_support_scope_recovery E rho hrec mono
        (postReset_written_window p c E rho hrec h0r hx hix hCB hmem) hwindow.le hx)
      hcov hy hiq hqa hT
      hFB row hrow


/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.15:2916–2923, H.2:729–735; plan J4A2-3 G5/S3;
B1/B13/B17/B18. DC: SAME pre-event output suffix through cut i.
J5-A supplies the exact named suffix wrapper. The complete HEAD history,
finality provenance and first output gate leases are proved guards.
The output reader a = i includes i = rho.events.length. -/
theorem postReset_written_outputs_succ
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    {ix : Nat} {x : V} {s : Slot} {C : Block} {B : FGBlock (Fin p.n)} {g : Nat}
    (hx : x ∈ rho.honest) (hix : IsGateTick p c rho ix x s) (hxi : ix ≤ i)
    (hpass : gatePassedAt p c E rho ix)
    (hres : gateResultAt p c E rho ix = some (some C))
    (hCB : Block.Preceq w.CStar (eraseFG B)) (hne : eraseFG B ≠ w.CStar)
    (hkey : (eraseFG B, g) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
        p.toParams.engine p.n
      (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s C)
    (hguard : SA.gateTime p.toParams s + 4 * p.Δ ≤ rho.horizon) :
    ∀ a y, y ∈ rho.honest → a ≤ i →
      HealSuffix p c rho (SA.gateTime p.toParams s + 4 * p.Δ) a →
      Block.Preceq (eraseFG B) (S_at p c E rho a y) := by
  obtain ⟨hmem, -, -, -, -⟩ := healing_support_key_cases p hkey
  have hgst := postReset_written_sync p c E rho hrec h0r hx hix hCB hmem
  have hheads := postReset_written_heads_succ p c E rho hrec mono source emittedNonempty emittedName
    writes xing origin h0r hinv hx hix hxi hpass hres
    hCB hne hkey
  have batches : ∀ l, s + 1 ≤ l → timeIdx rho (SA.voteTime p.toParams l) ≤ i →
      SA.voteTime p.toParams l ≤ rho.horizon →
      Gen.Pure.Batch (joinedHonest p E rho (SA.voteTime p.toParams l)).card
        (Gen.V2.Duty.faulty rho).card := by
    intro l hsl _hcut hhor
    have hCut := (postReset_written_window p c E rho hrec h0r hx hix hCB hmem).cut_mono
      (Nat.le_of_succ_le hsl)
    exact (healing_recovery_joined_counts E rho hrec l hCut.2 hCut.sync hhor).2
  apply healing_output_moving_suffix_at p c E rho hrec
    (healing_raw_service_scope_recovery E rho hrec mono) mono hgst.le batches hguard
  · intro l hsl hcut z hz H hH
    exact hheads z l H hz hsl (hcut.trans (Nat.le_succ i)) hH
  · intro b hbi y hy _hstart
    exact postReset_written_finality_compatible p c E rho hrec mono source emittedNonempty
      emittedName
      writes xing origin h0r hinv hx hix hxi hpass hres
      hCB hne hkey hbi hy
  · intro j y hy hj hji hFB
    exact postReset_written_gate_lease_compat p c E rho hrec mono source emittedNonempty emittedName
      writes xing origin h0r hinv hx hix hxi hpass hres
      hCB hne hkey hy hj hji hFB

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.15:2885–2923, H.2:709–746; plan J4A2-3 G7;
B1/B13/B17/B18. DC: SAME frozen PostResetLeaseStep for every i : Nat.
The antecedents are exactly the prior triple and RL at i + 1.
The proof uses only hinv from that triple; the remaining fields are unused.
Results, HEADs, proposals and outputs retain their complete frozen cuts. -/
theorem postReset_leaseSafe_succ : ∀ i, PostResetLeaseStep p c E rho w i := by
  intro i
  rw [PostResetLeaseStep_def]
  intro hprev _hresetNext
  have hinv := hprev.1
  rw [PostResetLeaseSafe_def]
  intro k hk x s B g C hx ht hp hr hCB hne pre hmem hgen hBC hg
  have hkey := written_key_of_guards p c E rho hmem hgen hBC hg
  have hb := (actView_blocks _ _).mp hmem |>.1
  rw [(clockPre_fields p _ _).2.1] at hb
  obtain ⟨Bfg, -, he⟩ := (cstoreInv_stateBefore E rho k x).baseTree B |>.mp hb
  have hki := Nat.le_of_lt_succ hk
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact postReset_leaseSafe_results_succ p c E rho hrec mono source emittedNonempty emittedName
      writes xing origin h0r hinv k hk x s B g C hx ht hp hr
      hCB hne hmem hgen hBC hg
  · have h := postReset_written_heads_succ p c E rho hrec mono source emittedNonempty emittedName
      writes xing origin h0r hinv hx ht hki hp hr
      (B := Bfg) (by rwa [he]) (by rwa [he]) (by rwa [he])
    simpa only [he] using h
  · have h := postReset_written_proposals_succ p c E rho hrec mono source emittedNonempty
      emittedName
      writes xing origin h0r
      hinv hx ht hki hp hr (B := Bfg) (by rwa [he]) (by rwa [he]) (by rwa [he])
    simpa only [he] using h
  · intro j y hj hy hguard hsuffix
    have h := postReset_written_outputs_succ p c E rho hrec mono source emittedNonempty emittedName
      writes xing origin h0r
      hinv hx ht hki hp hr (B := Bfg) (by rwa [he]) (by rwa [he]) (by rwa [he]) hguard
      j y hy (Nat.le_of_lt_succ hj) hsuffix
    simpa only [he] using h

end WrittenDomain

end AvailableChain.FGSA.Run
end

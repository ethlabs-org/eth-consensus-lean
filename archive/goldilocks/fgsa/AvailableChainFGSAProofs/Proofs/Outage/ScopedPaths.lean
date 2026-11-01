module
public import AvailableChainFGSAProofs.Proofs.Outage.ScopedRoots

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG AvailableChain.KitFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- The actual source gate precedes the previous early boundary. -/
theorem outage_source_gate_before_early (p : Params) (s q : Slot)
    (h : SA.gateTime p.toParams q ≤ SA.voteTime p.toParams (s + 1)) :
    SA.gateTime p.toParams q ≤ SA.earlyTime p.toParams s := by
  rw [arming_gate_eq, arming_vote_eq] at h
  rw [arming_gate_eq, arming_early_eq]
  push_cast at h
  have hd := p.deltaPos
  have hqs : q < s := by
    by_contra hn
    have hsq : (s : Int) ≤ (q : Int) := by exact_mod_cast (Nat.le_of_not_gt hn)
    nlinarith
  have hcast : (q : Int) + 1 ≤ (s : Int) := by exact_mod_cast (Nat.succ_le_of_lt hqs)
  nlinarith

theorem outage_source_held_at_action (hsch : V2.D.ScheduleWellFormed E rho)
    {k : Nat} {y : V} {r : Nat} {C : FGBlock (Fin p.n)}
    (hk : rho.events[k]? = some (.tick y (p.actionTime r)))
    (hC : actionSourceFG p c E rho y r = some (some C)) :
    C ∈ (storeAt p c E rho k y).fg.TF := by
  rw [actionSourceFG_def, postClock_def, preTick_def] at hC
  cases hl : V2.D.Run.tickIdx? rho y (p.actionTime r) with
  | none => simp only [hl, Option.map_none] at hC; contradiction
  | some l =>
    have he := fgsa_tick_unique E rho hsch (V2.D.Run.tickIdx?_spec hl) hk
    subst l
    simp only [hl, Option.map_some, Option.some.injEq] at hC
    have hm := (Finset.mem_filter.mp (pickPair_some_spec _ _ hC).1).1
    have ht := (KitFG.mem_filteredFromView _ _ _ _).mp hm |>.1
    change C ∈ (clock p (storeAt p c E rho k y) (p.actionTime r)).fg.TF at ht
    rw [clock_fg] at ht
    exact ht

/-- OUTPUT-DIRECT §3. DC: INTENTIONAL; crossing a held carrier gives an
original honest source of the exact crossed height. Its action precedes the
inclusive previous early boundary, and its full body was held at that action. -/
theorem outage_crossing_source_at_read (hsch : V2.D.ScheduleWellFormed E rho)
    (origin : RQCOrigin p c E rho) {i : Nat} {x : V} {s m : Nat}
    {W B : FGBlock (Fin p.n)} (hx : x ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams (s + 1))))
    (hW : W ∈ (storeAt p c E rho i x).fg.TF)
    (hm : 1 ≤ m) (hmW : m < (heightView p W).h)
    (hist : OutageSourceHistory p c E rho (eraseFG B) i) :
    ∃ k, k < i ∧ ∃ y r, ∃ (wire : RowWire p.n) (C : FGBlock (Fin p.n)),
      HonestRowAt p c E rho k y r wire ∧
      actionSourceFG p c E rho y r = some (some C) ∧
      (heightView p C).h = m ∧ Block.Compatible (eraseFG C) (eraseFG B) ∧
      C ∈ (storeAt p c E rho k y).fg.TF ∧
      p.actionTime r ≤ SA.earlyTime p.toParams s := by
  classical
  obtain ⟨Y, hYW, hYm, Q, hQ, hrows⟩ :=
    (fgCertificateLaws p).height.height_crossing W m hm hmW
  let rows : Fin p.n → FGBlock (Fin p.n) × Row (Fin p.n) := fun k =>
    if hk : k ∈ Q then
      (Classical.choose (hrows k hk), Classical.choose (Classical.choose_spec (hrows k hk)))
    else (.genesis, ⟨k, .empty, none⟩)
  have hr : ∀ k ∈ Q, FGBlock.Preceq (rows k).1 W ∧
      (rows k).2 ∈ (rows k).1.rows ∧ (rows k).2.signer = k ∧
      (rows k).2.height_pair.matchesEntry m Y.root = true := fun k hk => by
    simpa only [rows, hk, ↓reduceDIte] using
      Classical.choose_spec (Classical.choose_spec (hrows k hk))
  obtain ⟨q, hq, y, r, wire, ⟨k, hk, hrow⟩, _, _, C, G, hC, hn, _⟩ :=
    (origin i x W hx hW).1 m Y Q rows hm hmW hYW hYm hQ hr
  have hheight : (heightView p C).h = m := by
    have hmatch := (hr q hq).2.2.2
    cases hp : (rows q).2.height_pair with
    | empty => rw [hp] at hmatch; contradiction
    | vote h e tm =>
      rw [hp] at hmatch hn
      have he : h = m ∧ e = Y.root := of_decide_eq_true hmatch
      exact (Prod.mk.inj (Option.some.inj hn)).1.symm.trans he.1
  have hsource : actionSource p c E rho y r = some (some (eraseFG C)) := by
    change (actionSourceFG p c E rho y r).map (Option.map eraseFG) = _
    rw [hC]
    rfl
  have htime : p.actionTime r ≤ SA.voteTime p.toParams (s + 1) := by
    by_contra hn
    have := V2.D.Engine.eventIndex_lt_of_time_lt hsch hi hrow.2.1 (lt_of_not_ge hn)
    omega
  refine ⟨k, hk, y, r, wire, C, hrow, hC, hheight,
    hist.history k y r _ hk hrow.1 hrow.2.1 hsource,
    outage_source_held_at_action hsch hrow.2.1 hC, ?_⟩
  rw [fgsa_action_gate_time] at htime ⊢
  exact outage_source_gate_before_early p s (r * p.R) htime

/-- One selected non-genesis ancestor is served before freeze at an actual
joined reader. Its current F floor supplies exclusion at the service deadline. -/
theorem outage_frozen_selected_ancestor {ΔF : Time}
    (hBase : Base₂ p c E rho)
    (hSync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hf : FGFoundation p c E rho) {j i : Nat} {x y : V} {s : Slot} {t : Time}
    {P X : FGBlock (Fin p.n)}
    (hj : rho.events[j]? = some (.tick y t)) (hy : y ∈ rho.honest)
    (hP : P ∈ (storeAt p c E rho j y).fg.TF) (ht : t ≤ SA.earlyTime p.toParams s)
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams (s + 1))))
    (hx : x ∈ rho.honest)
    (hJ : joinedAt p E rho x (s + 1) (SA.voteTime p.toParams (s + 1)))
    (hGST : E.t_GST ≤ SA.voteTime p.toParams s)
    (hXP : FGBlock.Preceq X P) (hne : eraseFG X ≠ .genesis)
    (hFX : FGBlock.Preceq (storeAt p c E rho i x).fg.F X) :
    X ∈ voterBlocks p (clock p (storeAt p c E rho i x)
      (SA.voteTime p.toParams (s + 1))) (s + 1) := by
  have hs := hBase.valid.toScheduleWellFormed
  obtain ⟨Y, hY, heY⟩ := eraseFG_ancestor_mem (cstoreInv_stateBefore E rho j y).fg.closed
    hP (eraseFG_preceq hXP)
  have hXj : X ∈ (storeAt p c E rho j y).fg.TF := eraseFG_injective heY ▸ hY
  have hXb := ((cstoreInv_stateBefore E rho j y).baseTree _).mpr ⟨X, hXj, rfl⟩
  obtain ⟨k, hkj, send, o, hObj, hAcc⟩ := fgsa_block_accepted_origin E rho j y
    (eraseFG X) hne hXb
  have hSend : send < t := by
    obtain ⟨parent, hdel, _⟩ := hAcc.1
    by_contra hn
    have hjk := V2.D.Engine.tick_index_lt_delivery E rho hs hj hdel (le_of_not_gt hn)
    omega
  obtain ⟨r, N, hErase, hDecode⟩ : ∃ r N, N.erase = eraseFG X ∧
      (toWire p o).decode = some (.block r N) := by
    unfold blockOf? at hObj
    cases hd : (toWire p o).decode with
    | none => rw [hd] at hObj; contradiction
    | some m =>
      cases m <;> simp only [hd, reduceCtorEq, Option.some.injEq] at hObj
      exact ⟨_, _, hObj, rfl⟩
  have hFreeze : SA.freezeTime p.toParams s < SA.voteTime p.toParams (s + 1) := by
    rw [arming_freeze_eq, arming_vote_eq]; push_cast; linarith [p.deltaPos]
  have hhor : SA.voteTime p.toParams (s + 1) ≤ rho.horizon :=
    (hs.in_horizon _ (List.mem_of_getElem? hi)).2
  have hIdx : rho.idxBefore (SA.freezeTime p.toParams s) ≤ i := by
    apply Nat.le_of_not_gt
    intro hn
    exact (not_lt_of_ge hFreeze.le)
      ((Gen.V2.Duty.index_lt_idxBefore_iff hs hi _).mp hn)
  have hF : Block.Compatible N.erase
      (eraseFG (rho.stateBeforeTime E (SA.freezeTime p.toParams s) x).st.fg.F) := by
    rw [hErase, ← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs]
    exact block_compatible_of_common (block_preceq_refl _) (block_preceq_trans
      (eraseFG_preceq (hf.mono _ i x hx hIdx).1) (eraseFG_preceq hFX))
  obtain ⟨hService⟩ := outage_transfer_path_proposal_service hBase hSync hx hy hJ hhor
    hDecode hAcc (hSend.trans_le ht) ((hGST.trans (arming_vote_lt_early p s).1.le)) hF
  have ho : o = ofWire p ⟨.proposer r, .proposal N⟩ := by
    apply toWire_injective
    rw [toWire_ofWire]
    exact decode_eq_block.mp hDecode
  subst o
  obtain ⟨Z, hZ, hEZ⟩ := hService.proposal hs hx hBase.receiptIdealization
  have hXcut : X ∈ (rho.stateBeforeTime E (SA.freezeTime p.toParams s) x).st.fg.TF :=
    eraseFG_injective (hEZ.trans hErase) ▸ hZ
  have hAw := outage_restored_reader_awake hJ
    (by rw [arming_freeze_eq]; have := p.deltaPos; positivity)
    (by rw [arming_freeze_eq]; change 4 * p.Δ * (s : Int) ≤ _; linarith [p.deltaPos])
    hFreeze.le
  have htf : ((4 * s + 3 : Nat) : Time) * p.Δ = SA.freezeTime p.toParams s := by
    rw [arming_freeze_eq]; push_cast; ring
  obtain ⟨jf, hjf, _⟩ := fgsa_tick_total E rho hs hBase.delta x hx (4 * s + 3)
    (by rw [htf]; exact hFreeze.le.trans hhor)
    (by rw [htf]; exact hAw)
  rw [htf] at hjf
  have hfi := V2.D.Engine.eventIndex_lt_of_time_lt hs hjf hi hFreeze
  have hEpoch := inclusion_epoch_of_joined_tick E rho hs hi hJ
    (a := SA.freezeTime p.toParams s) (by
      change 4 * p.Δ * (((s + 1 : Nat) : Int) - 1) < 4 * p.Δ * (s : Int) + 3 * p.Δ
      push_cast; linarith [p.deltaPos])
  have hXf : X ∈ (storeAt p c E rho jf x).fg.TF := by
    rw [arming_tick_store_on hs hjf (hEpoch.mono le_rfl hfi.le)]
    rwa [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs] at hXcut
  exact outage_frozen_path_at_joined_read hBase hf hjf hi hJ
    (by rw [arming_freeze_eq]; have := p.deltaPos; positivity)
    (by change 4 * p.Δ * (((s + 1 : Nat) : Int) - 1) < _
        rw [arming_freeze_eq]; push_cast; linarith [p.deltaPos])
    (by simp only [Nat.add_sub_cancel]; exact le_rfl) hfi.le hXf hFX

/-- The uncontested read has its frozen path from one prior good HEAD and,
when needed, the actual honest crossing source of the current height floor. -/
theorem outage_uncontested_frozen_path {ΔF : Time}
    (hBase : Base₂ p c E rho)
    (hSync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hf : FGFoundation p c E rho) (origin : RQCOrigin p c E rho)
    {B : FGBlock (Fin p.n)} (hne : eraseFG B ≠ .genesis) {i : Nat} {x : V} {s : Slot}
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams (s + 1))))
    (hx : x ∈ rho.honest)
    (hJ : joinedAt p E rho x (s + 1) (SA.voteTime p.toParams (s + 1)))
    (hGST : E.t_GST ≤ SA.voteTime p.toParams s)
    (hist : OutageSourceHistory p c E rho (eraseFG B) i)
    (hPrior : ∃ j y P, rho.events[j]? = some (.tick y (SA.voteTime p.toParams s)) ∧
      y ∈ rho.honest ∧ P ∈ (storeAt p c E rho j y).fg.TF ∧
      Block.Preceq (eraseFG B) (eraseFG P))
    (hRoot : Block.Compatible (liveRoot p (clock p (storeAt p c E rho i x)
      (SA.voteTime p.toParams (s + 1)))) (eraseFG B))
    (hBad : ¬ Block.Preceq (eraseFG B) (headVote p (clock p (storeAt p c E rho i x)
      (SA.voteTime p.toParams (s + 1))) (s + 1)))
    (hNT : (controls p (clock p (storeAt p c E rho i x)
      (SA.voteTime p.toParams (s + 1)))).contest = false) :
    ∀ C, Block.Prec (liveRoot p (clock p (storeAt p c E rho i x)
        (SA.voteTime p.toParams (s + 1)))) C → Block.Preceq C (eraseFG B) →
      ∃ X ∈ voterBlocks p (clock p (storeAt p c E rho i x)
          (SA.voteTime p.toParams (s + 1))) (s + 1), eraseFG X = C ∧
        ∃ W ∈ voterBlocks p (clock p (storeAt p c E rho i x)
            (SA.voteTime p.toParams (s + 1))) (s + 1),
          FGBlock.Preceq X W ∧
          (controls p (clock p (storeAt p c E rho i x)
            (SA.voteTime p.toParams (s + 1)))).lo ≤ (heightView p W).h := by
  let dst := clock p (storeAt p c E rho i x) (SA.voteTime p.toParams (s + 1))
  have hinv := cstoreInv_clock p _ (cstoreInv_stateBefore E rho i x)
    (SA.voteTime p.toParams (s + 1))
  have hBA : ¬ Block.Preceq (eraseFG B) (liveRoot p dst) := by
    intro hBA
    apply hBad
    change Block.Preceq _ (if s + 1 = 0 then .genesis else headInTree p dst _ _ _)
    rw [ite_eq_right (Nat.succ_ne_zero s)]
    exact block_preceq_trans hBA (liveRoot_preceq_headInTree p dst _ _ _)
  have hAB : Block.Preceq (liveRoot p dst) (eraseFG B) := by
    rcases Bool.or_eq_true_iff.mp hRoot with h | h
    · exact h
    · exact (hBA h).elim
  have hFB : FGBlock.Preceq (storeAt p c E rho i x).fg.F B := by
    apply eraseFG_preceq_iff.mp
    have hfB := block_preceq_trans (F_preceq_liveRoot p dst hinv) hAB
    simpa only [dst, clock_fg] using hfB
  obtain ⟨j, y, P, hj, hy, hP, hBP⟩ := hPrior
  have path {X : FGBlock (Fin p.n)} (hFX : FGBlock.Preceq (storeAt p c E rho i x).fg.F X)
      (hXB : FGBlock.Preceq X B) (hXne : eraseFG X ≠ .genesis) :
      X ∈ voterBlocks p dst (s + 1) :=
    outage_frozen_selected_ancestor hBase hSync hf hj hy hP (arming_vote_lt_early p s).1.le
      hi hx hJ hGST (preceq_trans hXB (eraseFG_preceq_iff.mp hBP)) hXne hFX
  have hBm := path hFB (preceq_refl B) hne
  have hlo : (controls p dst).lo = dst.fg.h_max - 1 := by
    change (if (controls p dst).contest then dst.fg.h_max else dst.fg.h_max - 1) = _
    rw [hNT]
    rfl
  have witness : ∃ W ∈ voterBlocks p dst (s + 1), FGBlock.Preceq B W ∧
      (controls p dst).lo ≤ (heightView p W).h := by
    by_cases hlow : dst.fg.h_max - 1 ≤ (heightView p B).h
    · exact ⟨B, hBm, preceq_refl B, hlo ▸ hlow⟩
    obtain ⟨W, hW, hWh⟩ := KitFG.store_frontier_witness p.E (heightView p) (finalityView p)
      (fgCertificateLaws p) dst.fg hinv.fg
    have hWpre : W ∈ (storeAt p c E rho i x).fg.TF := by
      change W ∈ (clock p _ _).fg.TF at hW
      rwa [clock_fg] at hW
    have hBpos := (fgCertificateLaws p).height.one_le_h B
    change ¬ ((_ : Nat) ≤ _) at hlow
    change (1 : Nat) ≤ _ at hBpos
    change (_ : Nat) = _ at hWh
    have hm : 1 ≤ dst.fg.h_max - 1 := by change (1 : Nat) ≤ _; omega
    have hmW : dst.fg.h_max - 1 < (heightView p W).h := by change (_ : Nat) < _; omega
    obtain ⟨k, _, y, r, wire, U, hrow, _, hUh, hUB, hU, htime⟩ :=
      outage_crossing_source_at_read hBase.valid.toScheduleWellFormed origin hx hi hWpre
        hm hmW hist
    have hBU : FGBlock.Preceq B U := by
      rcases Bool.or_eq_true_iff.mp hUB with h | h
      · have hmono := (fgCertificateLaws p).height.h_mono (eraseFG_preceq_iff.mp h)
        rw [hUh] at hmono
        exact (hlow hmono).elim
      · exact eraseFG_preceq_iff.mp h
    have hUne : eraseFG U ≠ .genesis := by
      intro he
      apply hne
      exact block_preceq_antisymm (he ▸ eraseFG_preceq hBU) (block_genesis_preceq _)
    have hFrozen := outage_frozen_selected_ancestor hBase hSync hf hrow.2.1 hrow.1 hU htime
      hi hx hJ hGST (preceq_refl U) hUne (preceq_trans hFB hBU)
    exact ⟨U, hFrozen, hBU, by rw [hlo, hUh]⟩
  obtain ⟨W, hW, hBW, hWh⟩ := witness
  intro C hAC hCB
  obtain ⟨X, _, heX⟩ := eraseFG_ancestor_mem hinv.fg.closed
    (Finset.mem_filter.mp (Finset.mem_filter.mp hBm).1).1 hCB
  have hXB := eraseFG_preceq_iff.mp (heX ▸ hCB)
  have hFX : FGBlock.Preceq (storeAt p c E rho i x).fg.F X := by
    apply eraseFG_preceq_iff.mp
    rw [heX]
    have hAC' := (Bool.and_eq_true_iff.mp hAC).2
    have hfC := block_preceq_trans (F_preceq_liveRoot p dst hinv) hAC'
    change Block.Preceq (eraseFG (storeAt p c E rho i x).fg.F) C
    simpa only [dst, clock_fg] using hfC
  have hXne : eraseFG X ≠ .genesis := by
    intro he
    have hCA : Block.Preceq C (liveRoot p dst) := heX ▸ he.symm ▸ block_genesis_preceq _
    have hEq := block_preceq_antisymm (Bool.and_eq_true_iff.mp hAC).2 hCA
    have hn := (Bool.and_eq_true_iff.mp hAC).1
    simp only [hEq, decide_true, Bool.not_true, Bool.false_eq_true] at hn
  exact ⟨X, path hFX hXB hXne, heX, W, hW, preceq_trans hXB hBW, hWh⟩

/-- The contested filter is compatible at the actual named frame and live root. -/
theorem outage_contested_head_of_names
    (hf : FGFoundation p c E rho) {B : FGBlock (Fin p.n)} {i : Nat} {x : V} {s : Slot}
    (hx : x ∈ rho.honest) (hNames : OutageNamedHistory p c E rho B i)
    (hRoot : Block.Compatible (liveRoot p (clock p (storeAt p c E rho i x)
      (SA.voteTime p.toParams s))) (eraseFG B))
    (hContest : (controls p (clock p (storeAt p c E rho i x)
      (SA.voteTime p.toParams s))).contest = true) :
    Block.Compatible (headVote p (clock p (storeAt p c E rho i x)
      (SA.voteTime p.toParams s)) s) (eraseFG B) := by
  have hCtrl : controls p (clock p (storeAt p c E rho i x) (SA.voteTime p.toParams s)) =
      controls p (storeAt p c E rho i x) := by
    change KitFG.treeStoreControlsView (heightView p) (clock p _ _).fg = _
    rw [clock_fg]
    rfl
  have hct := hContest
  rw [hCtrl] at hct
  have hc := (fgsa_cpCompat_of_scopedFrame p c E rho hf.store hf.strat
    i x B hx hNames.history).2.2.2.2 hct
  apply outageV_contested_head p _ (cstoreInv_clock p _ (cstoreInv_stateBefore E rho i x) _)
    B s hRoot ?_ hContest
  intro W hW hh
  rw [clock_fg] at hW
  change (heightView p W).h = (controls p (clock p (storeAt p c E rho i x)
    (SA.voteTime p.toParams s))).H at hh
  rw [hCtrl] at hh
  exact outageV_contest_top p _ B hc.1 hc.2 W hW hh

/-- The first actual joined regression produces its own durable nonzero marker.
Root, scores, filtered path, receipt floors and epochs are all produced here. -/
theorem outage_regression_marker_no_lower [Fintype V]
    {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (origin : RQCOrigin p c E rho) (htsrc : TSrc p c E rho)
    (hnamed : ∀ k x r (a : RowWire p.n) e,
      HonestRowAt p c E rho k x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hprov : ArmingJoinedProvenance (c := c) E rho)
    {B : Block} (hne : B ≠ .genesis) {l : Slot} {D : Block}
    {Dh β : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh) (hβ : eraseFG β = B)
    {k : Nat} {s : Slot}
    (hReg : OutageScopedRegression (p := p) (c := c) (E := E) (rho := rho)
      fast b₀ b₁ B k s)
    (hNo : ∀ j q, q < s → ¬ OutageScopedRegression (p := p) (c := c) (E := E)
      (rho := rho) fast b₀ b₁ B j q) :
    ∃ x P, rho.events[k]? = some (.tick x (SA.voteTime p.toParams s)) ∧
      x ∈ rho.honest ∧ joinedAt p E rho x s (SA.voteTime p.toParams s) ∧
      P ∈ (storeAt p c E rho k x).fg.TF ∧
      FGBlock.Preceq β (heightView p P).J ∧ (heightView p P).h_j ≠ 0 ∧
      Block.Compatible (headVote p (clock p (storeAt p c E rho k x)
        (SA.voteTime p.toParams s)) s) (eraseFG β) := by
  subst B
  obtain ⟨q, K, hk, hR, hK, hBad, hScores, hPrior⟩ := outage_regression_scores_no_lower
    h hf htsrc hnamed hsrc hState hprov hne hc rfl hReg hNo
  obtain ⟨hResults, hSource, hNames, _, hCover⟩ := outage_regression_prefix_no_lower
    h hf htsrc hnamed hsrc hState hprov hne hc rfl hReg hNo
  have hRoot := outage_scoped_head_root h hf hc rfl hk hR hNames (hCover _)
    (fun j q C hj => hResults j _ q C hj hR.1.1)
  have hslot : slotAt p (SA.voteTime p.toParams s) = s :=
    slotOf_offset p s p.Δ p.deltaPos.le
      (by have := p.deltaPos; dsimp [Time] at *; omega)
  have hJ : joinedAt p E rho (rho.seatOf (.base (.head s)) q) s
      (SA.voteTime p.toParams s) := by simpa only [hslot] using hR.1.2
  have hpos : 0 < s := (Nat.zero_le _).trans_lt hReg.1
  have heq : s - 1 + 1 = s := Nat.sub_add_cancel hpos
  have hBad' := (headTargetAtEmission_at_tick E rho h.pre.base.valid.toScheduleWellFormed
    hK hk rfl) ▸ hBad
  have hrs := hReg.1
  have hGST := h.gst.trans (outage_restored_vote_cut p b₁
    (show restoredLabel p b₁ ≤ s - 1 by dsimp only [Slot] at *; omega))
  have hPath := outage_uncontested_frozen_path h.pre.base h.sync hf origin hne
    (heq.symm ▸ hk) hR.1.1 (heq.symm ▸ hJ) hGST hSource hPrior
    (heq.symm ▸ hRoot) (heq.symm ▸ hBad')
  have hContest := outage_regression_contested_of_retained_batch (Nat.ne_of_gt hpos)
    hBad' hRoot hScores (by simpa only [heq] using hPath)
  obtain ⟨P, hP, hBJ, hnz⟩ := outage_contested_marker_of_names hf hR.1.1 hNames hContest
  exact ⟨_, P, hk, hR.1.1, hJ, hP, hBJ, hnz,
    outage_contested_head_of_names hf hR.1.1 hNames hRoot hContest⟩

/-- The first actual joined regression produces its durable marker. -/
theorem outage_first_regression_marker [Fintype V]
    {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (origin : RQCOrigin p c E rho) (htsrc : TSrc p c E rho)
    (hnamed : ∀ k x r (a : RowWire p.n) e,
      HonestRowAt p c E rho k x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hprov : ArmingJoinedProvenance (c := c) E rho)
    {B : Block} (hne : B ≠ .genesis) {l : Slot} {D : Block}
    {Dh β : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh) (hβ : eraseFG β = B)
    {k : Nat} {s : Slot}
    (hReg : OutageScopedRegression (p := p) (c := c) (E := E) (rho := rho)
      fast b₀ b₁ B k s)
    (hFirst : ∀ j, j < k → ∀ q, ¬ OutageScopedRegression (p := p) (c := c) (E := E)
      (rho := rho) fast b₀ b₁ B j q) :
    ∃ x P, rho.events[k]? = some (.tick x (SA.voteTime p.toParams s)) ∧
      x ∈ rho.honest ∧ joinedAt p E rho x s (SA.voteTime p.toParams s) ∧
      P ∈ (storeAt p c E rho k x).fg.TF ∧
      FGBlock.Preceq β (heightView p P).J ∧ (heightView p P).h_j ≠ 0 := by
  obtain ⟨x, P, hk, hx, hJ, hP, hBJ, hnz, _⟩ := outage_regression_marker_no_lower h hf
    origin htsrc hnamed hsrc hState hprov hne hc hβ hReg
    (outage_no_lower_of_first_event h.pre.base.valid.toScheduleWellFormed hReg hFirst)
  exact ⟨x, P, hk, hx, hJ, hP, hBJ, hnz⟩

end AvailableChain.FGSA.Run
end

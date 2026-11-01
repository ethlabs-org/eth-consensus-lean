module
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingLocal
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingSleep

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Clean supplies provenance only at the joined receiver's actual HEAD duty. -/
abbrev ArmingJoinedProvenance (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) : Prop :=
  ∀ s i y, y ∈ rho.honest →
    rho.events[i]? = some (.tick y (SA.voteTime p.toParams (s + 1))) →
    joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
    ∀ o ∈ headVotes p (clock p (storeAt p c E rho i y)
      (SA.voteTime p.toParams (s + 1))) (s + 1), ∀ q, GridCO.headSeat? o = some q →
      o ∈ GridCO.votesAt (storeAt p c E rho i y).base s ∨
        GridCO.equivocates (GridCO.votesAt (storeAt p c E rho i y).base s) q = true

/-- Before an in-cut pending gate, actual Clean sources bound the whole prefix. -/
theorem arming_prefix_before_cut {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {b₀ : Time} (hV : V2.D.ExecutionValid E rho)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (hroots : NamedRootCollisionFree p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    {q : Slot} {D : Block} {Dh : FGBlock (Fin p.n)} (hDh : eraseFG Dh = D)
    (hD : (q, D) ∈ cleanResults p c E rho (timeIdx rho b₀))
    (hcut : SA.gateTime p.toParams (q + 1) ≤ b₀)
    (hmax : ∀ r C, (r, C) ∈ cleanResults p c E rho (timeIdx rho b₀) → r ≤ q →
      Block.Preceq C D) : ArmingPrefixState p c E rho q D Dh := by
  have hs := hV.toScheduleWellFormed
  have hq := ((arming_gate_le_iff p q (q + 1)).mpr (Nat.le_succ q)).trans hcut
  have hentry := arming_sleep_entry_below hs (hState _ le_rfl) hDh hq hmax
  intro i y hi _ hy
  have hiCut : i ≤ timeIdx rho b₀ := hi.trans
    ((fgsa_idxBefore_mono rho hcut).trans (arming_idxBefore_le_timeIdx rho b₀))
  obtain ⟨hF, hJ, hZ, hn, hlo⟩ := arming_frame_below
    (hroots := hroots) (hstrat := hf.strat)
    (hScope := hDh.symm ▸ rootScope_result hV hD)
    hs hf.store hf.frame.1 hsrc hDh hentry hi hy
  refine ⟨hF, hJ, hZ, hn, hlo, ?_⟩
  intro row hr
  obtain ⟨j, hji, s, C, ht, hpass, hres, hrow⟩ := (hState i hiCut).leases y row hr
  have htime := (Gen.V2.Duty.index_lt_idxBefore_iff hs ht _).mp (hji.trans_le hi)
  have hsq := arming_lt_pending p q s htime
  exact block_preceq_trans hrow (hmax s C
    ⟨j, hji.trans_le hiCut, y, ht, (arming_enabled_of_pass ht hpass).2, hres⟩ hsq)

/-- One previous healthy batch covers the next joined HEAD, even if its gate is absent. -/
theorem arming_joined_head_from_previous [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c fast E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (htransfer : ∀ y z s C H, y ∈ rho.honest → z ∈ rho.honest →
      joinedAt p E rho z (s + 1) (SA.voteTime p.toParams (s + 1)) →
      SA.gateTime p.toParams s ≤ b₀ → gateResult p c E rho y s = some (some C) →
      vHead p c E rho z s = some H → Block.Preceq C H)
    (hprov : ArmingJoinedProvenance (c := c) E rho)
    {q : Slot} {D : Block} {Dh : FGBlock (Fin p.n)} (hDh : eraseFG Dh = D)
    (hD : (q, D) ∈ cleanResults p c E rho (timeIdx rho b₀)) (hDne : D ≠ .genesis)
    (hcut : SA.gateTime p.toParams (q + 1) ≤ b₀)
    (hmax : ∀ r C, (r, C) ∈ cleanResults p c E rho (timeIdx rho b₀) → r ≤ q →
      Block.Preceq C D) {y : V} (hy : y ∈ rho.honest) {i : Nat}
    (hi : rho.events[i]? = some (.tick y (SA.voteTime p.toParams (q + 2))))
    (hJ : joinedAt p E rho y (q + 2) (SA.voteTime p.toParams (q + 2))) :
    Block.Preceq D (headVote p (clock p (storeAt p c E rho i y)
      (SA.voteTime p.toParams (q + 2))) (q + 2)) := by
  have hs := h.pre.base.valid.toScheduleWellFormed
  have hq := ((arming_gate_le_iff p q (q + 1)).mpr (Nat.le_succ q)).trans hcut
  have hprefix := arming_prefix_before_cut h.pre.base.valid hf hsrc h.pre.base.idealization
    hState hDh hD hcut hmax
  have hw := arming_joined_window (c := c) hy hJ
  have hearly : SA.earlyTime p.toParams (q + 1) < SA.voteTime p.toParams (q + 2) :=
    (arming_duty_window p q).2.2.2.trans (arming_duty_window p q).2.1
  have hFloor : Block.Preceq
      (eraseFG (rho.stateBeforeTime E (SA.earlyTime p.toParams (q + 1)) y).st.fg.F) D := by
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs]
    exact (hprefix _ y (fgsa_idxBefore_mono rho
      ((arming_early_next p q).trans_le
        ((arming_gate_le_iff p q (q + 1)).mpr (Nat.le_succ q))))
      (arming_idxBefore_le_length rho _) hy).1
  have hb := arming_healthy_batch_window h hq
    (fun z hz hJ k hk => arming_head_ge_on hs htransfer hD hz hJ hk)
    (arming_window_mono hw hearly.le) hFloor
  apply arming_head_covers_on h.pre.base.valid hf h.pre.base.cstar hDh hDne
    ⟨h.sleepPre.joinedPartBefore _
      (by rw [arming_vote_eq]; have := p.deltaPos; positivity)
      ((arming_vote_lt_early p _).1.trans_le ((arming_early_next p q).trans_le hq))⟩
    hprefix hy hb hi
  · intro k hk
    apply (arming_window_epoch hs hw hi le_rfl).mono ?_ le_rfl
    by_contra hn
    have ht := (V2.D.Engine.index_lt_actionCut_iff hs hk _).mp (lt_of_not_ge hn)
    have hstart : slotStartZ p ((q + 1 : Nat) : Int) < SA.earlyTime p.toParams (q + 1) := by
      change 4 * p.Δ * ((q + 1 : Nat) : Int) <
        4 * p.Δ * ((q + 1 : Nat) : Int) + 2 * p.Δ
      linarith [p.deltaPos]
    rcases ht with ht | ⟨ht, _⟩
    · exact (not_lt.mpr hstart.le) ht
    · exact (ne_of_lt hstart) ht.symm
  · intro k w j hj hkj he
    have hji := V2.D.Engine.eventIndex_lt_of_time_lt hs hj hi hearly
    have hwT : w ≤ SA.voteTime p.toParams (q + 2) := by
      by_contra hn
      have hik := V2.D.Engine.eventIndex_lt_of_time_lt hs hi he (lt_of_not_ge hn)
      omega
    have hw0 := (hs.in_horizon _ (List.mem_of_getElem? he)).1
    have hbound := hJ.2.2 w hw0 hwT (List.mem_of_getElem? he)
    have hstart : slotStartZ p (((q + 2 : Nat) : Int) - 1) <
        SA.earlyTime p.toParams (q + 1) := by
      change 4 * p.Δ * (((q + 2 : Nat) : Int) - 1) <
        4 * p.Δ * ((q + 1 : Nat) : Int) + 2 * p.Δ
      push_cast; linarith [p.deltaPos]
    exact hbound.trans_lt hstart
  · exact hprov (q + 1) i y hy hi hJ

/-- The comparison can come from an earlier result when the cut gate is suppressed. -/
structure ArmingSleepGateCert (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (fast : Bool) (T b₀ : Time)
    (B : Block) (l : Slot) (D : Block) (Dh : FGBlock (Fin p.n)) : Prop where
  origin : ∃ r C, 1 ≤ r ∧ (r, C) ∈ cleanResults p c E rho (timeIdx rho b₀) ∧
    SA.gateTime p.toParams r ≤ T ∧ Block.Preceq B C
  max_lift : eraseFG Dh = D
  max_read : Block.Preceq B D
  max_mem : ∃ q, q ≤ l ∧ (q, D) ∈ cleanResults p c E rho (timeIdx rho b₀)
  max_le : ∀ r C, (r, C) ∈ cleanResults p c E rho (timeIdx rho b₀) → r ≤ l →
    Block.Preceq C D
  gate_le_cut : SA.gateTime p.toParams l ≤ b₀
  cut_lt_pending : b₀ < SA.gateTime p.toParams (l + 1)
  cover_label : coverLabel p b₀ = l + 1
  source_below : ∀ y r C, y ∈ rho.honest →
    p.actionTime r < SA.gateTime p.toParams (l + 1) →
    actionSource p c E rho y r = some (some C) → Block.Preceq C D
  joined_heads : ∀ z, z ∈ rho.honest →
    joinedAt p E rho z (l + 1) (SA.voteTime p.toParams (l + 1)) →
    ∀ k, rho.events[k]? = some (.tick z (SA.voteTime p.toParams (l + 1))) →
    Block.Preceq D (headVote p (clock p (storeAt p c E rho k z)
      (SA.voteTime p.toParams (l + 1))) (l + 1))
  f_below : ∀ i y, i ≤ rho.idxBefore (SA.gateTime p.toParams (l + 1)) →
    y ∈ rho.honest → Block.Preceq (F_at p c E rho i y) D
  pending_input : ∀ i y, IsGateTick p c rho i y (l + 1) →
    y ∈ coveredNodes p E rho fast b₀ →
    Block.Preceq B (F_at p c E rho i y) ∨
      ArmingGateInput p (clockPre p (storeAt p c E rho i y)
        (SA.gateTime p.toParams (l + 1))) fast (l + 1) B D

/-- Keep the Round 4 certificate API as the attained-last-label special case. -/
theorem arming_sleep_gate_cert_of_last {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {fast : Bool} {T b₀ : Time} {B : Block} {l : Slot} {D : Block}
    {Dh : FGBlock (Fin p.n)} (hc : ArmingSleepCert p c E rho fast T b₀ B l D Dh)
    (hHeads : ∀ z, z ∈ rho.honest →
      joinedAt p E rho z (l + 1) (SA.voteTime p.toParams (l + 1)) →
      ∀ k, rho.events[k]? = some (.tick z (SA.voteTime p.toParams (l + 1))) →
      Block.Preceq D (headVote p (clock p (storeAt p c E rho k z)
        (SA.voteTime p.toParams (l + 1))) (l + 1))) :
    ArmingSleepGateCert p c E rho fast T b₀ B l D Dh :=
  ⟨hc.origin, hc.max_lift, hc.max_read, ⟨l, le_rfl, hc.max_mem⟩, hc.max_le,
    hc.gate_le_cut, hc.cut_lt_pending, hc.cover_label, hc.source_below, hHeads, hc.f_below,
    hc.pending_input⟩

/-- Execute the general comparison certificate at the protected pending gate. -/
theorem arming_sleep_gate_core_scoped {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hvalid : V2.D.ExecutionValid E rho) (hdelta : E.Δ = p.Δ)
    {fast : Bool} {T b₀ : Time} {B : Block} (hne : B ≠ .genesis)
    {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh)
    (hgate : SA.gateTime p.toParams (l + 1) ≤ rho.horizon) :
    ∀ y ∈ coveredNodes p E rho fast b₀,
      let I := afterTicksIdx rho (SA.gateTime p.toParams (l + 1))
      let st := storeAt p c E rho I y
      Block.Preceq B (S_at p c E rho I y) ∧
      (Block.Preceq B (F_at p c E rho I y) ∨
        (Block.Preceq (F_at p c E rho I y) B ∧ F_at p c E rho I y ≠ B ∧
          ∃ dl, FGSA.leaseOf st B = some dl ∧ SA.gateTime p.toParams (l + 1) < dl ∧
            SA.gateTime p.toParams (l + 1) + L p ≤ dl ∧ B ∈ st.base.blocks)) := by
  intro y hyG I st
  have hs := hvalid.toScheduleWellFormed
  have hScope : (if fast then l + 1 = coverLabel p b₀
      else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ ((l + 1 : Nat) : Int) ∧
        l + 1 ≤ coverLabel p b₀) := by
    rw [hc.cover_label]
    cases fast with
    | true => exact rfl
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      have hk : (1 : Int) ≤ (p.k : Int) := by exact_mod_cast (show 1 ≤ p.k by
        have := p.kLarge; omega)
      exact ⟨by omega, le_rfl⟩
  have hy := (arming_receiver_window hyG hScope).1
  obtain ⟨i, hi⟩ := arming_tick_exists hs hdelta hy (4 * (l + 1) + 6)
    (arming_gate_nat p (l + 1)) hgate (arming_receiver_times hyG hScope).2
  let P := clockPre p (storeAt p c E rho i y) (SA.gateTime p.toParams (l + 1))
  have hI : storeAt p c E rho I y = gateStep p P (l + 1) := by
    change (V2.D.Run.stateBefore E rho I y).st = _
    rw [← afterTicks_eq_stateBefore E rho hs, afterTicks_node E rho hs hi]
    exact (tick_st (c := c) E rho _ y _).trans (arming_clock_gate p _ (l + 1))
  have hFI : F_at p c E rho I y = F_at p c E rho i y := by
    change eraseFG (storeAt p c E rho I y).fg.F = eraseFG (storeAt p c E rho i y).fg.F
    rw [hI, gateStep_fg, clockPre_fg]
  rcases hc.pending_input i y hi hyG with hBF | hIn
  · have hBF' := hFI.symm ▸ hBF
    exact ⟨block_preceq_trans hBF'
      (finalized_preceq_stable p _ (reachable_stateBefore E rho I y)), Or.inl hBF'⟩
  have hG := arming_receiver_enabled hs hyG hScope hi
  have hJoined : joinedNow p P = true := by
    dsimp only [P]
    rw [clockPre_joined]
    exact fgsa_gate_joined_of_enabled E rho hG
  obtain ⟨Cj, hraw, hDCj⟩ := hIn.raw
  have hEpoch := (arming_pending_epochs hs hc.gate_le_cut hc.cut_lt_pending
    hc.cover_label hyG hi).2.1
  have hst := arming_tick_store_on hs hi hEpoch
  have hFD : Block.Preceq (eraseFG P.fg.F) D := by
    dsimp only [P]
    rw [clockPre_fg, hst]
    exact hc.f_below _ y le_rfl hy
  have hlev : SA.releaseThreshold p.toParams ≤
      SA.Root.prefixSupport p.toParams (actView P) (l + 1) B ∨
      GridCO.slowEligible p.toParams.engine (actView P) (l + 1) B = true := by
    cases fast with
    | true => exact Or.inl (hIn.fast_support rfl)
    | false =>
      right
      obtain ⟨hk2, hwin⟩ := hIn.slow_rows rfl
      apply Bool.and_eq_true_iff.mpr
      refine ⟨decide_eq_true hk2, List.all_eq_true.mpr ?_⟩
      intro a ha
      obtain ⟨Ca, hsv, hBCa⟩ := hwin a (List.mem_range.mp ha)
      rw [show GridCO.savedGenuine (actView P) (l + 1 - (a + 1)) = some (some Ca) from hsv]
      exact hBCa
  obtain ⟨_, hblocks, hS, d, hrow, hd⟩ := arming_gate_write p P (l + 1) hJoined hIn.fresh hraw
    (fun row hr => block_compatible_of_common (block_preceq_trans (hIn.leases row hr) hDCj)
      (block_preceq_refl Cj)) (block_preceq_trans hFD hDCj) hIn.active hne
    (block_preceq_trans hc.max_read hDCj) hlev
  refine ⟨?_, ?_⟩
  · change Block.Preceq B (storeAt p c E rho I y).base.stableRecord
    rw [hI]
    exact hS
  by_cases hBF : Block.Preceq B (F_at p c E rho I y)
  · exact Or.inl hBF
  right
  have hFB : Block.Preceq (F_at p c E rho I y) B := by
    rw [hFI]
    have hPF : eraseFG P.fg.F = F_at p c E rho i y := by
      dsimp only [P]
      rw [clockPre_fg]
      rfl
    rcases Bool.or_eq_true_iff.mp hIn.compatible with h | h
    · exact hPF ▸ h
    · exact absurd (hFI.symm ▸ hPF ▸ h) hBF
  refine ⟨hFB, fun he => hBF (he ▸ block_preceq_refl _), d, ?_, ?_, hd, ?_⟩
  · have hm : (B, SA.releaseThreshold p.toParams, d) ∈ st.base.obligations := by
      change _ ∈ (storeAt p c E rho I y).base.obligations
      rw [hI]
      exact hrow
    exact arming_leaseOf p st (cstoreInv_stateBefore E rho I y) hm
  · exact lt_of_lt_of_le (lt_add_of_pos_right _ (arming_L_pos p)) hd
  · change B ∈ (storeAt p c E rho I y).base.blocks
    rw [hI, hblocks]
    exact ((actView_blocks P B).mp hIn.active).1


/-- The scoped frame consumer returns the full lease-or-finality result to P-Ou.
P-Ou supplies compatibility of all earlier honest named rows from its source history. -/
theorem pending_gate_lease_or_F_scoped_on {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hvalid : V2.D.ExecutionValid E rho) (hdelta : E.Δ = p.Δ)
    (hf : FGFoundation p c E rho)
    {fast : Bool} {T b₀ : Time} {B : Block} (hne : B ≠ .genesis)
    {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh)
    (hgate : SA.gateTime p.toParams (l + 1) ≤ rho.horizon)
    (hRows : ∀ y r (a : RowWire p.n) (e : FGBlock (Fin p.n)) (Bh : FGBlock (Fin p.n)),
      eraseFG Bh = B →
      HonestRowBefore p c E rho (afterTicksIdx rho (SA.gateTime p.toParams (l + 1))) y r a →
      namedEntry a.payload.height_pair = some ((heightView p e).h, e.root) →
      RootBlockInRun p c E rho (eraseFG e) → FGBlock.Preceq e Bh ∨ FGBlock.Preceq Bh e) :
    ∀ y ∈ coveredNodes p E rho fast b₀,
      let I := afterTicksIdx rho (SA.gateTime p.toParams (l + 1))
      let st := storeAt p c E rho I y
      Block.Preceq B (S_at p c E rho I y) ∧
      (Block.Preceq B (F_at p c E rho I y) ∨
        (Block.Preceq (F_at p c E rho I y) B ∧ F_at p c E rho I y ≠ B ∧
          ∃ dl, FGSA.leaseOf st B = some dl ∧ SA.gateTime p.toParams (l + 1) < dl ∧
            SA.gateTime p.toParams (l + 1) + L p ≤ dl ∧
            ((∃ X ∈ FGSA.fullTree p st, eraseFG X = B) ∨
              Block.Preceq B (eraseFG (FGSA.controls p st).Z)))) := by
  classical
  intro y hyG I st
  obtain ⟨hS, hF | ⟨hFB, hneF, dl, hlease, hdl, hlong, hB⟩⟩ :=
    arming_sleep_gate_core_scoped hvalid hdelta hne hc hgate y hyG
  · exact ⟨hS, Or.inl hF⟩
  refine ⟨hS, Or.inr ⟨hFB, hneF, dl, hlease, hdl, hlong, ?_⟩⟩
  have hy : y ∈ rho.honest := (Finset.mem_filter.mp hyG).1
  have hinv : CStoreInv p st := cstoreInv_stateBefore E rho I y
  obtain ⟨Bh, hBh, hBe⟩ := (hinv.baseTree B).1 hB
  have hFBh : FGBlock.Preceq st.fg.F Bh := arming_lift (hBe ▸ hFB)
  obtain ⟨_, _, hdom, _⟩ := (fgsa_cpCompat_of_scopedFrame p c E rho hf.store hf.strat
    I y Bh hy (fun z r a e ha he hScope => hRows z r a e Bh hBe ha he hScope)).2
  rcases hdom hBh hFBh with hZ | hD
  · exact Or.inr (hBe ▸ eraseFG_preceq hZ)
  · left
    refine ⟨Bh, ?_, hBe⟩
    rw [fgsa_fullTree_eq_filtered, ← fgsa_domainR_eq_filtered]
    exact hD


/-- A comparison result and the actual joined batch construct the fast pending input. -/
theorem arming_fast_cert_of_comparison [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c true E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (htsrc : TSrc p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hHist : CleanHist p c E rho (timeIdx rho b₀))
    {x : V} {B : Block}
    (hread : Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x T))
    (hne : B ≠ .genesis)
    {l : Slot} (hLabel : l = (((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat))
    {D : Block} {Dh : FGBlock (Fin p.n)} (hDh : eraseFG Dh = D)
    (hD : ∃ q, q ≤ l ∧ (q, D) ∈ cleanResults p c E rho (timeIdx rho b₀))
    (hBD : Block.Preceq B D)
    (hmax : ∀ r C, (r, C) ∈ cleanResults p c E rho (timeIdx rho b₀) → r ≤ l →
      Block.Preceq C D)
    (hHeads : ∀ z, z ∈ rho.honest →
      joinedAt p E rho z (l + 1) (SA.voteTime p.toParams (l + 1)) →
      ∀ k, rho.events[k]? = some (.tick z (SA.voteTime p.toParams (l + 1))) →
      Block.Preceq D (headVote p (clock p (storeAt p c E rho k z)
        (SA.voteTime p.toParams (l + 1))) (l + 1))) :
    ArmingSleepGateCert p c E rho true T b₀ B l D Dh := by
  have hs := h.pre.base.valid.toScheduleWellFormed
  obtain ⟨r, C, hr, hOrigin, hTime, hBC⟩ :=
    arming_protected_origin_on hs h.order.2.1 hState hHist hread hne
  have h6 : 6 * p.Δ ≤ b₀ := by
    have hg := (arming_gate_le_iff p 0 r).mpr (Nat.zero_le r)
    simpa only [arming_gate_eq, Nat.cast_zero, mul_zero, zero_add] using
      hg.trans (hTime.trans h.order.2.1)
  have hl := hLabel ▸ (arming_label p b₀ h6).1
  have hcut := hLabel ▸ (arming_label p b₀ h6).2
  have hcover : coverLabel p b₀ = l + 1 := by rw [hLabel]; rfl
  have hentry := arming_sleep_entry_below hs (hState _ le_rfl) hDh hl hmax
  obtain ⟨q, hql, hDq⟩ := hD
  have hF : ∀ i y, i ≤ rho.idxBefore (SA.gateTime p.toParams (l + 1)) →
      y ∈ rho.honest → Block.Preceq (F_at p c E rho i y) D := by
    intro i y hi hy
    exact (arming_frame_below (hroots := h.pre.base.idealization) (hstrat := hf.strat)
      (hScope := hDh.symm ▸ rootScope_result h.pre.base.valid hDq)
      hs hf.store hf.frame.1 hsrc hDh hentry hi hy).1
  refine ⟨⟨r, C, hr, hOrigin, hTime, hBC⟩, hDh, hBD, ⟨q, hql, hDq⟩, hmax, hl, hcut,
    hcover, arming_source_below hs htsrc hl hmax, hHeads, hF, ?_⟩
  intro i y hi hyG
  have hScope : l + 1 = coverLabel p b₀ := hcover.symm
  have hy := (arming_receiver_window hyG hScope).1
  obtain ⟨hCutEpoch, hTickEpoch, hEarlyEpoch⟩ :=
    arming_pending_epochs hs hl hcut hcover hyG hi
  have hCutI := (arming_timeIdx_le_idxBefore rho hcut).trans (by
    by_contra hn
    have ht := (Gen.V2.Duty.index_lt_idxBefore_iff hs hi _).mp (lt_of_not_ge hn)
    exact (lt_irrefl _ ht).elim)
  by_cases hBF : Block.Preceq B (F_at p c E rho (timeIdx rho b₀) y)
  · exact Or.inl (block_preceq_trans hBF (eraseFG_preceq (hf.mono _ _ y hy hCutI).1))
  right
  have hObl := arming_leases_interval_on hs hl y
    (arming_timeIdx_le_idxBefore rho hcut) le_rfl hCutEpoch
    (arming_leases_cut hs hcut (fun i y hi _ => (hState i hi).leases y) hmax le_rfl hy)
  have hFloor : Block.Preceq
      (eraseFG (rho.stateBeforeTime E (SA.earlyTime p.toParams (l + 1)) y).st.fg.F) D := by
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs]
    exact hF _ y (fgsa_idxBefore_mono rho (by
      rw [arming_early_eq, arming_gate_eq]; linarith [p.deltaPos])) hy
  obtain ⟨_, hAw, hEpoch⟩ := arming_receiver_window hyG hScope
  have hearly : SA.earlyTime p.toParams (l + 1) ≤
      SA.gateTime p.toParams (coverLabel p b₀) := by
    rw [hcover, arming_early_eq, arming_gate_eq]; linarith [p.deltaPos]
  have hw : ArmingReadWindow (c := c) E rho y (l + 1)
      (SA.earlyTime p.toParams (l + 1)) :=
    ⟨hy, fun t ht ha hb => hAw t ht ha (hb.trans hearly),
      fun w ha hb he => hEpoch w ha (hb.trans hearly) he⟩
  apply arming_sleep_pending_input h.pre.base.valid h.pre.base.cstar hBD
    ⟨h.sleepPre.joinedPartBefore _ (by rw [arming_vote_eq]; have := p.deltaPos; positivity)
      ((arming_vote_lt_early p _).1.trans_le ((arming_early_next p l).trans_le hl))⟩
    hi (fun k hk => hF k y hk hy) hObl
    (arming_healthy_batch_window h hl hHeads hw hFloor) hEarlyEpoch hTickEpoch true
  · intro _ H hH
    change (p.n + 1) / 2 ≤ H.card
    rw [arming_joined_head_card h.pre.base.cstar (l + 1) H hH]
    exact h.joinedFastPart rfl _
      (by rw [arming_vote_eq]; have := p.deltaPos; positivity)
      ((arming_vote_lt_early p _).1.trans_le ((arming_early_next p l).trans_le hl))
  · intro hfalse
    nomatch hfalse

/-- Fast arming includes the equal cut; the previous batch replaces a suppressed cut gate. -/
theorem fast_arming_scoped_on [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c true E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (htsrc : TSrc p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hHist : CleanHist p c E rho (timeIdx rho b₀))
    (htransfer : ∀ y z s C H, y ∈ rho.honest → z ∈ rho.honest →
      joinedAt p E rho z (s + 1) (SA.voteTime p.toParams (s + 1)) →
      SA.gateTime p.toParams s ≤ b₀ → gateResult p c E rho y s = some (some C) →
      vHead p c E rho z s = some H → Block.Preceq C H)
    (hprov : ArmingJoinedProvenance (c := c) E rho)
    {x : V} {B : Block}
    (hread : Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x T))
    (hne : B ≠ .genesis) :
    ∃ D Dh, ArmingSleepGateCert p c E rho true T b₀ B
      (((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat) D Dh := by
  classical
  let l := (((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat)
  have hs := h.pre.base.valid.toScheduleWellFormed
  by_cases hLast : ∃ C, (l, C) ∈ cleanResults p c E rho (timeIdx rho b₀)
  · obtain ⟨D, Dh, hc⟩ := fast_arming_on h hf hsrc htsrc hState hHist htransfer hread hne hLast
    exact ⟨D, Dh, arming_sleep_gate_cert_of_last hc
      (fun z hz hJ k hk => arming_head_ge_on hs htransfer hc.max_mem hz hJ hk)⟩
  obtain ⟨r, C, hr, hOrigin, hTime, hBC⟩ :=
    arming_protected_origin_on hs h.order.2.1 hState hHist hread hne
  have h6 : 6 * p.Δ ≤ b₀ := by
    have hg := (arming_gate_le_iff p 0 r).mpr (Nat.zero_le r)
    simpa only [arming_gate_eq, Nat.cast_zero, mul_zero, zero_add] using
      hg.trans (hTime.trans h.order.2.1)
  have hl := (arming_label p b₀ h6).1
  have hgap := arming_fast_gap p r T b₀ hTime h.lag
  have hlpos : 1 ≤ l := by dsimp only [l, Slot] at *; omega
  have hq : l - 1 + 1 = l := Nat.sub_add_cancel hlpos
  have hqcut : SA.gateTime p.toParams (l - 1) < b₀ :=
    ((arming_gate_lt_iff p _ l).mpr (by dsimp only [Slot] at *; omega)).trans_le hl
  obtain ⟨z, i, hG⟩ := arming_joined_gate_before h.sleepPre (l - 1) hqcut
  have hiCut := arming_lt_of_tick hs hG.1 hqcut.le
  obtain ⟨D₀, hD₀, _⟩ := hHist.nonempty i z (l - 1) hiCut hG
  have hD₀mem : (l - 1, D₀) ∈ cleanResults p c E rho (timeIdx rho b₀) :=
    ⟨i, hiCut, z, hG.1, hG.2, hD₀⟩
  obtain ⟨D, hD, hmax⟩ := arming_last_max_on hHist hD₀mem
  obtain ⟨Dh, hDh⟩ := arming_sleep_comparison_lift hs hD
  have hBD : Block.Preceq B D := block_preceq_trans hBC
    (hmax r C hOrigin (by dsimp only [l, Slot] at *; omega))
  have hDne : D ≠ .genesis := by
    intro hg
    exact hne (block_preceq_antisymm (hg ▸ hBD) (block_genesis_preceq B))
  have hmax' : ∀ r C, (r, C) ∈ cleanResults p c E rho (timeIdx rho b₀) → r ≤ l →
      Block.Preceq C D := by
    intro r C hC hrl
    have hrne : r ≠ l := fun he => hLast ⟨C, he ▸ hC⟩
    exact hmax r C hC (by dsimp only [Slot] at *; omega)
  refine ⟨D, Dh, arming_fast_cert_of_comparison h hf hsrc htsrc hState hHist hread hne
    rfl hDh ⟨l - 1, Nat.sub_le _ _, hD⟩ hBD hmax' ?_⟩
  intro y hy hJ k hk
  have hHeads := arming_joined_head_from_previous (i := k) h hf hsrc hState htransfer hprov
    hDh hD hDne (by rw [hq]; exact hl) hmax hy
  have heq : l - 1 + 2 = l + 1 := by dsimp only [Slot] at *; omega
  rw [heq] at hHeads
  exact hHeads hk hJ

/-- The slow producer supplies the general certificate and its joined HEAD bounds. -/
theorem slow_arming_scoped_on [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c false E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (htsrc : TSrc p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hHist : CleanHist p c E rho (timeIdx rho b₀))
    (htransfer : ∀ y z s C H, y ∈ rho.honest → z ∈ rho.honest →
      joinedAt p E rho z (s + 1) (SA.voteTime p.toParams (s + 1)) →
      SA.gateTime p.toParams s ≤ b₀ → gateResult p c E rho y s = some (some C) →
      vHead p c E rho z s = some H → Block.Preceq C H)
    (hSaved : ∀ {x : V} {q : Slot} {B : Block}, x ∈ rho.honest →
      SA.gateTime p.toParams q ≤ b₀ →
      AwakeClosed E x (slotStartZ p (q : Int)) b₀ →
      RestartFreeTime rho x (slotStartZ p (q : Int)) b₀ →
      (B = .genesis ∨ ∃ r C, r < q ∧
        (r, C) ∈ cleanResults p c E rho (timeIdx rho b₀) ∧ Block.Preceq B C) →
      Block.Preceq B (F_at p c E rho (timeIdx rho b₀) x) ∨
        ∃ C, GridCO.savedGenuine (storeAt p c E rho (timeIdx rho b₀) x).base q =
          some (some C) ∧ Block.Preceq B C)
    {x : V} {B : Block}
    (hread : Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x T))
    (hne : B ≠ .genesis)
    {y : V} (hyG : y ∈ coveredNodes p E rho false b₀) :
    ∃ D Dh, ArmingSleepGateCert p c E rho false T b₀ B
      (((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat) D Dh := by
  obtain ⟨D, Dh, hc⟩ := slow_arming_on h hf hsrc htsrc hState hHist htransfer hSaved
    hread hne hyG
  exact ⟨D, Dh, arming_sleep_gate_cert_of_last hc
    (fun z hz hJ k hk => arming_head_ge_on h.pre.base.valid.toScheduleWellFormed
      htransfer hc.max_mem hz hJ hk)⟩

end AvailableChain.FGSA.Run
end

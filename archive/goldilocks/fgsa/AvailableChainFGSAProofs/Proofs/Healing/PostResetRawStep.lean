module
public import AvailableChainFGSAProofs.Proofs.Healing.OpeningTicks
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetLeaseStep
public import AvailableChainFGSAProofs.Proofs.Healing.ReleaseScope
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetJoint

public section

/-! Blueprint 21 H.16:2924–2945, H.1:663–708, H.2:709–746;
plan J5-A-2; B1/B13/B17/B18. DC: SAME raw-result transfer.
First HEADs use the written-domain producer and the raw release proof.
The moving-domain guard uses the exact named J4A2-2 input. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private theorem rawStep_result_tick {y : V} {j : Slot} {C : Block}
    (hC : gateResult p c E rho y j = some (some C)) :
    ∃ k, IsGateTick p c rho k y j := by
  rw [gateResult_def, gateIn_def, preTick_def] at hC
  cases hk : V2.D.Run.tickIdx? rho y (SA.gateTime p.toParams j) with
  | none => rw [hk] at hC; cases hC
  | some k => exact ⟨k, V2.D.Run.tickIdx?_spec hk⟩

private theorem rawStep_result_mem (hs : V2.D.ScheduleWellFormed E rho)
    {ix : Nat} {x : V} {s : Slot} {C : Block}
    (hix : IsGateTick p c rho ix x s)
    (hres : gateResultAt p c E rho ix = some (some C)) :
    C ∈ (actView (clockPre p (storeAt p c E rho ix x)
      (SA.gateTime p.toParams s))).blocks := by
  have hconf := (gateResultAt_eq_gateResult p c E rho hs hix).symm.trans hres
  have hc := (fgsa_gate_raw_of_nonempty p c E rho hs hix hconf).2
  have hstore := cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho ix x)
    (SA.gateTime p.toParams s)
  have hm := compat_of_confirmation p _ hstore hc
  exact (actView_blocks _ C).mpr ⟨hm.2, hm.1⟩

private theorem rawStep_frozen_geometry [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {iy : Nat} {y : V} {s : Slot}
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

private theorem rawStep_proposals_at_gate_cut (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {s : Slot} {C : Block} (hi : IsGateTick p c rho i x s) :
    ∀ v Q, s + 2 ≤ v → timeIdx rho (SA.proposalTime p.toParams v) ≤ i + 1 →
      HonestProposal E rho (fgsaInterface p c) v Q → Block.Preceq C Q.parent := by
  intro v Q hsv hcut hp
  obtain ⟨_, o, ⟨ip, hip, _⟩, _⟩ := hp
  rw [proposalTime_fgsa p c v] at hip
  have hii : i < ip := healing_idx_lt_of_time_lt p c E rho hs hi hip (by
    change 4 * p.Δ * (s : Int) + 6 * p.Δ < 4 * p.Δ * (v : Int)
    have hh : (s : Int) + 2 ≤ v := by exact_mod_cast hsv
    nlinarith [p.deltaPos])
  have hpc : ip < timeIdx rho (SA.proposalTime p.toParams v) :=
    (V2.D.Engine.index_lt_read_length_iff hs _ hip).mpr le_rfl
  exact False.elim (Nat.not_lt_of_ge hcut (Nat.succ_le_of_lt hii |>.trans_lt hpc))

private theorem rawStep_outputs_at_gate_cut (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {s : Slot} {C : Block} (hi : IsGateTick p c rho i x s) :
    ∀ a y, a < i + 1 → y ∈ rho.honest → SA.gateTime p.toParams s + 4 * p.Δ ≤ rho.horizon →
      HealSuffix p c rho (SA.gateTime p.toParams s + 4 * p.Δ) a →
      Block.Preceq C (S_at p c E rho a y) := by
  intro a y hacut _hy _hhor hsuffix
  have htime : SA.gateTime p.toParams s + 4 * p.Δ = SA.gateTime p.toParams (s + 1) := by
    change 4 * p.Δ * (s : Int) + 6 * p.Δ + 4 * p.Δ =
      4 * p.Δ * ((s + 1 : Nat) : Int) + 6 * p.Δ
    push_cast
    ring
  rw [htime] at hsuffix
  delta HealSuffix healStart at hsuffix
  rw [(isGateTime_iff p _).mpr ⟨s + 1, rfl⟩, ite_eq_left rfl] at hsuffix
  have hlt : i < V2.D.Run.idxBefore rho (SA.gateTime p.toParams (s + 1)) :=
    (Gen.V2.Duty.index_lt_idxBefore_iff hs hi _).mpr (by
      change 4 * p.Δ * (s : Int) + 6 * p.Δ < 4 * p.Δ * ((s + 1 : Nat) : Int) + 6 * p.Δ
      push_cast
      linarith [p.deltaPos])
  have hpre : V2.D.Run.idxBefore rho (SA.gateTime p.toParams (s + 1)) ≤
      afterTicksIdx rho (SA.gateTime p.toParams (s + 1)) := by
    rw [V2.D.Run.idxBefore_def]
    exact (preIdx_le_afterTicksIdx E rho hs _).1
  exact False.elim (Nat.not_lt_of_ge (Nat.le_of_lt_succ hacut)
    (hlt.trans_le (hpre.trans hsuffix.1)))

variable [Fintype V] {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
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
    (mono : RMonoAll p c E rho) (source : TSrc p c E rho)
    (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    {w : HealingWitness} (h0r : H0Reset p c E rho w)

include hrec emittedNonempty emittedName writes mono source xing origin h0r

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.16:2938–2944, H.1:673–700; plan J5-A-2 R1;
B1/B13/B17/B18. DC: SAME first HEAD above the reset block.
No write key, fast threshold or passed-gate premise is required. -/
theorem postReset_raw_first_head_above
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    (hresetNext : PostResetResetLeaseCompatible p c E rho w (i + 1))
    (hleaseNext : PostResetLeaseSafe p c E rho w (i + 1))
    {ix : Nat} {x : V} {s : Slot} {C : Block} (hx : x ∈ rho.honest)
    (hlabel : w.sStar ≤ s) (hix : IsGateTick p c rho ix x s) (hxi : ix ≤ i)
    (hres : gateResultAt p c E rho ix = some (some C))
    (hCB : Block.Preceq w.CStar C)
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1)))) :
    Block.Preceq C (headAtIdx p c E rho iy (s + 1)) := by
  have hs := hrec.base.valid.toScheduleWellFormed
  have hmem := rawStep_result_mem p c E rho hs hix hres
  have hstore := cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho ix x)
    (SA.gateTime p.toParams s)
  obtain ⟨B, -, heB⟩ := hstore.baseTree C |>.mp ((actView_blocks _ C).mp hmem).1
  rw [← heB] at hCB hmem ⊢
  by_cases hZ : FGBlock.Preceq B (R_at p c E rho iy y).Z
  · exact healing_head_covers_root p c E rho hiy (l := s + 1) (Nat.succ_ne_zero s) (Or.inl hZ)
  by_cases hF : FGBlock.Preceq B (storeAt p c E rho iy y).fg.F
  · exact healing_head_covers_root p c E rho hiy (l := s + 1) (Nat.succ_ne_zero s) (Or.inr hF)
  have hyx : iy < ix := healing_idx_lt_of_time_lt p c E rho hs hiy hix (by
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ
    push_cast
    linarith [p.deltaPos])
  have hD := postReset_written_domain p c E rho hrec mono source emittedNonempty emittedName
    writes xing origin h0r hinv hx hix hres
    hCB hmem (heB ▸ Gen.Pure.block_preceq_refl C) hy hiy (hyx.le.trans hxi) hZ hF
  obtain ⟨hXv, hXc⟩ := rawStep_frozen_geometry p c E rho hrec hiy
    (healing_recovery_epoch_after_vote E rho hrec hy
      (by
        have hh : (w.sStar : Int) ≤ s := by exact_mod_cast hlabel
        have ht : SA.voteTime p.toParams w.sStar ≤ SA.voteTime p.toParams s := by
          change 4 * p.Δ * (w.sStar : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + p.Δ
          nlinarith [p.deltaPos]
        exact h0r.synchronous.trans ht)
      (by change 4 * p.Δ * (s : Int) + p.Δ < 4 * p.Δ * (s : Int) + 3 * p.Δ
          linarith [p.deltaPos]) _)
  have hgst := postReset_written_sync p c E rho hrec h0r hx hix hCB hmem
  have hq : SA.releaseTime p.toParams s = SA.voteTime p.toParams (s + 1) := by
    change 4 * p.Δ * (s : Int) + 5 * p.Δ = 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast
    ring
  have hread : postClock E rho y (SA.releaseTime p.toParams s) =
      some ((fgsa p c).clock (V2.D.Run.stateBefore E rho iy y)
        (SA.voteTime p.toParams (s + 1))) := by
    rw [hq, postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hs hiy]
    rfl
  have hreset : PostResetResetLeaseCompatible p c E rho w (i + 1) := by
    exact hresetNext
  have hrows := postReset_raw_release_compatible p c E rho hrec
    (healing_raw_service_scope_recovery E rho hrec mono) emittedNonempty emittedName
    writes h0r hinv hreset hleaseNext hx hlabel hix
    ((gateResultAt_eq_gateResult p c E rho hs hix).symm.trans hres) hxi hy hread
  have hlease : ∀ row ∈ (FGSA.clock p (storeAt p c E rho iy y)
      (SA.voteTime p.toParams (s + 1))).base.obligations, Block.Compatible row.1 C := by
    intro row hr
    apply hrows row hr
    have hm := healing_release_rows_expiry (storeAt p c E rho iy y) s row hr
    change row ∈ (GridCO.expire { (storeAt p c E rho iy y).base with
      now := SA.releaseTime p.toParams s } (SA.releaseTime p.toParams s)).obligations at hm
    change (clock p (storeAt p c E rho iy y)
      (SA.voteTime p.toParams (s + 1))).base.now < row.2.2
    rw [(clock_vn _ _).2, ← hq]
    exact of_decide_eq_true (List.mem_filter.mp hm).2
  rw [heB]
  exact healing_first_transfer_raw_domain p c E rho hrec
    (healing_raw_service_scope_recovery E rho hrec mono) hgst.le hx hix hres heB hy hiy
    (healing_first_transfer_scope_recovery E rho hrec mono hgst.le hx hy hix hiy
      (healing_gate_enabled_of_result E rho hs hix hres)
      (healing_recovery_joined E rho hrec hy
        ((postReset_written_window p c E rho hrec h0r hx hix hCB hmem).cut_mono
          (Nat.le_succ s)).2
        (by apply hgst.le.trans
            change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
            push_cast; linarith [p.deltaPos])
        (hs.in_horizon _ (List.mem_of_getElem? hiy)).2)).receiverGuard
    hXv hXc (by
      dsimp only [D_at] at hD ⊢
      simpa only [healing_domain_filter_F] using hD) hlease

private theorem rawStep_reset_first_head
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (w.sStar + 1))))
    (hyi : iy ≤ i) : Block.Preceq w.CStar (headAtIdx p c E rho iy (w.sStar + 1)) := by
  have hs := hrec.base.valid.toScheduleWellFormed
  obtain ⟨_, x0, _, B, ha, -, hsource, heB, -⟩ := h0r.fresh
  obtain ⟨-, C0, -, hG0, hBC, pre, hpre, hτ⟩ :=
    healing_source_decode p c E rho emittedNonempty emittedName ha hsource
  rw [← h0r.label] at hG0 hpre hτ
  obtain ⟨ix, hix⟩ := rawStep_result_tick p c E rho hG0
  have hpreEq : pre = clockPre p (storeAt p c E rho ix x0)
      (SA.gateTime p.toParams w.sStar) :=
    Option.some.inj (hpre.symm.trans (healing_support_gate_reads p c E rho hs hix).1)
  subst pre
  have hres := (gateResultAt_eq_gateResult p c E rho hs hix).trans hG0
  have hmem := actView_ancestor_closed p _
    (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho ix x0) _)
    (rawStep_result_mem p c E rho hs hix hres) hBC
  rw [← heB]
  by_cases hZ : FGBlock.Preceq B (R_at p c E rho iy y).Z
  · exact healing_head_covers_root p c E rho hiy (l := w.sStar + 1)
      (Nat.succ_ne_zero w.sStar) (Or.inl hZ)
  by_cases hF : FGBlock.Preceq B (storeAt p c E rho iy y).fg.F
  · exact healing_head_covers_root p c E rho hiy (l := w.sStar + 1)
      (Nat.succ_ne_zero w.sStar) (Or.inr hF)
  have hD := postReset_written_domain p c E rho hrec mono source emittedNonempty emittedName
    writes xing origin h0r hinv ha.1 hix hres
    (heB ▸ Gen.Pure.block_preceq_refl w.CStar) hmem hBC hy hiy hyi hZ hF
  obtain ⟨hXv, hXc⟩ := rawStep_frozen_geometry p c E rho hrec hiy
    (healing_recovery_epoch_after_vote E rho hrec hy h0r.synchronous
      (by change 4 * p.Δ * (w.sStar : Int) + p.Δ <
            4 * p.Δ * (w.sStar : Int) + 3 * p.Δ
          linarith [p.deltaPos]) _)
  exact healing_first_transfer_written p c E rho hrec mono writes ha.1 hix hres hBC
    h0r.synchronous
    (healing_window_of_cut E (healing_ready_vote_cutoff E (healing_reset_source_ready h0r)))
    (Or.inl hτ) hy hiy (healing_gate_enabled_of_result E rho hs hix hres)
    (healing_recovery_joined E rho hrec hy
      (healing_window_of_cut E (healing_ready_vote_cutoff E
        (healing_reset_source_ready h0r)) |>.cut_mono (Nat.le_succ w.sStar)).2
      (by apply h0r.synchronous.trans
          change 4 * p.Δ * (w.sStar : Int) + p.Δ ≤
            4 * p.Δ * ((w.sStar + 1 : Nat) : Int) + p.Δ
          push_cast; linarith [p.deltaPos])
      (hs.in_horizon _ (List.mem_of_getElem? hiy)).2) hXv hXc (by
      dsimp only [D_at] at hD ⊢
      simpa only [healing_domain_filter_F] using hD)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.16:2930–2944, H.1:663–708; plan J5-A-2 R1;
B1/B13/B17/B18. DC: SAME first HEAD for every raw result.
P1 excludes conflicts with CStar. Below CStar, use the reset's first
HEAD or its prior raw-transfer clause. Above it, use the frozen domain. -/
theorem postReset_raw_first_head
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    (hresetNext : PostResetResetLeaseCompatible p c E rho w (i + 1))
    (hleaseNext : PostResetLeaseSafe p c E rho w (i + 1))
    {ix : Nat} {x : V} {s : Slot} {C : Block} (hx : x ∈ rho.honest)
    (hlabel : w.sStar ≤ s) (hix : IsGateTick p c rho ix x s) (hxi : ix ≤ i)
    (hres : gateResultAt p c E rho ix = some (some C))
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1)))) :
    Block.Preceq C (headAtIdx p c E rho iy (s + 1)) := by
  have hs := hrec.base.valid.toScheduleWellFormed
  have hcompat := postReset_raw_reset_compatible p c E rho hrec
    (healing_raw_service_scope_recovery E rho hrec mono) emittedNonempty emittedName
    h0r hinv hx hlabel hix hres hxi
  rcases Bool.or_eq_true_iff.mp hcompat with hbelow | habove
  · exact postReset_raw_first_head_above p c E rho hrec emittedNonempty emittedName writes
      mono source xing origin h0r hinv hresetNext hleaseNext hx hlabel hix hxi hres hbelow hy hiy
  · apply Gen.Pure.block_preceq_trans habove
    have hyx : iy < ix := healing_idx_lt_of_time_lt p c E rho hs hiy hix (by
      change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ
      push_cast
      linarith [p.deltaPos])
    rcases eq_or_lt_of_le hlabel with he | hlt
    · subst s
      exact rawStep_reset_first_head p c E rho hrec emittedNonempty emittedName writes mono source
        xing origin h0r hinv hy hiy (hyx.le.trans hxi)
    · obtain ⟨_, x0, _, B0, ha, -, hsource, heB, -⟩ := h0r.fresh
      obtain ⟨-, C0, -, hG0, hBC, -⟩ :=
        healing_source_decode p c E rho emittedNonempty emittedName ha hsource
      rw [← h0r.label] at hG0
      obtain ⟨k0, hk0⟩ := rawStep_result_tick p c E rho hG0
      have hk0i : k0 < i := (healing_idx_lt_of_time_lt p c E rho hs hk0 hix (by
        change 4 * p.Δ * (w.sStar : Int) + 6 * p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ
        have hh : (w.sStar : Int) < s := by exact_mod_cast hlt
        nlinarith [p.deltaPos])).trans_le hxi
      have hread : headAtLabel p c E rho y (s + 1) =
          some (headAtIdx p c E rho iy (s + 1)) := by
        rw [healing_headAtIdx_tick p c E rho hiy]
        delta headAtLabel
        rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hs hiy]
        rfl
      have hcut : timeIdx rho (SA.voteTime p.toParams (s + 1)) ≤ i := by
        by_contra hn
        have ht := (V2.D.Engine.index_lt_read_length_iff hs _ hix).mp
          (hxi.trans_lt (Nat.lt_of_not_ge hn))
        change 4 * p.Δ * (s : Int) + 6 * p.Δ ≤
          4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ at ht
        push_cast at ht
        linarith [p.deltaPos]
      have hraw := hinv.raw_transfer
      rw [PostResetRawTransfer_def] at hraw
      exact Gen.Pure.block_preceq_trans (heB ▸ hBC)
        ((hraw k0 hk0i x0 w.sStar C0 ha.1 le_rfl hk0 hG0).2.1 y (s + 1) _ hy
          (Nat.succ_le_succ hlabel) hcut hread)


/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.16:2938–2944, H.1:663–708; plan J5-A-2 R1 label;
B1/B13/B17/B18. DC: SAME first HEAD through its complete label read. -/
theorem postReset_raw_first_head_label
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    (hresetNext : PostResetResetLeaseCompatible p c E rho w (i + 1))
    (hleaseNext : PostResetLeaseSafe p c E rho w (i + 1))
    {ix : Nat} {x : V} {s : Slot} {C : Block} (hx : x ∈ rho.honest)
    (hlabel : w.sStar ≤ s) (hix : IsGateTick p c rho ix x s) (hxi : ix ≤ i)
    (hres : gateResultAt p c E rho ix = some (some C))
    {y : V} {H : Block} (hy : y ∈ rho.honest)
    (hhead : headAtLabel p c E rho y (s + 1) = some H) : Block.Preceq C H := by
  delta headAtLabel at hhead
  rw [postClock_def, preTick_def] at hhead
  cases ht : V2.D.Run.tickIdx? rho y (SA.voteTime p.toParams (s + 1)) with
  | none => rw [ht] at hhead; cases hhead
  | some iy =>
    have hiy := V2.D.Run.tickIdx?_spec ht
    have heH : headAtIdx p c E rho iy (s + 1) = H := by
      rw [healing_headAtIdx_tick p c E rho hiy]
      rw [ht] at hhead
      exact Option.some.inj hhead
    rw [← heH]
    exact postReset_raw_first_head p c E rho hrec emittedNonempty emittedName writes mono source
      xing origin h0r hinv hresetNext hleaseNext hx hlabel hix hxi hres hy hiy

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.16:2940–2944; plan J5-A-2 R3 new-source HEAD;
B1/B13/B17/B18. DC: SAME HEAD clause at the source event's successor cut.
Only the first label can have an actual complete HEAD cut at i+1. -/
theorem postReset_raw_heads_at_gate_cut
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    (hresetNext : PostResetResetLeaseCompatible p c E rho w (i + 1))
    (hleaseNext : PostResetLeaseSafe p c E rho w (i + 1))
    {x : V} {s : Slot} {C : Block} (hx : x ∈ rho.honest)
    (hlabel : w.sStar ≤ s) (hi : IsGateTick p c rho i x s)
    (hres : gateResultAt p c E rho i = some (some C)) :
    ∀ y l H, y ∈ rho.honest → s + 1 ≤ l →
      timeIdx rho (SA.voteTime p.toParams l) ≤ i + 1 →
      headAtLabel p c E rho y l = some H → Block.Preceq C H := by
  intro y l H hy hsl hcut hhead
  rcases eq_or_lt_of_le hsl with rfl | hlt
  · exact postReset_raw_first_head_label p c E rho hrec emittedNonempty emittedName writes
      mono source xing origin h0r hinv hresetNext hleaseNext hx hlabel hi le_rfl hres hy hhead
  · delta headAtLabel at hhead
    rw [postClock_def, preTick_def] at hhead
    cases ht : V2.D.Run.tickIdx? rho y (SA.voteTime p.toParams l) with
    | none => rw [ht] at hhead; cases hhead
    | some iy =>
      have hiy := V2.D.Run.tickIdx?_spec ht
      have hyi : iy < timeIdx rho (SA.voteTime p.toParams l) :=
        (V2.D.Engine.index_lt_read_length_iff hrec.base.valid.toScheduleWellFormed _ hiy).mpr
          le_rfl
      have hii : i < iy := healing_idx_lt_of_time_lt p c E rho
        hrec.base.valid.toScheduleWellFormed hi hiy (by
          change 4 * p.Δ * (s : Int) + 6 * p.Δ < 4 * p.Δ * (l : Int) + p.Δ
          have hh : (s : Int) + 2 ≤ l := by exact_mod_cast (show s + 2 ≤ l from hlt)
          nlinarith [p.deltaPos])
      exact False.elim (Nat.not_lt_of_ge hcut (Nat.succ_le_of_lt hii |>.trans_lt hyi))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.16:2924–2945; plan J5-A-2 R3 new-source package;
B1/B13/B17/B18. DC: SAME all four raw clauses for the source at event i.
Later proposals and output suffixes cannot be readers at this cut.
This does not extend old raw results across their boundary readers. -/
theorem postReset_raw_at_gate_cut
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    (hresetNext : PostResetResetLeaseCompatible p c E rho w (i + 1))
    (hleaseNext : PostResetLeaseSafe p c E rho w (i + 1))
    {x : V} {s : Slot} {C : Block} (hx : x ∈ rho.honest)
    (hlabel : w.sStar ≤ s) (hi : IsGateTick p c rho i x s)
    (hres : gateResult p c E rho x s = some (some C)) :
    (∀ y nd, y ∈ rho.honest → timeIdx rho (SA.releaseTime p.toParams s) ≤ i + 1 →
      postClock E rho y (SA.releaseTime p.toParams s) = some nd →
      ∀ row ∈ nd.st.base.obligations, nd.st.base.now < row.2.2 → Block.Compatible row.1 C) ∧
    (∀ y l H, y ∈ rho.honest → s + 1 ≤ l →
      timeIdx rho (SA.voteTime p.toParams l) ≤ i + 1 →
      headAtLabel p c E rho y l = some H → Block.Preceq C H) ∧
    (∀ v Q, s + 2 ≤ v → timeIdx rho (SA.proposalTime p.toParams v) ≤ i + 1 →
      HonestProposal E rho (fgsaInterface p c) v Q → Block.Preceq C Q.parent) ∧
    (∀ a y, a < i + 1 → y ∈ rho.honest → SA.gateTime p.toParams s + 4 * p.Δ ≤ rho.horizon →
      HealSuffix p c rho (SA.gateTime p.toParams s + 4 * p.Δ) a →
      Block.Preceq C (S_at p c E rho a y)) := by
  have hs := hrec.base.valid.toScheduleWellFormed
  refine ⟨?_, ?_, rawStep_proposals_at_gate_cut p c E rho hs hi,
    rawStep_outputs_at_gate_cut p c E rho hs hi⟩
  · intro y nd hy _hcut hnd
    have hreset : PostResetResetLeaseCompatible p c E rho w (i + 1) := by
      exact hresetNext
    exact postReset_raw_release_compatible p c E rho hrec
      (healing_raw_service_scope_recovery E rho hrec mono) emittedNonempty emittedName writes
      h0r hinv hreset hleaseNext hx hlabel hi hres le_rfl hy hnd
  · exact postReset_raw_heads_at_gate_cut p c E rho hrec emittedNonempty emittedName writes
      mono source xing origin h0r hinv hresetNext hleaseNext hx hlabel hi
      ((gateResultAt_eq_gateResult p c E rho hs hi).trans hres)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.2:723–726,736–746; plan J5-A-2 R2 domain;
B1/B13/B17/B18. DC: SAME moving reader's frozen-domain guard.
This specializes J4A2-2 G2. The live-lease guard is proved in
PostResetRaw.lean by postReset_raw_moving_lease_compat. -/
theorem postReset_raw_moving_domain
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    {l : Slot} {B : FGBlock (Fin p.n)} (hgst : E.t_GST ≤ SA.voteTime p.toParams l)
    (hCB : Block.Preceq w.CStar (eraseFG B))
    (hbatch : ∀ z ∈ rho.honest, ∀ H, headAtLabel p c E rho z l = some H →
      Block.Preceq (eraseFG B) H)
    {iy : Nat} {y : V} {t : Time} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y t)) (hyi : iy ≤ i)
    (hafter : SA.freezeTime p.toParams l < t)
    (hupper : t ≤ SA.voteTime p.toParams (l + 1))
    (hnZ : ¬ FGBlock.Preceq B (R_at p c E rho iy y).Z)
    (hnF : ¬ FGBlock.Preceq B (storeAt p c E rho iy y).fg.F) :
    B ∈ D_at p c E rho iy y
      (storeAt p c E rho (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams l)) y).fg.TF := by
  have hcut := healing_support_idxBefore_le p c E rho hrec.base.valid.toScheduleWellFormed
    hiy hafter.le
  have hX := (fgsa_store_durable p c E rho hcut y).1
  exact postReset_moving_domain p c E rho hrec mono source emittedNonempty emittedName
    writes xing origin h0r hinv hgst hCB hbatch hy hiy hyi hafter hupper hX (Finset.Subset.refl _)
    hnZ hnF

omit writes source origin in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.16:2933–2938; plan J5-A-2 reset-lease adapter;
B1/B13/B17/B18. DC: INTENTIONAL; DC has no leases.
The existing C2 producer closes the joint step itself for every i. -/
theorem postReset_resetLease_succ_all (cap : RCap p c E rho) (source : TSrc p c E rho) :
    ∀ i, PostResetResetLeaseStep p c E rho w i := by
  intro i
  rw [PostResetResetLeaseStep_def]
  intro hprev
  have hreset : PostResetResetLeaseCompatible p c E rho w i := by
    exact hprev.2.1
  rw [PostResetResetLeaseCompatible_def]
  have hn := postReset_resetLease_succ p c E rho hrec
    (healing_raw_service_scope_recovery E rho hrec mono) emittedNonempty emittedName xing cap
    source h0r hprev.1 hreset
  rwa [PostResetResetLeaseCompatible_def] at hn


/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.16:2940–2944, H.2:723–726; plan J5-A-3 R6 HEAD;
B1/B13/B17/B18. DC: SAME complete successor HEAD cut above CStar. -/
theorem postReset_raw_heads_succ_above
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    (hresetNext : PostResetResetLeaseCompatible p c E rho w (i + 1))
    (hleaseNext : PostResetLeaseSafe p c E rho w (i + 1))
    {ix : Nat} {x : V} {s : Slot} {C : Block} (hx : x ∈ rho.honest)
    (hlabel : w.sStar ≤ s) (hix : IsGateTick p c rho ix x s) (hxi : ix ≤ i)
    (hres : gateResultAt p c E rho ix = some (some C)) (hCB : Block.Preceq w.CStar C) :
    ∀ y l H, y ∈ rho.honest → s + 1 ≤ l →
      timeIdx rho (SA.voteTime p.toParams l) ≤ i + 1 →
      headAtLabel p c E rho y l = some H → Block.Preceq C H := by
  intro y l H hy hsl hcut hhead
  have hs := hrec.base.valid.toScheduleWellFormed
  rcases eq_or_lt_of_le hsl with rfl | hsl
  · exact postReset_raw_first_head_label p c E rho hrec emittedNonempty emittedName writes
      mono source xing origin h0r hinv hresetNext hleaseNext hx hlabel hix hxi hres hy hhead
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ((Nat.zero_lt_succ s).trans hsl))
  have hsl : s + 1 ≤ l := Nat.le_of_lt_succ hsl
  delta headAtLabel at hhead
  rw [postClock_def, preTick_def] at hhead
  cases ht : V2.D.Run.tickIdx? rho y (SA.voteTime p.toParams (l + 1)) with
  | none => rw [ht] at hhead; cases hhead
  | some iy =>
    have hiy := V2.D.Run.tickIdx?_spec ht
    have hyi : iy ≤ i := by
      have hc := (V2.D.Engine.index_lt_read_length_iff hs _ hiy).mpr le_rfl
      change iy < timeIdx rho (SA.voteTime p.toParams (l + 1)) at hc
      exact Nat.le_of_lt_succ (hc.trans_le hcut)
    have heH : headAtIdx p c E rho iy (l + 1) = H := by
      rw [healing_headAtIdx_tick p c E rho hiy]
      rw [ht] at hhead
      exact Option.some.inj hhead
    rw [← heH]
    have hxi' : ix < i := (healing_idx_lt_of_time_lt p c E rho hs hix hiy (by
      change 4 * p.Δ * (s : Int) + 6 * p.Δ <
        4 * p.Δ * ((l + 1 : Nat) : Int) + p.Δ
      have hh : (s : Int) + 1 ≤ l := by exact_mod_cast hsl
      push_cast
      nlinarith [p.deltaPos])).trans_le hyi
    have hprevCut : timeIdx rho (SA.voteTime p.toParams l) ≤ i := by
      apply le_trans ?_ hyi
      by_contra hn
      have ht' := (V2.D.Engine.index_lt_read_length_iff hs _ hiy).mp (Nat.lt_of_not_ge hn)
      change 4 * p.Δ * ((l + 1 : Nat) : Int) + p.Δ ≤
        4 * p.Δ * (l : Int) + p.Δ at ht'
      push_cast at ht'
      linarith [p.deltaPos]
    have hraw := hinv.raw_transfer
    rw [PostResetRawTransfer_def] at hraw
    have hbatch := fun z hz K hK => (hraw ix hxi' x s C hx hlabel hix
      ((gateResultAt_eq_gateResult p c E rho hs hix).symm.trans hres)).2.1
      z l K hz hsl hprevCut hK
    have hmem := rawStep_result_mem p c E rho hs hix hres
    obtain ⟨B, -, heB⟩ := (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho ix x)
      (SA.gateTime p.toParams s)).baseTree C |>.mp ((actView_blocks _ C).mp hmem).1
    rw [← heB] at hCB hbatch ⊢
    by_cases hZ : FGBlock.Preceq B (R_at p c E rho iy y).Z
    · exact healing_head_covers_root p c E rho hiy (Nat.succ_ne_zero l) (Or.inl hZ)
    by_cases hF : FGBlock.Preceq B (storeAt p c E rho iy y).fg.F
    · exact healing_head_covers_root p c E rho hiy (Nat.succ_ne_zero l) (Or.inr hF)
    have hgst : E.t_GST ≤ SA.voteTime p.toParams l := by
      apply h0r.synchronous.trans
      have hh : (w.sStar : Int) ≤ l := by
        exact_mod_cast (hlabel.trans (Nat.le_of_succ_le hsl))
      change 4 * p.Δ * (w.sStar : Int) + p.Δ ≤ 4 * p.Δ * (l : Int) + p.Δ
      nlinarith [p.deltaPos]
    have hafter : SA.freezeTime p.toParams l < SA.voteTime p.toParams (l + 1) := by
      change 4 * p.Δ * (l : Int) + 3 * p.Δ < 4 * p.Δ * ((l + 1 : Nat) : Int) + p.Δ
      push_cast
      linarith [p.deltaPos]
    have hD := postReset_raw_moving_domain p c E rho hrec emittedNonempty emittedName writes
      mono source xing origin h0r
      hinv hgst hCB hbatch hy hiy hyi hafter le_rfl hZ hF
    have hreset : PostResetResetLeaseCompatible p c E rho w (i + 1) := by
      exact hresetNext
    have hlease := postReset_raw_moving_lease_compat p c E rho hrec
      (healing_raw_service_scope_recovery E rho hrec mono) emittedNonempty emittedName
      writes h0r hinv hreset hx hlabel hix hxi hres hsl (heB ▸ hbatch) hy hiy hyi hafter le_rfl
    obtain ⟨hXv, hXc⟩ := rawStep_frozen_geometry p c E rho hrec hiy
      (healing_recovery_epoch_after_vote E rho hrec hy hgst
        (by change 4 * p.Δ * (l : Int) + p.Δ < 4 * p.Δ * (l : Int) + 3 * p.Δ
            linarith [p.deltaPos]) _)
    have hCut := (healing_window_of_cut E (healing_ready_vote_cutoff E
      (healing_reset_source_ready h0r))).cut_mono (hlabel.trans (Nat.le_of_succ_le hsl))
    have hJ := healing_recovery_joined E rho hrec hy (hCut.cut_mono (Nat.le_succ l)).2
      (by apply hgst.trans
          change 4 * p.Δ * (l : Int) + p.Δ ≤ 4 * p.Δ * ((l + 1 : Nat) : Int) + p.Δ
          push_cast; linarith [p.deltaPos])
      (hs.in_horizon _ (List.mem_of_getElem? hiy)).2
    exact healing_next_transfer_domain p c E rho hrec mono hgst hbatch hy hiy
      (healing_next_transfer_scope_recovery E rho hrec hCut hy hiy hJ) hCut hXv hXc (by
      dsimp only [D_at] at hD ⊢
      simpa only [healing_domain_filter_F] using hD) (heB ▸ hlease)

omit [Fintype V] hrec mono source emittedNonempty emittedName writes xing origin h0r in
private theorem rawStep_proposal_read
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
Blueprint 21 H.16:2940–2944, H.2:736–746; plan J5-A-3 R6 proposal;
B1/B13/B17/B18. DC: SAME successor proposal cut above CStar. -/
theorem postReset_raw_proposals_succ_above
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    (hresetNext : PostResetResetLeaseCompatible p c E rho w (i + 1))
    {ix : Nat} {x : V} {s : Slot} {C : Block} (hx : x ∈ rho.honest)
    (hlabel : w.sStar ≤ s) (hix : IsGateTick p c rho ix x s) (hxi : ix ≤ i)
    (hres : gateResultAt p c E rho ix = some (some C)) (hCB : Block.Preceq w.CStar C) :
    ∀ v Q, s + 2 ≤ v → timeIdx rho (SA.proposalTime p.toParams v) ≤ i + 1 →
      HonestProposal E rho (fgsaInterface p c) v Q → Block.Preceq C Q.parent := by
  intro v Q hsv hcut hp
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt ((Nat.zero_lt_succ (s + 1)).trans_le hsv))
  have hsl : s + 1 ≤ l := Nat.le_of_succ_le_succ hsv
  have hs := hrec.base.valid.toScheduleWellFormed
  have hmem := rawStep_result_mem p c E rho hs hix hres
  obtain ⟨B, -, heB⟩ := (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho ix x)
    (SA.gateTime p.toParams s)).baseTree C |>.mp ((actView_blocks _ C).mp hmem).1
  rw [← heB] at hCB hres ⊢
  obtain ⟨ip, hip, hpar⟩ := rawStep_proposal_read p c E rho hp
  have hpi : ip ≤ i := by
    have hlt := (V2.D.Engine.index_lt_read_length_iff hs _ hip).mpr le_rfl
    change ip < timeIdx rho (SA.proposalTime p.toParams (l + 1)) at hlt
    exact Nat.le_of_lt_succ (hlt.trans_le hcut)
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
  have hgst : E.t_GST ≤ SA.voteTime p.toParams l := by
    apply h0r.synchronous.trans
    have hh : (w.sStar : Int) ≤ l := by exact_mod_cast (hlabel.trans (Nat.le_of_succ_le hsl))
    change 4 * p.Δ * (w.sStar : Int) + p.Δ ≤ 4 * p.Δ * (l : Int) + p.Δ
    nlinarith [p.deltaPos]
  have hxcut : ix < i := (healing_idx_lt_of_time_lt p c E rho hs hix hip (by
    change 4 * p.Δ * (s : Int) + 6 * p.Δ < 4 * p.Δ * ((l + 1 : Nat) : Int)
    have hh : (s : Int) + 1 ≤ l := by exact_mod_cast hsl
    push_cast
    nlinarith [p.deltaPos])).trans_le hpi
  have hprevCut : timeIdx rho (SA.voteTime p.toParams l) ≤ i := by
    apply le_trans ?_ hpi
    by_contra hn
    have ht := (V2.D.Engine.index_lt_read_length_iff hs _ hip).mp (Nat.lt_of_not_ge hn)
    change 4 * p.Δ * ((l + 1 : Nat) : Int) ≤ 4 * p.Δ * (l : Int) + p.Δ at ht
    push_cast at ht
    linarith [p.deltaPos]
  have hraw := hinv.raw_transfer
  rw [PostResetRawTransfer_def] at hraw
  have hbatch := fun z hz K hK => (hraw ix hxcut x s (eraseFG B) hx hlabel hix
    ((gateResultAt_eq_gateResult p c E rho hs hix).symm.trans hres)).2.1
    z l K hz hsl hprevCut hK
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
    (healing_window_of_cut E (healing_ready_vote_cutoff E
      (healing_reset_source_ready h0r)) |>.cut_mono
        (hlabel.trans (Nat.le_of_succ_le hsl))).2 hbatch hp
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
    have hreset : PostResetResetLeaseCompatible p c E rho w (i + 1) := by
      exact hresetNext
    exact postReset_raw_moving_lease_compat p c E rho hrec
      (healing_raw_service_scope_recovery E rho hrec mono) emittedNonempty emittedName writes
      h0r hinv hreset hx hlabel hix hxi hres hsl hbatch hy hip hpi hafter hupper

omit mono source emittedNonempty emittedName writes xing origin h0r in
private theorem rawStep_head_label {a : Nat} {z : V} {j : Slot}
    (ha : rho.events[a]? = some (.tick z (SA.voteTime p.toParams j))) :
    headAtLabel p c E rho z j = some (headAtIdx p c E rho a j) := by
  delta headAtLabel
  rw [postClock_def, preTick_def,
    fgsa_tickIdx_of_event p c E rho hrec.base.valid.toScheduleWellFormed ha]
  rw [healing_headAtIdx_tick p c E rho ha]
  rfl


/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.16:2940–2944, H.2:729–735; plan J5-A-3 R6 finality;
B1/B13/B17/B18. DC: SAME provenance and crossing proof at every state cut. -/
theorem postReset_raw_finality_compatible_above
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    (hresetNext : PostResetResetLeaseCompatible p c E rho w (i + 1))
    (hleaseNext : PostResetLeaseSafe p c E rho w (i + 1))
    {ix : Nat} {x : V} {s : Slot} {B : FGBlock (Fin p.n)} (hx : x ∈ rho.honest)
    (hlabel : w.sStar ≤ s) (hix : IsGateTick p c rho ix x s) (hxi : ix ≤ i)
    (hres : gateResultAt p c E rho ix = some (some (eraseFG B)))
    (hCB : Block.Preceq w.CStar (eraseFG B))
    {b : Nat} {y : V} (hbi : b ≤ i) (hy : y ∈ rho.honest) :
    Block.Compatible (F_at p c E rho b y) (eraseFG B) := by
  have hs := hrec.base.valid.toScheduleWellFormed
  have hmem := rawStep_result_mem p c E rho hs hix hres
  have hb := (actView_blocks _ _).mp hmem |>.1
  rw [(clockPre_fields p _ _).2.1] at hb
  obtain ⟨A, hA, heA⟩ := (cstoreInv_stateBefore E rho ix x).baseTree (eraseFG B) |>.mp hb
  have hBstore : B ∈ (storeAt p c E rho ix x).fg.TF := (eraseFG_injective heA) ▸ hA
  obtain ⟨-, -, -, Cfg, -, -, -, heC, hhC⟩ := h0r.fresh
  have hCBfg : FGBlock.Preceq Cfg B := eraseFG_preceq_iff.mp (by rwa [heC])
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
  have hheads := postReset_raw_heads_succ_above p c E rho hrec emittedNonempty emittedName
    writes mono source xing origin h0r hinv hresetNext hleaseNext hx hlabel hix hxi hres hCB
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
          (healing_window_of_cut E (healing_ready_vote_cutoff E
            (healing_reset_source_ready h0r)) |>.cut_mono hlabel).2 hx hix hres
      exact ⟨a, z, hz, ha, hCH, hr⟩
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
      have hawake := healing_vote_awake_of_recovery hrec.toRecovery₂ hx h0r.synchronous
        (hlabel.trans ((Nat.le_of_not_lt hr).trans (Nat.le_succ r)))
        (htime.le.trans ((hs.in_horizon _ (List.mem_of_getElem? hj)).2))
      obtain ⟨a, ha⟩ := healing_support_vote_tick E rho hs hrec.base.delta hx (r + 1)
        (htime.le.trans ((hs.in_horizon _ (List.mem_of_getElem? hj)).2)) hawake
      have hBH := hheads x (r + 1) _ hx (Nat.succ_le_succ (Nat.le_of_not_lt hr))
        (hcut.trans (hjb.le.trans (hbi.trans (Nat.le_succ i))))
        (rawStep_head_label p c E rho hrec ha)
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
Blueprint 21 H.16:2940–2944, H.2:729–735; plan J5-A-3 R6 gate;
B1/B13/B17/B18. DC: SAME stored leases at the first output gate.
Each row persists from the preceding vote tick, where R5 applies. -/
theorem postReset_raw_gate_lease_compat
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    (hresetNext : PostResetResetLeaseCompatible p c E rho w (i + 1))
    (hleaseNext : PostResetLeaseSafe p c E rho w (i + 1))
    {ix : Nat} {x : V} {s : Slot} {C : Block} (hx : x ∈ rho.honest)
    (hlabel : w.sStar ≤ s) (hix : IsGateTick p c rho ix x s) (hxi : ix ≤ i)
    (hres : gateResultAt p c E rho ix = some (some C))
    {j : Nat} {y : V} (hy : y ∈ rho.honest)
    (hj : IsGateTick p c rho j y (s + 1)) (hji : j ≤ i) :
    ∀ row ∈ (storeAt p c E rho j y).base.obligations, Block.Compatible row.1 C := by
  have hs := hrec.base.valid.toScheduleWellFormed
  have htime : SA.voteTime p.toParams (s + 1 + 1) < SA.gateTime p.toParams (s + 1) := by
    change 4 * p.Δ * ((s + 1 + 1 : Nat) : Int) + p.Δ <
      4 * p.Δ * ((s + 1 : Nat) : Int) + 6 * p.Δ
    push_cast
    linarith [p.deltaPos]
  have hawake := healing_vote_awake_of_recovery hrec.toRecovery₂ hy h0r.synchronous
    (hlabel.trans ((Nat.le_succ s).trans (Nat.le_succ (s + 1))))
    (htime.le.trans (hs.in_horizon _ (List.mem_of_getElem? hj)).2)
  obtain ⟨iq, hiq⟩ := healing_support_vote_tick E rho hs hrec.base.delta hy (s + 1 + 1)
    (htime.le.trans (hs.in_horizon _ (List.mem_of_getElem? hj)).2) hawake
  have hqj := healing_idx_lt_of_time_lt p c E rho hs hiq hj htime
  have hafter : SA.freezeTime p.toParams (s + 1) < SA.voteTime p.toParams (s + 1 + 1) := by
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + 3 * p.Δ <
      4 * p.Δ * ((s + 1 + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith [p.deltaPos]
  have hbatch : ∀ z ∈ rho.honest, ∀ H, headAtLabel p c E rho z (s + 1) = some H →
      Block.Preceq C H := fun z hz H hH => postReset_raw_first_head_label p c E rho hrec
    emittedNonempty emittedName writes mono source xing origin h0r hinv hresetNext hleaseNext
    hx hlabel hix hxi hres hz hH
  have hreset : PostResetResetLeaseCompatible p c E rho w (i + 1) := by
    exact hresetNext
  have hcompat := postReset_raw_moving_lease_compat p c E rho hrec
    (healing_raw_service_scope_recovery E rho hrec mono) emittedNonempty emittedName
    writes h0r hinv hreset hx hlabel hix hxi hres le_rfl hbatch hy hiq
    (hqj.le.trans hji) hafter le_rfl
  intro row hr
  obtain ⟨kw, hkw, q, D, hwrite, -, -, -, -, hdeadline, -, -⟩ := writes j y row hr
  have hql : q < s + 1 := by
    have ht := fgsa_tick_time_strict E rho hs hwrite hj hkw
    change 4 * p.Δ * (q : Int) + 6 * p.Δ <
      4 * p.Δ * ((s + 1 : Nat) : Int) + 6 * p.Δ at ht
    have h : (q : Int) < (s + 1 : Nat) := by nlinarith [p.deltaPos]
    exact_mod_cast h
  have hwq := healing_idx_lt_of_time_lt p c E rho hs hwrite hiq (by
    change 4 * p.Δ * (q : Int) + 6 * p.Δ <
      4 * p.Δ * ((s + 1 + 1 : Nat) : Int) + p.Δ
    have h : (q : Int) ≤ s := by exact_mod_cast Nat.le_of_lt_succ hql
    push_cast
    nlinarith [p.deltaPos])
  have hkeep := healing_lease_persist E rho hs hwrite (Nat.lt_succ_of_lt hwq)
    (Nat.succ_le_of_lt hqj) row hdeadline hr
  have hpost : storeAt p c E rho (iq + 1) y =
      FGSA.clock p (storeAt p c E rho iq y) (SA.voteTime p.toParams (s + 1 + 1)) := by
    change (V2.D.Run.stateBefore E rho (iq + 1) y).st = _
    rw [V2.D.Run.stateBefore_succ E rho hiq]
    simp only [V2.D.World.step, Function.update_self]
    exact tick_st (c := c) E rho _ y _
  exact hcompat row (hpost ▸ hkeep)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.16:2940–2944, H.2:729–735; plan J5-A-3 R6 output;
B1/B13/B17/B18. DC: SAME output suffix through the terminal state. -/
theorem postReset_raw_outputs_succ_above
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    (hresetNext : PostResetResetLeaseCompatible p c E rho w (i + 1))
    (hleaseNext : PostResetLeaseSafe p c E rho w (i + 1))
    {ix : Nat} {x : V} {s : Slot} {C : Block} (hx : x ∈ rho.honest)
    (hlabel : w.sStar ≤ s) (hix : IsGateTick p c rho ix x s) (hxi : ix ≤ i)
    (hres : gateResultAt p c E rho ix = some (some C)) (hCB : Block.Preceq w.CStar C) :
    ∀ a y, a < i + 1 → y ∈ rho.honest → SA.gateTime p.toParams s + 4 * p.Δ ≤ rho.horizon →
      HealSuffix p c rho (SA.gateTime p.toParams s + 4 * p.Δ) a →
      Block.Preceq C (S_at p c E rho a y) := by
  intro a y hacut hy hhor hsuffix
  have hs := hrec.base.valid.toScheduleWellFormed
  have hmem := rawStep_result_mem p c E rho hs hix hres
  obtain ⟨B, -, heB⟩ := (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho ix x)
    (SA.gateTime p.toParams s)).baseTree C |>.mp ((actView_blocks _ C).mp hmem).1
  rw [← heB] at hCB hres ⊢
  have hgst : E.t_GST ≤ SA.voteTime p.toParams s := by
    apply h0r.synchronous.trans
    have hh : (w.sStar : Int) ≤ s := by exact_mod_cast hlabel
    change 4 * p.Δ * (w.sStar : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + p.Δ
    nlinarith [p.deltaPos]
  have batches : ∀ l, s + 1 ≤ l → timeIdx rho (SA.voteTime p.toParams l) ≤ i →
      SA.voteTime p.toParams l ≤ rho.horizon →
      Gen.Pure.Batch (joinedHonest p E rho (SA.voteTime p.toParams l)).card
        (Gen.V2.Duty.faulty rho).card := by
    intro l hsl _hcut hhor
    have hCut := (healing_window_of_cut E (healing_ready_vote_cutoff E
      (healing_reset_source_ready h0r))).cut_mono (hlabel.trans (Nat.le_of_succ_le hsl))
    exact (healing_recovery_joined_counts E rho hrec l hCut.2 hCut.sync hhor).2
  apply healing_output_moving_suffix_at p c E rho hrec
    (healing_raw_service_scope_recovery E rho hrec mono) mono hgst batches hhor (cut := i)
    ?_ ?_ ?_ a y hy (Nat.le_of_lt_succ hacut) hsuffix
  · intro l hsl hcut z hz H hH
    exact postReset_raw_heads_succ_above p c E rho hrec emittedNonempty emittedName writes
      mono source xing origin h0r hinv hresetNext hleaseNext hx hlabel hix hxi hres hCB
      z l H hz hsl (hcut.trans (Nat.le_succ i)) hH
  · intro b hbi z hz _hstart
    exact postReset_raw_finality_compatible_above p c E rho hrec emittedNonempty emittedName
      writes mono source xing origin h0r hinv hresetNext hleaseNext hx hlabel hix hxi hres hCB
      hbi hz
  · intro j z hz hj hji _hF
    exact postReset_raw_gate_lease_compat p c E rho hrec emittedNonempty emittedName writes
      mono source xing origin h0r hinv hresetNext hleaseNext hx hlabel hix hxi hres hz hj hji


omit [Fintype V] hrec writes mono source xing origin in
private theorem rawStep_reset_result :
    ∃ k x C, x ∈ rho.honest ∧ IsGateTick p c rho k x w.sStar ∧
      gateResult p c E rho x w.sStar = some (some C) ∧ Block.Preceq w.CStar C := by
  obtain ⟨_, x, _, B, ha, -, hsource, heB, -⟩ := h0r.fresh
  obtain ⟨-, C, -, hC, hBC, -⟩ :=
    healing_source_decode p c E rho emittedNonempty emittedName ha hsource
  rw [← h0r.label] at hC
  obtain ⟨k, hk⟩ := rawStep_result_tick p c E rho hC
  exact ⟨k, x, C, ha.1, hk, hC, heB ▸ hBC⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.16:2940–2944, H.2:723–726; plan J5-A-3 R6 HEAD;
B1/B13/B17/B18. DC: SAME successor HEAD cut for every raw result. -/
theorem postReset_raw_heads_succ
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    (hresetNext : PostResetResetLeaseCompatible p c E rho w (i + 1))
    (hleaseNext : PostResetLeaseSafe p c E rho w (i + 1))
    {ix : Nat} {x : V} {s : Slot} {C : Block} (hx : x ∈ rho.honest)
    (hlabel : w.sStar ≤ s) (hix : IsGateTick p c rho ix x s) (hxi : ix ≤ i)
    (hres : gateResultAt p c E rho ix = some (some C)) :
    ∀ y l H, y ∈ rho.honest → s + 1 ≤ l →
      timeIdx rho (SA.voteTime p.toParams l) ≤ i + 1 →
      headAtLabel p c E rho y l = some H → Block.Preceq C H := by
  have hc := postReset_raw_reset_compatible p c E rho hrec
    (healing_raw_service_scope_recovery E rho hrec mono) emittedNonempty emittedName
    h0r hinv hx hlabel hix hres hxi
  rcases Bool.or_eq_true_iff.mp hc with habove | hbelow
  · exact postReset_raw_heads_succ_above p c E rho hrec emittedNonempty emittedName writes
      mono source xing origin h0r hinv hresetNext hleaseNext hx hlabel hix hxi hres habove
  intro y l H hy hsl hcut hhead
  rcases eq_or_lt_of_le hsl with rfl | hsl
  · exact postReset_raw_first_head_label p c E rho hrec emittedNonempty emittedName writes
      mono source xing origin h0r hinv hresetNext hleaseNext hx hlabel hix hxi hres hy hhead
  have hs := hrec.base.valid.toScheduleWellFormed
  have hhead' : headAtLabel p c E rho y l = some H := hhead
  delta headAtLabel at hhead'
  rw [postClock_def, preTick_def] at hhead'
  cases ht : V2.D.Run.tickIdx? rho y (SA.voteTime p.toParams l) with
  | none => rw [ht] at hhead'; cases hhead'
  | some iy =>
    have hiy := V2.D.Run.tickIdx?_spec ht
    have hyi : iy ≤ i := Nat.le_of_lt_succ
      (((V2.D.Engine.index_lt_read_length_iff hs _ hiy).mpr le_rfl).trans_le hcut)
    obtain ⟨k0, x0, C0, hx0, hk0, hC0, hresetC0⟩ :=
      rawStep_reset_result p c E rho emittedNonempty emittedName h0r
    have hk0i : k0 ≤ i := (healing_idx_lt_of_time_lt p c E rho hs hk0 hiy (by
      change 4 * p.Δ * (w.sStar : Int) + 6 * p.Δ < 4 * p.Δ * (l : Int) + p.Δ
      have hh : (w.sStar : Int) + 2 ≤ l := by
        exact_mod_cast (Nat.succ_le_succ (Nat.succ_le_succ hlabel)).trans hsl
      nlinarith [p.deltaPos])).le.trans hyi
    apply Gen.Pure.block_preceq_trans (Gen.Pure.block_preceq_trans hbelow hresetC0)
    exact postReset_raw_heads_succ_above p c E rho hrec emittedNonempty emittedName writes
      mono source xing origin h0r hinv hresetNext hleaseNext hx0 le_rfl hk0 hk0i
      ((gateResultAt_eq_gateResult p c E rho hs hk0).trans hC0) hresetC0 y l H hy
      ((Nat.succ_le_succ hlabel).trans hsl.le) hcut hhead

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.16:2940–2944, H.2:736–746; plan J5-A-3 R6 proposal;
B1/B13/B17/B18. DC: SAME successor proposal cut for every raw result. -/
theorem postReset_raw_proposals_succ
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    (hresetNext : PostResetResetLeaseCompatible p c E rho w (i + 1))
    (_hleaseNext : PostResetLeaseSafe p c E rho w (i + 1))
    {ix : Nat} {x : V} {s : Slot} {C : Block} (hx : x ∈ rho.honest)
    (hlabel : w.sStar ≤ s) (hix : IsGateTick p c rho ix x s) (hxi : ix ≤ i)
    (hres : gateResultAt p c E rho ix = some (some C)) :
    ∀ v Q, s + 2 ≤ v → timeIdx rho (SA.proposalTime p.toParams v) ≤ i + 1 →
      HonestProposal E rho (fgsaInterface p c) v Q → Block.Preceq C Q.parent := by
  have hc := postReset_raw_reset_compatible p c E rho hrec
    (healing_raw_service_scope_recovery E rho hrec mono) emittedNonempty emittedName
    h0r hinv hx hlabel hix hres hxi
  rcases Bool.or_eq_true_iff.mp hc with habove | hbelow
  · exact postReset_raw_proposals_succ_above p c E rho hrec emittedNonempty emittedName writes
      mono source xing origin h0r hinv hresetNext hx hlabel hix hxi hres habove
  intro v Q hsv hcut hp
  have hs := hrec.base.valid.toScheduleWellFormed
  obtain ⟨ip, hip, -⟩ := rawStep_proposal_read p c E rho hp
  have hpi : ip ≤ i := Nat.le_of_lt_succ
    (((V2.D.Engine.index_lt_read_length_iff hs _ hip).mpr le_rfl).trans_le hcut)
  obtain ⟨k0, x0, C0, hx0, hk0, hC0, hresetC0⟩ :=
    rawStep_reset_result p c E rho emittedNonempty emittedName h0r
  have hk0i : k0 ≤ i := (healing_idx_lt_of_time_lt p c E rho hs hk0 hip (by
    change 4 * p.Δ * (w.sStar : Int) + 6 * p.Δ < 4 * p.Δ * (v : Int)
    have hh : (w.sStar : Int) + 2 ≤ v := by
      exact_mod_cast (Nat.succ_le_succ (Nat.succ_le_succ hlabel)).trans hsv
    nlinarith [p.deltaPos])).le.trans hpi
  apply Gen.Pure.block_preceq_trans (Gen.Pure.block_preceq_trans hbelow hresetC0)
  exact postReset_raw_proposals_succ_above p c E rho hrec emittedNonempty emittedName writes
    mono source xing origin h0r hinv hresetNext hx0 le_rfl hk0 hk0i
    ((gateResultAt_eq_gateResult p c E rho hs hk0).trans hC0) hresetC0 v Q
    ((Nat.succ_le_succ (Nat.succ_le_succ hlabel)).trans hsv) hcut hp

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.16:2940–2944, H.2:729–735; plan J5-A-3 R6 output;
B1/B13/B17/B18. DC: SAME successor output cut for every raw result. -/
theorem postReset_raw_outputs_succ
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    (hresetNext : PostResetResetLeaseCompatible p c E rho w (i + 1))
    (hleaseNext : PostResetLeaseSafe p c E rho w (i + 1))
    {ix : Nat} {x : V} {s : Slot} {C : Block} (hx : x ∈ rho.honest)
    (hlabel : w.sStar ≤ s) (hix : IsGateTick p c rho ix x s) (hxi : ix ≤ i)
    (hres : gateResultAt p c E rho ix = some (some C)) :
    ∀ a y, a < i + 1 → y ∈ rho.honest → SA.gateTime p.toParams s + 4 * p.Δ ≤ rho.horizon →
      HealSuffix p c rho (SA.gateTime p.toParams s + 4 * p.Δ) a →
      Block.Preceq C (S_at p c E rho a y) := by
  have hc := postReset_raw_reset_compatible p c E rho hrec
    (healing_raw_service_scope_recovery E rho hrec mono) emittedNonempty emittedName
    h0r hinv hx hlabel hix hres hxi
  rcases Bool.or_eq_true_iff.mp hc with habove | hbelow
  · exact postReset_raw_outputs_succ_above p c E rho hrec emittedNonempty emittedName writes
      mono source xing origin h0r hinv hresetNext hleaseNext hx hlabel hix hxi hres habove
  intro a y hacut hy hhor hsuffix
  have hs := hrec.base.valid.toScheduleWellFormed
  have ht : ∀ q : Slot, SA.gateTime p.toParams q + 4 * p.Δ = SA.gateTime p.toParams (q + 1) := by
    intro q
    change 4 * p.Δ * (q : Int) + 6 * p.Δ + 4 * p.Δ =
      4 * p.Δ * ((q + 1 : Nat) : Int) + 6 * p.Δ
    push_cast
    ring
  rw [ht] at hhor hsuffix
  have hsuf : HealSuffix p c rho (SA.gateTime p.toParams (s + 1)) a := hsuffix
  delta HealSuffix healStart at hsuf
  rw [(isGateTime_iff p _).mpr ⟨s + 1, rfl⟩, ite_eq_left rfl] at hsuf
  obtain ⟨k0, x0, C0, hx0, hk0, hC0, hresetC0⟩ :=
    rawStep_reset_result p c E rho emittedNonempty emittedName h0r
  have hk0pre : k0 < V2.D.Run.idxBefore rho (SA.gateTime p.toParams (s + 1)) :=
    (Gen.V2.Duty.index_lt_idxBefore_iff hs hk0 _).mpr (by
      change 4 * p.Δ * (w.sStar : Int) + 6 * p.Δ <
        4 * p.Δ * ((s + 1 : Nat) : Int) + 6 * p.Δ
      have hh : (w.sStar : Int) ≤ s := by exact_mod_cast hlabel
      push_cast
      nlinarith [p.deltaPos])
  have hpre : V2.D.Run.idxBefore rho (SA.gateTime p.toParams (s + 1)) ≤
      afterTicksIdx rho (SA.gateTime p.toParams (s + 1)) := by
    rw [V2.D.Run.idxBefore_def]
    exact (preIdx_le_afterTicksIdx E rho hs _).1
  have hk0i : k0 ≤ i := (hk0pre.le.trans (hpre.trans hsuf.1)).trans (Nat.le_of_lt_succ hacut)
  have htime : SA.gateTime p.toParams (w.sStar + 1) ≤ SA.gateTime p.toParams (s + 1) := by
    change 4 * p.Δ * ((w.sStar + 1 : Nat) : Int) + 6 * p.Δ ≤
      4 * p.Δ * ((s + 1 : Nat) : Int) + 6 * p.Δ
    have hh : (w.sStar : Int) ≤ s := by exact_mod_cast hlabel
    push_cast
    nlinarith [p.deltaPos]
  have hsuffix0 : HealSuffix p c rho (SA.gateTime p.toParams w.sStar + 4 * p.Δ) a := by
    rw [ht]
    delta HealSuffix healStart
    rw [(isGateTime_iff p _).mpr ⟨w.sStar + 1, rfl⟩, ite_eq_left rfl]
    exact ⟨(afterTicksIdx_mono rho htime).trans hsuf.1, hsuf.2⟩
  apply Gen.Pure.block_preceq_trans (Gen.Pure.block_preceq_trans hbelow hresetC0)
  exact postReset_raw_outputs_succ_above p c E rho hrec emittedNonempty emittedName writes
    mono source xing origin h0r hinv hresetNext hleaseNext hx0 le_rfl hk0 hk0i
    ((gateResultAt_eq_gateResult p c E rho hs hk0).trans hC0) hresetC0 a y hacut hy
    (by rw [ht]; exact htime.trans hhor) hsuffix0


/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.16:2924–2945, H.2:723–746; plan J5-A-3 R4;
B1/B13/B17/B18. DC: SAME raw-transfer successor for every event cut.
The exact joint antecedents suffice. New sources reuse the gate-cut
package; older sources use the three proved successor readers. -/
theorem postReset_rawTransfer_succ : ∀ i, PostResetRawStep p c E rho w i := by
  intro i
  rw [PostResetRawStep_def]
  intro hprev hresetNext hleaseNext _hfprovNext
  have hinv := hprev.1
  rw [PostResetRawTransfer_def]
  intro k hk x s C hx hlabel hgate hres
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hki | rfl
  · have hs := hrec.base.valid.toScheduleWellFormed
    have hresAt := (gateResultAt_eq_gateResult p c E rho hs hgate).trans hres
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro y nd hy _hcut hnd
      have hreset : PostResetResetLeaseCompatible p c E rho w (i + 1) := by
        exact hresetNext
      exact postReset_raw_release_compatible p c E rho hrec
        (healing_raw_service_scope_recovery E rho hrec mono) emittedNonempty emittedName writes
        h0r hinv hreset hleaseNext hx hlabel hgate hres hki.le hy hnd
    · exact postReset_raw_heads_succ p c E rho hrec emittedNonempty emittedName writes
        mono source xing origin h0r hinv hresetNext hleaseNext hx hlabel hgate hki.le hresAt
    · exact postReset_raw_proposals_succ p c E rho hrec emittedNonempty emittedName writes
        mono source xing origin h0r hinv hresetNext hleaseNext hx hlabel hgate hki.le hresAt
    · exact postReset_raw_outputs_succ p c E rho hrec emittedNonempty emittedName writes
        mono source xing origin h0r hinv hresetNext hleaseNext hx hlabel hgate hki.le hresAt
  · exact postReset_raw_at_gate_cut p c E rho hrec emittedNonempty emittedName writes mono source
      xing origin h0r hinv hresetNext hleaseNext hx hlabel hgate hres

omit writes source origin in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.16:2933–2938; plan J5-A-3 reset-lease adapter;
B1/B13/B17/B18. DC: INTENTIONAL; DC has no leases.
The existing all-cut adapter supplies the requested successor name. -/
theorem postReset_resetLease_succ' (cap : RCap p c E rho) (source : TSrc p c E rho) :
    ∀ i, PostResetResetLeaseStep p c E rho w i :=
  postReset_resetLease_succ_all p c E rho hrec emittedNonempty emittedName mono xing h0r cap source

end AvailableChain.FGSA.Run

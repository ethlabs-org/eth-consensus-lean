module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetProject
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetRead
public import AvailableChainFGSAProofs.Proofs.Healing.DescentLossUnanimous

public import AvailableChainFGSAProofs.Proofs.Healing.RecoveryProducers

public section

/-! Blueprint 21 H2′:3297–3300, proof:3382–3391; H.17 and H.2.
Centaur fgsa-s5-h2p-route; B1/B13/B17/B18.
DC: SAME honest-proposal coverage at later HEAD reads. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- Blueprint 21 H2′:3297–3300, proof:3382–3391; Centaur late route;
B1/B17/B18. DC: SAME actual gate result below each late HEAD.
Only inv.service and inv.raw_transfer at events.length + 1 are used.
The reader tick supplies the gate horizon; no continuation input is added. -/
theorem postReset_h2Prime_late (hs : V2.D.ScheduleWellFormed E rho)
    {w : HealingWitness} (inv : ∀ k, PostResetInv p c E rho w k)
    {v : Slot} {Q : Block} (hQ : HonestProposal E rho (fgsaInterface p c) v Q)
    (hv : w.sStar + 2 ≤ v) {x : V} {i : Slot} {H : Block}
    (hx : x ∈ rho.honest) (hi : v + 2 ≤ i)
    (hH : headAtLabel p c E rho x i = some H) : Block.Preceq Q H := by
  have hhor : SA.voteTime p.toParams i ≤ rho.horizon := by
    unfold headAtLabel at hH
    rw [postClock_def, preTick_def] at hH
    cases ht : V2.D.Run.tickIdx? rho x (SA.voteTime p.toParams i) with
    | none => rw [ht] at hH; cases hH
    | some k => exact (hs.in_horizon _
        (List.mem_of_getElem? (V2.D.Run.tickIdx?_spec ht))).2
  have hg : SA.gateTime p.toParams v ≤ rho.horizon := by
    apply le_trans _ hhor
    change 4 * p.Δ * (v : Int) + 6 * p.Δ ≤ 4 * p.Δ * (i : Int) + p.Δ
    have hic : (v : Int) + 2 ≤ (i : Int) := by exact_mod_cast hi
    nlinarith [p.deltaPos]
  let N := rho.events.length + 1
  have hc (t : Time) : timeIdx rho t ≤ N :=
    (List.length_filter_le _ _).trans (Nat.le_succ _)
  have ha (t : Time) : afterTicksIdx rho t ≤ N :=
    (List.length_filter_le _ _).trans (Nat.le_succ _)
  have service := (inv N).service
  rw [PostResetService_def] at service
  obtain ⟨hraw, ⟨k, hk, ht, hpass⟩, hrest⟩ :=
    (service v Q hQ hv (hc _)).2 hg (ha _) x hx
  have raw := (inv N).raw_transfer
  rw [PostResetRawTransfer_def] at raw
  have hsv : w.sStar ≤ v := (Nat.le_add_right w.sStar 2).trans hv
  have hvi : v + 1 ≤ i := (Nat.le_succ (v + 1)).trans hi
  exact (raw k hk x v Q hx hsv ht hraw).2.1 x i H hx hvi (hc _) hH

private theorem h2Prime_lift {A B : FGBlock (Fin p.n)}
    (h : Block.Preceq (eraseFG A) (eraseFG B)) : FGBlock.Preceq A B :=
  eraseFG_preceq_iff.mp h

section Sources
variable [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    (cap : RCap p c E rho)
    (source : TSrc p c E rho)
    (rowCovered : ∀ (_hb : Base₂ p c E rho)
      (_hf : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
      (x : V), x ∈ rho.honest → ∀ (r : Nat) (nd : Node p),
      postClock E rho x (p.actionTime r) = some nd → ∀ C : FGBlock (Fin p.n),
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st → (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))
    {w : HealingWitness} (h0r : H0Reset p c E rho w)

include hrec cap source rowCovered h0r

/-- ROOT-DIGEST W2b. Blueprint 21 H2′:3382–3391, H.14 S2:2823; Centaur reset-prefix route;
B1/B13/B17/B18. DC: SAME C* strictly below an honest proposal.
Named producers: fgsa_rCap_channel, sourceDiscipline_tSrc, rowPermission_covered.
The all-cut carrier is used only by postReset_tCarrier_reset. -/
theorem postReset_cStar_below_proposal (inv : ∀ i, PostResetInv p c E rho w i)
    {v : Slot} {Q : Block} (hQ : HonestProposal E rho (fgsaInterface p c) v Q)
    (hv : w.sStar + 2 ≤ v) : Block.Prec w.CStar Q := by
  obtain ⟨j, y, a, C0, hrow, hname, hsrc, he0, hh0⟩ := h0r.fresh
  have hhC : high p w C0 := by rw [high_def, hh0]
  have hparent : Block.Preceq w.CStar Q.parent := by
    rw [← he0]
    exact postReset_tCarrier_reset p c E rho hrec.toRecovery₂ cap source rowCovered h0r inv
      y w.rStar C0 v Q hrow.1 hsrc hhC hQ (by rw [← h0r.label]; exact hv)
  have hslot := repair_proposal_slot E rho hQ
  cases Q with
  | genesis =>
    have hpos : 0 < v := lt_of_lt_of_le (Nat.succ_pos (w.sStar + 1)) hv
    exact False.elim (Nat.ne_of_gt hpos hslot.symm)
  | node parent slot root body =>
    have hp : Block.Preceq parent (.node parent slot root body) := by
      change (decide (parent = Block.node parent slot root body) || Block.preceq parent parent) =
        true
      rw [Gen.Pure.block_preceq_refl parent, Bool.or_true]
    have hne : w.CStar ≠ .node parent slot root body := by
      intro he
      rw [he] at hparent
      have hc := Gen.Pure.block_preceq_antisymm hparent hp
      have hd := congrArg Block.depth hc
      change parent.depth + 1 = parent.depth at hd
      omega
    change (Bool.not (decide (w.CStar = Block.node parent slot root body)) &&
      Block.preceq w.CStar (.node parent slot root body)) = true
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
    exact ⟨hne, Gen.Pure.block_preceq_trans hparent hp⟩

include mono

/-- ROOT-DIGEST W2b. Blueprint 21 H2′:3382–3391; Centaur first-reader route;
B1/B13/B15/B17/B18. DC: SAME coverage before the proposal's gate.
Named producers: fgsa_rXing and sourceDiscipline_qcOrigin, in addition to
those of postReset_cStar_below_proposal. The path view contains every high
source because H2.A puts that source below the unanimous slot-v HEAD. -/
theorem postReset_h2Prime_first (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    (inv : ∀ i, PostResetInv p c E rho w i)
    {v : Slot} {Q : Block} (hQ : HonestProposal E rho (fgsaInterface p c) v Q)
    (hv : w.sStar + 2 ≤ v) {x : V} {H : Block}
    (hReader : headReader p E rho x (v + 1) (SA.voteTime p.toParams (v + 1)))
    (hH : headAtLabel p c E rho x (v + 1) = some H) :
    Block.Preceq Q H := by
  classical
  have hs := hrec.base.valid.toScheduleWellFormed
  have hx := hReader.1
  have hDelta := hrec.base.delta
  unfold headAtLabel at hH
  rw [postClock_def, preTick_def] at hH
  cases hi : V2.D.Run.tickIdx? rho x (SA.voteTime p.toParams (v + 1)) with
  | none => rw [hi] at hH; cases hH
  | some iy =>
  rw [hi] at hH
  have hiy := V2.D.Run.tickIdx?_spec hi
  have hhor := (hs.in_horizon _ (List.mem_of_getElem? hiy)).2
  have hvi : SA.voteTime p.toParams v + p.Δ ≤ SA.voteTime p.toParams (v + 1) := by
    change 4 * p.Δ * (v : Int) + p.Δ + p.Δ ≤
      4 * p.Δ * ((v + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith [p.deltaPos]
  have hhv : SA.voteTime p.toParams v ≤ rho.horizon :=
    ((le_add_of_nonneg_right p.deltaPos.le).trans hvi).trans hhor
  have hgst : E.t_GST ≤ SA.voteTime p.toParams v := by
    have h := postReset_synchronous_window p c E rho w h0r hv
    change E.t_GST ≤ 4 * p.Δ * (v : Int) - p.Δ at h
    change E.t_GST ≤ 4 * p.Δ * (v : Int) + p.Δ
    linarith [p.deltaPos]
  have hCut : HealingWindow p E 1 v := by
    refine ⟨(Nat.le_add_left 1 (w.sStar + 1)).trans hv, ?_⟩
    have hbase := healing_ready_vote_cutoff E (healing_reset_source_ready h0r)
    have hI : (w.sStar : Int) ≤ (v : Int) := by
      exact_mod_cast (Nat.le_add_right w.sStar 2).trans hv
    change E.t_GST ≤ 4 * p.Δ * ((w.sStar : Int) - 1) at hbase
    change E.t_GST ≤ 4 * p.Δ * ((v : Int) - 1)
    nlinarith [p.deltaPos]
  let N := rho.events.length + 1
  have hc (t : Time) : timeIdx rho t ≤ N :=
    (List.length_filter_le _ _).trans (Nat.le_succ _)
  have service := (inv N).service
  rw [PostResetService_def] at service
  have hbatch := (service v Q hQ hv (hc _)).1 hhv (hc _)
  have hbelow : ∀ K s, SourceBefore p c E rho iy K s → high p w K →
      Block.Preceq (eraseFG K) Q := by
    intro K s hK hhK
    obtain ⟨j, y, r, a, hj, hrow, hsrc, hlabel⟩ := hK
    obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hrow.2.1
    obtain ⟨hyl, hye⟩ := List.getElem?_eq_some_iff.mp hiy
    have hk := (List.pairwise_iff_getElem.mp hs.sorted) j iy hjl hyl hj
    rw [hje, hye] at hk
    have ht := V2.D.Engine.time_le_of_key_le _ _ hk
    change SA.gateTime p.toParams (r * p.R) ≤ SA.voteTime p.toParams (v + 1) at ht
    have hl : r * p.R + 1 ≤ v := by
      change 4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ ≤
        4 * p.Δ * ((v + 1 : Nat) : Int) + p.Δ at ht
      simp only [Nat.cast_add, Nat.cast_one] at ht
      have : ((r * p.R : Nat) : Int) < (v : Int) := by nlinarith [p.deltaPos]
      exact_mod_cast this
    exact (postReset_h2A_reset p c E rho hrec.toRecovery₂ cap source rowCovered h0r inv
      y r K hrow.1 hsrc hhK).1 x v Q
      ⟨hx, healing_recovery_joined_window E rho hrec hCut hx hhv⟩ hl (hbatch x hx)
  have hCQ := postReset_cStar_below_proposal p c E rho hrec cap source rowCovered h0r inv hQ hv
  have hCQ' : Block.Preceq w.CStar Q := by
    change (Bool.not (decide (w.CStar = Q)) && Block.preceq w.CStar Q) = true at hCQ
    exact (Bool.and_eq_true_iff.mp hCQ).2
  have hact : p.actionTime w.rStar < SA.voteTime p.toParams (v + 1) := by
    have hvI : (w.sStar : Int) + 2 ≤ (v : Int) := by exact_mod_cast hv
    change SA.gateTime p.toParams (w.rStar * p.R) < _
    rw [← h0r.label]
    change 4 * p.Δ * (w.sStar : Int) + 6 * p.Δ <
      4 * p.Δ * ((v + 1 : Nat) : Int) + p.Δ
    push_cast
    nlinarith [p.deltaPos]
  have hcut : afterTicksIdx rho (p.actionTime w.rStar) ≤ iy := by
    apply le_trans (preIdx_le_afterTicksIdx E rho hs _).2
    apply le_trans (b := V2.D.Run.idxBefore rho (SA.voteTime p.toParams (v + 1)))
    · rw [V2.D.Run.idxBefore_def, ← List.countP_eq_length_filter,
        ← List.countP_eq_length_filter]
      exact List.countP_mono_left (fun e _ he =>
        decide_eq_true (lt_of_le_of_lt (of_decide_eq_true he) hact))
    · exact healing_support_idxBefore_le p c E rho hs hiy le_rfl
  have fprov := (inv (iy + 1)).fprov
  rw [PostResetFProv_def] at fprov
  have hFQ : Block.Preceq (eraseFG (storeAt p c E rho iy x).fg.F) Q := by
    rcases (fprov iy (Nat.lt_succ_self iy) x hx hcut).1 with hF | ⟨K, s, hK, hhK, ht, hF⟩
    · exact Gen.Pure.block_preceq_trans hF hCQ'
    · exact Gen.Pure.block_preceq_trans hF (hbelow K s hK hhK)
  have hsourceHead := hbatch x hx
  unfold headAtLabel at hsourceHead
  rw [postClock_def, preTick_def] at hsourceHead
  cases hj : V2.D.Run.tickIdx? rho x (SA.voteTime p.toParams v) with
  | none => rw [hj] at hsourceHead; cases hsourceHead
  | some j =>
  rw [hj] at hsourceHead
  have hjtick := V2.D.Run.tickIdx?_spec hj
  have heQ := Option.some.inj hsourceHead
  have hQstore : Q ∈ (storeAt p c E rho j x).base.blocks := by
    rw [← heQ]
    have hm := headVote_stored p
      (FGSA.clock p (storeAt p c E rho j x) (SA.voteTime p.toParams v))
      (cstoreInv_clock p _ (cstoreInv_stateBefore E rho j x) (SA.voteTime p.toParams v)) v
    rwa [clock_base_blocks] at hm
  have hfreeze : SA.earlyTime p.toParams v + p.Δ = SA.freezeTime p.toParams v := by
    change 4 * p.Δ * (v : Int) + 2 * p.Δ + p.Δ = 4 * p.Δ * (v : Int) + 3 * p.Δ
    ring
  have hfr : SA.freezeTime p.toParams v ≤ SA.voteTime p.toParams (v + 1) := by
    change 4 * p.Δ * (v : Int) + 3 * p.Δ ≤ 4 * p.Δ * ((v + 1 : Nat) : Int) + p.Δ
    push_cast; linarith [p.deltaPos]
  have hFE := healing_receipt_floor_before_tick E rho hs mono hx hiy hfr hFQ
  have hpub : V2.PublicTime E (SA.earlyTime p.toParams v) := by
    refine ⟨4 * v + 2, ?_⟩
    rw [hDelta]
    change 4 * p.Δ * (v : Int) + 2 * p.Δ = _
    push_cast; ring
  have htarget : TargetReceiptService E rho Q (SA.freezeTime p.toParams v) x := by
    rw [← hfreeze]
    apply healing_target_service_of_earlier_tick E rho hrec hx hx hjtick hQstore
    · change 4 * p.Δ * (v : Int) + p.Δ < 4 * p.Δ * (v : Int) + 2 * p.Δ
      linarith [p.deltaPos]
    · exact hpub
    · apply le_trans hgst
      change 4 * p.Δ * (v : Int) + p.Δ ≤ 4 * p.Δ * (v : Int) + 2 * p.Δ
      linarith [p.deltaPos]
    · exact hfreeze ▸ hfr.trans hhor
    · exact hfreeze ▸ block_compatible_of_common (block_preceq_refl Q) hFE
  have hEpoch : V2.D.restartFree rho x
      (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams v)) iy := by
    apply healing_recovery_epoch E rho hrec hx (fgsa_idxBefore_mono rho ?_)
    have hd1 : (1 : Int) ≤ p.Δ := Int.add_one_le_iff.mpr p.deltaPos
    change E.t_GST ≤ 4 * p.Δ * (v : Int) + p.Δ at hgst
    change E.t_GST + 1 ≤ 4 * p.Δ * (v : Int) + 3 * p.Δ
    linarith
  obtain ⟨Qfg, hefg, hpath⟩ := healing_block_path_sync p c E rho hs hx hiy hEpoch Q
    htarget hrec.base.receiptIdealization
  let dst := FGSA.clock p (storeAt p c E rho iy x) (SA.voteTime p.toParams (v + 1))
  change ∀ A, FGBlock.Preceq A Qfg → A ∈ dst.fg.TF ∧
    GridCO.stampBlock dst.base (eraseFG A) < SA.freezeTime p.toParams v at hpath
  let X := dst.fg.TF.filter (fun A => FGBlock.preceq A Qfg)
  have path : ∀ A, FGBlock.Preceq A Qfg → A ∈ X := by
    intro A hA
    exact Finset.mem_filter.mpr ⟨(hpath A hA).1, hA⟩
  let Y := X.filter (fun A => FGBlock.Preceq (storeAt p c E rho iy x).fg.F A)
  have hYv : Y ⊆ voterBlocks p dst (v + 1) := by
    intro A hA
    obtain ⟨hA, hFA⟩ := Finset.mem_filter.mp hA
    obtain ⟨hm, hp⟩ := Finset.mem_filter.mp hA
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨hm, ?_⟩, Bool.or_eq_true_iff.mpr (Or.inl ?_)⟩
    · change FGBlock.Preceq (FGSA.clock p _ _).fg.F A
      rw [clock_fg]
      exact hFA
    · simpa only [Nat.add_sub_cancel, decide_eq_true_eq] using (hpath A hp).2
  have hYc : ∀ W ∈ Y, ∀ A, FGBlock.Preceq (storeAt p c E rho iy x).fg.F A →
      FGBlock.Preceq A W → A ∈ Y := by
    intro W hW A hFA hAW
    exact Finset.mem_filter.mpr
      ⟨path A (KitFG.preceq_trans hAW (Finset.mem_filter.mp (Finset.mem_filter.mp hW).1).2),
        hFA⟩
  obtain ⟨jr, yr, ar, C0, hrow0, hname0, hsrc0, he0, hh0⟩ := h0r.fresh
  have hC0Q : FGBlock.Preceq C0 Qfg := h2Prime_lift p (by rwa [he0, hefg])
  have hX : X ⊆ (storeAt p c E rho iy x).fg.TF := by
    intro A hA
    have hm := (Finset.mem_filter.mp hA).1
    change A ∈ dst.fg.TF at hm
    rwa [clock_fg] at hm
  have cover : ∀ K s, SourceBefore p c E rho iy K s → high p w K → K ∈ X := by
    intro K s hK hhK
    exact path K (h2Prime_lift p (by rw [hefg]; exact hbelow K s hK hhK))
  have hkept := postReset_general_kept (hroots := hrec.base.idealization) p c E rho xing origin
    h0r (inv iy) hx hX
    (path C0 hC0Q) he0 cover path
    (Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl _) (by rwa [hefg]))
    (fun K s hK hhK => Gen.Pure.block_compatible_of_common
      (Gen.Pure.block_preceq_refl _) (by rw [hefg]; exact hbelow K s hK hhK))
  have hready : recoveryStart p E ≤ SA.voteTime p.toParams (v + 1) := by
    apply le_trans (healing_reset_source_ready h0r)
    change 4 * p.Δ * (w.sStar : Int) + p.Δ ≤ 4 * p.Δ * ((v + 1 : Nat) : Int) + p.Δ
    have hI : (w.sStar : Int) ≤ (v : Int) := by
      exact_mod_cast (Nat.le_add_right w.sStar 2).trans hv
    push_cast; nlinarith [p.deltaPos]
  have hJoined := healing_ready_head_guard E rho hrec hx hiy hready hhor
  have hRelease : joinedAtTime p (storeAt p c E rho iy x).restartTime
      (SA.releaseTime p.toParams v) = true := by
    unfold joinedNow at hJoined
    rw [fgsa_clock_restartTime, (clock_vn _ _).2] at hJoined
    have he : SA.releaseTime p.toParams v = SA.voteTime p.toParams (v + 1) := by
      change 4 * p.Δ * (v : Int) + 5 * p.Δ = 4 * p.Δ * ((v + 1 : Nat) : Int) + p.Δ
      push_cast; ring
    simpa only [he] using hJoined
  have hout := healing_unanimous_next_transfer_kept p c E rho hrec mono hgst hefg hbatch
    hx hiy (healing_next_transfer_scope_recovery E rho hrec hCut hx hiy hReader.2)
    hCut hRelease hYv hYc (by
      dsimp only [Kept, D_at] at hkept ⊢
      simpa only [Y, healing_domain_filter_F] using hkept)
  rw [healing_headAtIdx_tick p c E rho hiy] at hout
  exact (Option.some.inj hH) ▸ hout

/-- Blueprint 21 H2′:3297–3300, proof:3382–3391; Centaur split route;
B1/B13/B15/B17/B18. DC: SAME frozen honest-proposal HEAD coverage.
Combine the first reader with every later reader; H0Reset is the only reset input. -/
theorem postReset_h2Prime_reset (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    (inv : ∀ i, PostResetInv p c E rho w i) : H2Prime p c E rho w := by
  intro v Q hQ hv x i H hx hi hH
  rcases Nat.eq_or_lt_of_le hi with he | hl
  · subst i
    exact postReset_h2Prime_first p c E rho hrec mono cap source rowCovered
      h0r xing origin inv
      hQ hv hx hH
  · exact postReset_h2Prime_late p c E rho hrec.base.valid.toScheduleWellFormed inv
      hQ hv hx.1 hl hH

end Sources

end AvailableChain.FGSA.Run
end

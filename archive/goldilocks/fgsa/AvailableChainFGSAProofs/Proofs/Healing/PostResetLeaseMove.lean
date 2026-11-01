module
public import AvailableChainFGSAProofs.Proofs.Healing.RecoveryProducers
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetJoint -- shake: keep (J4A2-2 types)

public section

/-! Blueprint 21 H.15:2916–2923, H.2:709–746; plan J4A2-2 G2.
B1/B13/B17/B18. DC: INTENTIONAL reader time after freeze, including
proposal ticks. The prior high field and emitted-source no-loss supply
the domain guards. No THigh input or successor service field is used. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

omit [DecidableEq V] in
private theorem leaseMove_lift {A B : FGBlock (Fin p.n)}
    (h : Block.Preceq (eraseFG A) (eraseFG B)) : FGBlock.Preceq A B :=
  eraseFG_preceq_iff.mp h

/-- A prior source is served before freeze using the actual bounded reader.
No tick at the next vote is requested. -/
theorem healing_source_before_receipt_at_recovery [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    (source : TSrc p c E rho) {i k : Nat} {K : FGBlock (Fin p.n)} {s u : Slot}
    {x : V} {t : Time} (hSource : SourceBefore p c E rho i K s) (hsu : s ≤ u)
    (hSync : E.t_GST ≤ SA.voteTime p.toParams u) (hx : x ∈ rho.honest)
    (hk : rho.events[k]? = some (.tick x t)) (hafter : SA.freezeTime p.toParams u < t)
    (hFloor : FGBlock.Preceq (storeAt p c E rho k x).fg.F K) :
    TargetReceiptService E rho (eraseFG K) (SA.freezeTime p.toParams u) x := by
  obtain ⟨j, y, r, a, _, ha, hK, rfl⟩ := hSource
  obtain ⟨jz, z, W, hz, hjz, hW, hKW⟩ :=
    healing_source_supporter_head E rho hrec.toRecovery₂ source ha.1 hK
  have hKs := KitFG.ancestor_closed_of_parent_closed _
    (storeBundle_stateBefore E rho jz z).cstore.fg.closed W hW K hKW
  have he : SA.earlyTime p.toParams u + p.Δ = SA.freezeTime p.toParams u := by
    change 4 * p.Δ * (u : Int) + 2 * p.Δ + p.Δ = 4 * p.Δ * (u : Int) + 3 * p.Δ
    ring
  have hFE := healing_receipt_floor_before_tick E rho hrec.base.valid.toScheduleWellFormed
    mono hx hk hafter.le (eraseFG_preceq hFloor)
  have hpub : V2.PublicTime E (SA.earlyTime p.toParams u) := by
    refine ⟨4 * u + 2, ?_⟩
    rw [hrec.base.delta]
    change 4 * p.Δ * (u : Int) + 2 * p.Δ = _
    push_cast
    ring
  rw [← he] at hFE ⊢
  refine healing_target_service_of_earlier_tick E rho hrec hz hx hjz
    (((storeBundle_stateBefore E rho jz z).cstore.baseTree _).mpr ⟨K, hKs, rfl⟩)
    ?_ hpub ?_ ?_ (Bool.or_eq_true_iff.mpr (Or.inr hFE))
  · change 4 * p.Δ * ((r * p.R : Nat) : Int) + p.Δ < 4 * p.Δ * (u : Int) + 2 * p.Δ
    have hsuI : ((r * p.R : Nat) : Int) ≤ u := by exact_mod_cast hsu
    nlinarith [p.deltaPos]
  · apply le_trans hSync
    change 4 * p.Δ * (u : Int) + p.Δ ≤ 4 * p.Δ * (u : Int) + 2 * p.Δ
    linarith [p.deltaPos]
  · exact he ▸ hafter.le.trans (hrec.base.valid.in_horizon _ (List.mem_of_getElem? hk)).2

private theorem leaseMove_source_receipt [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    (source : TSrc p c E rho) {i : Nat} {K : FGBlock (Fin p.n)} {s : Slot}
    (hK : SourceBefore p c E rho i K s) {u : Slot} (hsu : s ≤ u)
    (hgst : E.t_GST ≤ SA.voteTime p.toParams u) {k : Nat} {x : V} {t : Time}
    (hafter : SA.freezeTime p.toParams u < t) (hx : x ∈ rho.honest)
    (hk : rho.events[k]? = some (.tick x t))
    (hF : FGBlock.Preceq (storeAt p c E rho k x).fg.F K) :
    K ∈ (storeAt p c E rho (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams u)) x).fg.TF := by
  have hs := hrec.base.valid.toScheduleWellFormed
  have hb := fgsa_target_receipt_on E rho hs hrec.base.receiptIdealization (eraseFG K)
    (SA.freezeTime p.toParams u) x hx
    (healing_source_before_receipt_at_recovery p c E rho hrec mono source
      hK hsu hgst hx hk hafter hF)
  obtain ⟨Y, hY, heY⟩ := ((storeBundle_stateBeforeTime E rho _ x).cstore.baseTree _).mp hb
  have he : Y = K := eraseFG_injective heY
  subst Y
  change K ∈ (rho.stateBefore E (V2.D.Run.idxBefore rho _) x).st.fg.TF
  rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hs]
  exact hY

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.15:2916–2923; plan J4A2-2 G1 cut guard;
B1/B17/B18. DC: SAME inclusive HEAD cut before a reader after freeze.
The event at iy is later than the label-l HEAD time. Thus the complete
HEAD batch is before iy, including equal-time HEAD events. -/
theorem postReset_moving_head_cut (hs : V2.D.ScheduleWellFormed E rho)
    {iy : Nat} {y : V} {l : Slot} {t : Time}
    (hiy : rho.events[iy]? = some (.tick y t))
    (hafter : SA.freezeTime p.toParams l < t) :
    timeIdx rho (SA.voteTime p.toParams l) ≤ iy := by
  by_contra hn
  have ht := (V2.D.Engine.index_lt_read_length_iff hs _ hiy).mp (Nat.lt_of_not_ge hn)
  have hvl : SA.voteTime p.toParams l ≤ SA.freezeTime p.toParams l := by
    change 4 * p.Δ * (l : Int) + p.Δ ≤ 4 * p.Δ * (l : Int) + 3 * p.Δ
    linarith [p.deltaPos]
  exact (not_lt_of_ge (ht.trans hvl)) hafter

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
private theorem leaseMove_source_label {iy : Nat} {y : V} {l : Slot} {t : Time}
    (hiy : rho.events[iy]? = some (.tick y t))
    (hupper : t ≤ SA.voteTime p.toParams (l + 1))
    {K : FGBlock (Fin p.n)} {r : Slot} (hK : SourceBefore p c E rho iy K r) :
    r + 1 ≤ l := by
  have ht := (healing_source_gate p c E rho
    hrec.base.valid.toScheduleWellFormed hK hiy).trans hupper
  change 4 * p.Δ * (r : Int) + 6 * p.Δ ≤
    4 * p.Δ * ((l + 1 : Nat) : Int) + p.Δ at ht
  push_cast at ht
  have hrs : (r : Int) < l := by
    by_contra hn
    have hlr : (l : Int) ≤ r := le_of_not_gt hn
    nlinarith [p.deltaPos]
  exact_mod_cast hrs

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.15:2916–2923, H.2:709–746; plan J4A2-2 G2;
B1/B13/B17/B18. DC: INTENTIONAL domain at a moving reader after freeze.
The label-l batch covers the target. The view contains the frozen store
and is a subset of the reader's tree. Root and finality coverage are the
other descent arms. Only the prior high field at i is read, with iy ≤ i.
No emitted-source witness for B, THigh input, or H4 input is used. -/
theorem postReset_moving_domain
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    {l : Slot} {B : FGBlock (Fin p.n)}
    (hgst : E.t_GST ≤ SA.voteTime p.toParams l)
    (hCB : Block.Preceq w.CStar (eraseFG B))
    (hbatch : ∀ z ∈ rho.honest, ∀ H, headAtLabel p c E rho z l = some H →
      Block.Preceq (eraseFG B) H)
    {iy : Nat} {y : V} {t : Time} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y t)) (hyi : iy ≤ i)
    (hafter : SA.freezeTime p.toParams l < t)
    (hupper : t ≤ SA.voteTime p.toParams (l + 1))
    {X : Finset (FGBlock (Fin p.n))}
    (hX : X ⊆ (storeAt p c E rho iy y).fg.TF)
    (hfrozen : (storeAt p c E rho
      (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams l)) y).fg.TF ⊆ X)
    (hnZ : ¬ FGBlock.Preceq B (R_at p c E rho iy y).Z)
    (hnF : ¬ FGBlock.Preceq B (storeAt p c E rho iy y).fg.F) :
    B ∈ D_at p c E rho iy y X := by
  have hs := hrec.base.valid.toScheduleWellFormed
  have hvl : SA.voteTime p.toParams l ≤ SA.freezeTime p.toParams l := by
    change 4 * p.Δ * (l : Int) + p.Δ ≤ 4 * p.Δ * (l : Int) + 3 * p.Δ
    linarith [p.deltaPos]
  have hhor := (hs.in_horizon _ (List.mem_of_getElem? hiy)).2
  obtain ⟨jy, hjy⟩ := healing_support_vote_tick E rho hs hrec.base.delta hy l
    (hvl.trans (hafter.le.trans hhor))
    (hrec.awake y hy _ hgst (hvl.trans (hafter.le.trans hhor)))
  have hhead : headAtLabel p c E rho y l = some (headAtIdx p c E rho jy l) := by
    delta headAtLabel
    rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hs hjy]
    rw [healing_headAtIdx_tick p c E rho hjy]
    rfl
  have hBH := hbatch y hy _ hhead
  have hHstore : headAtIdx p c E rho jy l ∈ (storeAt p c E rho jy y).base.blocks := by
    rw [healing_headAtIdx_tick p c E rho hjy]
    have hm := headVote_stored p _ (cstoreInv_clock p (storeAt p c E rho jy y)
      (cstoreInv_stateBefore E rho jy y) (SA.voteTime p.toParams l)) l
    rwa [clock_base_blocks] at hm
  obtain ⟨W, hW, heW⟩ := (cstoreInv_stateBefore E rho jy y).baseTree _ |>.mp hHstore
  have hBstore : B ∈ (storeAt p c E rho jy y).fg.TF := by
    obtain ⟨A, hA, heA⟩ := eraseFG_ancestor_mem (cstoreInv_stateBefore E rho jy y).fg.closed
      hW (heW ▸ hBH)
    exact (eraseFG_injective heA) ▸ hA
  obtain ⟨-, -, -, Cfg, -, -, -, heC, hhC⟩ := h0r.fresh
  have hCBfg : FGBlock.Preceq Cfg B := leaseMove_lift p (by rwa [heC])
  have hhB : high p w B := by
    rw [high_def]
    exact hhC ▸ (fgCertificateLaws p).height.h_mono hCBfg
  have noLoss := (healing_high_source_compat p c E rho hrec
    (healing_loss_service_scope_recovery E rho hrec mono source emittedNonempty emittedName)
    mono emittedNonempty
    emittedName writes xing origin).1
  have hBK : ∀ K r, SourceBefore p c E rho iy K r → high p w K →
      Block.Compatible (eraseFG B) (eraseFG K) := by
    intro K r hK hhK
    have hrs := leaseMove_source_label p c E rho hrec hiy hupper hK
    have hKn : HighSrcN p c E rho K r := by
      rw [HighSrcN_def]
      rw [high_def] at hhK
      exact ⟨healing_srcN_of_source p c E rho hK,
        (Nat.succ_le_succ h0r.mu_le).trans hhK⟩
    have hKH : Block.Preceq (eraseFG K) (headAtIdx p c E rho jy l) := by
      by_contra hn
      apply noLoss jy K r
      rw [Lost_def]
      exact ⟨hKn, y, l, hy, hrs, hjy, hn⟩
    exact Gen.Pure.block_compatible_of_common hBH hKH
  have hFB : FGBlock.Preceq (storeAt p c E rho iy y).fg.F B := by
    by_cases hFg : (storeAt p c E rho iy y).fg.F = .genesis
    · rw [hFg]; exact KitFG.genesis_preceq B
    obtain ⟨D, hD, hDF, K, r, hK, hhK, hKF, -⟩ :=
      healing_finality_source (hroots := hrec.base.idealization) p c E rho hs origin hy hFg
    by_cases hl : (finalityView p D).h_F < (heightView p B).h
    · exact xing iy (iy + jy) y y D B hy (Nat.le_add_right iy jy) hD hDF
        ⟨hy, (fgsa_store_durable p c E rho (Nat.le_add_left jy iy) y).1 hBstore⟩ hl
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
      · exact (KitFG.preceq_total_of_common hFK (leaseMove_lift p h)).resolve_right hnF
      · exact KitFG.preceq_trans hFK (leaseMove_lift p h)
  have he : SA.earlyTime p.toParams l + p.Δ = SA.freezeTime p.toParams l := by
    change 4 * p.Δ * (l : Int) + 2 * p.Δ + p.Δ = 4 * p.Δ * (l : Int) + 3 * p.Δ
    ring
  have hpub : V2.PublicTime E (SA.earlyTime p.toParams l) := by
    refine ⟨4 * l + 2, ?_⟩
    rw [hrec.base.delta]
    change 4 * p.Δ * (l : Int) + 2 * p.Δ = _
    push_cast
    ring
  have hFloor := healing_receipt_floor_before_tick E rho hs mono hy hiy hafter.le
    (eraseFG_preceq hFB)
  have hFH := Gen.Pure.block_preceq_trans hFloor hBH
  rw [← he] at hFH
  have service := healing_target_service_of_earlier_tick E rho hrec hy hy hjy hHstore
    (by change 4 * p.Δ * (l : Int) + p.Δ < 4 * p.Δ * (l : Int) + 2 * p.Δ
        linarith [p.deltaPos]) hpub
    (by apply hgst.trans
        change 4 * p.Δ * (l : Int) + p.Δ ≤ 4 * p.Δ * (l : Int) + 2 * p.Δ
        linarith [p.deltaPos])
    (he ▸ hafter.le.trans hhor) (Bool.or_eq_true_iff.mpr (Or.inr hFH))
  rw [he] at service
  have hb := fgsa_target_receipt_on E rho hs hrec.base.receiptIdealization _ _ y hy service
  obtain ⟨Y, hY, heY⟩ := ((storeBundle_stateBeforeTime E rho _ y).cstore.baseTree _).mp hb
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs] at hY
  have hBX : B ∈ X := by
    obtain ⟨A, hA, heA⟩ := eraseFG_ancestor_mem (cstoreInv_stateBefore E rho _ y).fg.closed
      hY (heY ▸ hBH)
    exact hfrozen ((eraseFG_injective heA) ▸ hA)
  have hcover : ∀ K r, SourceBefore p c E rho iy K r →
      FGBlock.Preceq (storeAt p c E rho iy y).fg.F K → FGBlock.Preceq B K →
      (heightView p B).h < (heightView p K).h →
      K ∈ X ∨ FGBlock.Preceq K (storeAt p c E rho iy y).fg.F := by
    intro K r hK hFK _hBK _hhK
    exact Or.inl (hfrozen (leaseMove_source_receipt p c E rho hrec mono source hK
      (Nat.le_of_succ_le (leaseMove_source_label p c E rho hrec hiy hupper hK))
      hgst hafter hy hiy hFK))
  have hhigh := hinv.high_compatible
  rw [PostResetHighCompatible_def] at hhigh
  have hsrc : ∀ K r, SourceBefore p c E rho iy K r → SourceBefore p c E rho i K r := by
    intro K r hK
    obtain ⟨a, z, q, row, haj, hrow, hsrc, he⟩ := hK
    exact ⟨a, z, q, row, haj.trans_le hyi, hrow, hsrc, he⟩
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
      (hhigh K K' r r' (hsrc K r hK) (hsrc K' r' hK') hhK hhK'))

end AvailableChain.FGSA.Run
end

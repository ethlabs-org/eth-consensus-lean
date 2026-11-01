module
public import AvailableChainFGSAProofs.Proofs.Healing.DeliveryReset
public import AvailableChainFGSAProofs.Proofs.Healing.DescentTimingRFProv
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetInvariant

public section

/-! Blueprint 21 H.12:2652–2666, IF.3(c); post-reset plan J1.
B1/B13/B15/B17/B18: reset-only inputs and compatibility before delivery.
DC: the pre-action reset transfer uses the honest supporting HEAD, not
an action source held only after the reset action. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private theorem reset_action_mono (p : Params) {r r' : Nat} (h : r ≤ r') :
    p.actionTime r ≤ p.actionTime r' := by
  change 4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ ≤
    4 * p.Δ * ((r' * p.R : Nat) : Int) + 6 * p.Δ
  gcongr
  linarith [p.deltaPos]

private theorem reset_release_before_action (p : Params) (w : HealingWitness)
    (hlabel : w.sStar = w.rStar * p.R) :
    SA.releaseTime p.toParams w.sStar < p.actionTime w.rStar := by
  rw [hlabel]
  change 4 * p.Δ * ((w.rStar * p.R : Nat) : Int) + 5 * p.Δ <
    4 * p.Δ * ((w.rStar * p.R : Nat) : Int) + 6 * p.Δ
  linarith [p.deltaPos]

private theorem reset_height_bound (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (cap : RCap p c E rho) (w : HealingWitness) (h0r : H0Reset p c E rho w)
    {i : Nat} {x : V} {W : FGBlock (Fin p.n)} (hW : HeldAt p c E rho i x W)
    (hcut : ∀ j z r a, j < i → HonestRowAt p c E rho j z r a →
      p.actionTime r < p.actionTime w.rStar) :
    (heightView p W).h ≤ w.M + 1 := by
  by_contra hn
  obtain ⟨j, z, r, a, e, hji, ha, he, _⟩ :=
    cap w.M i x W hW (by simp only [Height] at *; omega)
  have hr := h0r.reset_first r ⟨j, z, a, e, ha, he⟩
  exact (not_lt_of_ge (reset_action_mono p hr)) (hcut j z r a hji ha)

omit [DecidableEq V] in
private theorem reset_tick_cut (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {j : Nat} {x : V} {t : Time}
    (hj : rho.events[j]? = some (.tick x t)) : j < afterTicksIdx rho t := by
  by_contra hn
  have hc : cutPred (P := fgsa p c) t (.tick x t) = true := by
    change decide (toLex (t, 1) ≤ toLex (t, 1)) = true
    exact decide_eq_true le_rfl
  have hf := V2.D.Engine.filter_false_of_index_ge hs (cutPred t)
    (fun e f h ef => decide_eq_true (h.trans (of_decide_eq_true ef)))
    (Nat.le_of_not_gt hn) hj
  rw [hc] at hf
  contradiction

/-- Blueprint 21 IF.3(c), H.12:2652–2660; plan J1; B1/B13/B17.
DC: the existing after-action low arm with H0Reset in place of H0.
Only `fresh` is used. Assembly supplies `fgsa_rXing`; execution validity
supplies the schedule, and Recovery₂ supplies no restart. -/
theorem healing_low_finality_after_reset (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (hnr : V2.D.NoRestart rho) (xing : RXing p c E rho)
    (w : HealingWitness) (h0r : H0Reset p c E rho w) {i : Nat} {x : V}
    {D : FGBlock (Fin p.n)} (hx : x ∈ rho.honest)
    (hi : afterTicksIdx rho (p.actionTime w.rStar) ≤ i)
    (hD : D ∈ (storeAt p c E rho i x).fg.TF)
    (hDF : (finalityView p D).F = (storeAt p c E rho i x).fg.F)
    (hlow : (finalityView p D).h_F ≤ w.M) :
    Block.Preceq (F_at p c E rho i x) w.CStar := by
  obtain ⟨j, y, a, C, ha, _, hC, hCS, hCh⟩ := h0r.fresh
  have hji : j ≤ i := (Nat.le_of_lt (reset_tick_cut E rho hs ha.2.1)).trans hi
  have hheld := healing_action_source_held p c E rho hs ha.2.1 hC
  have hheld' := (fgsa_store_cumulative p c E rho hnr hji y).1 hheld
  have hFC := xing i i x y D C hx le_rfl hD hDF ⟨ha.1, hheld'⟩
    (by rw [hCh]; exact Nat.lt_succ_of_le hlow)
  rw [← hCS]
  exact eraseFG_preceq hFC

/-- Kept FG content supplies the after-action low arm through wake restarts. -/
theorem healing_low_finality_after_reset_on (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (xing : RXing p c E rho)
    (w : HealingWitness) (h0r : H0Reset p c E rho w) {i : Nat} {x : V}
    {D : FGBlock (Fin p.n)} (hx : x ∈ rho.honest)
    (hi : afterTicksIdx rho (p.actionTime w.rStar) ≤ i)
    (hD : D ∈ (storeAt p c E rho i x).fg.TF)
    (hDF : (finalityView p D).F = (storeAt p c E rho i x).fg.F)
    (hlow : (finalityView p D).h_F ≤ w.M) :
    Block.Preceq (F_at p c E rho i x) w.CStar := by
  obtain ⟨j, y, a, C, ha, _, hC, hCS, hCh⟩ := h0r.fresh
  have hji : j ≤ i := (Nat.le_of_lt (reset_tick_cut E rho hs ha.2.1)).trans hi
  have hheld := healing_action_source_held p c E rho hs ha.2.1 hC
  have hheld' := (fgsa_store_durable p c E rho hji y).1 hheld
  have hFC := xing i i x y D C hx le_rfl hD hDF ⟨ha.1, hheld'⟩
    (by rw [hCh]; exact Nat.lt_succ_of_le hlow)
  rw [← hCS]
  exact eraseFG_preceq hFC

/-- Blueprint 21:2652–2660, IF.3(c); plan J1; B1/B13/B17.
DC: pre-action finality floor at q_(s*). Assembly supplies `fgsa_rXing`,
`fgsa_rCap_channel`, and `sourceDiscipline_tSrc`, with exactly their channel
predicates. Recovery₂ supplies execution validity and no restart. -/
theorem healing_low_finality_at_reset_reset [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (xing : RXing p c E rho) (cap : RCap p c E rho) (source : TSrc p c E rho)
    (w : HealingWitness) (h0r : H0Reset p c E rho w) :
    ∀ x ∈ rho.honest, Block.Preceq
      (eraseFG (V2.D.Run.stateBeforeTime E rho (SA.releaseTime p.toParams w.sStar) x).st.fg.F)
      w.CStar := by
  have hs := hrec.base.valid.toScheduleWellFormed
  let i := V2.D.Run.idxBefore rho (SA.releaseTime p.toParams w.sStar)
  have hread := Gen.V2.Duty.stateBefore_idxBefore E rho
    (SA.releaseTime p.toParams w.sStar) hs
  have hqa := reset_release_before_action p w h0r.label
  intro x hx
  obtain ⟨j, y, a, C, ha, _, hC, hCS, hCh⟩ := h0r.fresh
  obtain ⟨k, z, W, hz, hk, hW, hCW⟩ :=
    healing_source_supporter_head E rho hrec source ha.1 hC
  have hCk : C ∈ (storeAt p c E rho k z).fg.TF :=
    KitFG.ancestor_closed_of_parent_closed _ (cstoreInv_stateBefore E rho k z).fg.closed
      W hW C hCW
  have hki : k ≤ i := by
    apply Nat.le_of_lt
    apply (Gen.V2.Duty.index_lt_idxBefore_iff hs hk _).mpr
    change SA.voteTime p.toParams (w.rStar * p.R) < _
    rw [h0r.label]
    change 4 * p.Δ * ((w.rStar * p.R : Nat) : Int) + p.Δ <
      4 * p.Δ * ((w.rStar * p.R : Nat) : Int) + 5 * p.Δ
    linarith [p.deltaPos]
  have hCi := (fgsa_store_durable p c E rho hki z).1 hCk
  obtain ⟨D, hD, hDF⟩ := (cstoreInv_stateBefore E rho i x).fg.Fcar
  have hDh := reset_height_bound E rho cap w h0r ⟨hx, hD⟩ (by
    intro l v r b hli hb
    have ht := (Gen.V2.Duty.index_lt_idxBefore_iff hs hb.2.1 _).mp hli
    exact ht.trans hqa)
  have hlow := KitFG.finalized_below_height_of_certificate p.E
    (heightView p) (finalityView p) (fgCertificateLaws p) D
  have hFC := xing i i x z D C hx le_rfl hD hDF ⟨hz, hCi⟩
    (by rw [hCh]; simp only [Height] at *; omega)
  rw [← hCS, ← hread]
  exact eraseFG_preceq hFC

/-- Blueprint 21:2655–2666; plan J1; B1/B13/B15/B17/B18.
DC: reset transfer at each node's own release tick, with its covered view.
The floor bound uses Controls.lo_le_H; the J/contest split proves Z ⪯ C.
Assembly supplies `fgsa_rXing`, `fgsa_rCap_channel`,
`sourceDiscipline_tSrc`, and `fgsa_rMono`. No common node state is used. -/
theorem healing_resetTransferCore [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (xing : RXing p c E rho) (cap : RCap p c E rho) (source : TSrc p c E rho)
    (mono : RMonoAll p c E rho) (w : HealingWitness) (h0r : H0Reset p c E rho w)
    (hServices : ∀ x ∈ rho.honest, ∀ j z W, z ∈ rho.honest →
      rho.events[j]? = some (.tick z (SA.voteTime p.toParams w.sStar)) →
      W ∈ (storeAt p c E rho j z).fg.TF →
      Block.Preceq w.CStar (eraseFG W) →
      FGBlock.Preceq
        (rho.stateBeforeTime E (SA.earlyTime p.toParams w.sStar) x).st.fg.F W →
      TargetReceiptService E rho (eraseFG W) (SA.earlyTime p.toParams w.sStar) x)
 :
    ResetTransferCore p c E rho w := by
  rw [ResetTransferCore_def]
  intro hhor j x hx hj
  have hs := hrec.base.valid.toScheduleWellFormed
  let i := V2.D.Run.idxBefore rho (SA.releaseTime p.toParams w.sStar)
  have hij : i ≤ j := by
    apply Nat.le_of_not_gt
    intro hn
    have ht := (Gen.V2.Duty.index_lt_idxBefore_iff hs hj _).mp hn
    exact (lt_irrefl _) ht
  have hdel := healing_tDelReset_core E rho hrec source mono w h0r hhor
    (healing_low_finality_at_reset_reset E rho hrec xing cap source w h0r) hServices x hx
  rw [Gen.V2.Duty.HoldsBefore_def,
    ← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs] at hdel
  obtain ⟨C, hC, hCS⟩ := hdel
  have hCj := (fgsa_store_durable p c E rho hij x).1 hC
  refine ⟨⟨C, hCj, hCS⟩, ?_⟩
  intro X C hX hCX hCS _hcover _hreset _hpair
  let st := storeAt p c E rho j x
  have hI : KitFG.FGStoreInvariant (heightView p) (finalityView p) st.fg :=
    (cstoreInv_stateBefore E rho j x).fg
  have hja : j < V2.D.Run.idxBefore rho (p.actionTime w.rStar) :=
    (Gen.V2.Duty.index_lt_idxBefore_iff hs hj _).mpr
      (reset_release_before_action p w h0r.label)
  have hcut : ∀ l z r a, l < j → HonestRowAt p c E rho l z r a →
      p.actionTime r < p.actionTime w.rStar := by
    intro l z r a hlj ha
    exact (Gen.V2.Duty.index_lt_idxBefore_iff hs ha.2.1 _).mp (hlj.trans hja)
  have hbound : ∀ W ∈ st.fg.TF, (heightView p W).h ≤ w.M + 1 := by
    intro W hW
    exact reset_height_bound E rho cap w h0r ⟨hx, hW⟩ hcut
  have hCh : (heightView p C).h = w.M + 1 := by
    obtain ⟨_, _, _, C0, _, _, _, hC0, hh⟩ := h0r.fresh
    have he : C = C0 := eraseFG_injective (hCS.trans hC0.symm)
    exact he ▸ hh
  have hmax : st.fg.h_max = w.M + 1 := by
    rw [hI.hmax]
    apply le_antisymm
    · have hup : st.fg.TF.sup (fun W => (heightView p W).h) ≤ w.M + 1 :=
        Finset.sup_le hbound
      exact sup_le hup (Nat.succ_le_succ (Nat.zero_le w.M))
    · have hsup : (heightView p C).h ≤ st.fg.TF.sup (fun W => (heightView p W).h) :=
        Finset.le_sup (f := fun W => (heightView p W).h) (show C ∈ st.fg.TF from hX hCX)
      exact hCh ▸ hsup.trans le_sup_left
  have hH : (R_at p c E rho j x).H = w.M + 1 := hmax
  have hlo : (R_at p c E rho j x).lo ≤ (heightView p C).h := by
    rw [hCh, ← hH]
    exact KitFG.Controls.lo_le_H _
  obtain ⟨D, hD, hDF⟩ := hI.Fcar
  have hDh := hbound D hD
  have hlow := KitFG.finalized_below_height_of_certificate p.E
    (heightView p) (finalityView p) (fgCertificateLaws p) D
  have hFC : FGBlock.Preceq st.fg.F C :=
    xing j j x x D C hx le_rfl hD hDF ⟨hx, hX hCX⟩
      (by rw [hCh]; simp only [Height] at *; omega)
  have hZC : FGBlock.Preceq (R_at p c E rho j x).Z C := by
    change FGBlock.Preceq (if (R_at p c E rho j x).rootIsJ then st.fg.J else st.fg.F) C
    cases hr : (R_at p c E rho j x).rootIsJ with
    | false => exact hFC
    | true =>
      have hr' := hr
      change (decide (st.fg.h_max = st.fg.h_j + 1) &&
        !(R_at p c E rho j x).contest) = true at hr'
      obtain ⟨htop, hnc⟩ := Bool.and_eq_true_iff.mp hr'
      have hc : (R_at p c E rho j x).contest = false := by
        simpa only [Bool.not_eq_true'] using hnc
      by_contra hn
      have ht : (R_at p c E rho j x).contest = true := by
        change (decide (st.fg.h_max = st.fg.h_j + 1) &&
          decide (∃ W ∈ st.fg.TF, FGBlock.Preceq st.fg.F W ∧
            (heightView p W).h = st.fg.h_max ∧ ¬ FGBlock.Preceq st.fg.J W)) = true
        exact Bool.and_eq_true_iff.mpr ⟨htop, decide_eq_true
          ⟨C, hX hCX, hFC, hCh.trans hmax.symm, hn⟩⟩
      rw [hc] at ht
      contradiction
  refine ⟨hCh, hH, hlo, ?_⟩
  intro _hpath
  have hdomain : C ∈ D_at p c E rho j x X :=
    (KitFG.mem_filteredFromView (heightView p) (R_at p c E rho j x) X C).mpr
      ⟨hCX, hFC, hZC, C, hCX, KitFG.preceq_refl C, hlo⟩
  exact ⟨hdomain, Or.inr (Or.inl hdomain)⟩

/-- Blueprint 21:2652–2660; plan J1; B1/B13/B17.
DC: thin H0 adapter to the reset-only delivery proof. Assembly supplies
`fgsa_rXing`, `fgsa_rCap_channel`, `sourceDiscipline_tSrc`, and `fgsa_rMono`.
The release finality premise is discharged; H0 is used only by this adapter. -/
theorem healing_tDelReset_of_reset [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (xing : RXing p c E rho) (cap : RCap p c E rho) (source : TSrc p c E rho)
    (mono : RMonoAll p c E rho) (w : HealingWitness)
    (hServices : H0Reset p c E rho w → SA.releaseTime p.toParams w.sStar ≤ rho.horizon →
      ∀ x ∈ rho.honest, ∀ j z W, z ∈ rho.honest →
      rho.events[j]? = some (.tick z (SA.voteTime p.toParams w.sStar)) →
      W ∈ (storeAt p c E rho j z).fg.TF →
      Block.Preceq w.CStar (eraseFG W) →
      FGBlock.Preceq
        (rho.stateBeforeTime E (SA.earlyTime p.toParams w.sStar) x).st.fg.F W →
      TargetReceiptService E rho (eraseFG W) (SA.earlyTime p.toParams w.sStar) x) :
    TDelReset p c E rho w := by
  intro h0 hhor
  exact healing_tDelReset_core E rho hrec source mono w h0.toH0Reset hhor
    (healing_low_finality_at_reset_reset E rho hrec xing cap source w h0.toH0Reset)
    (hServices h0.toH0Reset hhor)

end AvailableChain.FGSA.Run
end

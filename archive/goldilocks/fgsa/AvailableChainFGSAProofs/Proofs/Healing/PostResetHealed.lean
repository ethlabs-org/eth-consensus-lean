module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetService
public import AvailableChainFGSAProofs.Proofs.Healing.Repair
public import AvailableChainFGSAProofs.Proofs.Healing.ResetScope

public section

/-! Blueprint 21 H.18:3049–3103, H.22:3229–3241, H0 proof:3371–3374;
plan J7 A–E. DC: SAME reset fields, proposal grid, and frozen service fields.
Each missing service is a named field with its planned producer. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.18:3049–3103, H0 proof:3373–3374; plan J7 A.
DC: SAME source-to-parent transfer. Named TCarrier producer: J3 rest.
The actual fresh source has height M+1; its parent prefix gives C* ⪯ Q*. -/
theorem healing_sourcePrefix {w : HealingWitness}
    (tCarrier : TCarrier p c E rho w) (hreset : H0Reset p c E rho w)
    (start : PostResetStart p c E rho w) : Block.Preceq w.CStar w.QStar := by
  obtain ⟨j, y, a, K, hrow, _, hsource, herase, hheight⟩ := hreset.fresh
  have hhigh : high p w K := by rw [high_def, hheight]
  have hparent := tCarrier y w.rStar K w.u w.QStar hrow.1 hsource hhigh
    start.proposal (by simpa only [hreset.label] using start.proposal_lower)
  rw [herase] at hparent
  apply block_preceq_trans hparent
  cases w.QStar with
  | genesis => exact block_preceq_refl _
  | node P s root b =>
    change (decide (P = Block.node P s root b) || Block.preceq P P) = true
    exact Bool.or_eq_true_iff.mpr (Or.inr (block_preceq_refl P))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.18:3097–3100; plan J7 B.
DC: SAME t_(s*+1) < t_s implies s*+2 ≤ s on the 4Δ proposal grid. -/
theorem healing_proposal_grid_lower (w : HealingWitness) {s : Slot}
    (hstrict : SA.proposalTime p.toParams (w.sStar + 1) <
      SA.proposalTime p.toParams s) : w.sStar + 2 ≤ s := by
  change 4 * p.Δ * ((w.sStar + 1 : Nat) : Int) < 4 * p.Δ * (s : Int) at hstrict
  have hcast : (w.sStar : Int) + 1 < s := by
    push_cast at hstrict
    nlinarith [p.deltaPos]
  have hnat : w.sStar + 1 < s := by exact_mod_cast hcast
  exact Nat.succ_le_of_lt hnat

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.18:3057–3059,3097–3100; plan J7 B.
DC: SAME d_s ≤ a_(r*)+Γ+4Δ, from the strict proposal-grid trigger. -/
theorem healing_firstProposal_deadline {w : HealingWitness}
    (hreset : H0Reset p c E rho w) (G : Time) {s : Slot}
    (hupper : SA.proposalTime p.toParams s ≤
      SA.proposalTime p.toParams (w.sStar + 1) + Γ p G) :
    SA.gateTime p.toParams s ≤ p.actionTime w.rStar + Γ p G + 4 * p.Δ := by
  have ha : p.actionTime w.rStar = SA.gateTime p.toParams (w.rStar * p.R) := rfl
  rw [← hreset.label] at ha
  change 4 * p.Δ * (s : Int) ≤
    4 * p.Δ * ((w.sStar + 1 : Nat) : Int) + Γ p G at hupper
  change p.actionTime w.rStar = 4 * p.Δ * (w.sStar : Int) + 6 * p.Δ at ha
  change 4 * p.Δ * (s : Int) + 6 * p.Δ ≤ _
  push_cast at hupper
  linarith

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.18:3097–3100, H.22:3239–3241; plan J7 B.
DC: SAME first actual honest proposal, selected by Nat.find.
The local horizon a_(r*)+Γ+4Δ ≤ horizon contains the full gap window and gate.
Recovery₂ supplies the gap, awake proposer, valid schedule, and Γ=G. -/
theorem healing_firstProposal [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {w : HealingWitness}
    (hreset : H0Reset p c E rho w)
    (hhor : p.actionTime w.rStar + Γ p G + 4 * p.Δ ≤ rho.horizon) :
    ∃ u Q, PostResetStart p c E rho {w with u := u, QStar := Q} ∧
      tstar p {w with u := u, QStar := Q} ≤
        p.actionTime w.rStar + Γ p G + 4 * p.Δ := by
  classical
  have hd := p.deltaPos
  have ha : p.actionTime w.rStar = SA.gateTime p.toParams (w.rStar * p.R) := rfl
  rw [← hreset.label] at ha
  have htrigger : recoveryStart p E ≤ SA.proposalTime p.toParams (w.sStar + 1) := by
    have hsync := healing_reset_source_ready hreset
    change recoveryStart p E ≤ 4 * p.Δ * (w.sStar : Int) + p.Δ at hsync
    change recoveryStart p E ≤ 4 * p.Δ * ((w.sStar + 1 : Nat) : Int)
    push_cast
    linarith
  have hwindow : SA.proposalTime p.toParams (w.sStar + 1) + G ≤ rho.horizon := by
    have := (fgsa_gamma_bounds p G).1
    change p.actionTime w.rStar = 4 * p.Δ * (w.sStar : Int) + 6 * p.Δ at ha
    change 4 * p.Δ * ((w.sStar + 1 : Nat) : Int) + G ≤ rho.horizon
    push_cast
    linarith
  obtain ⟨s, hlo, hhi, hs⟩ := hrec.gap _ (by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]) hwindow
  rw [proposalTime_fgsa] at hlo hhi
  have hlower := healing_proposal_grid_lower p w hlo
  obtain ⟨Q, hQ⟩ := repair_honest_proposal E rho hrec hs
    (by have := healing_recovery_start_lower (p := p) E
        linarith [p.deltaPos])
    ((healing_ready_proposal_window E (htrigger.trans hlo.le)).prior.cut_mono (Nat.sub_le s 1)).2
    (hhi.trans hwindow)
  have hex : ∃ v, w.sStar + 2 ≤ v ∧
      ∃ B, HonestProposal E rho (fgsaInterface p c) v B := ⟨s, hlower, Q, hQ⟩
  let u := Nat.find hex
  obtain ⟨hu, B, hB⟩ := Nat.find_spec hex
  have hus : u ≤ s := Nat.find_min' hex ⟨hlower, Q, hQ⟩
  have hfirst : ∀ v Q, w.sStar + 2 ≤ v →
      HonestProposal E rho (fgsaInterface p c) v Q → u ≤ v := by
    intro v Q hv hp
    exact Nat.find_min' hex ⟨hv, Q, hp⟩
  have hupper : SA.proposalTime p.toParams u ≤
      SA.proposalTime p.toParams (w.sStar + 1) + Γ p G := by
    have hgrid := repair_grid_Γ hhi
    have hcast : (u : Int) ≤ s := by exact_mod_cast hus
    change 4 * p.Δ * (u : Int) ≤ _
    change 4 * p.Δ * (s : Int) ≤ _ at hgrid
    nlinarith
  have hbound := healing_firstProposal_deadline p c E rho hreset G hupper
  have hgst : E.t_GST ≤ tstar p {w with u := u, QStar := B} := by
    have hcast : (w.sStar : Int) + 2 ≤ u := by exact_mod_cast hu
    have hsync := hreset.synchronous
    change E.t_GST ≤ 4 * p.Δ * (w.sStar : Int) + p.Δ at hsync
    change E.t_GST ≤ 4 * p.Δ * (u : Int) + 6 * p.Δ
    nlinarith
  refine ⟨u, B, ?_, hbound⟩
  exact
    { toH0Reset := by cases hreset; constructor <;> assumption
      proposal_lower := hu
      proposal := hB
      proposal_first := hfirst
      after_gst := hgst }

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H0 proof:3371–3374, H.22:3229–3241; plan J7 C.
DC: SAME reset data; only u and QStar change. Named TCarrier producer: J3 rest. -/
theorem healing_h0_of [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {w : HealingWitness}
    (tCarrier : TCarrier p c E rho w) (hreset : H0Reset p c E rho w)
    (hhor : p.actionTime w.rStar + Γ p G + 4 * p.Δ ≤ rho.horizon) :
    ∃ u Q, H0 p c E rho {w with u := u, QStar := Q} ∧
      tstar p {w with u := u, QStar := Q} ≤
        p.actionTime w.rStar + Γ p G + 4 * p.Δ := by
  obtain ⟨u, Q, start, htime⟩ := healing_firstProposal p c E rho hrec hreset hhor
  exact ⟨u, Q, PostResetStart.toH0 p c E rho start
    (healing_sourcePrefix p c E rho tCarrier start.toH0Reset start), htime⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.18:3061, H.22 H4; plan J7 D, first clause.
DC: SAME stable output at d_u. Named H3 producer: J6-3 PostResetService/opening_domain. -/
theorem healing_h4_stable [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {w : HealingWitness} (start : PostResetStart p c E rho w)
    (h3 : H3 p c E rho w) (hhor : tstar p w ≤ rho.horizon) :
    ∀ x ∈ rho.honest,
      (fgsaInterface p c).stable (afterTicks E rho (tstar p w) x) = w.QStar := by
  intro x hx
  have hReader := healing_recovery_gate_reader hrec hx
    (healing_reset_slot_cutoff start.toH0Reset |>.trans (by
      have hu : (w.sStar : Int) ≤ w.u := by
        exact_mod_cast (Nat.le_add_right w.sStar 2 |>.trans start.proposal_lower)
      change 4 * p.Δ * (w.sStar : Int) ≤ 4 * p.Δ * (w.u : Int)
      nlinarith [p.deltaPos])) hhor
  exact (h3 w.u w.QStar start.proposal start.proposal_lower).2 hhor x hx hReader |>.2.2.2.1

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.18:3061, H.22 H4; plan J7 D, first clause via carrier.
DC: SAME service cut. Named PostResetService producer: J6-3/opening_domain. -/
theorem healing_h4_stable_of_service [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {w : HealingWitness}
    (start : PostResetStart p c E rho w)
    (service : PostResetService p c E rho w rho.events.length)
    (hhor : tstar p w ≤ rho.horizon) :
    ∀ x ∈ rho.honest,
      (fgsaInterface p c).stable (afterTicks E rho (tstar p w) x) = w.QStar :=
  healing_h4_stable p c E rho hrec start
    (healing_postReset_exactService E rho w rho.events.length le_rfl service) hhor

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.18:3079–3093; plan J7 D, event cut.
DC: SAME a healing cut is before the strict cut at each later time. -/
private theorem healed_cut_lt {a b : Time} (hab : a < b) :
    healStart p c rho a ≤ V2.D.Run.idxBefore rho b := by
  rw [healStart_def]
  split
  all_goals
    change (rho.events.filter _).length ≤ (rho.events.filter _).length
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    apply List.countP_mono_left
    intro e _ he
  · have hea : e.time ≤ a := by
      rcases Prod.Lex.toLex_le_toLex.mp (of_decide_eq_true he) with h | ⟨h, _⟩
      · exact h.le
      · exact h.le
    exact decide_eq_true (hea.trans_lt hab)
  · exact decide_eq_true ((of_decide_eq_true he).trans_lt hab)

/-- A selected high source is after the reset cut, by durable membership. -/
private theorem healed_high_source_time (hs : V2.D.ScheduleWellFormed E rho)
    {w : HealingWitness} (h0r : H0Reset p c E rho w)
    {x : V} {r : Nat} {C : FGBlock (Fin p.n)} (hx : x ∈ rho.honest)
    (hsrc : actionSourceFG p c E rho x r = some (some C)) (hh : high p w C) :
    w.u₀ < p.actionTime r := by
  have htick : ∃ i : Nat, rho.events[i]? = some (.tick x (p.actionTime r)) := by
    rw [actionSourceFG_def, postClock_def, preTick_def] at hsrc
    cases hi : V2.D.Run.tickIdx? rho x (p.actionTime r) with
    | none => simp only [hi, Option.map_none] at hsrc; contradiction
    | some i => exact ⟨i, V2.D.Run.tickIdx?_spec hi⟩
  obtain ⟨i, hi⟩ := htick
  by_contra hn
  have hidx : i ≤ timeIdx rho w.u₀ :=
    ((V2.D.Engine.index_lt_read_length_iff hs w.u₀ hi).mpr (le_of_not_gt hn)).le
  have hheld := healing_action_source_held p c E rho hs hi hsrc
  have hcut := (fgsa_store_durable p c E rho hidx x).1 hheld
  have hI : KitFG.FGStoreInvariant (heightView p) (finalityView p)
      (storeAt p c E rho (timeIdx rho w.u₀) x).fg :=
    (cstoreInv_stateBefore E rho (timeIdx rho w.u₀) x).fg
  have hheight : (heightView p C).h ≤
      (storeAt p c E rho (timeIdx rho w.u₀) x).fg.h_max := by
    rw [hI.hmax]
    exact le_sup_of_le_left (Finset.le_sup (f := fun B => (heightView p B).h) hcut)
  have hfront : honestFrontier p c E rho w.u₀ =
      rho.honest.sup (fun y => (storeAt p c E rho (timeIdx rho w.u₀) y).fg.h_max) := by
    unfold honestFrontier storeAt timeIdx
    rw [V2.D.Engine.readAt_eq_stateBefore hs w.u₀]
  have hmax := Finset.le_sup
    (f := fun y => (storeAt p c E rho (timeIdx rho w.u₀) y).fg.h_max) hx
  rw [← hfront, ← h0r.frontier] at hmax
  rw [high_def] at hh
  simp only [Height] at *
  omega

/-- A positive clock after GST comes from a tick in the recovery suffix. -/
private theorem healed_now_tick [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {i : Nat} {x : V} (hx : x ∈ rho.honest)
    (hpos : 0 < (storeAt p c E rho i x).base.now)
    (hgst : E.t_GST < (storeAt p c E rho i x).base.now) :
    ∃ j < i, rho.events[j]? = some (.tick x (storeAt p c E rho i x).base.now) := by
  rcases V2.D.Engine.stateBefore_now_source_atRestart (fgsaClock p c)
    (fgsaRestoreTimeLaw p c) E rho i x with hzero | ⟨j, hj, ht | hr⟩
  · rw [fgsa_clock_now p c (rho.stateBefore E i x)] at hzero
    exact (ne_of_gt hpos hzero).elim
  · rw [fgsa_clock_now p c (rho.stateBefore E i x)] at ht
    exact ⟨j, hj, ht⟩
  · rw [fgsa_clock_now p c (rho.stateBefore E i x)] at hr
    have hbound := healing_scope_restart_bound hrec hx
      (hrec.base.valid.in_horizon _ (List.mem_of_getElem? hr)).2 le_rfl
      (List.mem_of_getElem? hr)
    exact (not_le.mpr hgst hbound).elim

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.18:3076–3093; plan J7 D, cross-node finality clause.
DC: SAME coverage at every suffix event prefix, including old finalizations.
Named H2A producer: J3 rest. Named PostResetInv producer: the joint induction
PostResetInv ∧ ResetLeaseCompatible ∧ OpeningDomain. No standalone induction is used. -/
theorem healing_h4_crossBelow [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {w : HealingWitness}
    (start : PostResetStart p c E rho w) (h2A : H2A p c E rho w)
    (inv : ∀ i, PostResetInv p c E rho w i) (hhor : tstar p w ≤ rho.horizon) :
    ∀ i x y, HealSuffix p c rho (tstar p w) i → x ∈ rho.honest → confirmedReaderIdx p c E rho y i →
      Block.Preceq (F_at p c E rho i x) (S_at p c E rho i y) := by
  have hd := p.deltaPos
  have hs := hrec.base.valid.toScheduleWellFormed
  have hR : (2 : Time) ≤ p.R := by exact_mod_cast p.RLarge
  have hP : 8 * p.Δ ≤ P p := by
    change 8 * p.Δ ≤ 4 * (p.R : Time) * p.Δ
    nlinarith
  have hreset := start.toH0Reset
  have ha : p.actionTime w.rStar = SA.gateTime p.toParams w.sStar := by
    rw [hreset.label]
    rfl
  have hlate : p.actionTime w.rStar + 4 * p.Δ < tstar p w := by
    have hu : (w.sStar : Int) + 2 ≤ w.u := by exact_mod_cast start.proposal_lower
    rw [ha, tstar_def]
    change 4 * p.Δ * (w.sStar : Int) + 6 * p.Δ + 4 * p.Δ <
      4 * p.Δ * (w.u : Int) + 6 * p.Δ
    nlinarith
  have hgate := (isGateTime_iff p (tstar p w)).mpr ⟨w.u, rfl⟩
  have hstart : healStart p c rho (tstar p w) = afterTicksIdx rho (tstar p w) := by
    rw [healStart_def, hgate]
    rfl
  have hresetIdx : afterTicksIdx rho (p.actionTime w.rStar) ≤
      healStart p c rho (tstar p w) := by
    rw [hstart]
    exact afterTicksIdx_mono rho (by linarith)
  obtain ⟨j, z, a, K, hrow, _, hK, heK, hhK⟩ := hreset.fresh
  have hhigh : high p w K := by rw [high_def, hhK]
  intro i x y hi hx hReader
  have hy := hReader.1.1
  have hC : Block.Preceq w.CStar (S_at p c E rho i y) := by
    rw [← heK]
    apply (h2A z w.rStar K hrow.1 hK hhigh).2 i y hReader
    · exact hlate.le.trans hhor
    · exact ⟨(healed_cut_lt p c rho hlate).trans
        ((preIdx_le_afterTicksIdx E rho hs (tstar p w)).1.trans
          (hstart ▸ hi.1)), hi.2⟩
  have hf := (inv (i + 1)).fprov
  rw [PostResetFProv_def] at hf
  rcases (hf i (Nat.lt_succ_self i) x hx (hresetIdx.trans hi.1)).1 with hlo | hhi
  · exact block_preceq_trans hlo hC
  · obtain ⟨C, s, hsource, hhigh, hwait, hFC⟩ := hhi
    obtain ⟨k, z, r, a, _, hrow, hsource, hlabel⟩ := hsource
    have hdeadline : p.actionTime r + 4 * p.Δ < (storeAt p c E rho i x).base.now := by
      rw [hlabel] at hwait
      have har : p.actionTime r = SA.gateTime p.toParams (r * p.R) := rfl
      rw [har]
      linarith
    have hnowPos : 0 < (storeAt p c E rho i x).base.now := by
      have hgatePos : 0 < p.actionTime r := by
        change 0 < 4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ
        have hnat : (0 : Int) ≤ (r * p.R : Nat) := Int.natCast_nonneg _
        nlinarith
      linarith
    have hSourceCut := healed_high_source_time p c E rho hs start.toH0Reset
      hrow.1 hsource hhigh
    have hGSTnow : E.t_GST < (storeAt p c E rho i x).base.now := by
      have hstartLower := healing_recovery_start_lower (p := p) E
      have hcutLower := start.toH0Reset.cut_lower
      linarith
    obtain ⟨kNow, hkNow, htick⟩ := healed_now_tick p c E rho hrec hx hnowPos hGSTnow
    have htime := (hs.in_horizon _ (List.mem_of_getElem? htick)).2
    have hcut : healStart p c rho (p.actionTime r + 4 * p.Δ) ≤ i :=
      (healed_cut_lt p c rho hdeadline).trans
        ((healing_support_idxBefore_le p c E rho hs htick le_rfl).trans hkNow.le)
    exact block_preceq_trans hFC
      ((h2A z r C hrow.1 hsource hhigh).2 i y hReader (hdeadline.le.trans htime) ⟨hcut, hi.2⟩)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.18:3062–3067; plan J7 D, different raw labels.
DC: SAME low-support results have an honest supporter.
Named H5RawTransfer producer: J5-A. Its HEAD clause covers the earlier result. -/
private theorem healed_raw_later [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {w : HealingWitness}
    (hreset : H0Reset p c E rho w) (h5 : H5RawTransfer p c E rho w)
    {r s : Slot} {x y : V} {C D : Block} {i : Nat}
    (hx : x ∈ rho.honest) (hy : y ∈ rho.honest) (hr : w.sStar ≤ r) (hrs : r < s)
    (hC : gateResult p c E rho x r = some (some C))
    (ht : IsGateTick p c rho i y s) (hD : gateResult p c E rho y s = some (some D)) :
    Block.Compatible C D := by
  have hs := hrec.base.valid.toScheduleWellFormed
  have hgst : E.t_GST ≤ SA.voteTime p.toParams s := by
    have hcast : (w.sStar : Int) ≤ s := by exact_mod_cast hr.trans hrs.le
    have hsync := hreset.synchronous
    change E.t_GST ≤ 4 * p.Δ * (w.sStar : Int) + p.Δ at hsync
    change E.t_GST ≤ 4 * p.Δ * (s : Int) + p.Δ
    nlinarith [p.deltaPos]
  have hhor := (hs.in_horizon _ (List.mem_of_getElem? ht)).2
  have hmajority := healing_slow_majority E rho hs ht hD (block_preceq_refl D)
  have hEnabled := healing_gate_enabled_of_result E rho hs ht
    ((gateResultAt_eq_gateResult p c E rho hs ht).trans hD)
  have hRead := healing_joined_tick_of_guard p c E rho hrec.base.valid hy ht
    (by simpa only [joinedNow, fgsa_clock_restartTime, (clock_vn _ _).2, storeAt] using
      fgsa_gate_joined_of_enabled E rho hEnabled)
  have hCut := healing_window_of_cut E (healing_reset_vote_cutoff (s := s) hreset
    ((Nat.succ_le_succ hr).trans (Nat.succ_le_of_lt hrs)))
  obtain ⟨k, o, hk, ho, hseat, hsup⟩ :=
    healing_slow_honest_seat E rho hrec hgst hhor hy ht
      (healing_proposal_support_scope_recovery E rho hrec hCut hRead (Or.inr rfl))
      hEnabled hmajority
  obtain ⟨K, hK, hKm, _, _, hvote, hlabel⟩ := healing_support_clean_target E rho o ho
  obtain ⟨j, hj, htarget⟩ :=
    healing_support_honest_head E rho hrec.base.valid hvote hlabel hseat hk
  let H := headVote p (FGSA.clock p
    (rho.stateBefore E j (rho.seatOf (.base (.head s)) k)).st (SA.voteTime p.toParams s)) s
  have hhead : headAtLabel p c E rho (rho.seatOf (.base (.head s)) k) s = some H := by
    unfold headAtLabel
    rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hs hj]
    rfl
  have hCH := (h5 x r C hx hr hC).2.1 _ s H
    ⟨hk, healing_recovery_joined_window E rho hrec hCut hk
      (postReset_head_horizon p c rho hhor)⟩ (Nat.succ_le_of_lt hrs) hhead
  have hDH : Block.Preceq D H := by
    have hlookup : Gen.AC.Root.resolvedTarget?
        (actView (clockPre p (storeAt p c E rho i y)
          (SA.gateTime p.toParams s))).blocks o = some K :=
      actView_target_of_resolvedHead p _
        (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho i y) _) o hK
    rw [Gen.AC.Root.voteSupports_def, hlookup] at hsup
    have heq : K = H := stored_eq_headVote E rho hrec.base.idealization i y hKm j
      (rho.seatOf (.base (.head s)) k) (SA.voteTime p.toParams s) s
      (Option.some.inj ((resolvedHead_root _ o hK).symm.trans htarget))
    exact heq ▸ (Bool.and_eq_true_iff.mp hsup).2
  exact block_compatible_of_common hCH hDH

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.18:3062–3067; plan J7 D, raw-result chain.
DC: SAME all nonempty honest raw results at post-reset labels are compatible.
Named H5RawTransfer producer: J5-A. Equal labels use IF.6; different labels use
the earlier result's protected HEAD at the later result's honest supporter. -/
theorem healing_h4_rawCompatible [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {w : HealingWitness}
    (hreset : H0Reset p c E rho w) (h5 : H5RawTransfer p c E rho w)
    {r s : Slot} {x y : V} {C D : Block} {i j : Nat}
    (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hr : w.sStar ≤ r) (hs : w.sStar ≤ s)
    (hti : IsGateTick p c rho i x r) (htj : IsGateTick p c rho j y s)
    (hC : gateResult p c E rho x r = some (some C))
    (hD : gateResult p c E rho y s = some (some D)) : Block.Compatible C D := by
  rcases lt_trichotomy r s with hlt | rfl | hgt
  · exact healed_raw_later p c E rho hrec hreset h5 hx hy hr hlt hC htj hD
  · have hgst : E.t_GST ≤ SA.voteTime p.toParams r := by
      have hcast : (w.sStar : Int) ≤ r := by exact_mod_cast hr
      have hsync := hreset.synchronous
      change E.t_GST ≤ 4 * p.Δ * (w.sStar : Int) + p.Δ at hsync
      change E.t_GST ≤ 4 * p.Δ * (r : Int) + p.Δ
      nlinarith [p.deltaPos]
    have hhor := (hrec.base.valid.toScheduleWellFormed.in_horizon _
      (List.mem_of_getElem? hti)).2
    exact fgsa_sameLabel_on (hroots := hrec.base.idealization) p c E rho hrec.base.valid
      r (healing_recovery_same_label E rho hrec r hgst) x y C D hx hy hC hD
  · have h := healed_raw_later p c E rho hrec hreset h5 hy hx hs hgt hD hti hC
    change (Block.preceq C D || Block.preceq D C) = true
    change (Block.preceq D C || Block.preceq C D) = true at h
    rwa [Bool.or_comm]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.18:3076–3093; plan J7 D, reset output coverage.
DC: SAME C* is in every suffix output. Named H2A producer: J3 rest. -/
private theorem healed_reset_below [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {w : HealingWitness}
    (start : PostResetStart p c E rho w) (h2A : H2A p c E rho w)
    (hhor : tstar p w ≤ rho.horizon) {i : Nat} {y : V}
    (hi : HealSuffix p c rho (tstar p w) i) (hReader : confirmedReaderIdx p c E rho y i) :
    Block.Preceq w.CStar (S_at p c E rho i y) := by
  have hreset := start.toH0Reset
  have ha : p.actionTime w.rStar = SA.gateTime p.toParams w.sStar := by
    rw [hreset.label]
    rfl
  have hlate : p.actionTime w.rStar + 4 * p.Δ < tstar p w := by
    have hu : (w.sStar : Int) + 2 ≤ w.u := by exact_mod_cast start.proposal_lower
    rw [ha, tstar_def]
    change 4 * p.Δ * (w.sStar : Int) + 6 * p.Δ + 4 * p.Δ <
      4 * p.Δ * (w.u : Int) + 6 * p.Δ
    nlinarith [p.deltaPos]
  have hgate := (isGateTime_iff p (tstar p w)).mpr ⟨w.u, rfl⟩
  have hstart : healStart p c rho (tstar p w) = afterTicksIdx rho (tstar p w) := by
    rw [healStart_def, hgate]
    rfl
  obtain ⟨j, z, a, K, hrow, _, hK, heK, hhK⟩ := hreset.fresh
  have hhigh : high p w K := by rw [high_def, hhK]
  rw [← heK]
  apply (h2A z w.rStar K hrow.1 hK hhigh).2 i y hReader (hlate.le.trans hhor)
  exact ⟨(healed_cut_lt p c rho hlate).trans
    ((preIdx_le_afterTicksIdx E rho hrec.base.valid.toScheduleWellFormed (tstar p w)).1.trans
        (hstart ▸ hi.1)), hi.2⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.18:3076–3095; plan J7 D, reconciliation case.
DC: SAME a delivered finalization is below the output before its delivery.
Named H2A producer: J3 rest. Named PostResetInv producer: the joint induction
PostResetInv ∧ ResetLeaseCompatible ∧ OpeningDomain. -/
private theorem healed_reconcile_below [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {w : HealingWitness}
    (start : PostResetStart p c E rho w) (h2A : H2A p c E rho w)
    (inv : ∀ i, PostResetInv p c E rho w i) (hhor : tstar p w ≤ rho.horizon)
    {i : Nat} {x : V} {o : Obj p} {t : Time}
    (hi : HealSuffix p c rho (tstar p w) i) (hx : x ∈ rho.honest)
    (hReader : confirmedReaderIdx p c E rho x i)
    (he : rho.events[i]? = some (.deliver x o t)) :
    Block.Preceq (F_at p c E rho (i + 1) x) (S_at p c E rho i x) := by
  have hd := p.deltaPos
  have hs := hrec.base.valid.toScheduleWellFormed
  have hR : (2 : Time) ≤ p.R := by exact_mod_cast p.RLarge
  have hP : 8 * p.Δ ≤ P p := by
    change 8 * p.Δ ≤ 4 * (p.R : Time) * p.Δ
    nlinarith
  have hnow : (storeAt p c E rho (i + 1) x).base.now =
      (storeAt p c E rho i x).base.now := by
    change (rho.stateBefore E (i + 1) x).st.base.now = (rho.stateBefore E i x).st.base.now
    rw [V2.D.Run.stateBefore_succ E rho he]
    simp only [V2.D.World.step, Function.update_self]
    exact process_base_now _ _
  have hreset := start.toH0Reset
  have ha : p.actionTime w.rStar = SA.gateTime p.toParams w.sStar := by
    rw [hreset.label]
    rfl
  have htime : p.actionTime w.rStar ≤ tstar p w := by
    have hu : (w.sStar : Int) + 2 ≤ w.u := by exact_mod_cast start.proposal_lower
    rw [ha, tstar_def]
    change 4 * p.Δ * (w.sStar : Int) + 6 * p.Δ ≤
      4 * p.Δ * (w.u : Int) + 6 * p.Δ
    nlinarith
  have hgate := (isGateTime_iff p (tstar p w)).mpr ⟨w.u, rfl⟩
  have hstart : healStart p c rho (tstar p w) = afterTicksIdx rho (tstar p w) := by
    rw [healStart_def, hgate]
    rfl
  have hidx : afterTicksIdx rho (p.actionTime w.rStar) ≤ i + 1 := by
    exact ((afterTicksIdx_mono rho htime).trans (hstart ▸ hi.1)).trans (Nat.le_succ i)
  have hf := (inv (i + 2)).fprov
  rw [PostResetFProv_def] at hf
  rcases (hf (i + 1) (by omega) x hx hidx).1 with hlo | hhi
  · exact block_preceq_trans hlo
      (healed_reset_below p c E rho hrec start h2A hhor hi hReader)
  · obtain ⟨C, s, hsource, hhigh, hwait, hFC⟩ := hhi
    rw [hnow] at hwait
    obtain ⟨k, z, r, a, _, hrow, hsource, hlabel⟩ := hsource
    have hdeadline : p.actionTime r + 4 * p.Δ < (storeAt p c E rho i x).base.now := by
      rw [hlabel] at hwait
      have har : p.actionTime r = SA.gateTime p.toParams (r * p.R) := rfl
      rw [har]
      linarith
    have hnowPos : 0 < (storeAt p c E rho i x).base.now := by
      have hgatePos : 0 < p.actionTime r := by
        change 0 < 4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ
        have hnat : (0 : Int) ≤ (r * p.R : Nat) := Int.natCast_nonneg _
        nlinarith
      linarith
    have hSourceCut := healed_high_source_time p c E rho hs start.toH0Reset
      hrow.1 hsource hhigh
    have hGSTnow : E.t_GST < (storeAt p c E rho i x).base.now := by
      have hstartLower := healing_recovery_start_lower (p := p) E
      have hcutLower := start.toH0Reset.cut_lower
      linarith
    obtain ⟨kNow, hkNow, htick⟩ := healed_now_tick p c E rho hrec hx hnowPos hGSTnow
    have htime := (hs.in_horizon _ (List.mem_of_getElem? htick)).2
    have hcut : healStart p c rho (p.actionTime r + 4 * p.Δ) ≤ i :=
      (healed_cut_lt p c rho hdeadline).trans
        ((healing_support_idxBefore_le p c E rho hs htick le_rfl).trans hkNow.le)
    exact block_preceq_trans hFC
      ((h2A z r C hrow.1 hsource hhigh).2 i x hReader (hdeadline.le.trans htime) ⟨hcut, hi.2⟩)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.18:3049–3095; plan J7 D, full H4.
DC: SAME cross-time chain, local monotonicity, and cross-node finality coverage.
Named H2A producer: J3 rest; H3/PostResetService/opening_domain: J6-3;
H5RawTransfer: J5-A; PostResetInv: the joint induction
PostResetInv ∧ ResetLeaseCompatible ∧ OpeningDomain.
The output induction consumes the all-cut carrier; it does not prove that carrier. -/
theorem healing_h4 [Fintype V] {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    {w : HealingWitness} (start : PostResetStart p c E rho w)
    (h2A : H2A p c E rho w) (h3 : H3 p c E rho w)
    (h5 : H5RawTransfer p c E rho w) (inv : ∀ i, PostResetInv p c E rho w i)
    (hhor : tstar p w ≤ rho.horizon)
    (readers : ∀ i x, HealSuffix p c rho (tstar p w) i → x ∈ rho.honest →
      confirmedReaderIdx p c E rho x i) : H4 p c E rho w := by
  classical
  have hsch := hrec.base.valid.toScheduleWellFormed
  have hstable := healing_h4_stable p c E rho hrec start h3 hhor
  have hgate := (isGateTime_iff p (tstar p w)).mpr ⟨w.u, rfl⟩
  have hstart : healStart p c rho (tstar p w) = afterTicksIdx rho (tstar p w) := by
    rw [healStart_def, hgate]
    rfl
  let Origin (i : Nat) (x : V) : Prop := ∃ s j, w.sStar ≤ s ∧
    IsGateTick p c rho j x s ∧ gateResult p c E rho x s = some (some (S_at p c E rho i x))
  have initial : ∀ x ∈ rho.honest, Origin (healStart p c rho (tstar p w)) x := by
    intro x hx
    obtain ⟨hraw, ⟨j, ht, _⟩, _, _, _⟩ :=
      (h3 w.u w.QStar start.proposal start.proposal_lower).2 hhor x hx
        (healing_recovery_gate_reader hrec hx
          (healing_reset_slot_cutoff start.toH0Reset |>.trans (by
            have hu : (w.sStar : Int) ≤ w.u := by
              exact_mod_cast (Nat.le_add_right w.sStar 2 |>.trans start.proposal_lower)
            change 4 * p.Δ * (w.sStar : Int) ≤ 4 * p.Δ * (w.u : Int)
            nlinarith [p.deltaPos])) hhor)
    have hS : S_at p c E rho (healStart p c rho (tstar p w)) x = w.QStar := by
      rw [hstart]
      change (fgsaInterface p c).stable (rho.stateBefore E (afterTicksIdx rho (tstar p w)) x) = _
      rw [← afterTicks_eq_stateBefore E rho hsch]
      exact hstable x hx
    exact ⟨w.u, j, (Nat.le_add_right w.sStar 2).trans start.proposal_lower, ht.1, hS ▸ hraw⟩
  have step (i : Nat) (hi : HealSuffix p c rho (tstar p w) i)
      (origin : ∀ x ∈ rho.honest, Origin i x) :
      ∀ x ∈ rho.honest, Block.Preceq (S_at p c E rho i x) (S_at p c E rho (i + 1) x) ∧
        Origin (i + 1) x := by
    intro x hx
    have keep (heq : S_at p c E rho (i + 1) x = S_at p c E rho i x) :
        Block.Preceq (S_at p c E rho i x) (S_at p c E rho (i + 1) x) ∧ Origin (i + 1) x := by
      dsimp only [Origin]
      rw [heq]
      exact ⟨block_preceq_refl _, origin x hx⟩
    rcases fgsaAC_output_step E rho i x with hsame | ⟨s, ht⟩ | hrc | ⟨t, hr, _⟩
    · exact keep hsame
    · have htime : tstar p w ≤ SA.gateTime p.toParams s := by
        by_contra hn
        have hlt := (Gen.V2.Duty.index_lt_idxBefore_iff hsch ht (tstar p w)).mpr
          (lt_of_not_ge hn)
        have hpre := (preIdx_le_afterTicksIdx E rho hsch (tstar p w)).1
        rw [← hstart] at hpre
        exact (not_lt.mpr (hpre.trans hi.1)) hlt
      have hlabel : w.sStar ≤ s := by
        have hcast : (w.u : Int) ≤ s := by
          change 4 * p.Δ * (w.u : Int) + 6 * p.Δ ≤
            4 * p.Δ * (s : Int) + 6 * p.Δ at htime
          nlinarith [p.deltaPos]
        have hu : w.u ≤ s := by exact_mod_cast hcast
        exact ((Nat.le_add_right w.sStar 2).trans start.proposal_lower).trans hu
      have hEnabled := healing_recovery_gate_enabled E rho hrec hx ht
        (healing_reset_slot_cutoff start.toH0Reset |>.trans (by
          have hl : (w.sStar : Int) ≤ s := by exact_mod_cast hlabel
          change 4 * p.Δ * (w.sStar : Int) ≤ 4 * p.Δ * (s : Int)
          nlinarith [p.deltaPos]))
      have gate := fgsaAC_gate_write E rho i s x
        (by rw [clockPre_joined]; exact fgsa_gate_joined_of_enabled E rho hEnabled) ht
      rcases gate.effects with hskip | hrun
      · exact keep hskip.2.1
      · cases hraw : (fgsaAC E rho).raw i s x with
        | none => exact keep (hrun.empty hraw).1
        | some C =>
          by_cases hguard : ∀ lease ∈ ((fgsaAC E rho).gateView i x s).obligations,
              Block.Compatible (Gen.AC.Lease.target lease) C
          · have hrawEq : SA.Root.confirmationFrom p.toParams
                (eraseFG (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)).fg.F)
                (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))) s =
                (fgsaAC E rho).raw i s x := by
              rw [clockPre_fg]
              have heq := congrArg (fun v => SA.Root.confirmationFrom p.toParams
                (eraseFG (storeAt p c E rho i x).fg.F) v s)
                (fgsa_clockPre_gateView p (storeAt p c E rho i x) s)
              exact heq
            have hresult : gateResult p c E rho x s = some (some C) := by
              apply (gateResult_eq_saved p c E rho hsch ht).trans
              have hSaved := fgsa_gate_saved_result E rho hsch ht
                (fgsa_gate_joined_of_enabled E rho hEnabled)
              have hRaw := hrawEq.trans hraw
              rw [clockPre_fg] at hRaw
              exact hSaved.trans (congrArg some hRaw)
            obtain ⟨r, j, hr, hj, hresultOld⟩ := origin x hx
            have hcompat := healing_h4_rawCompatible p c E rho hrec start.toH0Reset h5
              hx hx hr hlabel hj ht hresultOld hresult
            have hadv : Block.Preceq (S_at p c E rho i x)
                (GridCO.advance (S_at p c E rho i x) C) := by
              unfold GridCO.advance
              split
              · exact block_preceq_refl _
              · next hn =>
                rcases Bool.or_eq_true_iff.mp hcompat with hSC | hCS
                · exact hSC
                · exact (hn hCS).elim
            have hout := (hrun.accept C hraw hguard).1
            change S_at p c E rho (i + 1) x = Gen.AC.normalizeOutput
              (F_at p c E rho i x) (GridCO.advance (S_at p c E rho i x) C) at hout
            have hfloor : Block.preceq (F_at p c E rho i x)
                (GridCO.advance (S_at p c E rho i x) C) = true :=
              block_preceq_trans (nestOK_stateBefore E rho i x) hadv
            rw [Gen.AC.normalizeOutput_def, ite_eq_left hfloor] at hout
            refine ⟨?_, ?_⟩
            · rwa [hout]
            dsimp only [Origin]
            rw [hout]
            unfold GridCO.advance
            split
            · exact origin x hx
            · exact ⟨s, i, hlabel, ht, hresult⟩
          · have hveto : ∃ lease ∈ ((fgsaAC E rho).gateView i x s).obligations,
                ¬ Block.Compatible (Gen.AC.Lease.target lease) C := by
              simpa only [not_forall, exists_prop] using hguard
            exact keep (hrun.veto C hraw hveto).1
    · obtain ⟨o, t, B, he, _, _, hout⟩ := hrc
      have hbelow := healed_reconcile_below p c E rho hrec start h2A inv hhor hi hx
        (readers i x hi hx) he
      change S_at p c E rho (i + 1) x =
        Gen.AC.normalizeOutput (F_at p c E rho (i + 1) x) (S_at p c E rho i x) at hout
      change Block.preceq (F_at p c E rho (i + 1) x) (S_at p c E rho i x) = true at hbelow
      rw [Gen.AC.normalizeOutput_def, ite_eq_left hbelow] at hout
      exact keep hout
    · have hGSTstart : E.t_GST < tstar p w := by
        have hsync := start.toH0Reset.synchronous
        have hu : (w.sStar : Int) + 2 ≤ (w.u : Int) := by
          exact_mod_cast start.proposal_lower
        change E.t_GST ≤ 4 * p.Δ * (w.sStar : Int) + p.Δ at hsync
        change E.t_GST < 4 * p.Δ * (w.u : Int) + 6 * p.Δ
        nlinarith [p.deltaPos]
      have hbound := healing_scope_restart_bound hrec hx
        (hsch.in_horizon _ (List.mem_of_getElem? hr)).2 le_rfl
        (List.mem_of_getElem? hr)
      have hbefore := (Gen.V2.Duty.index_lt_idxBefore_iff hsch hr (tstar p w)).mpr
        (hbound.trans_lt hGSTstart)
      have hcut := (preIdx_le_afterTicksIdx E rho hsch (tstar p w)).1
      rw [← hstart] at hcut
      exact ((Nat.not_lt.mpr (hcut.trans hi.1)) hbefore).elim
  have allOrigin : ∀ i, HealSuffix p c rho (tstar p w) i →
      ∀ x ∈ rho.honest, Origin i x := by
    intro i hi
    obtain ⟨hli, hlen⟩ := hi
    induction i, hli using Nat.le_induction with
    | base => exact initial
    | succ i hli ih =>
      have hprev : i ≤ rho.events.length := (Nat.le_succ i).trans hlen
      exact fun x hx => (step i ⟨hli, hprev⟩ (ih hprev) x hx).2
  refine ⟨hstable, ?_, ?_, healing_h4_crossBelow p c E rho hrec start h2A inv hhor⟩
  · intro i j x y hi hj hRx hRy
    have hx := hRx.1.1
    have hy := hRy.1.1
    obtain ⟨r, k, hr, hk, hC⟩ := allOrigin i hi x hx
    obtain ⟨s, l, hs, hl, hD⟩ := allOrigin j hj y hy
    exact healing_h4_rawCompatible p c E rho hrec start.toH0Reset h5
      hx hy hr hs hk hl hC hD
  · intro i j x hi hj hij hRx _hRj
    have hx := hRx.1.1
    have mono : ∀ j, i ≤ j → j ≤ rho.events.length →
        Block.Preceq (S_at p c E rho i x) (S_at p c E rho j x) := by
      intro j hij
      induction j, hij using Nat.le_induction with
      | base => intro _; exact block_preceq_refl _
      | succ j hij ih =>
        intro hlen
        have hsuffix : HealSuffix p c rho (tstar p w) j :=
          ⟨hi.1.trans hij, (Nat.le_succ j).trans hlen⟩
        exact block_preceq_trans (ih hsuffix.2)
          (step j hsuffix (allOrigin j hsuffix) x hx).1
    exact mono j hij hj.2

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.18:3097–3101; plan J7 E, grid step.
DC: SAME d_u ≤ t_s gives u ≤ s, since t_s=4Δs and d_u=4Δu+6Δ. -/
theorem healing_healed_proposal_lower (w : HealingWitness) {s : Slot}
    (hafter : tstar p w ≤ V2.D.proposalTime (fgsaInterface p c) s) : w.u ≤ s := by
  rw [proposalTime_fgsa] at hafter
  change 4 * p.Δ * (w.u : Int) + 6 * p.Δ ≤ 4 * p.Δ * (s : Int) at hafter
  have hcast : (w.u : Int) ≤ s := by nlinarith [p.deltaPos]
  exact_mod_cast hcast

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.18:3049–3103; plan J7 E.
DC: SAME safety suffix and later honest proposal service.
Named H3 producer: J6-3 PostResetService/opening_domain. H4 is the J7 D input.
PostResetStart supplies the label lower bound for H3 at all later proposal times. -/
theorem healing_healed [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {w : HealingWitness} (start : PostResetStart p c E rho w)
    (h4 : H4 p c E rho w) (h3 : H3 p c E rho w) : Healed p c E rho (tstar p w) := by
  refine ⟨h4.2.1, h4.2.2.1, ?_, ?_⟩
  · exact h4.2.2.2
  · intro s B hafter hgate hp t x ht hx
    subst t
    have hs := start.proposal_lower.trans (healing_healed_proposal_lower p c w hafter)
    change Block.Preceq B ((fgsaInterface p c).stable
      (afterTicks E rho (SA.gateTime p.toParams s) x))
    have hReader := healing_recovery_gate_reader hrec hx.1
      (healing_reset_slot_cutoff start.toH0Reset |>.trans (by
        have hl : (w.sStar : Int) ≤ s := by
          exact_mod_cast (Nat.le_add_right w.sStar 2 |>.trans hs)
        change 4 * p.Δ * (w.sStar : Int) ≤ 4 * p.Δ * (s : Int)
        nlinarith [p.deltaPos])) hgate
    rw [(h3 s B hp hs).2 hgate x hx.1 hReader |>.2.2.2.1]
    exact block_preceq_refl B

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.11:1572–1595, H.22:3229–3241; plan J7 B (lead review nit 1).
DC: SAME first reset row: rG, u₀, M and r* are unique, so two reset witnesses agree on r*. -/
theorem healing_reset_rStar_unique {w w' : HealingWitness}
    (h : H0Reset p c E rho w) (h' : H0Reset p c E rho w') : w.rStar = w'.rStar := by
  have hrG : w.rG = w'.rG :=
    le_antisymm (h.rG_first _ h'.rG_after) (h'.rG_first _ h.rG_after)
  have hu : w.u₀ = w'.u₀ := by rw [h.cut, h'.cut, hrG]
  have hM : w.M = w'.M := by rw [h.frontier, h'.frontier, hu]
  have hrow : HeightRow p c E rho w'.rStar (w.M + 1) := by rw [hM]; exact h'.reset_row
  have hrow' : HeightRow p c E rho w.rStar (w'.M + 1) := by rw [← hM]; exact h.reset_row
  exact le_antisymm (h.reset_first _ hrow) (h'.reset_first _ hrow')

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.18:3097–3100; plan J7 B, ∀-w form (lead review nit 1).
DC: SAME deadline for every full witness: by proposal_first its slot u is at most
the first proposal that healing_firstProposal builds from the same reset data. -/
theorem healing_tstar_le_of_h0 [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {w : HealingWitness} (h0 : H0 p c E rho w)
    (hhor : p.actionTime w.rStar + Γ p G + 4 * p.Δ ≤ rho.horizon) :
    tstar p w ≤ p.actionTime w.rStar + Γ p G + 4 * p.Δ := by
  obtain ⟨u, Q, start, htime⟩ := healing_firstProposal p c E rho hrec h0.toH0Reset hhor
  have hle : w.u ≤ u := h0.proposal_first u Q start.proposal_lower start.proposal
  have hcast : (w.u : Int) ≤ u := by exact_mod_cast hle
  have hd := p.deltaPos
  change 4 * p.Δ * (w.u : Int) + 6 * p.Δ ≤ _
  change 4 * p.Δ * (u : Int) + 6 * p.Δ ≤ _ at htime
  nlinarith

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.11, H.18:3097–3100; plan J7 B; producer of J10's named `timeBound`
(the second conjunct of HealingInputOfH0Statement). Named input: ResetArrivalStatement
(producer: J8 H-RESET). DC: SAME a_(r*) < GST + B'_reset^F for the unique reset row. -/
theorem healing_timeBound_of_resetArrival (G ΔF : Time)
    (hReset : ResetArrivalStatement p G ΔF) :
    p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∀ w, H0 p c E rho w → tstar p w ≤ p.actionTime w.rStar + Γ p G + 4 * p.Δ := by
  intro hδ V _ _ In c E rho hset hbound hhor w h0
  have hd := p.deltaPos
  have hΓ := (fgsa_gamma_bounds p G).1
  have hG := hset.gapPos
  obtain ⟨w₀, h0r, hlt⟩ := hReset hδ c E rho hset hbound (by linarith)
  have hr : w.rStar = w₀.rStar := healing_reset_rStar_unique p c E rho h0.toH0Reset h0r
  apply healing_tstar_le_of_h0 p c E rho hset h0
  rw [hr]
  linarith

end AvailableChain.FGSA.Run
end

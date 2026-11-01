module
public import AvailableChainFGSARun.Proofs.Join
-- shake keep reason: source declarations
public import AvailableChainFGSAProofs.Proofs.Shared.HeldReceipt -- shake: keep

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

/-- Receipt for one selected witness at an actual joined read.
The receiver floor is read at the strict service deadline. The target service
keeps the original object history, anchor, and receiver epoch. Producer: OPEN,
P-H2 with P-ShA's object service constructors; this record is an input. -/
structure WitnessReceiptScope {p : Params} {In V : Type} [DecidableEq V]
    {c : AppCodec In} (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (W : FGBlock (Fin p.n)) (deadline : Time) : Prop where
  atRead : ∀ iy y t, y ∈ rho.honest → rho.events[iy]? = some (.tick y t) →
    joinedNow p (clock p (storeAt p c E rho iy y) t) = true → deadline ≤ t →
    Block.Preceq (eraseFG (rho.stateBeforeTime E deadline y).st.fg.F) (eraseFG W) →
    TargetReceiptService E rho (eraseFG W) deadline y

/-- The scoped receipt result for the selected ancestor of a serviced witness.
This is a consumer result, not an object-service producer. -/
structure WitnessHeldScope {p : Params} {In V : Type} [DecidableEq V]
    {c : AppCodec In} (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (W : FGBlock (Fin p.n)) (deadline : Time) : Prop where
  atRead : ∀ iy y t, y ∈ rho.honest → rho.events[iy]? = some (.tick y t) →
    joinedNow p (clock p (storeAt p c E rho iy y) t) = true → deadline ≤ t →
    Block.Preceq (eraseFG (rho.stateBeforeTime E deadline y).st.fg.F) (eraseFG W) →
    W ∈ (rho.stateBeforeTime E deadline y).st.fg.TF

/-- One HEAD witness and its serviced height witness are selected together. -/
structure HeadWitnessReceiptScope {p : Params} {In V : Type} [DecidableEq V]
    {c : AppCodec In} (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (x : V) (s : Slot) : Prop where
  witness :
    let st := clock p (storeAt p c E rho i x) (SA.voteTime p.toParams s)
    ∃ K ∈ fullTree p st, eraseFG K = headVote p st s ∧
      ∃ W ∈ (storeAt p c E rho i x).fg.TF, FGBlock.Preceq K W ∧
        (R_at p c E rho i x).lo ≤ (heightView p W).h ∧
        WitnessReceiptScope E rho W (SA.voteTime p.toParams s + p.Δ)

/-- Select only the frontier/top/contest witnesses used by settlement. -/
structure PhaseWitnessReceiptScope {p : Params} {In V : Type} [DecidableEq V]
    {c : AppCodec In} (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i m : Nat) (deadline : Time) : Prop where
  frontier : ∃ x W, HeldAt p c E rho i x W ∧ (heightView p W).h = m ∧
    WitnessReceiptScope E rho W deadline
  top : TopEvidence p c E rho i m →
    ∃ x C, HeldAt p c E rho i x C ∧ (heightView p C).h = m ∧
      (heightView p C).h_j + 1 = m ∧
      (heightView p C).J = (storeAt p c E rho i x).fg.J ∧
      WitnessReceiptScope E rho C deadline
  contest : ContestEvidence p c E rho i m →
    ∃ x C W, HeldAt p c E rho i x C ∧ HeldAt p c E rho i x W ∧
      (heightView p C).h = m ∧ (heightView p W).h = m ∧
      (heightView p C).h_j + 1 = m ∧ ¬ FGBlock.Preceq (heightView p C).J W ∧
      WitnessReceiptScope E rho C deadline ∧ WitnessReceiptScope E rho W deadline

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)} {G ΔF : Time}

/-- Recovery bounds each honest restart through the exact horizon by GST.
A restart at GST is permitted. -/
theorem healing_scope_restart_bound (hrec : RecoverySleep₂ p c E rho G ΔF)
    {x : V} (hx : x ∈ rho.honest) {t : Time} (hh : t ≤ rho.horizon)
    {w : Time} (hwt : w ≤ t) (he : V2.Event.restart x w ∈ rho.events) :
    w ≤ E.t_GST := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp he
  by_contra hn
  exact hrec.suffixNoRestart x hx j w hj (lt_of_not_ge hn)
    ((hwt.trans hh).trans_lt (lt_add_of_pos_right _ (by decide)))

/-- The recovery suffix supplies the exact proposer restart cutoff.
The caller must prove GST is at or before the previous slot start. -/
theorem healing_recovery_restart_cutoff (hrec : RecoverySleep₂ p c E rho G ΔF)
    {x : V} (hx : x ∈ rho.honest) {t b : Time} (hh : t ≤ rho.horizon)
    (hb : E.t_GST ≤ b) :
    ∀ w, 0 ≤ w → w ≤ t → V2.Event.restart x w ∈ rho.events → w ≤ b := by
  intro w _ hwt he
  exact (healing_scope_restart_bound hrec hx hh hwt he).trans hb

/-- Convert the exact recovery cutoff to the post-clock joined duty guard. -/
theorem healing_recovery_joinedNow (hrec : RecoverySleep₂ p c E rho G ΔF)
    {i : Nat} {x : V} {t : Time} (hx : x ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick x t)) (hh : t ≤ rho.horizon)
    (hb : E.t_GST ≤ slotStartZ p ((p.slotOf t : Int) - 1)) :
    joinedNow p (FGSA.clock p (V2.D.Run.stateBefore E rho i x).st t) = true := by
  exact fgsa_joinedNow_of_joinedEnv E rho hrec.base.valid.toScheduleWellFormed hi
    (healing_recovery_restart_cutoff hrec hx hh hb)

/-- The caller's gate cutoff proves the actual enabled gate guard. -/
theorem healing_scope_enabled_gate (hrec : RecoverySleep₂ p c E rho G ΔF)
    {i : Nat} {x : V} {s : Slot} (hx : x ∈ rho.honest)
    (hi : IsGateTick p c rho i x s) (hcut : E.t_GST ≤ slotStartZ p (s : Int))
    (_hhor : SA.gateTime p.toParams s ≤ rho.horizon) : enabledGateAt p c E rho i x s := by
  refine ⟨hi, ?_⟩
  have hb := fgsa_restartTime_bound E rho i x (slotStartZ p (s : Int)) (by
    intro k t _ hk
    have ht : t ≤ rho.horizon :=
      (hrec.base.valid.in_horizon _ (List.mem_of_getElem? hk)).2
    have hb : t ≤ E.t_GST := by
      by_contra hn
      exact hrec.suffixNoRestart x hx k t hk (lt_of_not_ge hn)
        (Int.lt_add_one_iff.mpr ht)
    exact hb.trans hcut)
  change (match (storeAt p c E rho i x).restartTime with
    | none => True | some t => t ≤ slotStartZ p (s : Int))
  cases hr : (storeAt p c E rho i x).restartTime with
  | none => trivial
  | some t => exact hb t hr

/-- The actual enabled gate catches up every honest recovery reader.
The post-tick cut includes the gate and its preceding same-time wake. -/
theorem healing_recovery_gate_reader (hrec : RecoverySleep₂ p c E rho G ΔF)
    {x : V} (hx : x ∈ rho.honest) {s : Slot}
    (hcut : E.t_GST ≤ slotStartZ p (s : Int))
    (hhor : SA.gateTime p.toParams s ≤ rho.horizon) :
    confirmedReaderAtIdx p c E rho x (afterTicksIdx rho (SA.gateTime p.toParams s))
      (SA.gateTime p.toParams s) := by
  have hs := hrec.base.valid.toScheduleWellFormed
  have hsg : slotStartZ p (s : Int) ≤ SA.gateTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have awake := hrec.awake x hx _ (hcut.trans hsg) hhor
  have htime : ((4 * s + 6 : Nat) : Time) * p.Δ = SA.gateTime p.toParams s := by
    change ((4 * s + 6 : Nat) : Int) * p.Δ = 4 * p.Δ * (s : Int) + 6 * p.Δ
    push_cast
    ring
  obtain ⟨j, hj, _⟩ := fgsa_tick_total E rho hs hrec.base.delta x hx (4 * s + 6)
    (htime ▸ hhor) (by simpa only [htime] using awake)
  rw [htime] at hj
  have hslot : p.slotOf (SA.gateTime p.toParams s) = s + 1 := by
    exact (fgsa_postClock_slot (c := c) (rho.stateBefore E j x) _).2.symm.trans
      (fgsa_gate_slot (c := c) _ s)
  have hg := healing_recovery_joinedNow hrec hx hj hhor (by
    simpa only [hslot, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hcut)
  have enabled : enabledGateAt p c E rho j x s := by
    unfold enabledGateAt
    refine ⟨hj, ?_⟩
    unfold joinedNow at hg
    rw [fgsa_clock_restartTime, (clock_vn _ _).2] at hg
    change joinedAtTime p (storeAt p c E rho j x).restartTime
      (SA.gateTime p.toParams s) = true at hg
    unfold joinedAtTime at hg
    cases hr : (storeAt p c E rho j x).restartTime with
    | none => trivial
    | some w =>
      rw [hr, hslot] at hg
      change w ≤ 4 * p.Δ * (s : Int)
      simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using of_decide_eq_true hg
  have hjcut : j < afterTicksIdx rho (SA.gateTime p.toParams s) := by
    by_contra hn
    have hn' := V2.D.Engine.filter_false_of_index_ge hs (cutPred (P := fgsa p c) _)
      (by
        intro e f hk hf
        exact decide_eq_true (hk.trans (of_decide_eq_true hf)))
      (Nat.le_of_not_gt hn) hj
    have ht : cutPred (P := fgsa p c) (SA.gateTime p.toParams s)
        (.tick x (SA.gateTime p.toParams s) : V2.Event V (Obj p)) = true :=
      by change decide (toLex (_, 1) ≤ toLex (_, 1)) = true; exact decide_eq_true le_rfl
    exact Bool.noConfusion (ht.symm.trans hn')
  refine ⟨hx, awake, ?_⟩
  cases hr : (storeAt p c E rho (afterTicksIdx rho (SA.gateTime p.toParams s)) x).restartTime
    with
  | none => trivial
  | some w =>
    refine ⟨s, j, ?_, le_rfl, hjcut, enabled, ?_, ?_⟩
    · apply fgsa_restartTime_bound E rho _ x _ ?_ w hr
      intro k t _ hk
      exact (healing_scope_restart_bound hrec hx
        (hs.in_horizon _ (List.mem_of_getElem? hk)).2 le_rfl
        (List.mem_of_getElem? hk)).trans hcut
    · intro t _ hlo hhi
      exact hrec.awake x hx t (hcut.trans hlo) (hhi.trans hhor)
    · intro t hlo hhi he
      exact (not_lt.mpr ((healing_scope_restart_bound hrec hx hhor hhi he).trans hcut)) hlo

/-- The receiver epoch starts after all restart events at the action anchor.
Use event indices; a restart at the anchor is already inside actionCut. -/
theorem healing_recovery_restartFree (hrec : RecoverySleep₂ p c E rho G ΔF)
    {x : V} (hx : x ∈ rho.honest) {a d : Time}
    (ha : E.t_GST ≤ a) (hd : d ≤ rho.horizon) :
    V2.D.restartFree rho x (V2.D.Run.actionCut rho a) (V2.D.Run.idxBefore rho d) := by
  have hs := hrec.base.valid.toScheduleWellFormed
  intro k w hka hkd he
  have hwa : a < w := by
    have hn := (V2.D.Engine.index_lt_actionCut_iff hs he a).not.mp (Nat.not_lt.mpr hka)
    change ¬ (w < a ∨ (w = a ∧ (0 : Nat) = 0)) at hn
    rcases lt_trichotomy w a with hlt | heq | hgt
    · exact (hn (Or.inl hlt)).elim
    · exact (hn (Or.inr ⟨heq, rfl⟩)).elim
    · exact hgt
  have hwd := (Gen.V2.Duty.index_lt_idxBefore_iff hs he d).mp hkd
  exact hrec.suffixNoRestart x hx k w he (ha.trans_lt hwa)
    ((hwd.le.trans hd).trans_lt (lt_add_of_pos_right _ (by decide)))

/-- The receiver epoch includes the consuming action index.
A restart at the anchor precedes actionCut, including when the anchor is GST. -/
theorem healing_recovery_action_epoch (hrec : RecoverySleep₂ p c E rho G ΔF)
    {x : V} (hx : x ∈ rho.honest) {a : Time} (ha : E.t_GST ≤ a) (j : Nat) :
    V2.D.restartFree rho x (V2.D.Run.actionCut rho a) j := by
  have hs := hrec.base.valid.toScheduleWellFormed
  intro k t hka _ hk
  have ht : t ≤ rho.horizon := (hs.in_horizon _ (List.mem_of_getElem? hk)).2
  have hbound := healing_scope_restart_bound hrec hx ht le_rfl
    (List.mem_of_getElem? hk)
  have hbefore := (V2.D.Engine.index_lt_actionCut_iff hs hk a).mpr (by
    change t < a ∨ (t = a ∧ (0 : Nat) = 0)
    rcases lt_or_eq_of_le (hbound.trans ha) with hlt | heq
    · exact Or.inl hlt
    · exact Or.inr ⟨heq, rfl⟩)
  omega

/-- Local stamp preservation extends to the action that consumes the receipt. -/
theorem healing_recovery_action_stamps (hrec : RecoverySleep₂ p c E rho G ΔF)
    (epoch : RStoreEpoch p c E rho) {x : V} (hx : x ∈ rho.honest)
    {a : Time} (ha : E.t_GST ≤ a) {j : Nat}
    (hij : V2.D.Run.actionCut rho a ≤ j) (hj : j ≤ rho.events.length) :
    (storeAt p c E rho (V2.D.Run.actionCut rho a) x).base.blockStamp <+:
      (storeAt p c E rho j x).base.blockStamp ∧
    (storeAt p c E rho (V2.D.Run.actionCut rho a) x).base.voteStamp <+:
      (storeAt p c E rho j x).base.voteStamp :=
  epoch _ j x hx hij hj (healing_recovery_action_epoch hrec hx ha j)

omit [Fintype V] in
/-- Durable FG trees remain available to H2 consumers across each restart. -/
theorem healing_scope_durable (durable : RStoreDurable p c E rho)
    (i j : Nat) (x : V) (hx : x ∈ rho.honest)
    (hij : i ≤ j) (hj : j ≤ rho.events.length) :
    (storeAt p c E rho i x).fg.TF ⊆ (storeAt p c E rho j x).fg.TF :=
  (durable i j x hx hij hj).1

omit [Fintype V] in
/-- FG finality is monotone through the kept store, including pre-GST restarts. -/
theorem healing_recovery_finality (mono : RMonoAll p c E rho)
    (i j : Nat) (x : V) (hx : x ∈ rho.honest)
    (hij : i ≤ j) :
    FGBlock.Preceq (storeAt p c E rho i x).fg.F (storeAt p c E rho j x).fg.F :=
  (mono i j x hx hij).1

/-- Recovery preserves stamps only on the exact receiver event interval. -/
theorem healing_scope_stamps (hrec : RecoverySleep₂ p c E rho G ΔF)
    (epoch : RStoreEpoch p c E rho)
    {x : V} (hx : x ∈ rho.honest) {a d : Time}
    (ha : E.t_GST ≤ a) (hd : d ≤ rho.horizon)
    (hij : V2.D.Run.actionCut rho a ≤ V2.D.Run.idxBefore rho d)
    (hj : V2.D.Run.idxBefore rho d ≤ rho.events.length) :
    (storeAt p c E rho (V2.D.Run.actionCut rho a) x).base.blockStamp <+:
      (storeAt p c E rho (V2.D.Run.idxBefore rho d) x).base.blockStamp ∧
    (storeAt p c E rho (V2.D.Run.actionCut rho a) x).base.voteStamp <+:
      (storeAt p c E rho (V2.D.Run.idxBefore rho d) x).base.voteStamp :=
  epoch _ _ x hx hij hj (healing_recovery_restartFree hrec hx ha hd)

/-- The next-frame companion keeps wires through restarts and stamps in the receiver epoch. -/
theorem healing_recovery_frame_prefixes (hrec : RecoverySleep₂ p c E rho G ΔF)
    (frame : RFrameNextEpoch p c E rho) {x : V} (hx : x ∈ rho.honest) {a d : Time}
    (ha : E.t_GST ≤ a) (hd : d ≤ rho.horizon)
    (hij : V2.D.Run.actionCut rho a ≤ V2.D.Run.idxBefore rho d)
    (hj : V2.D.Run.idxBefore rho d ≤ rho.events.length) :
    (storeAt p c E rho (V2.D.Run.actionCut rho a) x).proposals <+:
      (storeAt p c E rho (V2.D.Run.idxBefore rho d) x).proposals ∧
    (storeAt p c E rho (V2.D.Run.actionCut rho a) x).rowPool <+:
      (storeAt p c E rho (V2.D.Run.idxBefore rho d) x).rowPool ∧
    (storeAt p c E rho (V2.D.Run.actionCut rho a) x).base.blockStamp <+:
      (storeAt p c E rho (V2.D.Run.idxBefore rho d) x).base.blockStamp ∧
    (storeAt p c E rho (V2.D.Run.actionCut rho a) x).base.voteStamp <+:
      (storeAt p c E rho (V2.D.Run.idxBefore rho d) x).base.voteStamp := by
  obtain ⟨_, _, _, _, _, _, _, _, hkept⟩ := (frame _ x hx).2.2.2
  obtain ⟨hP, hR, hE⟩ := hkept _ hij hj
  exact ⟨hP, hR, hE (healing_recovery_restartFree hrec hx ha hd)⟩

/-- Wires persist through restarts; local stamps persist through the consuming action. -/
theorem healing_recovery_action_frame (hrec : RecoverySleep₂ p c E rho G ΔF)
    (frame : RFrameNextEpoch p c E rho) {x : V} (hx : x ∈ rho.honest)
    {a : Time} (ha : E.t_GST ≤ a) {j : Nat}
    (hij : V2.D.Run.actionCut rho a ≤ j) (hj : j ≤ rho.events.length) :
    (storeAt p c E rho (V2.D.Run.actionCut rho a) x).proposals <+:
      (storeAt p c E rho j x).proposals ∧
    (storeAt p c E rho (V2.D.Run.actionCut rho a) x).rowPool <+:
      (storeAt p c E rho j x).rowPool ∧
    (storeAt p c E rho (V2.D.Run.actionCut rho a) x).base.blockStamp <+:
      (storeAt p c E rho j x).base.blockStamp ∧
    (storeAt p c E rho (V2.D.Run.actionCut rho a) x).base.voteStamp <+:
      (storeAt p c E rho j x).base.voteStamp := by
  obtain ⟨_, _, _, _, _, _, _, _, hkept⟩ := (frame _ x hx).2.2.2
  obtain ⟨hP, hR, hE⟩ := hkept j hij hj
  exact ⟨hP, hR, hE (healing_recovery_action_epoch hrec hx ha j)⟩

end AvailableChain.FGSA.Run
end

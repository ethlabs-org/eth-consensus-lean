module
public import AvailableChainFGSAProofs.Proofs.Shared.Regimes
public import AvailableChainFGSAProofs.Proofs.Healing.ResetScope
public import AvailableChainFGSAClaims.Statements.FrameNext
public import AvailableChainFGSARun.Proofs.Join
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedConsumers

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

/-- The joined batch cutoff uses integer labels and requires a real predecessor. -/
@[expose] def HealingWindow (p : Params) {V : Type} (E : Generic.Env V)
    (back : Nat) (s : Slot) : Prop :=
  back ≤ s ∧ E.t_GST ≤ slotStartZ p ((s : Int) - (back : Int))

/-- A stronger cutoff also puts the saved labels after the recovery start. -/
def StrongHealingWindow (p : Params) {V : Type} (E : Generic.Env V)
    (back : Nat) (s : Slot) : Prop :=
  back ≤ s ∧ max E.t_GST (recoveryStart p E) ≤
    slotStartZ p ((s : Int) - (back : Int))

/-- The stronger cutoff supplies the batch cutoff. -/
theorem StrongHealingWindow.window {p : Params} {V : Type} {E : Generic.Env V}
    {back : Nat} {s : Slot} (h : StrongHealingWindow p E back s) :
    HealingWindow p E back s :=
  ⟨h.1, (le_max_left _ _).trans h.2⟩

/-- Later labels keep the same batch cutoff. -/
theorem HealingWindow.cut_mono {p : Params} {V : Type} {E : Generic.Env V}
    {back : Nat} {s w : Slot} (h : HealingWindow p E back s) (hsw : s ≤ w) :
    HealingWindow p E back w := by
  refine ⟨h.1.trans hsw, h.2.trans ?_⟩
  have hi : (s : Int) ≤ w := by exact_mod_cast hsw
  unfold slotStartZ
  nlinarith [p.deltaPos]

/-- A batch window includes the source vote's transport anchor. -/
theorem HealingWindow.sync {p : Params} {V : Type} {E : Generic.Env V}
    {back : Nat} {s : Slot} (h : HealingWindow p E back s) :
    E.t_GST ≤ SA.voteTime p.toParams s := by
  refine h.2.trans ?_
  change 4 * p.Δ * ((s : Int) - (back : Int)) ≤ 4 * p.Δ * (s : Int) + p.Δ
  have hb : (0 : Int) ≤ back := by positivity
  nlinarith [p.deltaPos]

/-- A two-label proposal window supplies the preceding current-batch window. -/
theorem HealingWindow.prior {p : Params} {V : Type} {E : Generic.Env V}
    {s : Slot} (h : HealingWindow p E 2 s) : HealingWindow p E 1 (s - 1) := by
  have hc : (2 : Nat) ≤ s := h.1
  constructor
  · change (1 : Nat) ≤ (s : Nat) - 1
    omega
  · have hs : ((s - 1 : Nat) : Int) - 1 = (s : Int) - 2 := by omega
    have hcut : E.t_GST ≤ slotStartZ p ((s : Int) - 2) := h.2
    change E.t_GST ≤ slotStartZ p (((s - 1 : Nat) : Int) - 1)
    rw [hs]
    exact hcut

/-- A source-slot cutoff supplies the next and all later batch windows. -/
theorem HealingWindow.after {p : Params} {V : Type} {E : Generic.Env V}
    {s w : Slot} (hc : E.t_GST ≤ slotStartZ p (s : Int)) (hw : s + 1 ≤ w) :
    HealingWindow p E 1 w := by
  have hwN : (s : Nat) + 1 ≤ w := hw
  have hpos : (1 : Nat) ≤ w := (Nat.succ_le_succ (Nat.zero_le s)).trans hwN
  refine ⟨hpos, hc.trans ?_⟩
  have hwI : (s : Int) + 1 ≤ (w : Int) := by exact_mod_cast hwN
  change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * ((w : Int) - 1)
  nlinarith [p.deltaPos]

/-- Nonnegative GST makes an integer batch cutoff imply a real saved label. -/
theorem healing_window_of_cut {p : Params} {V : Type} (E : Generic.Env V)
    {back : Nat} {s : Slot}
    (hc : E.t_GST ≤ slotStartZ p ((s : Int) - (back : Int))) :
    HealingWindow p E back s := by
  refine ⟨?_, hc⟩
  have ht : 0 ≤ 4 * p.Δ * ((s : Int) - (back : Int)) := E.t_GST_nonneg.trans hc
  have hs : (back : Int) ≤ (s : Int) := by nlinarith [p.deltaPos]
  exact_mod_cast hs

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}

/-- Recovery permits a restart at GST and excludes later honest restarts. -/
theorem healing_recovery_restart_bound (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {x : V} (hx : x ∈ rho.honest)
    {k : Nat} {t : Time} (hk : rho.events[k]? = some (.restart x t)) :
    t ≤ E.t_GST := by
  by_contra hn
  have ht : t ≤ rho.horizon :=
    (hrec.base.valid.in_horizon _ (List.mem_of_getElem? hk)).2
  exact hrec.suffixNoRestart x hx k t hk (lt_of_not_ge hn) (Int.lt_add_one_iff.mpr ht)

/-- An index after every event at GST starts a local recovery epoch. -/
theorem healing_recovery_epoch (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {x : V} (hx : x ∈ rho.honest)
    {i j : Nat} (hi : V2.D.Run.idxBefore rho (E.t_GST + 1) ≤ i) :
    V2.D.restartFree rho x i j := by
  intro k t hik _ hk
  have ht := healing_recovery_restart_bound E rho hrec hx hk
  have hkcut := (Gen.V2.Duty.index_lt_idxBefore_iff
    hrec.base.valid.toScheduleWellFormed hk (E.t_GST + 1)).mpr (Int.lt_add_one_iff.mpr ht)
  omega

omit [Fintype V] in
/-- Durable content and FG bounds use the all-restart foundation producers. -/
theorem healing_recovery_durable (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (durable : RStoreDurable p c E rho)
    (mono : RMonoAll p c E rho) {i j : Nat} {x : V}
    (hx : x ∈ rho.honest) (hij : i ≤ j) (hj : j ≤ rho.events.length) :
    (storeAt p c E rho i x).fg.TF ⊆ (storeAt p c E rho j x).fg.TF ∧
      (storeAt p c E rho i x).base.blocks <+: (storeAt p c E rho j x).base.blocks ∧
      FGBlock.Preceq (storeAt p c E rho i x).fg.F (storeAt p c E rho j x).fg.F := by
  have hd := durable i j x hx hij hj
  exact ⟨hd.1, hd.2.1, (mono i j x hx hij).1⟩

/-- Stamp prefixes use the same event-index epoch as the receiver service. -/
theorem healing_recovery_stamps (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (epoch : RStoreEpoch p c E rho)
    {i j : Nat} {x : V}
    (hx : x ∈ rho.honest) (hij : i ≤ j) (hj : j ≤ rho.events.length)
    (hi : V2.D.Run.idxBefore rho (E.t_GST + 1) ≤ i) :
    (storeAt p c E rho i x).base.blockStamp <+:
        (storeAt p c E rho j x).base.blockStamp ∧
      (storeAt p c E rho i x).base.voteStamp <+:
        (storeAt p c E rho j x).base.voteStamp :=
  epoch i j x hx hij hj (healing_recovery_epoch E rho hrec hx hi)

/-- Frame metadata stays durable; frame stamps use the receiver's suffix epoch. -/
theorem healing_recovery_frame_metadata (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (frame : RFrameNextEpoch p c E rho)
    {i j : Nat} {x : V} (hx : x ∈ rho.honest) (hij : i ≤ j)
    (hj : j ≤ rho.events.length) (hi : V2.D.Run.idxBefore rho (E.t_GST + 1) ≤ i) :
    (storeAt p c E rho i x).proposals <+: (storeAt p c E rho j x).proposals ∧
      (storeAt p c E rho i x).rowPool <+: (storeAt p c E rho j x).rowPool ∧
      (storeAt p c E rho i x).base.blockStamp <+:
        (storeAt p c E rho j x).base.blockStamp ∧
      (storeAt p c E rho i x).base.voteStamp <+:
        (storeAt p c E rho j x).base.voteStamp := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hprefix⟩ := frame i x hx
  obtain ⟨hp, hr, hs⟩ := hprefix j hij hj
  exact ⟨hp, hr, hs (healing_recovery_epoch E rho hrec hx hi)⟩

/-- Recovery readers are joined once their previous-slot cutoff includes GST. -/
theorem healing_recovery_joined (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {x : V} (hx : x ∈ rho.honest)
    {s : Slot} {t : Time} (hcut : E.t_GST ≤ slotStartZ p ((s : Int) - 1))
    (hgst : E.t_GST ≤ t) (hhor : t ≤ rho.horizon) : joinedAt p E rho x s t := by
  refine ⟨hrec.awake x hx t hgst hhor, ?_, ?_⟩
  · intro u hu hut hw
    by_contra hn
    have ha := hrec.awake x hx (u - 1) (by dsimp [Time] at *; omega)
      (by dsimp [Time] at *; omega)
    have hf := hw.2
    rw [ha] at hf
    exact Bool.noConfusion hf
  · intro u _ _ hu
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hu
    exact (healing_recovery_restart_bound E rho hrec hx hk).trans hcut

/-- The finite recovery suffix is joined at every read after recoveryStart. -/
theorem healing_joined_at_or_after_start (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {x : V} (hx : x ∈ rho.honest)
    {t : Time} (hready : recoveryStart p E ≤ t) (hhor : t ≤ rho.horizon) :
    joinedAt p E rho x (slotAt p t) t := by
  have hlo := healing_recovery_start_lower (p := p) E
  exact healing_recovery_joined E rho hrec hx (healing_ready_read_cutoff E hready)
    (by linarith [p.deltaPos]) hhor

omit [DecidableEq V] [Fintype V] in
/-- A proposal after recoveryStart supplies the exact prior-batch window. -/
theorem healing_ready_proposal_window (E : Generic.Env V) {s : Slot}
    (hready : recoveryStart p E ≤ SA.proposalTime p.toParams s) :
    HealingWindow p E 2 s :=
  healing_window_of_cut E (healing_ready_proposal_cutoff E hready)

/-- At an actual bounded tick, the environmental join enables the duty guard. -/
theorem healing_joinedNow_at_or_after_start (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {i : Nat} {x : V} {t : Time}
    (hx : x ∈ rho.honest) (hi : rho.events[i]? = some (.tick x t))
    (hready : recoveryStart p E ≤ t) (hhor : t ≤ rho.horizon) :
    joinedNow p (clock p (storeAt p c E rho i x) t) = true := by
  apply healing_recovery_joinedNow hrec hx hi hhor
  exact healing_ready_read_cutoff E hready

/-- The actual bounded HEAD tick executes the joined duty after recoveryStart. -/
theorem healing_ready_head_guard (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {i : Nat} {x : V} {s : Slot}
    (hx : x ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams s)))
    (hready : recoveryStart p E ≤ SA.voteTime p.toParams s)
    (hhor : SA.voteTime p.toParams s ≤ rho.horizon) :
    joinedNow p (clock p (storeAt p c E rho i x) (SA.voteTime p.toParams s)) = true :=
  healing_joinedNow_at_or_after_start E rho hrec hx hi hready hhor

/-- Readiness enables this actual bounded gate; a scheduled label is insufficient. -/
theorem healing_ready_gate_enabled (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {i : Nat} {x : V} {s : Slot}
    (hx : x ∈ rho.honest) (hi : IsGateTick p c rho i x s)
    (hready : recoveryStart p E ≤ SA.gateTime p.toParams s)
    (hhor : SA.gateTime p.toParams s ≤ rho.horizon) : enabledGateAt p c E rho i x s := by
  have hcut := healing_ready_read_cutoff E hready
  have hs : slotAt p (SA.gateTime p.toParams s) = s + 1 :=
    (fgsa_postClock_slot (c := c) (rho.stateBefore E i x) _).2.symm.trans
      (fgsa_gate_slot (c := c) _ s)
  apply healing_scope_enabled_gate hrec hx hi _ hhor
  simpa only [hs, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hcut

/-- The joined suffix includes every honest HEAD voter after the previous-slot cutoff. -/
theorem healing_recovery_joinedHonest (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (s : Slot)
    (hcut : E.t_GST ≤ slotStartZ p ((s : Int) - 1))
    (hgst : E.t_GST ≤ SA.voteTime p.toParams s)
    (hhor : SA.voteTime p.toParams s ≤ rho.horizon) :
    joinedHonest p E rho (SA.voteTime p.toParams s) = rho.honest := by
  classical
  let x := rho.seatOf (.base .fg) ⟨0, p.nPos⟩
  have hslot : slotAt p (SA.voteTime p.toParams s) = s :=
    (fgsa_postClock_slot (c := c) (rho.stateBefore E 0 x) _).2.symm.trans
      (fgsa_vote_slot (c := c) (rho.stateBefore E 0 x) s)
  change rho.honest.filter _ = rho.honest
  apply Finset.filter_eq_self.mpr
  intro x hx
  rw [hslot]
  exact healing_recovery_joined E rho hrec hx hcut hgst hhor

/-- Joined recovery voters supply both exact-service count conditions. -/
theorem healing_recovery_joined_counts (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (s : Slot)
    (hcut : E.t_GST ≤ slotStartZ p ((s : Int) - 1))
    (hgst : E.t_GST ≤ SA.voteTime p.toParams s)
    (hhor : SA.voteTime p.toParams s ≤ rho.horizon) :
    SA.releaseThreshold p.toParams ≤ (joinedHonest p E rho (SA.voteTime p.toParams s)).card ∧
      Gen.Pure.Batch (joinedHonest p E rho (SA.voteTime p.toParams s)).card
        (Gen.V2.Duty.faulty rho).card := by
  rw [healing_recovery_joinedHonest E rho hrec s hcut hgst hhor]
  have hn : Fintype.card V = p.n :=
    (V2.D.CStar.seats_eq (ℓ := .base .fg) hrec.base.linked.toCStar trivial).symm
  have hc := Finset.card_le_univ rho.honest
  rw [hn] at hc
  have hf : (Gen.V2.Duty.faulty rho).card = p.n - rho.honest.card := by
    rw [Gen.V2.Duty.faulty_def, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, hn]
  have hb := hrec.fault
  rw [hf] at hb
  have hpos := p.nPos
  constructor
  · change (p.n + 1) / 2 ≤ rho.honest.card
    omega
  · constructor
    rw [hf]
    omega

/-- A late source window supplies every honest voter in its current batch. -/
theorem healing_recovery_joined_window (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {s : Slot} {x : V}
    (h : HealingWindow p E 1 s) (hx : x ∈ rho.honest)
    (hh : SA.voteTime p.toParams s ≤ rho.horizon) :
    joinedAt p E rho x s (SA.voteTime p.toParams s) :=
  healing_recovery_joined E rho hrec hx h.2 h.sync hh

/-- A late source also supplies the actual next-label reader's join. -/
theorem healing_recovery_joined_next (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {s : Slot} {x : V} {t : Time}
    (h : HealingWindow p E 1 s) (hx : x ∈ rho.honest)
    (ht : SA.voteTime p.toParams s ≤ t) (hh : t ≤ rho.horizon) :
    joinedAt p E rho x (s + 1) t := by
  apply healing_recovery_joined E rho hrec hx _ (h.sync.trans ht) hh
  have hd := p.deltaPos
  have hc := h.2
  change E.t_GST ≤ 4 * p.Δ * ((s : Int) - 1) at hc
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  change E.t_GST ≤ 4 * p.Δ * (s : Int)
  linarith

/-- An actual next vote tick bounds the finite join service window. -/
theorem healing_recovery_joined_vote_next (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {s : Slot} {i : Nat} {x : V}
    (hCut : HealingWindow p E 1 s) (hx : x ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams (s + 1)))) :
    joinedAt p E rho x (s + 1) (SA.voteTime p.toParams (s + 1)) := by
  apply healing_recovery_joined_next E rho hrec hCut hx _
    (hrec.base.valid.in_horizon _ (List.mem_of_getElem? hi)).2
  change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
  push_cast
  linarith [p.deltaPos]

/-- The next vote reader uses the source-slot cutoff at its own clock label. -/
theorem healing_recovery_next_vote_joined_of_cut (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {s : Slot} {i : Nat} {x : V}
    (hc : E.t_GST ≤ slotStartZ p (s : Int)) (hx : x ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams (s + 1)))) :
    joinedAt p E rho x (s + 1) (SA.voteTime p.toParams (s + 1)) := by
  apply healing_recovery_joined E rho hrec hx
  · simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hc
  · refine hc.trans ?_
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith [p.deltaPos]
  · exact (hrec.base.valid.in_horizon _ (List.mem_of_getElem? hi)).2

/-- A bounded proposal tick uses its own next-label join cutoff. -/
theorem healing_recovery_joined_proposal_next (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {r : Slot} {i : Nat} {x : V}
    (hc : HealingWindow p E 1 r) (hx : x ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick x (SA.proposalTime p.toParams (r + 1)))) :
    joinedAt p E rho x (r + 1) (SA.proposalTime p.toParams (r + 1)) := by
  apply healing_recovery_joined_next E rho hrec hc hx _
    (hrec.base.valid.in_horizon _ (List.mem_of_getElem? hi)).2
  change 4 * p.Δ * (r : Int) + p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Int)
  push_cast
  linarith [p.deltaPos]

/-- Recovery derives the enabled gate and its index epoch; object services stay local. -/
theorem healing_recovery_gate_scope (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {i : Nat} {x : V} {s : Slot}
    (hx : x ∈ rho.honest) (hi : IsGateTick p c rho i x s)
    (hcut : E.t_GST ≤ slotStartZ p (s : Int))
    (hgst : E.t_GST ≤ SA.voteTime p.toParams s)
    (hhor : SA.gateTime p.toParams s ≤ rho.horizon)
    (hServices : ∀ q K, rho.seatOf (.base (.head s)) q ∈ rho.honest →
      HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
        (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K →
      Nonempty (FreshHeadService E rho s q K.root (SA.earlyTime p.toParams s) x) ∧
      TargetReceiptService E rho K (SA.earlyTime p.toParams s) x) :
    GateReceiptScope E rho i x s := by
  have henabled : enabledGateAt p c E rho i x s := by
    refine ⟨hi, ?_⟩
    have hb := fgsa_restartTime_bound E rho i x (slotStartZ p (s : Int)) (by
      intro k t _ hk
      exact (healing_recovery_restart_bound E rho hrec hx hk).trans hcut)
    change (match (rho.stateBefore E i x).st.restartTime with
      | none => True
      | some t => t ≤ slotStartZ p (s : Int))
    cases hr : (rho.stateBefore E i x).st.restartTime with
    | none => trivial
    | some t => exact hb t hr
  have hvg : SA.voteTime p.toParams s ≤ SA.gateTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hjoin : joinedAt p E rho x (s + 1) (SA.gateTime p.toParams s) := by
    apply healing_recovery_joined E rho hrec hx
    · simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hcut
    · exact hgst.trans hvg
    · exact hhor
  refine ⟨henabled, hjoin, ?_, hServices⟩
  intro k t hki _ hk
  have ht := healing_recovery_restart_bound E rho hrec hx hk
  have hve : SA.voteTime p.toParams s < SA.earlyTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + p.Δ < 4 * p.Δ * (s : Int) + 2 * p.Δ
    linarith [p.deltaPos]
  have hbefore := (Gen.V2.Duty.index_lt_idxBefore_iff
    hrec.base.valid.toScheduleWellFormed hk (SA.earlyTime p.toParams s)).mpr
      (ht.trans_lt (hgst.trans_lt hve))
  omega

/-- Exact ready service uses joined counts and the supplied local gate scopes. -/
theorem repair_exact_service_on (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (s : Slot) (Q : Block)
    (hne : Q ≠ .genesis) (hcut : E.t_GST ≤ slotStartZ p ((s : Int) - 1))
    (hgst : E.t_GST ≤ SA.voteTime p.toParams s)
    (hhead : SA.voteTime p.toParams s ≤ rho.horizon →
      ∀ x ∈ rho.honest, joinedAt p E rho x s (SA.voteTime p.toParams s) →
        headAtLabel p c E rho x s = some Q)
    (hgeometry : ∀ i x, x ∈ rho.honest → IsGateTick p c rho i x s →
      ExactServiceGateGeometry E rho i x s Q)
    (hScopes : ∀ i x,
      confirmedReaderAtIdx p c E rho x (afterTicksIdx rho (SA.gateTime p.toParams s))
        (SA.gateTime p.toParams s) → IsGateTick p c rho i x s →
      GateReceiptScope E rho i x s)
    (hhor : SA.voteTime p.toParams s ≤ rho.horizon) : ExactService p c E rho s Q := by
  obtain ⟨hfast, hbatch⟩ := healing_recovery_joined_counts E rho hrec s hcut hgst hhor
  exact exactService_of_head_recovery_on E rho G hrec.toRecovery₂ s Q hne hgst
    hhead hfast hbatch hgeometry hScopes

/-- Recovery awake facts turn an emitted or accepted object into an exact ready trigger. -/
theorem healing_recovery_readyTrigger (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF) (o : Obj p) (send a d : Time)
    (x : V) (hx : x ∈ rho.honest) (hgst : E.t_GST ≤ a) (hd : d ≤ rho.horizon)
    (htrigger : Gen.V2.Duty.Trigger E rho o send) :
    Gen.V2.Duty.ReadyTrigger E rho o send x a d := by
  have hlink (v : V) : V2.D.LinkReadyOn E rho v x a d := by
    intro t hat htd
    exact hrec.awake x hx t (hgst.trans hat) (htd.le.trans hd)
  rcases htrigger with ⟨v, hv, he⟩ | ⟨v, hv, i, hi⟩
  · exact ⟨v, hv, Or.inl he, hlink v⟩
  · exact ⟨v, hv, Or.inr ⟨i, hi⟩, hlink v⟩

/-- Recovery supplies transport and the receiver epoch. Retained history stays per object. -/
theorem healing_recovery_receiverService (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (o : Obj p) (send a freeze : Time)
    (x : V) (hx : x ∈ rho.honest) (hgst : E.t_GST ≤ a) (ha : 0 ≤ a)
    (hsa : send ≤ a) (haf : a + p.Δ ≤ freeze) (hfh : freeze ≤ rho.horizon)
    (htrigger : Gen.V2.Duty.Trigger E rho o send)
    (hhistory : Gen.V2.Duty.HistorySafeAt E rho x o a)
    (hhandlers : ∀ j t, a ≤ t → t < a + p.Δ → V2.D.Run.handlesAt E rho j x o t →
      (fgsa p c).wellFormed o = true ∧
      (fgsa p c).depsPresent (V2.D.Run.stateBefore E rho j x) o = true ∧
      fgsaTimely p (V2.D.Run.stateBefore E rho j x) o)
    (hexclude : (fgsa p c).excludes (V2.D.Run.stateBeforeTime E rho (a + p.Δ) x) o = false) :
    Nonempty (ReceiverService E rho o send freeze x) := by
  have hready := healing_recovery_readyTrigger E rho hrec.toRecovery₂ o send a
    (a + p.Δ) x hx hgst (haf.trans hfh) htrigger
  let dl := fun t => max t E.t_GST + p.Δ
  have hd : dl a = a + p.Δ := congrArg (· + p.Δ) (max_eq_left hgst)
  have delay (o : Obj p) (hn : ¬ isRowObject o) : fgsaDelay E.Δ ΔF o = p.Δ := by
    rw [fgsaDelay_nonrow E.Δ ΔF o hn, hrec.base.delta]
  have hw := Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy E rho hrec.sync
    (fun o => ¬ isRowObject o) p.Δ delay
  refine ⟨⟨dl, rho.horizon, a, hw, hd.symm ▸ hready, hsa, ha,
    hd.symm ▸ lt_add_of_pos_right a p.deltaPos,
    hd.symm ▸ haf.trans hfh, hd.symm ▸ haf.trans hfh, hd.symm ▸ haf,
    hhistory, ?_, hd.symm ▸ hhandlers, hd.symm ▸ hexclude⟩⟩
  apply Gen.V2.Duty.restartFree_actionCut_idxBefore hrec.base.valid.toScheduleWellFormed
    ((lt_add_of_pos_right a p.deltaPos).trans_le haf)
  intro k t hk hat htf
  exact hrec.suffixNoRestart x hx k t hk (hgst.trans_lt hat)
    (htf.trans_le (hfh.trans (le_add_of_nonneg_right (by decide))))

/-- H6 retained service supplies exact HEADs for joined readers.
Each object service contains ReadyTrigger, HistorySafeAt and its local index epoch. -/
theorem repair_head_exact (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF) (s : Slot)
    (hgst : E.t_GST ≤ SA.proposalTime p.toParams s - p.Δ)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (hinput : ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      joinedAt p E rho y s (SA.voteTime p.toParams s) →
      RetainedH6Input p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s)
    (hservices : ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      joinedAt p E rho y s (SA.voteTime p.toParams s) →
      TargetReceiptService E rho N.erase (SA.voteTime p.toParams s) y)
    (hscopes : ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      joinedAt p E rho y s (SA.voteTime p.toParams s) →
      RetainedServiceScope E rho ip ih x y s N)
    (hhor : SA.voteTime p.toParams s ≤ rho.horizon) :
    ∀ y ∈ rho.honest, joinedAt p E rho y s (SA.voteTime p.toParams s) →
      headAtLabel p c E rho y s = some N.erase := by
  have hreads := fgsa_retainedReads_H6_joined (hroots := hrec.base.receiptIdealization)
    E rho hrec.base.valid s hx hip hseat N hem hinput hservices
  exact exactService_head_of_retained_proposal_recovery_on E rho G hrec s hgst hx hip
    hseat N hem _ hreads hscopes hhor

end AvailableChain.FGSA.Run
end

module
public import AvailableChainFGSAProofs.Proofs.Clean.Action
public import AvailableChainFGSAProofs.Proofs.Clean.StepGate

public section

/-! P3 §§8.2–8.7; bp02 §§5.4–6. Closure at the inclusive event cut. -/
namespace AvailableChain.FGSA.Run

variable {ΔF : Time}
open AvailableChain.SimplexFG
variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

omit [DecidableEq V] in
private theorem closure_gate_label {j : Nat} {x : V} {s : Slot}
    (hj : IsGateTick p c rho j x s) : labelBoundAt p c rho j = s := by
  dsimp only [labelBoundAt]
  rw [show rho.events[j]? = some (.tick x (SA.gateTime p.toParams s)) from hj]
  change ((4 * p.Δ * (s : Int) + 6 * p.Δ - 6 * p.Δ) / (4 * p.Δ)).toNat = s
  have hd : (4 : Int) * p.Δ ≠ 0 := by have := p.deltaPos; positivity
  rw [add_sub_cancel_right, Int.mul_ediv_cancel_left _ hd, Int.toNat_natCast]

omit [DecidableEq V] in
private theorem closure_label_mono (hs : V2.D.ScheduleWellFormed E rho)
    {j i : Nat} (hji : j ≤ i) : labelBoundAt p c rho j ≤ labelBoundAt p c rho i := by
  rcases Nat.lt_or_eq_of_le hji with hji | rfl
  · have ht : (match rho.events[j]? with | some e => e.time | none => rho.horizon) ≤
        (match rho.events[i]? with | some e => e.time | none => rho.horizon) := by
      cases hj : rho.events[j]? with
      | none =>
        have hjl := List.getElem?_eq_none_iff.mp hj
        have hi : rho.events[i]? = none := List.getElem?_eq_none_iff.mpr (by omega)
        rw [hi]
      | some e =>
        cases hi : rho.events[i]? with
        | none => exact (hs.in_horizon e (List.mem_of_getElem? hj)).2
        | some f =>
          obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
          obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
          have hk := (List.pairwise_iff_getElem.mp hs.sorted) j i hjl hil hji
          rw [hje, hie] at hk
          exact V2.D.Engine.time_le_of_key_le _ _ hk
    have hd : (0 : Int) < 4 * p.Δ := by have := p.deltaPos; positivity
    have hb := Int.toNat_le_toNat (Int.ediv_le_ediv hd (sub_le_sub_right ht (6 * p.Δ)))
    dsimp only [labelBoundAt]
    cases hj : rho.events[j]? <;> cases hi : rho.events[i]? <;>
      rw [hj, hi] at hb <;> exact hb
  · exact Nat.le_refl _

/-- P3 §8.4 and bp02 §5.6. Class B. DC counterpart:
Execution/WeakGenesisGSTZeroActionSources:106; INTENTIONAL divergence.
FG-SA reads its source after the same-tick fast write, even without an
emitted row. The supplied history bounds every relative state call.
Saved values are used only in the receiver epoch.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem clean_actionSources_body [Fintype V] (b₀ : Time) :
  CleanCutSet p c E rho b₀ ΔF → Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card →
  FGFoundation p c E rho → SrcFrameAboveStmt p c E rho →
  ∀ i, i ≤ timeIdx rho b₀ → CleanHist p c E rho i →
    ∀ j x r C, j < i → x ∈ rho.honest →
      rho.events[j]? = some (.tick x (p.actionTime r)) →
      actionSource p c E rho x r = some (some C) →
      BelowLabel p c E rho i (labelBoundAt p c rho j) C := by
  intro h hq hf hsrc i hi hh j x r C hj _ ht hread
  have hs := h.base.valid.toScheduleWellFormed
  have hj1 : j + 1 ≤ i := Nat.succ_le_of_lt hj
  have hstate := cleanState_of_hist h hq hf hsrc (clean_actionStep p c E rho)
    (hj1.trans hi) (cleanHist_restrict hj1 hh)
  let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho j x) (p.actionTime r)).st
  have hfg : ∃ B, actionSourceFG p c E rho x r = some (some B) ∧ eraseFG B = C := by
    dsimp only [actionSource] at hread
    change (actionSourceFG p c E rho x r).map (Option.map eraseFG) = some (some C) at hread
    cases hb : actionSourceFG p c E rho x r with
    | none => rw [hb] at hread; cases hread
    | some ob =>
      cases ob with
      | none => rw [hb] at hread; cases hread
      | some B =>
        rw [hb] at hread
        exact ⟨B, rfl, Option.some.inj (Option.some.inj hread)⟩
  obtain ⟨B, hB, rfl⟩ := hfg
  have hsource : fgSource p st = some B := by
    rw [actionSourceFG_eq_round p c E rho hs ht] at hB
    change deepest _ = some B
    rw [(fgsa_action_slot_round (c := c) (V2.D.Run.stateBefore E rho j x) r).2]
    exact Option.some.inj hB
  have hmem : eraseFG B ∈ sourceCandidates p st := by
    rw [fgSource_eq_jointSource] at hsource
    exact of_decide_eq_true (Finset.mem_filter.mp (FGSA.pickPair_some_spec _ _ hsource).1).2
  have hfw : eraseFG B ∈ (fastWriteAt st (r * p.R)).getD [] := by
    rw [sourceCandidates_def] at hmem
    have hm := (Finset.mem_filter.mp hmem).1
    rw [(fgsa_action_slot_round (c := c) (V2.D.Run.stateBefore E rho j x) r).2] at hm
    exact List.mem_toFinset.mp hm
  have hst : storeAt p c E rho (j + 1) x = st := by
    change (V2.D.Run.stateBefore E rho (j + 1) x).st = st
    rw [(V2.D.Run.step_tick_eq E rho ht).1]
    exact tick_st (p := p) (c := c) E rho _ _ _
  rw [← hst] at hfw
  obtain ⟨k, hk, hRF, hkt, _, G, hG, hBG, _⟩ := hstate.fastWrite x (r * p.R) _ hfw
  rw [closure_gate_label p c rho (show IsGateTick p c rho j x (r * p.R) from ht)]
  exact belowLabel_of_preceq hBG
    (belowLabel_of_gateResultAt hs (Nat.lt_of_lt_of_le hk hj1) hkt.1 hG le_rfl)


/-- P3 §8.7 F2.6 (lead Q2: before cleanHistoryAt); bp02 §5.6. The frozen
all-source-read statement, from `clean_actionSources_body` through the
first-unfold equation. DC counterpart: Protocol/Grades/JointHistoryGapsIdx.lean
:26,141 (conditional same-index action sources); INTENTIONAL difference: FG-SA
reads include asleep nodes that emit no row (bp02 §5.6).
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem clean_actionSources [Fintype V] (b₀ : Time) :
    CleanActionSourcesStmt (ΔF := ΔF) p c E rho b₀ := by
  rw [CleanActionSourcesStmt_def (ΔF := ΔF)]
  exact clean_actionSources_body p c E rho b₀

/-- P3 §8.5:5282–5288, bp02 §5.7. Class B. DC counterparts:
Legacy/Definitions/SafetyRegimes:53–80 and Protocol/Grades/JointHistoryGapsIdx:26,141.
INTENTIONAL divergence: raw optional SA results and a finite inclusive cut.
Nat induction uses only history and states at indices at most the current
index. Saved values are used only in the receiver epoch.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem clean_invariant [Fintype V] {b₀ : Time}
    (h : CleanCutSet p c E rho b₀ ΔF) (hq : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho) :
    ∀ i, i ≤ timeIdx rho b₀ → CleanHist p c E rho i := by
  intro i
  induction i with
  | zero => intro _; exact cleanHist_zero
  | succ i ih =>
    intro hi1
    have hi : i < timeIdx rho b₀ := Nat.lt_of_succ_le hi1
    have hh := ih (Nat.le_of_lt hi)
    have hall : ∀ k, k ≤ i → CleanState p c E rho k := by
      intro k hki
      exact cleanState_of_hist h hq hf hsrc (clean_actionStep p c E rho)
        (hki.trans (Nat.le_of_lt hi)) (cleanHist_restrict hki hh)
    have hlen : timeIdx rho b₀ ≤ rho.events.length := List.length_filter_le ..
    have hil := Nat.lt_of_lt_of_le hi hlen
    obtain ⟨e, he⟩ : ∃ e, rho.events[i]? = some e :=
      ⟨rho.events[i], List.getElem?_eq_some_iff.mpr ⟨hil, rfl⟩⟩
    cases e with
    | restart v t => exact cleanHist_step_restart he hh
    | deliver v o t => exact cleanHist_step_delivery he hh
    | tick v t =>
      cases ht : isGateTime p t with
      | false => exact cleanHist_step_noGateTick he ht hh
      | true =>
        obtain ⟨s, hs⟩ := (isGateTime_iff p t).mp ht
        have hg := clean_gateHistStep (ΔF := ΔF) p c E rho b₀
        rw [CleanGateHistStep_def (ΔF := ΔF), CleanHistStep_def (ΔF := ΔF)] at hg
        apply hg h hq hf hsrc i hi ?_ hh hall
        rw [CleanGateTick_def]
        refine ⟨v, s, ?_⟩
        change rho.events[i]? = some (.tick v (SA.gateTime p.toParams s))
        rw [hs]
        exact he

/-- P3 §8.7, bp02 §5.7. DC: Legacy/Definitions/SafetyRegimes.lean:53–80.
INTENTIONAL difference: FG-SA uses an event-index AG rule at a finite cut.
The completed history and state prove both conclusions (CleanAGStmt).
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem clean_agRule [Fintype V] (b₀ : Time) : CleanAGStmt (ΔF := ΔF) p c E rho b₀ := by
  rw [CleanAGStmt_def (ΔF := ΔF)]
  intro h hq hf hsrc
  refine ⟨?_, ?_⟩
  · intro i _
    rw [GR_def]
    intro hi
    have hs := cleanState_of_hist h hq hf hsrc (clean_actionStep p c E rho) hi
      (clean_invariant p c E rho h hq hf hsrc i hi)
    exact ⟨hs.sources.2, hs.fOrigin⟩
  · intro i _ _
    rw [GT_def]
    intro hi
    exact clean_invariant p c E rho h hq hf hsrc (i + 1) (Nat.succ_le_of_lt hi)

/-- P3 §8.4. DC: Legacy/Definitions/SafetyRegimes.lean:53–80.
INTENTIONAL difference: FG-SA restarts keep durable state and reset local caches.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem clean_restartStep [Fintype V] (b₀ : Time) : CleanRestartStep (ΔF := ΔF) p c E rho b₀ := by
  rw [CleanRestartStep_def (ΔF := ΔF)]
  intro h hf hsrc j v t _ he hs
  exact clean_restartStateStep h hf hsrc hs he

private theorem closure_gate_index [Fintype V] {b₀ : Time}
    (h : CleanCutSet p c E rho b₀ ΔF) {x : V} (hx : x ∈ rho.honest)
    {s : Slot} (ht : SA.gateTime p.toParams s ≤ b₀)
    (hAw : E.awake x (SA.gateTime p.toParams s) = true) :
    ∃ j, j < timeIdx rho b₀ ∧ IsGateTick p c rho j x s := by
  have heq : ((4 * s + 6 : Nat) : Time) * p.Δ = SA.gateTime p.toParams s := by
    change ((4 * s + 6 : Nat) : Int) * p.Δ = 4 * p.Δ * (s : Int) + 6 * p.Δ
    push_cast
    ring
  obtain ⟨j, hj, _⟩ := fgsa_tick_total E rho h.base.valid.toScheduleWellFormed
    h.base.delta x hx (4 * s + 6) (heq ▸ ht.trans h.cut.2) (heq ▸ hAw)
  rw [heq] at hj
  exact ⟨j, (V2.D.Engine.index_lt_read_length_iff
    h.base.valid.toScheduleWellFormed b₀ hj).mpr ht, hj⟩

private theorem closure_row_tick {j : Nat} {x : V} {r : Nat} {a : RowWire p.n}
    (ha : HonestRowAt p c E rho j x r a) :
    rho.events[j]? = some (.tick x (p.actionTime r)) := ha.2.1

/-- P3 §§4.7, 8.5; bp02 §§5.4–6. Class B. DC counterparts:
Legacy/Definitions/SafetyRegimes:53–80 and Protocol/Grades/JointHistoryGapsIdx:26,141.
INTENTIONAL divergence: the seven clauses use raw SA results, exact
lease/saved/fast-write origins, and the finite inclusive event cut.
This is the unfolded public history body; only Export imports Claims.
Saved values are used only in the receiver epoch.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem cleanHistoryAt_body [Fintype V] {b₀ : Time}
    (h : CleanCutSet p c E rho b₀ ΔF) (hq : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho) :
  (∀ x y r s B C, x ∈ rho.honest → y ∈ rho.honest →
    SA.gateTime p.toParams r ≤ b₀ → SA.gateTime p.toParams s ≤ b₀ →
    confirmedReader p c E rho x (SA.gateTime p.toParams r) →
    confirmedReader p c E rho y (SA.gateTime p.toParams s) →
    gateResult p c E rho x r = some (some B) →
    gateResult p c E rho y s = some (some C) →
    (r < s → Block.Preceq B C) ∧ (r = s → Block.Compatible B C)) ∧
  (∀ j x s, j < timeIdx rho b₀ → x ∈ rho.honest →
    enabledGateAt p c E rho j x s →
    ∃ B, gateResultAt p c E rho j = some (some B) ∧ (s = 0 → B = .genesis)) ∧
  (∀ x y s B H, x ∈ rho.honest → y ∈ rho.honest →
    SA.gateTime p.toParams s ≤ b₀ → gateResult p c E rho x s = some (some B) →
    joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
    vHead p c E rho y s = some H → Block.Preceq B H) ∧
  (∀ i v, i ≤ timeIdx rho b₀ → v ∈ rho.honest →
    let st := storeAt p c E rho i v
    let below := BelowLabel p c E rho i (labelBoundAt p c rho i)
    below (F_at p c E rho i v) ∧ below (J_at p c E rho i v) ∧ below (S_at p c E rho i v) ∧
    (∀ row ∈ st.base.obligations, below row.1 ∧
      ∃ j < i, ∃ s B, enabledGateAt p c E rho j v s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B) ∧
    (∀ s C, GridCO.savedGenuine st.base s = some (some C) → below C ∧
      ∃ j < i, V2.D.restartFree rho v j i ∧
        enabledGateAt p c E rho j v s ∧ gateResultAt p c E rho j = some (some C)) ∧
    (∀ j s C, j < i → enabledGateAt p c E rho j v s →
      V2.D.restartFree rho v j i →
      FGSA.activeCompatible st C = true →
      gateResultAt p c E rho j = some (some C) → GridCO.savedGenuine st.base s = some (some C)) ∧
    (∀ s X, X ∈ (FGSA.fastWriteAt st s).getD [] → below X ∧
      ∃ j < i, V2.D.restartFree rho v j i ∧ enabledGateAt p c E rho j v s
        ∧ gatePassedAt p c E rho j ∧
        ∃ C, gateResultAt p c E rho j = some (some C) ∧ Block.Preceq X C ∧ fastAt p c E rho v s X) ∧
    (S_at p c E rho i v = .genesis ∨
      (∃ j < i, ∃ s, enabledGateAt p c E rho j v s ∧
        gateResultAt p c E rho j = some (some (S_at p c E rho i v))) ∨
      (∃ j ≤ i, S_at p c E rho i v = F_at p c E rho j v))) ∧
  (∀ i j x r C, i ≤ timeIdx rho b₀ → j < i → x ∈ rho.honest →
    rho.events[j]? = some (.tick x (p.actionTime r)) →
    actionSource p c E rho x r = some (some C) →
    BelowLabel p c E rho i (labelBoundAt p c rho j) C) ∧
  (∀ i j x r a e, i ≤ timeIdx rho b₀ → j < i → HonestRowAt p c E rho j x r a →
    namedEntry a.payload.height_pair = some e →
    ∃ C, actionSourceFG p c E rho x r = some (some C) ∧ EntryBelow p e C ∧
      BelowLabel p c E rho i (labelBoundAt p c rho j) (eraseFG C)) ∧
  (∀ i v, i < timeIdx rho b₀ → v ∈ rho.honest → FAdvanceAt p c E rho i v →
    let st := storeAt p c E rho i v
    let st' := storeAt p c E rho (i + 1) v
    st'.base.obligations = st.base.obligations ∧
    st'.base.genuine = st.base.genuine ∧ st'.fastWrite = st.fastWrite) := by
  have hs := h.base.valid.toScheduleWellFormed
  have hist := clean_invariant p c E rho h hq hf hsrc
  have state (i : Nat) (hi : i ≤ timeIdx rho b₀) : CleanState p c E rho i :=
    cleanState_of_hist h hq hf hsrc (clean_actionStep p c E rho) hi (hist i hi)
  have gateBelow {i j : Nat} {v : V} {s : Slot} {B : Block}
      (hji : j < i) (ht : enabledGateAt p c E rho j v s)
      (hB : gateResultAt p c E rho j = some (some B)) :
      BelowLabel p c E rho i (labelBoundAt p c rho i) B := by
    apply belowLabel_of_gateResultAt hs hji ht.1 hB
    rw [← closure_gate_label p c rho ht.1]
    exact closure_label_mono p c E rho hs (Nat.le_of_lt hji)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y r s B C hx hy hr hsTime hRx hRy hB hC
    obtain ⟨j, hj, hjt⟩ := closure_gate_index p c E rho h hx hr hRx.2.1
    obtain ⟨k, hk, hkt⟩ := closure_gate_index p c E rho h hy hsTime hRy.2.1
    rw [← gateResultAt_eq_gateResult p c E rho hs hjt] at hB
    rw [← gateResultAt_eq_gateResult p c E rho hs hkt] at hC
    have hBm : (r, B) ∈ cleanResults p c E rho (timeIdx rho b₀) :=
      ⟨j, hj, x, hjt, (clean_gate_enabled_of_result hs hjt hB).2, hB⟩
    have hCm : (s, C) ∈ cleanResults p c E rho (timeIdx rho b₀) :=
      ⟨k, hk, y, hkt, (clean_gate_enabled_of_result hs hkt hC).2, hC⟩
    refine ⟨(hist _ le_rfl).ordered r s B C hBm hCm, ?_⟩
    intro hrs
    subst s
    exact (hist _ le_rfl).same r B C hBm hCm
  · intro j x s hj _ ht
    exact (hist _ le_rfl).nonempty j x s hj ht
  · intro x y s B H hx hy hcut hB hJ hH
    have hex : ∃ j : Nat, IsGateTick p c rho j x s := by
      have hres := hB
      rw [gateResult_def] at hres
      obtain ⟨st, hgate, _⟩ := Option.map_eq_some_iff.mp hres
      rw [gateIn_def, preTick_def] at hgate
      obtain ⟨nd, hpre, _⟩ := Option.map_eq_some_iff.mp hgate
      obtain ⟨j, htick, _⟩ := Option.map_eq_some_iff.mp hpre
      exact ⟨j, V2.D.Run.tickIdx?_spec htick⟩
    obtain ⟨j, hjt⟩ := hex
    have hj := (V2.D.Engine.index_lt_read_length_iff hs b₀ hjt).mpr hcut
    have htime : SA.voteTime p.toParams (s + 1) < SA.gateTime p.toParams s := by
      change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ
      push_cast
      have := p.deltaPos
      nlinarith
    have heq : ((4 * (s + 1) + 1 : Nat) : Time) * p.Δ = SA.voteTime p.toParams (s + 1) := by
      change ((4 * (s + 1) + 1 : Nat) : Int) * p.Δ = 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
      push_cast
      ring
    obtain ⟨k, hk, _⟩ := fgsa_tick_total E rho hs h.base.delta y hy
      (4 * (s + 1) + 1) (heq ▸ htime.le.trans (hcut.trans h.cut.2)) (heq ▸ hJ.1)
    rw [heq] at hk
    have hkj := V2.D.Engine.eventIndex_lt_of_time_lt hs hk hjt htime
    rw [← gateResultAt_eq_gateResult p c E rho hs hjt] at hB
    rw [vHead_eq_headAtIdx p c E rho hs hk] at hH
    cases Option.some.inj hH
    exact (hist _ le_rfl).continues j k x y s B hj hkj hjt hk hJ hB
  · intro i v hi _
    have st := state i hi
    refine ⟨(st.fOrigin v).1, (st.fOrigin v).2, ?_, ?_, ?_, st.saved v, ?_, ?_⟩
    · rcases st.sOrigin v with hg | ⟨j, hj, s, ht, hB⟩ | ⟨j, hj, he⟩
      · exact Or.inl hg
      · exact gateBelow hj (clean_gate_enabled_of_result hs ht hB) hB
      · rw [he]
        exact belowLabel_mono_index hj (belowLabel_mono_label
          (closure_label_mono p c E rho hs hj) ((state j (hj.trans hi)).fOrigin v).1)
    · intro row hr
      have ho := st.leases v row hr
      obtain ⟨j, hj, s, B, ht, hpass, hB, hp⟩ := ho
      exact ⟨belowLabel_of_preceq hp (gateBelow hj (clean_gate_enabled_of_result hs ht hB) hB),
        j, hj, s, B, clean_gate_enabled_of_result hs ht hB, hpass, hB, hp⟩
    · intro s C hC
      have ho := st.savedOnly v s C hC
      obtain ⟨j, hj, hRF, ht, hB⟩ := ho
      exact ⟨gateBelow hj ht hB, st.savedOnly v s C hC⟩
    · intro s X hX
      have ho := st.fastWrite v s X hX
      obtain ⟨j, hj, hRF, ht, hpass, C, hC, hp, hfast⟩ := ho
      exact ⟨belowLabel_of_preceq hp (gateBelow hj ht hC), st.fastWrite v s X hX⟩
    · rcases st.sOrigin v with hg | ⟨j, hj, s, ht, hB⟩ | hf
      · exact Or.inl hg
      · exact Or.inr (Or.inl ⟨j, hj, s, clean_gate_enabled_of_result hs ht hB, hB⟩)
      · exact Or.inr (Or.inr hf)
  · intro i j x r C hi hj hx ht hC
    exact clean_actionSources_body p c E rho b₀ h hq hf hsrc i hi (hist i hi)
      j x r C hj hx ht hC
  · intro i j x r a e hi hj ha he
    have hr := (state i hi).sources.1
    rw [CleanRowSources_def] at hr
    obtain ⟨C, hC, heq, hp, hb⟩ := hr j x r a e hj ha he
    refine ⟨C, hC, ?_, ?_⟩
    · delta EntryBelow
      simp only [heightView_eq_simplex p,
        KitFG.simplexHeightView_def, KitFG.heightOf_def]
      refine ⟨(derive p.E p.cfg C).T_h, hp, ?_⟩
      rw [heq]
      exact Prod.ext (KitFG.entry_same_height p.E p.cfg C) rfl
    · rw [closure_gate_label p c rho (show IsGateTick p c rho j x (r * p.R) from
        closure_row_tick p c E rho ha)]
      exact hb
  · intro i v hi hv ha
    obtain ⟨o, t, he⟩ := ha.1
    exact (state (i + 1) (Nat.succ_le_of_lt hi)).harmless i v o t
      (Nat.lt_succ_self i) hv he ha

/-- P3 §8.2:5146–5153, bp02 §6. Class B. DC counterpart:
Generic/Properties:41 MonotoneFrom. INTENTIONAL divergence: all nodes and
event indices at the inclusive cut. No supplied history is needed.
Saved values are used only in the receiver epoch.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem sExtends [Fintype V] {b₀ : Time}
    (h : CleanCutSet p c E rho b₀ ΔF) (hq : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho) :
    ∀ v j k, j ≤ k → k ≤ timeIdx rho b₀ →
      Block.Preceq (S_at p c E rho j v) (S_at p c E rho k v) :=
  sExtends_upTo p c E rho h hq hf hsrc le_rfl
    (clean_invariant p c E rho h hq hf hsrc _ le_rfl)

end AvailableChain.FGSA.Run
end

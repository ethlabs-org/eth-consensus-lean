module
public import AvailableChainFGSAClaims.Statements.Channels
public import AvailableChainFGSAClaims.Statements.Regimes
public import AvailableChainFGSAProofs.Proofs.Clean.State
public import AvailableChainGeneric.Statements.Pure.Props

public section

namespace AvailableChain.FGSA.Run

variable {ΔF : Time}
open AvailableChain.SimplexFG
open Gen.Pure (CompatOn MonoOn)

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

theorem zero_export_no_gate (h : HealthyPrefix₂ p c E rho 0 ΔF)
    {j : Nat} {v : V} {s : Slot} (hj : j < timeIdx rho 0)
    (hg : IsGateTick p c rho j v s) : False := by
  have ht := (V2.D.Engine.index_lt_read_length_iff h.base.valid.toScheduleWellFormed
    0 hg).mp hj
  change SA.gateTime p.toParams s ≤ 0 at ht
  have hn : (0 : Time) ≤ s := Int.natCast_nonneg s
  have hd := p.deltaPos
  change 4 * p.Δ * (s : Time) + 6 * p.Δ ≤ 0 at ht
  nlinarith

private def ZeroState (st : FGSA.State p.n) : Prop :=
  st.fg = Store.init ∧ st.base.stableRecord = .genesis ∧
  st.base.obligations = [] ∧ st.base.genuine = [] ∧ st.fastWrite = [] ∧ st.base.now ≤ 0

private theorem zero_gate_pos (s : Slot) : 0 < SA.gateTime p.toParams s := by
  change 0 < 4 * p.Δ * (s : Int) + 6 * p.Δ
  have hn : (0 : Int) ≤ s := Int.natCast_nonneg s
  nlinarith [p.deltaPos]

private theorem zero_event_time (h : HealthyPrefix₂ p c E rho 0 ΔF)
    {i : Nat} {e : V2.Event V (fgsa p c).Object}
    (hi : i < timeIdx rho 0) (he : rho.events[i]? = some e) : e.time = 0 := by
  have hb := (V2.D.Engine.index_lt_read_length_iff h.base.valid.toScheduleWellFormed 0 he).mp hi
  have hn := (h.base.valid.in_horizon e (List.mem_of_getElem? he)).1
  exact le_antisymm hb hn

private theorem zero_no_gate (h : HealthyPrefix₂ p c E rho 0 ΔF)
    {i : Nat} (hi : i < timeIdx rho 0) (x : V) (s : Slot) :
    ¬ IsGateTick p c rho i x s := by
  intro he
  have ht := zero_event_time h hi he
  have hp := zero_gate_pos (p := p) s
  change SA.gateTime p.toParams s = 0 at ht
  exact (ne_of_gt hp) ht

private theorem zero_state (h : HealthyPrefix₂ p c E rho 0 ΔF)
    (i : Nat) (hi : i ≤ timeIdx rho 0) (v : V) : ZeroState (storeAt p c E rho i v) := by
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd => ZeroState nd.st) (Nat.zero_le i) v ?_ ?_
  · intro k e _ hki he hv hk
    have ht := zero_event_time h (lt_of_lt_of_le hki hi) he
    have hnext : ZeroState (storeAt p c E rho (k + 1) v) := by
      cases e with
      | restart u t =>
        have hp := (h.base.restartsAtWakes u t (List.mem_of_getElem? he)).1
        change t = 0 at ht
        exact (ne_of_gt hp) ht |>.elim
      | tick u t =>
        change u = v at hv
        subst u
        change t = 0 at ht
        subst t
        have hn : isGateTime p 0 = false := by
          apply Bool.eq_false_iff.mpr
          intro hg
          obtain ⟨s, hs⟩ := (isGateTime_iff p 0).mp hg
          have hp := zero_gate_pos (p := p) s
          exact (ne_of_gt hp) hs
        obtain ⟨hf, hs, ho, hg, hw⟩ := clean_noGate_fields (E := E) he hn
        have hnow : (storeAt p c E rho (k + 1) v).base.now = 0 := by
          dsimp only [storeAt]
          rw [← fgsa_clock_now p c (V2.D.Run.stateBefore E rho (k + 1) v)]
          rw [V2.D.Run.stateBefore_succ E rho he]
          simp only [V2.D.World.step, Function.update_self, V2.D.Engine.ClockLaws.now_tick]
        exact ⟨hf.trans hk.1, hs.trans hk.2.1,
          List.eq_nil_of_sublist_nil (hk.2.2.1 ▸ ho), hg.trans hk.2.2.2.1,
          hw.trans hk.2.2.2.2.1, le_of_eq hnow⟩
      | deliver u o t =>
        change u = v at hv
        subst u
        have href : ∀ s N P,
            (toWire p o).decode = some (.block s N) →
            namedParentHeld (storeAt p c E rho k v) N = true →
            parentFG (storeAt p c E rho k v) N.erase = some P →
            blockAccepted p (storeAt p c E rho k v) s N P = false := by
          intro s N P _ _ _
          apply Bool.eq_false_iff.mpr
          intro ha
          have hb := (blockAccepted_slot_pos ha).2
          have hn := hk.2.2.2.2.2
          change (4 : Int) * p.Δ ≤ (V2.D.Run.stateBefore E rho k v).st.base.now at hb
          have hp : (0 : Int) < 4 * p.Δ := by linarith [p.deltaPos]
          exact (not_le_of_gt hp) (le_trans hb hn)
        obtain ⟨hf, hs, ho, hg, hw⟩ := clean_delivery_fields he href
        have hnow : (storeAt p c E rho (k + 1) v).base.now ≤ 0 := by
          dsimp only [storeAt]
          rw [← fgsa_clock_now p c (V2.D.Run.stateBefore E rho (k + 1) v)]
          rw [V2.D.Run.stateBefore_succ E rho he]
          simpa only [V2.D.World.step, Function.update_self, (fgsaClock p c).process,
            fgsa_clock_now p c (V2.D.Run.stateBefore E rho k v)] using
            hk.2.2.2.2.2
        exact ⟨hf.trans hk.1, hs.trans hk.2.1, ho.trans hk.2.2.1,
          hg.trans hk.2.2.2.1, hw.trans hk.2.2.2.2.1, hnow⟩
    dsimp only [storeAt] at hnext
    rw [V2.D.Run.stateBefore_succ E rho he] at hnext
    exact hnext
  · exact ⟨rfl, rfl, rfl, rfl, rfl, le_refl 0⟩

omit [Fintype V] in
private theorem zero_row_tick {j : Nat} {x : V} {r : Nat} {a : RowWire p.n}
    (ha : HonestRowAt p c E rho j x r a) :
    rho.events[j]? = some (.tick x (p.actionTime r)) := ha.2.1

private theorem zero_history (h : HealthyPrefix₂ p c E rho 0 ΔF) :
  (∀ x y r s B C, x ∈ rho.honest → y ∈ rho.honest →
    SA.gateTime p.toParams r ≤ 0 → SA.gateTime p.toParams s ≤ 0 →
    gateResult p c E rho x r = some (some B) →
    gateResult p c E rho y s = some (some C) →
    (r < s → Block.Preceq B C) ∧ (r = s → Block.Compatible B C)) ∧
  (∀ j x s, j < timeIdx rho 0 → x ∈ rho.honest → IsGateTick p c rho j x s →
    ∃ B, gateResultAt p c E rho j = some (some B) ∧ (s = 0 → B = .genesis)) ∧
  (∀ x y s B H, x ∈ rho.honest → y ∈ rho.honest →
    SA.gateTime p.toParams s ≤ 0 → gateResult p c E rho x s = some (some B) →
    vHead p c E rho y s = some H → Block.Preceq B H) ∧
  (∀ i v, i ≤ timeIdx rho 0 → v ∈ rho.honest →
    let st := storeAt p c E rho i v
    let below := BelowLabel p c E rho i (labelBoundAt p c rho i)
    below (F_at p c E rho i v) ∧ below (J_at p c E rho i v) ∧ below (S_at p c E rho i v) ∧
    (∀ row ∈ st.base.obligations, below row.1 ∧
      ∃ j < i, ∃ s B, IsGateTick p c rho j v s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B) ∧
    (∀ s C, GridCO.savedGenuine st.base s = some (some C) → below C ∧
      ∃ j < i, IsGateTick p c rho j v s ∧ gateResultAt p c E rho j = some (some C)) ∧
    (∀ j s C, j < i → IsGateTick p c rho j v s →
      gateResultAt p c E rho j = some (some C) → GridCO.savedGenuine st.base s = some (some C)) ∧
    (∀ s X, X ∈ (FGSA.fastWriteAt st s).getD [] → below X ∧
      ∃ j < i, IsGateTick p c rho j v s ∧ gatePassedAt p c E rho j ∧
        ∃ C, gateResultAt p c E rho j = some (some C) ∧ Block.Preceq X C ∧ fastAt p c E rho v s X) ∧
    (S_at p c E rho i v = .genesis ∨
      (∃ j < i, ∃ s, IsGateTick p c rho j v s ∧
        gateResultAt p c E rho j = some (some (S_at p c E rho i v))) ∨
      (∃ j ≤ i, S_at p c E rho i v = F_at p c E rho j v))) ∧
  (∀ i j x r C, i ≤ timeIdx rho 0 → j < i → x ∈ rho.honest →
    rho.events[j]? = some (.tick x (p.actionTime r)) →
    actionSource p c E rho x r = some (some C) →
    BelowLabel p c E rho i (labelBoundAt p c rho j) C) ∧
  (∀ i j x r a e, i ≤ timeIdx rho 0 → j < i → HonestRowAt p c E rho j x r a →
    namedEntry a.payload.height_pair = some e →
    ∃ C, actionSourceFG p c E rho x r = some (some C) ∧ EntryBelow p e C ∧
      BelowLabel p c E rho i (labelBoundAt p c rho j) (eraseFG C)) ∧
  (∀ i v, i < timeIdx rho 0 → v ∈ rho.honest → FAdvanceAt p c E rho i v →
    let st := storeAt p c E rho i v
    let st' := storeAt p c E rho (i + 1) v
    st'.base.obligations = st.base.obligations ∧
    st'.base.genuine = st.base.genuine ∧ st'.fastWrite = st.fastWrite) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y r s B C _ _ hr
    exact (not_le_of_gt (zero_gate_pos r) hr).elim
  · intro j x s hj _ hg
    exact (zero_no_gate h hj x s hg).elim
  · intro x y s B H _ _ hs
    exact (not_le_of_gt (zero_gate_pos s) hs).elim
  · intro i v hi _
    obtain ⟨hf, hs, ho, hg, hw, _⟩ := zero_state h i hi v
    have hF : F_at p c E rho i v = .genesis := by
      change eraseFG (storeAt p c E rho i v).fg.F = _
      rw [hf]; rfl
    have hJ : J_at p c E rho i v = .genesis := by
      change eraseFG (storeAt p c E rho i v).fg.J = _
      rw [hf]; rfl
    refine ⟨Or.inl hF, Or.inl hJ, Or.inl hs, ?_, ?_, ?_, ?_, Or.inl hs⟩
    · intro row hr
      rw [ho] at hr
      cases hr
    · intro s C hc
      change ((storeAt p c E rho i v).base.genuine.find? _).map _ = _ at hc
      rw [hg] at hc
      cases hc
    · intro j s C hj ht
      exact (zero_no_gate h (lt_of_lt_of_le hj hi) v s ht).elim
    · intro s X hx
      change X ∈ (((storeAt p c E rho i v).fastWrite.find? _).map _).getD [] at hx
      rw [hw] at hx
      cases hx
  · intro i j x r C hi hj _ ht
    exact (zero_no_gate h (lt_of_lt_of_le hj hi) x (r * p.R) ht).elim
  · intro i j x r a e hi hj ha
    exact (zero_no_gate h (lt_of_lt_of_le hj hi) x (r * p.R) (zero_row_tick ha)).elim
  · intro i v hi _ _
    have ha := zero_state h i (Nat.le_of_lt hi) v
    have hb := zero_state h (i + 1) hi v
    exact ⟨hb.2.2.1.trans ha.2.2.1.symm,
      hb.2.2.2.1.trans ha.2.2.2.1.symm,
      hb.2.2.2.2.1.trans ha.2.2.2.2.1.symm⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 §8.5:5320–5346, bp02 initialization and §6, SYN L39.
DC Legacy/Definitions/SafetyRegimes:53–80 is the nearest counterpart.
Three-class rule: INTENTIONAL divergence, since strict-before-cut
participation permits false FaultQ at zero. Admission requires 4Δ ≤ now;
gates and actions require at least 6Δ. The time-zero event prefix can be
nonempty, but its FG tree and all Clean origins stay initial. No F1 channel
or extra honesty premise is used. There is no UNMOTIVATED or UNCLEAR change.
At the zero cut, positive wake restarts are outside the event prefix.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem cleanCut_zero_body (h : HealthyPrefix₂ p c E rho 0 ΔF) :
  ((∀ x y r s B C, x ∈ rho.honest → y ∈ rho.honest →
    SA.gateTime p.toParams r ≤ 0 → SA.gateTime p.toParams s ≤ 0 →
    gateResult p c E rho x r = some (some B) →
    gateResult p c E rho y s = some (some C) →
    (r < s → Block.Preceq B C) ∧ (r = s → Block.Compatible B C)) ∧
  (∀ j x s, j < timeIdx rho 0 → x ∈ rho.honest → IsGateTick p c rho j x s →
    ∃ B, gateResultAt p c E rho j = some (some B) ∧ (s = 0 → B = .genesis)) ∧
  (∀ x y s B H, x ∈ rho.honest → y ∈ rho.honest →
    SA.gateTime p.toParams s ≤ 0 → gateResult p c E rho x s = some (some B) →
    vHead p c E rho y s = some H → Block.Preceq B H) ∧
  (∀ i v, i ≤ timeIdx rho 0 → v ∈ rho.honest →
    let st := storeAt p c E rho i v
    let below := BelowLabel p c E rho i (labelBoundAt p c rho i)
    below (F_at p c E rho i v) ∧ below (J_at p c E rho i v) ∧ below (S_at p c E rho i v) ∧
    (∀ row ∈ st.base.obligations, below row.1 ∧
      ∃ j < i, ∃ s B, IsGateTick p c rho j v s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B) ∧
    (∀ s C, GridCO.savedGenuine st.base s = some (some C) → below C ∧
      ∃ j < i, IsGateTick p c rho j v s ∧ gateResultAt p c E rho j = some (some C)) ∧
    (∀ j s C, j < i → IsGateTick p c rho j v s →
      gateResultAt p c E rho j = some (some C) → GridCO.savedGenuine st.base s = some (some C)) ∧
    (∀ s X, X ∈ (FGSA.fastWriteAt st s).getD [] → below X ∧
      ∃ j < i, IsGateTick p c rho j v s ∧ gatePassedAt p c E rho j ∧
        ∃ C, gateResultAt p c E rho j = some (some C) ∧ Block.Preceq X C ∧ fastAt p c E rho v s X) ∧
    (S_at p c E rho i v = .genesis ∨
      (∃ j < i, ∃ s, IsGateTick p c rho j v s ∧
        gateResultAt p c E rho j = some (some (S_at p c E rho i v))) ∨
      (∃ j ≤ i, S_at p c E rho i v = F_at p c E rho j v))) ∧
  (∀ i j x r C, i ≤ timeIdx rho 0 → j < i → x ∈ rho.honest →
    rho.events[j]? = some (.tick x (p.actionTime r)) →
    actionSource p c E rho x r = some (some C) →
    BelowLabel p c E rho i (labelBoundAt p c rho j) C) ∧
  (∀ i j x r a e, i ≤ timeIdx rho 0 → j < i → HonestRowAt p c E rho j x r a →
    namedEntry a.payload.height_pair = some e →
    ∃ C, actionSourceFG p c E rho x r = some (some C) ∧ EntryBelow p e C ∧
      BelowLabel p c E rho i (labelBoundAt p c rho j) (eraseFG C)) ∧
  (∀ i v, i < timeIdx rho 0 → v ∈ rho.honest → FAdvanceAt p c E rho i v →
    let st := storeAt p c E rho i v
    let st' := storeAt p c E rho (i + 1) v
    st'.base.obligations = st.base.obligations ∧
    st'.base.genuine = st.base.genuine ∧ st'.fastWrite = st.fastWrite)) ∧
  (CompatOn (· ∈ rho.honest) (S_at p c E rho) (· ≤ timeIdx rho 0) ∧
  MonoOn (· ∈ rho.honest) (S_at p c E rho) (· ≤ timeIdx rho 0) ∧
  (∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
    CompatOn (· ∈ rho.honest) (fun t x => V2.D.outputAt E rho g x t) (fun t => 0 ≤ t ∧ t ≤ 0) ∧
    MonoOn (· ∈ rho.honest) (fun t x => V2.D.outputAt E rho g x t) (fun t => 0 ≤ t ∧ t ≤ 0)) ∧
  ((∀ x y r s B C, x ∈ rho.honest → y ∈ rho.honest →
    SA.gateTime p.toParams r ≤ 0 → SA.gateTime p.toParams s ≤ 0 →
    gateResult p c E rho x r = some (some B) →
    gateResult p c E rho y s = some (some C) →
    (r < s → Block.Preceq B C) ∧ (r = s → Block.Compatible B C)) ∧
  (∀ j x s, j < timeIdx rho 0 → x ∈ rho.honest → IsGateTick p c rho j x s →
    ∃ B, gateResultAt p c E rho j = some (some B) ∧ (s = 0 → B = .genesis)) ∧
  (∀ x y s B H, x ∈ rho.honest → y ∈ rho.honest →
    SA.gateTime p.toParams s ≤ 0 → gateResult p c E rho x s = some (some B) →
    vHead p c E rho y s = some H → Block.Preceq B H) ∧
  (∀ i v, i ≤ timeIdx rho 0 → v ∈ rho.honest →
    let st := storeAt p c E rho i v
    let below := BelowLabel p c E rho i (labelBoundAt p c rho i)
    below (F_at p c E rho i v) ∧ below (J_at p c E rho i v) ∧ below (S_at p c E rho i v) ∧
    (∀ row ∈ st.base.obligations, below row.1 ∧
      ∃ j < i, ∃ s B, IsGateTick p c rho j v s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B) ∧
    (∀ s C, GridCO.savedGenuine st.base s = some (some C) → below C ∧
      ∃ j < i, IsGateTick p c rho j v s ∧ gateResultAt p c E rho j = some (some C)) ∧
    (∀ j s C, j < i → IsGateTick p c rho j v s →
      gateResultAt p c E rho j = some (some C) → GridCO.savedGenuine st.base s = some (some C)) ∧
    (∀ s X, X ∈ (FGSA.fastWriteAt st s).getD [] → below X ∧
      ∃ j < i, IsGateTick p c rho j v s ∧ gatePassedAt p c E rho j ∧
        ∃ C, gateResultAt p c E rho j = some (some C) ∧ Block.Preceq X C ∧ fastAt p c E rho v s X) ∧
    (S_at p c E rho i v = .genesis ∨
      (∃ j < i, ∃ s, IsGateTick p c rho j v s ∧
        gateResultAt p c E rho j = some (some (S_at p c E rho i v))) ∨
      (∃ j ≤ i, S_at p c E rho i v = F_at p c E rho j v))) ∧
  (∀ i j x r C, i ≤ timeIdx rho 0 → j < i → x ∈ rho.honest →
    rho.events[j]? = some (.tick x (p.actionTime r)) →
    actionSource p c E rho x r = some (some C) →
    BelowLabel p c E rho i (labelBoundAt p c rho j) C) ∧
  (∀ i j x r a e, i ≤ timeIdx rho 0 → j < i → HonestRowAt p c E rho j x r a →
    namedEntry a.payload.height_pair = some e →
    ∃ C, actionSourceFG p c E rho x r = some (some C) ∧ EntryBelow p e C ∧
      BelowLabel p c E rho i (labelBoundAt p c rho j) (eraseFG C)) ∧
  (∀ i v, i < timeIdx rho 0 → v ∈ rho.honest → FAdvanceAt p c E rho i v →
    let st := storeAt p c E rho i v
    let st' := storeAt p c E rho (i + 1) v
    st'.base.obligations = st.base.obligations ∧
    st'.base.genuine = st.base.genuine ∧ st'.fastWrite = st.fastWrite)) ∧
  (∀ i v, i ≤ timeIdx rho 0 → v ∈ rho.honest →
    let st := storeAt p c E rho i v
    (FGSA.controls p st).contest = false ∧
    BelowLabel p c E rho i (labelBoundAt p c rho i) (eraseFG (FGSA.controls p st).Z) ∧
    (∀ B ∈ st.fg.TF,
      BelowLabel p c E rho i (labelBoundAt p c rho i) (eraseFG B) →
      Block.Preceq (eraseFG B) (eraseFG (FGSA.controls p st).Z) ∨
      Block.Preceq (eraseFG B) (eraseFG st.fg.F) ∨
      (FGBlock.Preceq st.fg.F (FGSA.controls p st).Z ∧
        FGBlock.Preceq (FGSA.controls p st).Z B ∧ B ∈ FGSA.fullTree p st))) ∧
  (∀ l x, SA.gateTime p.toParams l ≤ 0 → x ∈ rho.honest →
    ∃ B, gateResult p c E rho x l = some (some B) ∧
      (∃ j, IsGateTick p c rho j x l ∧ gatePassedAt p c E rho j) ∧
      Block.Preceq B (S_at p c E rho (afterTicksIdx rho (SA.gateTime p.toParams l)) x) ∧
      ∀ l' < l, ∀ B', gateResult p c E rho x l' = some (some B') → Block.Preceq B' B)) := by
  have hh := zero_history h
  have hS (i : Nat) (hi : i ≤ timeIdx rho 0) (v : V) :
      S_at p c E rho i v = .genesis := (zero_state h i hi v).2.1
  have hc : Gen.Pure.CompatOn (· ∈ rho.honest) (S_at p c E rho)
      (· ≤ timeIdx rho 0) := by
    intro i j x y hi hj _ _
    rw [hS i hi x, hS j hj y]
    rfl
  have hm : Gen.Pure.MonoOn (· ∈ rho.honest) (S_at p c E rho)
      (· ≤ timeIdx rho 0) := by
    intro i j x hi hj _ _
    rw [hS i hi x, hS j hj x]
    exact Gen.Pure.block_preceq_refl _
  refine ⟨hh, hc, hm, ?_, hh, ?_, ?_⟩
  · have hr (g) (hg : g ∈ [(fgsaInterface p c).stable,
        (fgsaInterface p c).confirmed]) (t : Time) (ht : 0 ≤ t ∧ t ≤ 0) (x : V) :
        V2.D.outputAt E rho g x t = .genesis := by
      have he : t = 0 := le_antisymm ht.2 ht.1
      subst t
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl <;>
        change (V2.D.Run.readAt E rho 0 x).st.base.stableRecord = _ <;>
        rw [V2.D.Engine.readAt_eq_stateBefore h.base.valid.toScheduleWellFormed 0] <;>
        exact hS _ le_rfl x
    intro g hg
    constructor
    · intro t u x y ht hu _ _
      change Block.Compatible (V2.D.outputAt E rho g x t) (V2.D.outputAt E rho g y u)
      rw [hr g hg t ht x, hr g hg u hu y]
      rfl
    · intro t u x ht hu _ _
      change Block.Preceq (V2.D.outputAt E rho g x t) (V2.D.outputAt E rho g x u)
      rw [hr g hg t ht x, hr g hg u hu x]
      exact Gen.Pure.block_preceq_refl _
  · intro i v hi _
    have hf := (zero_state h i hi v).1
    have hctl : (FGSA.controls p (storeAt p c E rho i v)).contest = false := by
      change (KitFG.treeStoreControlsView (heightView p)
        (storeAt p c E rho i v).fg).contest = false
      rw [hf]
      apply Bool.eq_false_iff.mpr
      intro ht
      obtain ⟨W, _, _, _, hn⟩ :=
        KitFG.treeStoreControlsView_contest_witness (heightView p) _ ht
      exact hn (KitFG.genesis_preceq W)
    have hz : (FGSA.controls p (storeAt p c E rho i v)).Z = .genesis := by
      change (KitFG.treeStoreControlsView (heightView p)
        (storeAt p c E rho i v).fg).Z = .genesis
      rw [hf]
      change (if _ then FGBlock.genesis else FGBlock.genesis) = _
      exact ite_self _
    refine ⟨hctl, ?_, ?_⟩
    · rw [hz]
      exact Or.inl rfl
    · intro B hB _
      rw [hf] at hB
      have he : B = .genesis := Finset.mem_singleton.mp hB
      subst B
      left
      rw [hz]
      exact Gen.Pure.block_preceq_refl _
  · intro l x hl
    exact (not_le_of_gt (zero_gate_pos l) hl).elim

end AvailableChain.FGSA.Run
end

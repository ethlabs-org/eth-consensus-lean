module
public import AvailableChainSAPC.Proofs.RunCleanPath
public import AvailableChainSAPC.Proofs.TransferRegimes

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- Membership in a source closure needs no assumption that its sources
are comparable. The separate clean-history proof establishes that order. -/
theorem gateWithPC_source_closed (p : Params) {n : Nat} (st : GridCO.State n)
    (r : Slot) (cert : Option (PC n)) {path : Block → Prop}
    (closed : ∀ a b, Block.Preceq a b → path b → path a)
    (hs : CleanStateOnPath path st)
    (raw : ∀ b, SA.confirmation p st r = some b → path b) :
    CleanStateOnPath path (gateWithPC p st r cert) := by
  have advance (a b : Block) (ha : path a) (hb : path b) : path (GridCO.advance a b) := by
    unfold GridCO.advance
    split <;> assumption
  have records := gateWithPC_records p st r cert
  constructor
  · rcases records.1 with he | ⟨b, hb, he⟩
    · exact he ▸ hs.stable
    · rw [he]; exact advance _ _ hs.stable (raw b hb)
  · rcases records.2 with he | ⟨b, hb, he⟩
    · exact he ▸ hs.goldfish
    · rw [he]; exact advance _ _ hs.goldfish (raw b hb)
  · intro b g d hm
    rcases gateWithPC_row_origin p st r cert b g d hm with hold | ⟨c, hc, hp, rest⟩
    · exact hs.finite b g d hold
    · exact closed b c hp (raw c hc)
  · intro s b hm
    rw [gateWithPC_genuine] at hm
    rcases @GridCO.recordGenuine_origin GridCO.slowLeasePolicy n st r s
        (SA.confirmation p st r) (some b) hm with hold | ⟨_, he⟩
    · exact hs.saved s b hold
    · exact raw b he.symm

/-- The PC lease loop preserves the SA source rule even when it vetoes
S. Clock phases before the gate only remove rows. -/
theorem clock_target_genuine_origin (p : Params) {n : Nat} (st : State n) (t : Time)
    (hs : GridCO.ReceiptStamped st.base) (b : Block) (g : Nat) (d : Time)
    (hm : (b, g, d) ∈ (clock p st t).base.obligations) :
    (b, g, d) ∈ st.base.obligations ∨ ∃ r c,
      t = gateTime p r ∧ SA.confirmation p st.base r = some c ∧ Block.Preceq b c := by
  rw [clock_eq_gate_prestate] at hm
  dsimp only at hm
  split at hm
  · rename_i hg
    rcases gateWithPC_row_origin p _ _ _ b g d hm with hold | ⟨c, hc, hp, rest⟩
    · rw [clockPreGate_base] at hold
      exact Or.inl (GridCO.clockPreGate_obligations_subset p.engine st.base t _ hold)
    · refine Or.inr ⟨_, c, by simpa using (Bool.and_eq_true_iff.mp hg).2, ?_, hp⟩
      rw [clockPreGate_base] at hc
      exact (@GridCO.confirmation_eq_of_receiptData GridCO.slowLeasePolicy p.engine n
        _ st.base (GridCO.clockPreGate_receiptData p.engine st.base t) hs _).symm.trans hc
  · rw [clockPreGate_base] at hm
    exact Or.inl (GridCO.clockPreGate_obligations_subset p.engine st.base t _ hm)

/-- Every finite row has a strictly earlier raw gate source in the same
reader's execution. No clean regime, cap, PC condition, or S order is used. -/
theorem run_target_genuine_origin {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) (index : Nat) (reader : V) (b : Block) (g : Nat) (d : Time)
    (hm : (b, g, d) ∈ (Run.stateBefore (sapc p) rho index reader).base.obligations) :
    ∃ j < index, ∃ r c,
      rho.events[j]? = some (.tick reader (gateTime p r)) ∧
      SA.confirmation p (Run.stateBefore (sapc p) rho j reader).base r = some c ∧
      Block.Preceq b c := by
  set_option backward.isDefEq.respectTransparency false in
  induction index with
  | zero => simp [Run.stateBefore, World.init, sapc, initial, GridCO.initial] at hm
  | succ index ih =>
    cases he : rho.events[index]? with
    | none =>
      obtain ⟨j, hj, rest⟩ := ih (by simpa [Run.stateBefore, List.take_add_one, he] using hm)
      exact ⟨j, by omega, rest⟩
    | some e =>
      rw [stateBefore_succ_event he] at hm
      cases e with
      | tick v t =>
        by_cases hv : reader = v
        · subst v
          simp only [World.step, sapc, Function.update_self] at hm
          rcases clock_target_genuine_origin p _ t (base_receiptStamped_at_fold p _ reader)
              b g d hm with hold | ⟨r, c, ht, hc, hp⟩
          · obtain ⟨j, hj, rest⟩ := ih hold
            exact ⟨j, by omega, rest⟩
          · exact ⟨index, by omega, r, c, ht ▸ he, hc, hp⟩
        · obtain ⟨j, hj, rest⟩ := ih (by simpa [World.step, hv] using hm)
          exact ⟨j, by omega, rest⟩
      | deliver v obj t =>
        have hold : (b, g, d) ∈ (Run.stateBefore (sapc p) rho index reader).base.obligations := by
          by_cases hv : reader = v
          · subst v
            simpa only [World.step, sapc, Function.update_self, process_obligations] using! hm
          · simpa only [World.step, Function.update_of_ne hv] using hm
        obtain ⟨j, hj, rest⟩ := ih hold
        exact ⟨j, by omega, rest⟩

/-- Both records, every saved raw result, and every finite target belong
to the run's source closure. Comparability and continuation are not assumed.
This supplies the state clause of the corrected invariant independently. -/
theorem state_on_cleanRunPath {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (rho : Run V (sapc p)) (index : Nat) (reader : V)
    (hr : reader ∈ rho.honest) :
    CleanStateOnPath (cleanRunPath p rho index)
      (Run.stateBefore (sapc p) rho index reader).base := by
  set_option backward.isDefEq.respectTransparency false in
  induction index with
  | zero =>
    exact ⟨Or.inl rfl, Or.inl rfl, by simp [Run.stateBefore, World.init, sapc, initial,
      GridCO.initial], by simp [Run.stateBefore, World.init, sapc, initial, GridCO.initial]⟩
  | succ i ih =>
    have hs : CleanStateOnPath (cleanRunPath p rho (i + 1))
        (Run.stateBefore (sapc p) rho i reader).base :=
      ⟨cleanRunPath_mono p rho (Nat.le_succ i) ih.stable,
        cleanRunPath_mono p rho (Nat.le_succ i) ih.goldfish,
        fun b g d hm => cleanRunPath_mono p rho (Nat.le_succ i) (ih.finite b g d hm),
        fun r b hm => cleanRunPath_mono p rho (Nat.le_succ i) (ih.saved r b hm)⟩
    cases he : rho.events[i]? with
    | none => simpa [Run.stateBefore, List.take_add_one, he] using hs
    | some e =>
      rw [stateBefore_succ_event he]
      cases e with
      | deliver v obj t =>
        by_cases hv : reader = v
        · subst v
          simpa only [World.step, sapc, Function.update_self] using process_clean p _ obj hs
        · simpa only [World.step, Function.update_of_ne hv] using hs
      | tick v t =>
        by_cases hv : reader = v
        · subst v
          simp only [World.step, sapc, Function.update_self, clock_eq_gate_prestate]
          have hpre := (clockPreGate_clean p _ t hs).1
          split
          · rename_i hg
            apply gateWithPC_source_closed p _ _ _ (cleanRunPath_closed p rho (i + 1)) hpre
            intro b hb
            have ht : t = gateTime p ((t - 6 * p.Δ) / (4 * p.Δ)).toNat := by
              simpa using (Bool.and_eq_true_iff.mp hg).2
            have hb' : SA.confirmation p (Run.stateBefore (sapc p) rho i reader).base
                ((t - 6 * p.Δ) / (4 * p.Δ)).toNat = some b := by
              rw [clockPreGate_base] at hb
              exact (@GridCO.confirmation_eq_of_receiptData GridCO.slowLeasePolicy p.engine p.n
                _ _ (GridCO.clockPreGate_receiptData p.engine _ t)
                (base_receiptStamped_at_fold p _ reader) _).symm.trans hb
            exact Or.inr ⟨b, .genuine i (Nat.lt_succ_self i) reader hr _ b (ht ▸ he) hb',
              GridCO.block_preceq_self b⟩
          · exact hpre
        · simpa only [World.step, Function.update_of_ne hv] using hs

/-- Honest finite roots have actual genuine sources, not an assumed
position below the public stable record. -/
theorem finite_target_on_cleanRunPath {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (rho : Run V (sapc p)) (i : Nat) (v : V) (hv : v ∈ rho.honest)
    (b : Block) (g : Nat) (d : Time)
    (hm : (b, g, d) ∈ (Run.stateBefore (sapc p) rho i v).base.obligations) :
    cleanRunPath p rho i b := by
  obtain ⟨j, hj, r, c, ht, hc, hp⟩ := run_target_genuine_origin p rho i v b g d hm
  exact Or.inr ⟨c, .genuine j hj v hv r c ht hc, hp⟩

/-- A finite row at the next HEAD comes from a label strictly before r.
The gate for r is still pending. This is the same source boundary used
by the shared SA induction. -/
theorem nextHead_target_genuine_origin {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (r : Slot) (reader : V) (b : Block) (g : Nat) (d : Time)
    (hm : (b, g, d) ∈ (headState p rho (r + 1) reader).base.obligations) :
    ∃ s c, s < r ∧
      SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p s) reader).base s =
        some c ∧ Block.Preceq b c := by
  have input := base_receiptStamped_at_fold p
    (rho.events.filter (fun e => decide (e.time < voteTime p (r + 1)))) reader
  rcases clock_target_genuine_origin p _ (voteTime p (r + 1)) input b g d hm with
    hold | ⟨s, c, ht, hc, hp⟩
  · change (b, g, d) ∈
      (Run.stateBeforeTime (sapc p) rho (voteTime p (r + 1)) reader).base.obligations at hold
    rw [time_input_eq_event_prefix p E rho hs] at hold
    obtain ⟨j, hj, s, c, ht, hc, hp⟩ := run_target_genuine_origin p rho _ reader b g d hold
    have htime := Int.le_sub_one_iff.mp
      ((index_lt_read_length_iff hs (voteTime p (r + 1) - 1) ht).mp hj)
    have hsr : s < r := by
      by_contra hn
      have hle : (r : Time) ≤ s := by exact_mod_cast (le_of_not_gt hn)
      change 4 * p.Δ * (s : Time) + 6 * p.Δ <
        4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ at htime
      push_cast at htime
      nlinarith [p.deltaPos]
    rw [stateBefore_tick_eq_stateBeforeTime hs ht] at hc
    exact ⟨s, c, hsr, hc, hp⟩
  · have hne := GridCO.releaseTime_ne_gateTime p.engine r s
    rw [GridCO.release_eq_next_vote] at hne
    exact (hne ht).elim

/-- Ordered genuine history supplies the finite-root premise of the
actual SA-PC transfer theorem. No PC premise enters this source argument. -/
theorem nextHead_root_compatible_of_history {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (r : Slot)
    (history : GridCO.GenuineExtends (fun v => v ∈ rho.honest)
      (fun s v => SA.confirmation p
        (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).base s) r)
    (source reader : V) (hsource : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (b : Block)
    (hb : SA.confirmation p
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) source).base r = some b) :
    Block.Compatible (GridCO.liveRoot (headState p rho (r + 1) reader).base) b := by
  rcases (GridCO.liveRoot_is_deepest (headState p rho (r + 1) reader).base).1 with hg | hm
  · rw [hg]
    exact Bool.or_eq_true_iff.mpr (Or.inl (GridCO.genesis_prefix b))
  · obtain ⟨⟨target, g, d⟩, hm, ht⟩ := List.mem_filterMap.mp hm
    dsimp only at ht
    split at ht
    · have he := Option.some.inj ht
      obtain ⟨s, c, hsr, hc, hp⟩ := nextHead_target_genuine_origin p E rho hs
        r reader target g d hm
      obtain ⟨b', hb', hcb⟩ := history s hsr reader hr c hc source hsource
      have hbb : b' = b := Option.some.inj (hb'.symm.trans hb)
      subst b'
      rw [← he]
      exact Bool.or_eq_true_iff.mpr (Or.inl (GridCO.prefix_trans target c b hp hcb))
    · contradiction

/-- The SA-PC instance of the shared label induction. The finite-root
obligation is discharged by actual row sources and ordered history.
The two remaining inputs are batch preservation and PC compatibility;
they are proof interfaces, not added contract premises. -/
theorem clean_genuine_history_of_steps {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (r : Slot) (hh : gateTime p r ≤ rho.horizon)
    (preserve : ∀ s, s < r →
      GridCO.GenuineContinues (fun v => v ∈ rho.honest)
        (fun s v => SA.confirmation p
          (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).base s)
        (fun s v => (headData p rho (s + 1) v).target) s →
      ∀ source ∈ rho.honest, ∀ b,
        SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p s) source).base s =
          some b → ∀ reader ∈ rho.honest, ∃ c,
        SA.confirmation p
          (Run.stateBeforeTime (sapc p) rho (gateTime p (s + 1)) reader).base (s + 1) =
            some c ∧ Block.Preceq b c)
    (pc : ∀ s, s ≤ r →
      GridCO.GenuineExtends (fun v => v ∈ rho.honest)
        (fun s v => SA.confirmation p
          (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).base s) s →
      ∀ source ∈ rho.honest, ∀ b,
        SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p s) source).base s =
          some b → ∀ reader ∈ rho.honest, ∀ cert,
        capBroken p (headState p rho (s + 1) reader) = false →
        selectedPC p (headState p rho (s + 1) reader) (s + 1) = some cert →
          Block.Compatible cert.target b) :
    GridCO.GenuineExtends (fun v => v ∈ rho.honest)
      (fun s v => SA.confirmation p
        (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).base s) r ∧
    GridCO.GenuineContinues (fun v => v ∈ rho.honest)
      (fun s v => SA.confirmation p
        (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).base s)
      (fun s v => (headData p rho (s + 1) v).target) r := by
  apply GridCO.genuine_history_induction _ _ _ r preserve
  intro s hsr history source hsource b hb reader hr
  have htime : gateTime p s ≤ rho.horizon :=
    ((GridCO.gateTime_le_iff p.engine s r).mpr hsr).trans hh
  have hsync : E.t_GST ≤ earlyTime p s := by
    rw [hs.gst_zero]
    change 0 ≤ 4 * p.Δ * (s : Time) + 2 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg s]
  have root := nextHead_root_compatible_of_history p E rho hs.execution.toScheduleWellFormed s
    history source reader hsource hr b hb
  cases mode : capBroken p (headState p rho (s + 1) reader) with
  | false =>
    exact synchronous_genuine_compatiblePC_head_covers p E rho hs.execution hΔ hs.acceptedRelay
      s hsync htime source reader hsource hr b b hb (GridCO.block_preceq_self b) root
      (fun cert hc => pc s hsr history source hsource b hb reader hr cert mode hc)
  | true =>
    obtain ⟨forward, backward⟩ := synchronous_transfer_relays p E rho hΔ hs.acceptedRelay
      s hsync htime
    have hfreeze : freezeTime p s ≤ rho.horizon := by
      apply le_trans _ htime
      change 4 * p.Δ * (s : Time) + 3 * p.Δ ≤ 4 * p.Δ * (s : Time) + 6 * p.Δ
      linarith [p.deltaPos]
    simpa only [headData, headTarget, Nat.add_eq_zero_iff, Nat.one_ne_zero,
      and_false, decide_false, Bool.false_eq_true, ↓reduceIte, mode, choice] using!
      genuine_ordinary_head_covers p E rho hs.execution hΔ s source reader hsource hr
        hfreeze forward backward b b hb (GridCO.block_preceq_self b) root

end AvailableChain.SAPC
end

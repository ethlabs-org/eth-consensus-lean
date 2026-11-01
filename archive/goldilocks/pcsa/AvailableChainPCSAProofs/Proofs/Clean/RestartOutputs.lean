module
public import AvailableChainPCSAProofs.Proofs.Clean.RestartStep
public import AvailableChainPCSAProofs.Proofs.Shared.RestartSuffix
public import AvailableChainPCSAProofs.Proofs.Clean.RestartRecord

public section

/-! The outputs of the CI restart from label `a` (pcsa34-r5 §5.5): the record
history from the seed gate and the recovered-suffix invariant through the cut. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- A record read after a cut index is the record at the cut or the result of a
later own gate. -/
theorem pcsa_record_stateBefore_origin_from (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (c₀ k : Nat) (hck : c₀ ≤ k) (x : V) (hx : x ∈ rho.honest) :
    (V2.D.Run.stateBefore E rho k x).st.base.stableRecord =
        (V2.D.Run.stateBefore E rho c₀ x).st.base.stableRecord ∨
      ∃ j, c₀ ≤ j ∧ j < k ∧ ∃ s X, rho.events[j]? = some (.tick x (SA.gateTime p.toParams s)) ∧
        gateResultAt p c E rho x s = some (some X) ∧
        (V2.D.Run.stateBefore E rho k x).st.base.stableRecord = X := by
  induction k, hck using Nat.le_induction with
  | base => exact Or.inl rfl
  | succ k hck ih =>
    have carry (hkeep : (V2.D.Run.stateBefore E rho (k + 1) x).st.base.stableRecord =
        (V2.D.Run.stateBefore E rho k x).st.base.stableRecord) :
        (V2.D.Run.stateBefore E rho (k + 1) x).st.base.stableRecord =
            (V2.D.Run.stateBefore E rho c₀ x).st.base.stableRecord ∨
          ∃ j, c₀ ≤ j ∧ j < k + 1 ∧ ∃ s X,
            rho.events[j]? = some (.tick x (SA.gateTime p.toParams s)) ∧
            gateResultAt p c E rho x s = some (some X) ∧
            (V2.D.Run.stateBefore E rho (k + 1) x).st.base.stableRecord = X := by
      rw [hkeep]
      rcases ih with hh | ⟨j, hcj, hj, rest⟩
      · exact Or.inl hh
      · exact Or.inr ⟨j, hcj, Nat.lt_succ_of_lt hj, rest⟩
    cases he : rho.events[k]? with
    | none =>
      apply carry
      have hsame : V2.D.Run.stateBefore E rho (k + 1) = V2.D.Run.stateBefore E rho k := by
        delta V2.D.Run.stateBefore
        rw [List.take_add_one, he]
        simp only [Option.toList_none, List.append_nil]
      rw [hsame]
    | some e =>
      have hstep := V2.D.Run.stateBefore_succ E rho he
      by_cases hn : e.node = x
      · cases e with
        | restart y t => exact (h.noRestart k y t he).elim
        | deliver y o t =>
          change y = x at hn
          subst y
          apply carry
          have hf := (hF x hx (k + 1)).1
          rw [hstep] at hf ⊢
          change (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.fg.F = .genesis at hf
          change (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.base.stableRecord = _
          rw [Function.update_self] at hf ⊢
          exact pcsa_process_record_of_genesis p _ (toWire p o) hf
        | tick y t =>
          change y = x at hn
          subst y
          have hclock : (V2.D.Run.stateBefore E rho (k + 1) x).st =
              clock p (V2.D.Run.stateBefore E rho k x).st t := by
            rw [hstep]
            change (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st = _
            rw [Function.update_self]
            exact pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k x) x t
          rcases pcsa_clock_record_origin p (V2.D.Run.stateBefore E rho k x).st t
              (hF x hx k).1 with hold | ⟨s, X, ht, hr, hX⟩
          · exact carry (by rw [hclock]; exact hold)
          · have hread : gateResultAt p c E rho x s = some (some X) := by
              have hk : rho.events[k]? = some (.tick x (SA.gateTime p.toParams s)) := ht ▸ he
              rw [pcsa_gateResultAt_at_tick E rho h.valid.nodup k x s hk,
                pcsa_clock_confirmation_eq_pre]
              rw [← ht]
              exact congrArg some hr
            exact Or.inr ⟨k, hck, Nat.lt_succ_self k, s, X, ht ▸ he, hread,
              by rw [hclock]; exact hX⟩
      · apply carry
        have hh := V2.D.World.step_apply_of_node_ne E rho (V2.D.Run.stateBefore E rho k) hn
        rw [hstep, hh]

/-- Two own gate ticks in event order have increasing labels. -/
theorem pcsa_gate_tick_label_lt {E : Generic.Env V} (rho : V2.D.Run V (pcsaWith m p c))
    (h : Base₂ p c E rho)
    {x : V} {i j : Nat} {s s' : Slot} (hij : i < j)
    (hi : rho.events[i]? = some (.tick x (SA.gateTime p.toParams s)))
    (hj : rho.events[j]? = some (.tick x (SA.gateTime p.toParams s'))) : s < s' := by
  have hs := h.valid.toScheduleWellFormed
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
  have ht := (List.pairwise_iff_getElem.mp hs.sorted) i j hil hjl hij
  rw [hie, hje] at ht
  have hle := V2.D.Engine.time_le_of_key_le _ _ ht
  have hne : SA.gateTime p.toParams s ≠ SA.gateTime p.toParams s' := by
    intro hst
    rw [hst] at hi
    have := (List.Nodup.getElem?_inj hil h.valid.nodup).mp (hi.trans hj.symm)
    omega
  have hlt := lt_of_le_of_ne hle hne
  change 4 * p.Δ * (s : Int) + 6 * p.Δ < 4 * p.Δ * (s' : Int) + 6 * p.Δ at hlt
  have hp : (0 : Int) < p.Δ := p.deltaPos
  have : (s : Int) < s' := by nlinarith
  exact_mod_cast this

/-- An honest node ticks at every gate inside the horizon. -/
theorem pcsa_gate_tick_exists {E : Generic.Env V} (rho : V2.D.Run V (pcsaWith m p c))
    (h : Base₂ p c E rho)
    (x : V) (hx : x ∈ rho.honest) (s : Slot) (hc : SA.gateTime p.toParams s ≤ rho.horizon) :
    ∃ k : Nat, rho.events[k]? = some (V2.Event.tick x (SA.gateTime p.toParams s)) := by
  have hp : V2.PublicTime E (SA.gateTime p.toParams s) := by
    refine ⟨4 * s + 6, ?_⟩
    rw [h.delta]
    change 4 * p.Δ * (s : Int) + 6 * p.Δ = ((4 * s + 6 : Nat) : Int) * p.Δ
    push_cast
    ring
  have hz : 0 ≤ SA.gateTime p.toParams s := by
    have hd := p.deltaPos
    change 0 ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    positivity
  exact List.mem_iff_getElem?.mp (h.valid.tick_total x hx _ hp hz hc)
end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}

/-- After its seed gate tick, the record of an honest node is an own result of a
label at least `a`. -/
theorem pcsa_restart_record_origin_index (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) (hF : StageOneFrame p c E rho)
    {a : Slot} {A : Block} (hS : CleanRestartSeed p c E rho a A)
    (x : V) (hx : x ∈ rho.honest) (ka : Nat)
    (hka : rho.events[ka]? = some (.tick x (SA.gateTime p.toParams a))) (k : Nat) (hk : ka < k) :
    ∃ j i X, j < k ∧ rho.events[j]? = some (.tick x (SA.gateTime p.toParams i)) ∧ a ≤ i ∧
      gateResultAt p c E rho x i = some (some X) ∧
      (V2.D.Run.stateBefore E rho k x).st.base.stableRecord = X := by
  have hA : (V2.D.Run.stateBefore E rho (ka + 1) x).st.base.stableRecord = A := by
    have hpost := pcsa_restart_post_gate_record E rho h hF hS x hx _
      (pcsa_postClock_at_tick E rho h.valid.nodup ka x _ hka)
    rw [V2.D.Run.stateBefore_succ E rho hka, pcsa_tick_step]
    exact hpost
  have hres : gateResultAt p c E rho x a = some (some A) := by
    have h1 := pcsa_gateResultAt_at_tick E rho h.valid.nodup ka x a hka
    rw [h1, hS.result x hx _ h1]
  rcases pcsa_record_stateBefore_origin_from E rho h hF (ka + 1) k hk x hx with
    hold | ⟨j, hcj, hjk, i, X, hj, hX, hrec⟩
  · exact ⟨ka, a, A, hk, hka, le_rfl, hres, hold.trans hA⟩
  · exact ⟨j, i, X, hjk, hj, (pcsa_gate_tick_label_lt rho h hcj hka hj).le, hX, hrec⟩

/-- From the seed gate tick, ordered own results of labels at least `a` make each
record update monotone. -/
theorem pcsa_restart_record_step_mono (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) (hF : StageOneFrame p c E rho)
    {a : Slot} {A : Block} (hS : CleanRestartSeed p c E rho a A)
    (x : V) (hx : x ∈ rho.honest) (ka : Nat)
    (hka : rho.events[ka]? = some (.tick x (SA.gateTime p.toParams a))) (limit : Nat)
    (horder : ∀ i i' X Y, a ≤ i → i < i' → ∀ j,
      rho.events[j]? = some (.tick x (SA.gateTime p.toParams i')) → j < limit →
      gateResultAt p c E rho x i = some (some X) →
      gateResultAt p c E rho x i' = some (some Y) → Block.Preceq X Y)
    (k : Nat) (hak : ka < k) (hk : k < limit) :
    Block.Preceq (V2.D.Run.stateBefore E rho k x).st.base.stableRecord
      (V2.D.Run.stateBefore E rho (k + 1) x).st.base.stableRecord := by
  have keep (heq : (V2.D.Run.stateBefore E rho (k + 1) x).st.base.stableRecord =
      (V2.D.Run.stateBefore E rho k x).st.base.stableRecord) :
      Block.Preceq (V2.D.Run.stateBefore E rho k x).st.base.stableRecord
        (V2.D.Run.stateBefore E rho (k + 1) x).st.base.stableRecord := by
    rw [heq]
    exact Gen.Pure.block_preceq_refl _
  cases he : rho.events[k]? with
  | none =>
    apply keep
    have hs : V2.D.Run.stateBefore E rho (k + 1) = V2.D.Run.stateBefore E rho k := by
      delta V2.D.Run.stateBefore
      rw [List.take_add_one, he]
      simp only [Option.toList_none, List.append_nil]
    rw [hs]
  | some e =>
    have hstep := V2.D.Run.stateBefore_succ E rho he
    by_cases hn : e.node = x
    · cases e with
      | restart y t => exact (h.noRestart k y t he).elim
      | deliver y o t =>
        change y = x at hn
        subst y
        apply keep
        have hf := (hF x hx (k + 1)).1
        rw [hstep] at hf ⊢
        change (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.fg.F = .genesis at hf
        change (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.base.stableRecord = _
        rw [Function.update_self] at hf ⊢
        exact pcsa_process_record_of_genesis p _ (toWire p o) hf
      | tick y t =>
        change y = x at hn
        subst y
        have hclock : (V2.D.Run.stateBefore E rho (k + 1) x).st =
            clock p (V2.D.Run.stateBefore E rho k x).st t := by
          rw [hstep]
          change (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st = _
          rw [Function.update_self]
          exact pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k x) x t
        rcases pcsa_clock_record_origin p _ t (hF x hx k).1 with
          hold | ⟨s, X, ht, hX, hs⟩
        · exact keep (by rw [hclock]; exact hold)
        · rw [hclock, hs]
          have hke : rho.events[k]? = some (.tick x (SA.gateTime p.toParams s)) := ht ▸ he
          have hread : gateResultAt p c E rho x s = some (some X) := by
            rw [pcsa_gateResultAt_at_tick E rho h.valid.nodup k x s hke,
              pcsa_clock_confirmation_eq_pre, ← ht]
            exact congrArg some hX
          obtain ⟨j, i, Y, hjk, hj, hai, hY, hrec⟩ :=
            pcsa_restart_record_origin_index E rho h hF hS x hx ka hka k hak
          rw [hrec]
          exact horder i s Y X hai (pcsa_gate_tick_label_lt rho h hjk hj hke) k hke hk hY hread
    · apply keep
      have hh := V2.D.World.step_apply_of_node_ne E rho (V2.D.Run.stateBefore E rho k) hn
      rw [hstep, hh]

/-- From the seed gate tick, ordered own results make indexed record reads monotone. -/
theorem pcsa_restart_record_indices_mono (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) (hF : StageOneFrame p c E rho)
    {a : Slot} {A : Block} (hS : CleanRestartSeed p c E rho a A)
    (x : V) (hx : x ∈ rho.honest) (ka : Nat)
    (hka : rho.events[ka]? = some (.tick x (SA.gateTime p.toParams a))) (limit : Nat)
    (horder : ∀ i i' X Y, a ≤ i → i < i' → ∀ j,
      rho.events[j]? = some (.tick x (SA.gateTime p.toParams i')) → j < limit →
      gateResultAt p c E rho x i = some (some X) →
      gateResultAt p c E rho x i' = some (some Y) → Block.Preceq X Y)
    (k k' : Nat) (hak : ka < k) (hkk : k ≤ k') (hk : k' ≤ limit) :
    Block.Preceq (V2.D.Run.stateBefore E rho k x).st.base.stableRecord
      (V2.D.Run.stateBefore E rho k' x).st.base.stableRecord := by
  induction k', hkk using Nat.le_induction with
  | base => exact Gen.Pure.block_preceq_refl _
  | succ b hb ih =>
    exact Gen.Pure.block_preceq_trans (ih (Nat.le_trans (Nat.le_succ b) hk))
      (pcsa_restart_record_step_mono E rho h hF hS x hx ka hka limit horder b
        (Nat.lt_of_lt_of_le hak hb) (Nat.lt_of_lt_of_le (Nat.lt_succ_self b) hk))

/-- From the restart state through label `u`, every lock read after `z_a` and before
gate `u` is below each result of label `u`. -/
theorem pcsa_restart_lock_below_gate_result (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    {a : Slot} {A : Block} (hS : CleanRestartSeed p c E rho a A)
    (u : Slot) (hau : a ≤ u) (hst : CleanStateFrom p c E rho a u)
    (hseed : ∃ w ∈ rho.honest, ∃ W, gateResultAt p c E rho w a = some (some W))
    (k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hzk : V2.D.Run.idxBefore rho (SA.freezeTime p.toParams a) ≤ k)
    (hk : k ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams u))
    (row : Block × Nat × Time) (hr : row ∈ (V2.D.Run.stateBefore E rho k x).st.base.obligations)
    (X : Block) (hX : gateResultAt p c E rho y u = some (some X)) : Block.Preceq row.1 X := by
  have hs := h.valid.toScheduleWellFormed
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  have hAX : Block.Preceq A X := by
    obtain ⟨w, hw, W, hW⟩ := hseed
    have hWA : W = A := Option.some.inj (hS.result w hw _ hW)
    rw [← hWA]
    rcases hau.lt_or_eq with hlt | heq
    · exact (hst.results w hw y hy a u W X le_rfl hau le_rfl hW hX).1 hlt
    · subst heq
      rw [hWA, Option.some.inj (hS.result y hy _ hX)]
      exact Gen.Pure.block_preceq_refl _
  let cut := V2.D.Run.idxBefore rho (SA.gateTime p.toParams a)
  have hzc : V2.D.Run.idxBefore rho (SA.freezeTime p.toParams a) ≤ cut := by
    change V2.D.Run.idxBefore rho _ ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams a)
    rw [V2.D.Run.idxBefore_def, V2.D.Run.idxBefore_def, ← List.countP_eq_length_filter,
      ← List.countP_eq_length_filter]
    apply List.countP_mono_left
    intro e _ he
    apply decide_eq_true
    apply (of_decide_eq_true he).trans_le
    change 4 * p.Δ * (a : Int) + 3 * p.Δ ≤ 4 * p.Δ * (a : Int) + 6 * p.Δ
    linarith
  rcases le_total k cut with hkc | hck
  · exact Gen.Pure.block_preceq_trans (hS.locksFromFreeze x hx k hzk hkc row hr) hAX
  · rcases pcsa_lock_stateBefore_origin_from E rho h cut k hck x row hr with
      hold | ⟨j, hcj, hjk, s', Y, hj, hY, hrY, _⟩
    · exact Gen.Pure.block_preceq_trans (hS.locksFromFreeze x hx cut hzc le_rfl row hold) hAX
    · have hge : ¬ SA.gateTime p.toParams s' < SA.gateTime p.toParams a := fun hlt =>
        absurd ((Gen.V2.Duty.index_lt_idxBefore_iff hs hj _).mpr hlt) (not_lt.mpr hcj)
      have has' : a ≤ s' := by
        by_contra hn
        apply hge
        change 4 * p.Δ * (s' : Int) + 6 * p.Δ < 4 * p.Δ * (a : Int) + 6 * p.Δ
        have : (s' : Int) + 1 ≤ a := by exact_mod_cast Nat.lt_of_not_ge hn
        nlinarith
      have ht := (Gen.V2.Duty.index_lt_idxBefore_iff hs hj _).mp (hjk.trans_le hk)
      have hi : s' < u := by
        by_contra hn
        exact absurd (pcsa_gate_time_mono p (Nat.le_of_not_gt hn)) (not_le.mpr ht)
      exact Gen.Pure.block_preceq_trans hrY
        ((hst.results x hx y hy s' u Y X has' hi.le le_rfl hY hX).1 hi)
end AvailableChain.PCSA.Run


namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}

/-- From label `a`: a HEAD whose early time is inside the cut covers every earlier
result of a label at least `a`. -/
theorem pcsa_restart_head_above_past (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {T₀ cut : Time} {a : Slot} {A : Block}
    (h : CleanWindow E rho a T₀ cut) (hF : StageOneFrame p c E rho)
    (hFault : FaultsBelowQA p c rho) (hS : CleanRestartSeed p c E rho a A)
    (s : Slot) (hc : SA.earlyTime p.toParams s ≤ cut) (x : V) (H : Block)
    (hH : HonestHeadAt p c E rho x s H) (y : V) (hy : y ∈ rho.honest) (i : Slot) (X : Block)
    (hai : a ≤ i) (hi : i < s) (hX : gateResultAt p c E rho y i = some (some X)) :
    Block.Preceq X H := by
  cases s with
  | zero => exact (Nat.not_lt_zero i hi).elim
  | succ s =>
    rw [earlyTime_succ_eq_gateTime] at hc
    have has : a ≤ s := Nat.le_of_lt_succ (hai.trans_lt hi)
    have hst := pcsa_restart_state_from E rho h hF hFault hS s has hc
    obtain ⟨D, hD⟩ := pcsa_clean_result_exists_win E rho h hF y hy s has hc
    have his : i ≤ s := Nat.le_of_lt_succ hi
    have hXD : Block.Preceq X D := by
      rcases his.lt_or_eq with hlt | heq
      · exact (hst.results y hy y hy i s X D hai his le_rfl hX hD).1 hlt
      · subst i
        have he : X = D := Option.some.inj (Option.some.inj (hX.symm.trans hD))
        rw [he]
        exact Gen.Pure.block_preceq_refl _
    exact Gen.Pure.block_preceq_trans hXD
      (pcsa_next_head_above_result_of_root_win E rho h.base hF h.strict y x hy s D H
        (pcsa_cleanWindow_floor E rho h s has) hc hD hH
        (fun R hR => hst.roots x hH.1 R hR y hy D hD))

/-- From label `a`: an earlier honest ack target is below every later ack target
whose early time is inside the cut. -/
theorem pcsa_restart_ack_order (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {T₀ cut : Time} {a : Slot} {A : Block}
    (h : CleanWindow E rho a T₀ cut) (hF : StageOneFrame p c E rho)
    (hFault : FaultsBelowQA p c rho) (hS : CleanRestartSeed p c E rho a A)
    (i s : Slot) (hai : a ≤ i) (hi : i < s) (hc : SA.earlyTime p.toParams s ≤ cut)
    (x y : V) (B C : Block) (hB : HonestAckAt p c E rho x i B)
    (hC : HonestAckAt p c E rho y s C) : Block.Preceq B C := by
  cases s with
  | zero => exact (Nat.not_lt_zero i hi).elim
  | succ s =>
    rw [earlyTime_succ_eq_gateTime] at hc
    have hst := pcsa_restart_state_from E rho h hF hFault hS s
      (Nat.le_of_lt_succ (hai.trans_lt hi)) hc
    obtain ⟨z, hz⟩ := pcsa_ack_has_honest_head E rho h.base hF hFault y (s + 1) C hC
    exact hst.ackHeads i (s + 1) hai hi le_rfl x B hB z C hz

/-- From label `a`: an honest ack target of a label at least `a` inside the cut is
compatible with each result of a label at least `a` inside the cut. -/
theorem pcsa_restart_ack_result (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {T₀ cut : Time} {a : Slot} {A : Block}
    (h : CleanWindow E rho a T₀ cut) (hF : StageOneFrame p c E rho)
    (hFault : FaultsBelowQA p c rho) (hS : CleanRestartSeed p c E rho a A)
    (s : Slot) (has : a ≤ s) (hs : SA.earlyTime p.toParams s ≤ cut)
    (z : V) (B : Block) (ha : HonestAckAt p c E rho z s B)
    (i : Slot) (hai : a ≤ i) (hi : SA.gateTime p.toParams i ≤ cut) (y : V) (hy : y ∈ rho.honest)
    (X : Block) (hX : gateResultAt p c E rho y i = some (some X)) : Block.Compatible B X := by
  rcases lt_trichotomy s i with hlt | heq | hgt
  · have hst := pcsa_restart_state_from E rho h hF hFault hS i hai hi
    exact Bool.or_eq_true_iff.mpr (Or.inl (hst.ackResults s i has hlt le_rfl z B ha y hy X hX))
  · subst i
    exact pcsa_honestAck_same_label_result_win E rho h hF hFault z y hy s B X has hi ha hX
  · obtain ⟨u, hu⟩ := pcsa_ack_has_honest_head E rho h.base hF hFault z s B ha
    exact Bool.or_eq_true_iff.mpr (Or.inr
      (pcsa_restart_head_above_past E rho h hF hFault hS s hs u B hu y hy i X hai hgt hX))

/-- From slot `a`: two held PCs of slot at least `a` inside the cut are ordered by
slot and equal at equal slots. -/
theorem pcsa_restart_pc_pair (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {T₀ cut : Time} {a : Slot} {A : Block}
    (h : CleanWindow E rho a T₀ cut) (hF : StageOneFrame p c E rho)
    (hFault : FaultsBelowQA p c rho) (hS : CleanRestartSeed p c E rho a A)
    (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest) (t t' : Time) (ht' : t' ≤ cut)
    (C D : PC p.n) (hCa : a ≤ C.slot) (hC : C ∈ (storeAt p c E rho x t).pcs)
    (hD : D ∈ (storeAt p c E rho y t').pcs) :
    (C.slot < D.slot → Block.Preceq C.target D.target) ∧
      (C.slot = D.slot → C.target = D.target) := by
  obtain ⟨_, u, hu, _⟩ := pcsa_pc_storeAt_timed_ack E rho h.base hFault x hx t C hC
  obtain ⟨_, v, hv, hDt⟩ := pcsa_pc_storeAt_timed_ack E rho h.base hFault y hy t' D hD
  exact ⟨fun hlt => pcsa_restart_ack_order E rho h hF hFault hS C.slot D.slot hCa hlt
      (hDt.trans ht') u v C.target D.target hu hv,
    fun heq => pcsa_ack_targets_unique E rho h.base hF hFault u v D.slot C.target D.target
      (heq ▸ hu) hv⟩

/-- The restart from label `a` gives the recovered-suffix invariant through the cut. -/
theorem pcsa_restart_suffix_invariant (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {T₀ cut : Time} {a : Slot} {A : Block}
    (h : CleanWindow E rho a T₀ cut) (hF : StageOneFrame p c E rho)
    (hFault : FaultsBelowQA p c rho) (hS : CleanRestartSeed p c E rho a A) :
    RecoveredSuffixInvariant p c E rho a A cut := by
  have hs := h.base.valid.toScheduleWellFormed
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  have readLen (t : Time) (x : V) : storeAt p c E rho x t = (V2.D.Run.stateBefore E rho
      (rho.events.filter (fun e : V2.Event V (Obj p) => decide (e.time ≤ t))).length x).st := by
    rw [storeAt_def, V2.D.Engine.readAt_eq_stateBefore hs]
    rfl
  have seedOf (w : V) (hw : w ∈ rho.honest) (hc : SA.gateTime p.toParams a ≤ cut) :
      ∃ W, gateResultAt p c E rho w a = some (some W) :=
    pcsa_clean_result_exists_win E rho h hF w hw a le_rfl hc
  have horder (x : V) (hx : x ∈ rho.honest) : ∀ i i' X Y, a ≤ i → i < i' → ∀ j,
      rho.events[j]? = some (.tick x (SA.gateTime p.toParams i')) →
      j < (rho.events.filter (fun e : V2.Event V (Obj p) => decide (e.time ≤ cut))).length →
      gateResultAt p c E rho x i = some (some X) →
      gateResultAt p c E rho x i' = some (some Y) → Block.Preceq X Y := by
    intro i i' X Y hai hii j hj hjl hX hY
    have hc := (V2.D.Engine.index_lt_read_length_iff hs cut hj).mp hjl
    exact ((pcsa_restart_state_from E rho h hF hFault hS i' (hai.trans hii.le) hc).results
      x hx x hx i i' X Y hai hii.le le_rfl hX hY).1 hii
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy i i' X Y hai hii hc hX hY
    exact (pcsa_restart_state_from E rho h hF hFault hS i' (hai.trans hii) hc).results
      x hx y hy i i' X Y hai hii le_rfl hX hY
  · intro x hx y hy t t' C D ht ht' hCa hDa hC hD
    have hCD := pcsa_restart_pc_pair E rho h hF hFault hS x y hx hy t t' ht' C D hCa hC hD
    have hDC := pcsa_restart_pc_pair E rho h hF hFault hS y x hy hx t' t ht D C hDa hD hC
    refine ⟨?_, hCD.1⟩
    rcases lt_trichotomy C.slot D.slot with hlt | heq | hgt
    · exact Bool.or_eq_true_iff.mpr (Or.inl (hCD.1 hlt))
    · rw [hCD.2 heq]
      exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl _)
        (Gen.Pure.block_preceq_refl _)
    · exact Bool.or_eq_true_iff.mpr (Or.inr (hDC.1 hgt))
  · intro x hx y hy t C i X ht hCa hai hi hC hX
    obtain ⟨_, u, hu, hCt⟩ := pcsa_pc_storeAt_timed_ack E rho h.base hFault x hx t C hC
    exact pcsa_restart_ack_result E rho h hF hFault hS C.slot hCa (hCt.trans ht) u C.target hu
      i hai hi y hy X hX
  · intro x hx t hz ht
    have hk : FGSA.Run.afterTicksIdx rho (SA.freezeTime p.toParams a) ≤
        (rho.events.filter (fun e : V2.Event V (Obj p) => decide (e.time ≤ t))).length :=
      (FGSA.Run.afterTicksIdx_mono rho hz).trans (FGSA.Run.preIdx_le_afterTicksIdx E rho hs t).2
    obtain ⟨C₀, hC₀, hC₀s, hC₀t⟩ := pcsa_stamped_held E rho hs h.base.noRestart hF x hx _ a A
      (hS.stamped x hx) _ hk
    rw [← readLen] at hC₀
    cases hl : latestPC (storeAt p c E rho x t) with
    | none =>
      have he := pcsa_bestPC_none _ hl
      rw [he] at hC₀
      exact absurd hC₀ List.not_mem_nil
    | some C =>
      have hC := bestPC_mem _ C hl
      have hCs : a ≤ C.slot := hC₀s ▸ pcsa_bestPC_slot_of_mem _ C₀ C hC₀ hl
      have hpair := pcsa_restart_pc_pair E rho h hF hFault hS x x hx hx t t ht C₀ C
        hC₀s.ge hC₀ hC
      refine ⟨C, hC, rfl, hCs, ?_⟩
      rw [← hC₀t]
      rcases (hC₀s ▸ hCs : C₀.slot ≤ C.slot).lt_or_eq with hlt | heq
      · exact hpair.1 hlt
      · rw [hpair.2 heq]
        exact Gen.Pure.block_preceq_refl _
  · intro x hx t hd ht
    obtain ⟨ka, hka⟩ := pcsa_gate_tick_exists rho h.base x hx a (hd.trans (ht.trans h.cut.2))
    have hkl := (V2.D.Engine.index_lt_read_length_iff hs t hka).mpr hd
    obtain ⟨j, i, X, hjk, hj, hai, hX, hrec⟩ :=
      pcsa_restart_record_origin_index E rho h.base hF hS x hx ka hka _ hkl
    refine ⟨i, X, hai, (V2.D.Engine.index_lt_read_length_iff hs t hj).mp hjk, hX, ?_⟩
    rw [readLen]
    exact hrec
  · intro x hx t t' hd htt ht'
    obtain ⟨ka, hka⟩ := pcsa_gate_tick_exists rho h.base x hx a
      (hd.trans (htt.trans (ht'.trans h.cut.2)))
    rw [readLen, readLen]
    exact pcsa_restart_record_indices_mono E rho h.base hF hS x hx ka hka _ (horder x hx) _ _
      ((V2.D.Engine.index_lt_read_length_iff hs t hka).mpr hd)
      (V2.D.Engine.read_length_mono (rho := rho) t t' htt)
      (V2.D.Engine.read_length_mono (rho := rho) t' cut ht')
  · intro u hau hu x hx X hX
    have hst := pcsa_restart_state_from E rho h hF hFault hS u hau hu
    obtain ⟨k, hk, hraw⟩ := pcsa_gateResultAt_source E rho x u X hX
    obtain ⟨ka, hka⟩ := pcsa_gate_tick_exists rho h.base x hx a
      ((pcsa_gate_time_mono p hau).trans (hu.trans h.cut.2))
    have hak : ka ≤ k := by
      by_contra hn
      exact absurd (pcsa_gate_tick_label_lt rho h.base (Nat.lt_of_not_ge hn) hk hka)
        (not_lt.mpr hau)
    rw [pcsa_clock_confirmation_eq_pre] at hraw
    have hread := V2.D.Engine.stateBefore_tick_eq_stateBeforeTime hs h.base.noRestart hk
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs] at hread
    have hzk : V2.D.Run.idxBefore rho (SA.freezeTime p.toParams a) ≤
        V2.D.Run.idxBefore rho (SA.gateTime p.toParams u) := by
      rw [V2.D.Run.idxBefore_def, V2.D.Run.idxBefore_def, ← List.countP_eq_length_filter,
        ← List.countP_eq_length_filter]
      apply List.countP_mono_left
      intro e _ he
      apply decide_eq_true
      apply (of_decide_eq_true he).trans_le
      apply le_trans _ (pcsa_gate_time_mono p hau)
      change 4 * p.Δ * (a : Int) + 3 * p.Δ ≤ 4 * p.Δ * (a : Int) + 6 * p.Δ
      linarith
    have hguard : (clockPre p (V2.D.Run.stateBefore E rho k x).st
        (SA.gateTime p.toParams u)).base.obligations.any
        (fun row => (clockPre p (V2.D.Run.stateBefore E rho k x).st
          (SA.gateTime p.toParams u)).base.now < row.2.2 &&
            !Block.compatible row.1 X) = false := by
      apply List.any_eq_false.mpr
      intro row hrow
      have hr := pcsa_clockPre_locks_subset p _ _ hrow
      rw [hread] at hr
      have hb := pcsa_restart_lock_below_gate_result E rho h.base hS u hau hst
        ⟨x, hx, seedOf x hx ((pcsa_gate_time_mono p hau).trans hu)⟩ _ x x hx hx hzk le_rfl
        row hr X hX
      have hc : Block.compatible row.1 X = true := Bool.or_eq_true_iff.mpr (Or.inl hb)
      simp [hc]
    have hXS := pcsa_clock_gate_record_covers_result p (V2.D.Run.stateBefore E rho k x).st u X
      (hF x hx k).1 (pcsa_gate_input_unsaved E rho h.base.valid.nodup k x u hk) hraw hguard
    have hpost : (V2.D.Run.stateBefore E rho (k + 1) x).st =
        clock p (V2.D.Run.stateBefore E rho k x).st (SA.gateTime p.toParams u) := by
      rw [V2.D.Run.stateBefore_succ E rho hk, pcsa_tick_step]
    rw [← hpost] at hXS
    rw [readLen]
    apply Gen.Pure.block_preceq_trans hXS
    have hkl := (V2.D.Engine.index_lt_read_length_iff hs (SA.gateTime p.toParams u) hk).mpr
      le_rfl
    exact pcsa_restart_record_indices_mono E rho h.base hF hS x hx ka hka _ (horder x hx) _ _
      (Nat.lt_succ_of_le hak) hkl (V2.D.Engine.read_length_mono (rho := rho) _ cut hu)
  · intro u B hau hP hu x hx
    have hst := pcsa_restart_state_from E rho h hF hFault hS u hau hu
    obtain ⟨X, hX⟩ := pcsa_clean_result_exists_win E rho h hF x hx u hau hu
    have hBX : Block.Preceq B X := pcsa_clean_result_covers_heads_win E rho h hF x hx u B X
      hau hu (fun y H hH => by
        rw [hst.headsEqual u B y H hau le_rfl hP hH]
        exact Gen.Pure.block_preceq_refl _) hX
    obtain ⟨hxP, N, hN, he⟩ := pcsa_honest_proposal_named E rho u B hP
    have hBs : B.slot = u := hN ▸ pcsa_proposal_emitted_slot E rho _ u N _ he
    obtain ⟨i, _, hc⟩ := pcsa_gateResultAt_source E rho x u X hX
    have hord := pcsa_reachable_slot_order p _
      (Reachable.tick (SA.gateTime p.toParams u) (pcsa_reachable_stateBefore E rho i x))
    have hXs := pcsa_result_prefix_slot p _ _ X X u
      (fun D hD => hord D (List.mem_filter.mp hD).1) hc (Gen.Pure.block_preceq_refl _)
    have hXB : B = X := by
      change GridCO.confirmationFrom p.toParams.engine _ _ u = some X at hc
      rcases GridCO.confirmationFrom_mem _ _ _ _ _ hc with ha | hm
      · have hXg : X = .genesis := by
          rw [ha, pcsa_body_clock_fg, (hF x hx i).1]
          rfl
        rw [hXg] at hBX ⊢
        exact of_decide_eq_true hBX
      · exact pcsa_prefix_eq_of_slot_ge B X (hord X (List.mem_filter.mp hm).1) hBX (hBs ▸ hXs)
    rw [hX, hXB]
end AvailableChain.PCSA.Run

end

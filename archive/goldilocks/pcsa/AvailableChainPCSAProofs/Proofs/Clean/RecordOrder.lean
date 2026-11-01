module
public import AvailableChainPCSAProofs.Proofs.Clean.RecordBounds

public section

/-! C6 RecordOrder: concrete receipt and count support. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- Order at actual gate events makes each record update monotone. -/
theorem pcsa_record_step_mono_at_limit (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (limit : Nat) (x : V) (hx : x ∈ rho.honest)
    (horder : ∀ i i' X Y, i < i' → ∀ a,
      rho.events[a]? = some (.tick x (SA.gateTime p.toParams i')) → a < limit →
      gateResultAt p c E rho x i = some (some X) →
      gateResultAt p c E rho x i' = some (some Y) → Block.Preceq X Y)
    (k : Nat) (hk : k < limit) :
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
          rcases pcsa_record_stateBefore_origin E rho h hF k x hx with
            hz | ⟨a, ha, i, Y, hea, hY, hS⟩
          · rw [hz]
            exact Gen.Pure.block_genesis_preceq _
          · rw [hS]
            have his : i ≤ s := by
              by_contra hnot
              have hsi : (s : Int) < (i : Int) := Int.ofNat_lt.mpr (Nat.lt_of_not_ge hnot)
              have htime : SA.gateTime p.toParams s < SA.gateTime p.toParams i := by
                change 4 * p.Δ * (s : Int) + 6 * p.Δ < 4 * p.Δ * (i : Int) + 6 * p.Δ
                have hp := p.deltaPos
                nlinarith
              have hka := V2.D.Engine.eventIndex_lt_of_time_lt h.valid.toScheduleWellFormed
                hke hea htime
              omega
            rcases his.lt_or_eq with hlt | heq
            · exact horder i s Y X hlt k hke hk hY hread
            · subst i
              have heq : Y = X := Option.some.inj (Option.some.inj (hY.symm.trans hread))
              rw [heq]
              exact Gen.Pure.block_preceq_refl _
    · apply keep
      have hh := V2.D.World.step_apply_of_node_ne E rho (V2.D.Run.stateBefore E rho k) hn
      rw [hstep, hh]

/-- Ordered own results make each bounded record update monotone. -/
theorem pcsa_record_step_mono (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (j : Slot) (x : V) (hx : x ∈ rho.honest)
    (horder : ∀ i i' X Y, i < i' → i' ≤ j →
      gateResultAt p c E rho x i = some (some X) →
      gateResultAt p c E rho x i' = some (some Y) → Block.Preceq X Y)
    (k : Nat) (hk : k < V2.D.Run.idxBefore rho (SA.voteTime p.toParams (j + 1))) :
    Block.Preceq (V2.D.Run.stateBefore E rho k x).st.base.stableRecord
      (V2.D.Run.stateBefore E rho (k + 1) x).st.base.stableRecord := by
  apply pcsa_record_step_mono_at_limit E rho h hF
    (V2.D.Run.idxBefore rho (SA.voteTime p.toParams (j + 1))) x hx ?_ k hk
  intro i i' X Y hi a ha hb hX hY
  exact horder i i' X Y hi (pcsa_gate_label_before_vote p i' j
    ((Gen.V2.Duty.index_lt_idxBefore_iff h.valid.toScheduleWellFormed ha _).mp hb)) hX hY

/-- Ordered own results make bounded indexed record reads monotone. -/
theorem pcsa_record_indices_mono (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (j : Slot) (x : V) (hx : x ∈ rho.honest)
    (horder : ∀ i i' X Y, i < i' → i' ≤ j →
      gateResultAt p c E rho x i = some (some X) →
      gateResultAt p c E rho x i' = some (some Y) → Block.Preceq X Y)
    (a b : Nat) (hab : a ≤ b)
    (hb : b ≤ V2.D.Run.idxBefore rho (SA.voteTime p.toParams (j + 1))) :
    Block.Preceq (V2.D.Run.stateBefore E rho a x).st.base.stableRecord
      (V2.D.Run.stateBefore E rho b x).st.base.stableRecord := by
  induction b, hab using Nat.le_induction with
  | base => exact Gen.Pure.block_preceq_refl _
  | succ b _ ih =>
    exact Gen.Pure.block_preceq_trans (ih (Nat.le_trans (Nat.le_succ b) hb))
      (pcsa_record_step_mono E rho h hF j x hx horder b (Nat.lt_of_lt_of_le
        (Nat.lt_succ_self b) hb))
end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- Ordered own results make bounded inclusive record reads monotone. -/
theorem pcsa_record_storeAt_mono (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (j : Slot) (x : V) (hx : x ∈ rho.honest)
    (horder : ∀ i i' X Y, i < i' → i' ≤ j →
      gateResultAt p c E rho x i = some (some X) →
      gateResultAt p c E rho x i' = some (some Y) → Block.Preceq X Y)
    (t t' : Time) (htt : t ≤ t') (ht : t' < SA.voteTime p.toParams (j + 1)) :
    Block.Preceq (storeAt p c E rho x t).base.stableRecord
      (storeAt p c E rho x t').base.stableRecord := by
  rw [storeAt_def, storeAt_def,
    V2.D.Engine.readAt_eq_stateBefore h.valid.toScheduleWellFormed,
    V2.D.Engine.readAt_eq_stateBefore h.valid.toScheduleWellFormed]
  apply pcsa_record_indices_mono E rho h hF j x hx horder
  · exact V2.D.Engine.read_length_mono t t' htt
  · rw [V2.D.Run.idxBefore_def, ← List.countP_eq_length_filter,
      ← List.countP_eq_length_filter]
    exact List.countP_mono_left (fun e _ he =>
      decide_eq_true (lt_of_le_of_lt (of_decide_eq_true he) ht))
end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- Order at actual gate events makes all record reads before an indexed limit monotone. -/
theorem pcsa_record_indices_mono_at_limit (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (limit : Nat) (x : V) (hx : x ∈ rho.honest)
    (horder : ∀ i i' X Y, i < i' → ∀ k,
      rho.events[k]? = some (.tick x (SA.gateTime p.toParams i')) → k < limit →
      gateResultAt p c E rho x i = some (some X) →
      gateResultAt p c E rho x i' = some (some Y) → Block.Preceq X Y)
    (a b : Nat) (hab : a ≤ b) (hb : b ≤ limit) :
    Block.Preceq (V2.D.Run.stateBefore E rho a x).st.base.stableRecord
      (V2.D.Run.stateBefore E rho b x).st.base.stableRecord := by
  induction b, hab using Nat.le_induction with
  | base => exact Gen.Pure.block_preceq_refl _
  | succ b _ ih =>
    exact Gen.Pure.block_preceq_trans (ih (Nat.le_trans (Nat.le_succ b) hb))
      (pcsa_record_step_mono_at_limit E rho h hF limit x hx horder b
        (Nat.lt_of_lt_of_le (Nat.lt_succ_self b) hb))
end AvailableChain.PCSA.Run

end

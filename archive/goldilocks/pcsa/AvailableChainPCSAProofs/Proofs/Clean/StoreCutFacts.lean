module
public import AvailableChainPCSAProofs.Proofs.Clean.LockEvents
public import AvailableChainPCSAProofs.Proofs.Clean.GateAdvance
public import AvailableChainPCSAProofs.Proofs.Clean.CutReads
public import AvailableChainPCSAProofs.Proofs.Clean.RecordOrder
public import AvailableChainPCSAProofs.Proofs.Clean.GateBatch
public import AvailableChainPCSAProofs.Proofs.Clean.GenuineKeys
public import AvailableChainPCSAProofs.Proofs.Clean.LockOrigins

public section

/-! C6 StoreCutFacts: concrete receipt and count support. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- Every lock at an inclusive read is below an own result at an already completed gate. -/
theorem pcsa_lock_storeAt_timed_origin (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (x : V) (t : Time) (row : Block × Nat × Time)
    (hr : row ∈ (storeAt p c E rho x t).base.obligations) :
    ∃ (k : Nat) (i : Slot) (X : Block),
      rho.events[k]? = some (V2.Event.tick x (SA.gateTime p.toParams i)) ∧
      SA.gateTime p.toParams i ≤ t ∧ gateResultAt p c E rho x i = some (some X) ∧
        Block.Preceq row.1 X := by
  rw [storeAt_def, V2.D.Engine.readAt_eq_stateBefore h.valid.toScheduleWellFormed] at hr
  obtain ⟨k, hk, i, X, he, hX, hb, _⟩ := pcsa_lock_stateBefore_origin E rho h _ x row hr
  exact ⟨k, i, X, he,
    (V2.D.Engine.index_lt_read_length_iff h.valid.toScheduleWellFormed t he).mp hk, hX, hb⟩
/-- An own result chain below the gate result makes the lock guard clear at that exact
gate input. -/
theorem pcsa_gate_guard_of_chain (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (s : Slot) (k : Nat) (x : V)
    (hk : rho.events[k]? = some (.tick x (SA.gateTime p.toParams s)))
    (X : Block) (hchain : ∀ (i : Slot) (Y : Block), i < s →
      gateResultAt p c E rho x i = some (some Y) → Block.Preceq Y X) :
    (clockPre p (V2.D.Run.stateBefore E rho k x).st (SA.gateTime p.toParams s)).base.obligations.any
      (fun row => (clockPre p (V2.D.Run.stateBefore E rho k x).st
        (SA.gateTime p.toParams s)).base.now < row.2.2 && !Block.compatible row.1 X) = false := by
  rw [List.any_eq_false]
  intro row hr
  have hrow := pcsa_clockPre_locks_subset p (V2.D.Run.stateBefore E rho k x).st _ hr
  have hpre := V2.D.Engine.stateBefore_tick_eq_stateBeforeTime h.valid.toScheduleWellFormed
    h.noRestart hk
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ h.valid.toScheduleWellFormed] at hpre
  rw [hpre] at hrow
  obtain ⟨a, ha, i, Y, he, hY, hrowY, _⟩ := pcsa_lock_stateBefore_origin E rho h _ x row hrow
  have ht := (Gen.V2.Duty.index_lt_idxBefore_iff h.valid.toScheduleWellFormed he _).mp ha
  have hi : i < s := by
    apply Nat.lt_of_not_ge
    intro hn
    exact not_lt_of_ge (pcsa_gate_time_mono p hn) ht
  have hc : Block.compatible row.1 X = true := Bool.or_eq_true_iff.mpr
    (Or.inl (Gen.Pure.block_preceq_trans hrowY (hchain i Y hi hY)))
  rw [hc]
  simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, not_false_eq_true]
/-- A completed gate places its raw result below the actual post-event S when the earlier
own results are below it. -/
theorem pcsa_result_below_post_gate_of_chain (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) (hF : StageOneFrame p c E rho)
    (i : Slot) (x : V) (hx : x ∈ rho.honest) (k : Nat)
    (hk : rho.events[k]? = some (.tick x (SA.gateTime p.toParams i))) (X : Block)
    (hX : gateResultAt p c E rho x i = some (some X))
    (hchain : ∀ (i' : Slot) (Y : Block), i' < i →
      gateResultAt p c E rho x i' = some (some Y) → Block.Preceq Y X) :
    Block.Preceq X (V2.D.Run.stateBefore E rho (k + 1) x).st.base.stableRecord := by
  have hraw := Option.some.inj ((pcsa_gateResultAt_at_tick E rho h.valid.nodup k x i
    hk).symm.trans hX)
  rw [pcsa_clock_confirmation_eq_pre] at hraw
  have hs := pcsa_clock_gate_record_covers_result p (V2.D.Run.stateBefore E rho k x).st i X
    (hF x hx k).1 (pcsa_gate_input_unsaved E rho h.valid.nodup k x i hk) hraw
    (pcsa_gate_guard_of_chain E rho h i k x hk X hchain)
  have hpost : (V2.D.Run.stateBefore E rho (k + 1) x).st =
      clock p (V2.D.Run.stateBefore E rho k x).st (SA.gateTime p.toParams i) := by
    rw [V2.D.Run.stateBefore_succ E rho hk]
    change (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st = _
    rw [Function.update_self]
    exact pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k x) x _
  rwa [hpost]
/-- Every lock at an inclusive read through the cut is below the S of that read when the own
results through the cut form a chain. -/
theorem pcsa_lock_below_record_of_chain (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) (hF : StageOneFrame p c E rho)
    {cut : Time} (x : V) (hx : x ∈ rho.honest)
    (hchain : ∀ (i i' : Slot) (X Y : Block), i < i' → SA.gateTime p.toParams i' ≤ cut →
      gateResultAt p c E rho x i = some (some X) →
      gateResultAt p c E rho x i' = some (some Y) → Block.Preceq X Y)
    (t : Time) (ht : t ≤ cut)
    (row : Block × Nat × Time) (hr : row ∈ (storeAt p c E rho x t).base.obligations) :
    Block.Preceq row.1 (storeAt p c E rho x t).base.stableRecord := by
  obtain ⟨k, i, X, hk, hi, hX, hrowX⟩ := pcsa_lock_storeAt_timed_origin E rho h x t row hr
  have hXS := pcsa_result_below_post_gate_of_chain E rho h hF i x hx k hk X hX
    (fun i' Y hi' hY => hchain i' i Y X hi' (hi.trans ht) hY hX)
  have hkt : k + 1 ≤ (rho.events.filter (fun e : V2.Event V (Obj p) => decide (e.time ≤
    t))).length :=
    Nat.succ_le_of_lt ((V2.D.Engine.index_lt_read_length_iff h.valid.toScheduleWellFormed t
      hk).mpr hi)
  have hmono := pcsa_record_indices_mono_at_limit E rho h hF _ x hx
    (fun i i' X Y hii k hk hkl hX hY => hchain i i' X Y hii
      ((V2.D.Engine.index_lt_read_length_iff h.valid.toScheduleWellFormed cut hk).mp hkl) hX hY)
    (k + 1) _ hkt (V2.D.Engine.read_length_mono (rho := rho) t cut ht)
  rw [storeAt_def, V2.D.Engine.readAt_eq_stateBefore h.valid.toScheduleWellFormed]
  exact Gen.Pure.block_preceq_trans hrowX (Gen.Pure.block_preceq_trans hXS hmono)
end AvailableChain.PCSA.Run

end

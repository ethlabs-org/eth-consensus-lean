module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Premises
public import Mathlib.Tactic
@[expose] public section

/-! # The attestation clause of `Sync`: the two traces that refuted the old form

Before 2026-11-03 `SyncOn.attestation` asked that every attestation an honest node signs or
admits be processed by every honest node **not before the signing or admission** and strictly
before the deadline at `Δ_F`, with no order between `Δ` and `Δ_F` (`LowerBoundAttClause` writes
that clause out). Two run traces refute it. Each is meant as the node-level image of an engine
run under `PSync` (argued, not proved: the engine forwards an admitted attestation as the same
object, and one relayed together with a block in the block's relay wrapper, within `Δ`):

* **`T1`, an earlier receipt**: a faulty `z = 0` gets an attestation `a` to `y = 1` at `1` and
  to `x = 2` at `2`; `x` admits it at `2`. `y` already holds the object, so it processes nothing
  in `[2, 4)`, and at its call at `4 = 2 + Δ_F` the old clause fails. `Δ = Δ_F = 2`.
* **`T2`, an admission relayed with a block** (`Δ_F < Δ`): `x` admits `a` at `1`; `y` processes
  it at `3`, within `Δ = 3` but not strictly before `1 + Δ_F = 3`. `Δ_F = 2`.

In both traces every labelled cut is an `fg_on_attestation(a)` call of an honest node, the
honest set is `{1, 2}`, nobody signs, and there is no AC, block or restart cut. The current
clause (an earlier processing counts, and `Δ ≤ Δ_F`) holds on `T1`, excludes `T2` at
`Δ_F = 2` and holds on `T2` at `Δ_F = Δ = 3`. The positive check on an honest Goldilocks run,
with signings and admissions, is `tickRun_syncOn` (`ConsensusLeanTest/GoldilocksWitness`). -/

namespace Consensus.Goldilocks.Test.AttPremise

/-- Three validators, `Δ = d`, public times the multiples of `d`. -/
abbrev P (d : Nat) (hd : 0 < d) : Params where
  n := 3
  hn := by decide
  Δ := d
  hΔ := by exact_mod_cast hd
  slotTime s := 4 * d * s
  slotTime_zero := by simp
  slotTime_strictMono := fun a b h => by
    change (4 * d * a : Int) < 4 * d * b
    have : (0 : Int) < 4 * d := by positivity
    exact mul_lt_mul_of_pos_left (by exact_mod_cast h) this
  slotTime_public := fun s => ⟨4 * s, by ring⟩
  genesisRoot := 0
  δt := 2

/-- An AC with no state and no messages. -/
def acOf (d : Nat) (hd : 0 < d) : NodeAC (P d hd) where
  State := Unit
  Msg := Empty
  Payload := Unit
  validPayload _ := True
  validMsg _ := True
  holdsMsg _ _ := False
  genesisPayload := ()
  initial := ()
  onMessage _ s _ _ _ := (s, [])
  onBlock _ s _ _ _ := (s, [])
  onTick _ s _ _ := (s, [])
  proposal s _ _ := (s, none)
  toFG s _ _ := (s, none)
  confirmed _ Φ _ := Φ.F
  head _ Φ _ := Φ.fcRoot
  restart _ s _ _ := (s, [])

/-- The attestation of validator `0` (the faulty one). -/
def att (d : Nat) (hd : 0 < d) : FG.Att (P d hd).n := ⟨0, 1, 0, false, none⟩

/-- The node state with `a` in its pool. -/
def holding (d : Nat) (hd : 0 < d) : NodeState (acOf d hd) :=
  { Node.init (acOf d hd) with fg := { (Node.init (acOf d hd)).fg with atts := [att d hd] } }

/-- The trace: cuts `0, 1, 2` are `fg_on_attestation(a)` calls of the nodes `ns` at the times
`ts`, each leaving `a` in the pool; later cuts stutter at node `0`, at times after `ts 2`. -/
noncomputable def trace (d : Nat) (hd : 0 < d) (ns : Nat → Fin 3) (ts : Nat → Time) :
    RunTrace (acOf d hd) where
  init _ := Node.init (acOf d hd)
  node i := if i < 3 then ns i else 0
  time i := if i < 3 then ts i else i + 2
  event i := i
  pos _ := 0
  label i := if i < 3 then some (.fg (.attestation (att d hd))) else none
  post _ := holding d hd
  awake _ _ := True

/-- The honest validators. -/
def H : Set (Fin 3) := {1, 2}

/-- The earlier-receipt trace (`Δ = 2`): `y = 1` at `1`, `x = 2` at `2`, `y` at `4`. -/
noncomputable def T1 : RunTrace (acOf 2 (by decide)) :=
  trace 2 (by decide) (fun i => if i = 1 then 2 else 1)
    (fun i => if i = 0 then 1 else if i = 1 then 2 else 4)

/-- The relayed-with-a-block trace (`Δ = 3`): `x = 2` at `1`, `y = 1` at `3` and at `4`. -/
noncomputable def T2 : RunTrace (acOf 3 (by decide)) :=
  trace 3 (by decide) (fun i => if i = 0 then 2 else 1)
    (fun i => if i = 0 then 1 else if i = 1 then 3 else 4)

/-- The attestation clause of `GSTRun H ΔF 0` before 2026-11-03: processing not before the
signing or admission, strictly before the deadline at `Δ_F`. -/
def LowerBoundAttClause {d : Nat} {hd : 0 < d} (T : RunTrace (acOf d hd)) (ΔF : Time) : Prop :=
  ∀ x ∈ H, ∀ i a, T.SendOrAdmitAttAt x i a → ∀ y ∈ H, ∀ j, T.IsCall y j →
    T.deadline y j (max (T.time i) 0) ΔF ≤ T.time j →
      ∃ k ≤ j, T.time i ≤ T.time k ∧ T.ProcessAttAt y k a ∧
        T.time k < T.deadline y k (max (T.time i) 0) ΔF

variable {d : Nat} {hd : 0 < d} {ns : Nat → Fin 3} {ts : Nat → Time}

theorem callAt_iff {y : Fin 3} {i : Nat} {c : Cut (acOf d hd)} :
    (trace d hd ns ts).CallAt y i c ↔ i < 3 ∧ ns i = y ∧ c = .fg (.attestation (att d hd)) := by
  unfold Trace.CallAt
  constructor
  · rintro ⟨hn, hl⟩
    by_cases h : i < 3
    · simp only [trace, h, ↓reduceIte] at hn hl
      exact ⟨h, hn, (Option.some.inj hl).symm⟩
    · simp only [trace, h, ↓reduceIte] at hl
      exact absurd hl (by simp)
  · rintro ⟨h, hn, rfl⟩
    simp only [trace, h, ↓reduceIte]
    exact ⟨hn, trivial⟩

/-- No restart: the deadline is `τ + Δ'`. -/
theorem deadline_eq (y : Fin 3) (k : Nat) (τ Δ' : Time) :
    (trace d hd ns ts).deadline y k τ Δ' = τ + Δ' := by
  have : ∀ k, (trace d hd ns ts).lastWake y k = ⊥ := by
    intro k
    induction k with
    | zero =>
      simp only [RunTrace.lastWake, ite_eq_right_iff]
      rintro ⟨ℓ, hc, -⟩
      exact absurd (callAt_iff.1 hc).2.2 (by simp)
    | succ k ih =>
      simp only [RunTrace.lastWake, ih, ite_eq_right_iff]
      rintro ⟨ℓ, hc, -⟩
      exact absurd (callAt_iff.1 hc).2.2 (by simp)
  simp only [RunTrace.deadline, this]
  rfl

/-- The only processing is the `fg_on_attestation(a)` calls. -/
theorem processAttAt_iff {y : Fin 3} {k : Nat} {a : FG.Att 3} :
    (trace d hd ns ts).ProcessAttAt y k a ↔ k < 3 ∧ ns k = y ∧ a = att d hd := by
  constructor
  · rintro (h | ⟨B, h, -⟩)
    · obtain ⟨hk, hn, hc⟩ := callAt_iff.1 h
      simp only [Cut.fg.injEq, FGLabel.attestation.injEq] at hc
      exact ⟨hk, hn, hc⟩
    · exact absurd (callAt_iff.1 h).2.2 (by simp)
  · rintro ⟨hk, hn, rfl⟩
    exact Or.inl (callAt_iff.2 ⟨hk, hn, rfl⟩)

theorem time_lt {i : Nat} (hi : i < 3) : (trace d hd ns ts).time i = ts i := by
  simp [trace, hi]

/-- Nothing is sent, accepted or signed: every label is an attestation call. -/
theorem no_ac {x : Fin 3} {i : Nat} {ℓ} : ¬ (trace d hd ns ts).CallAt x i (.ac ℓ) :=
  fun h => by simpa using (callAt_iff.1 h).2.2

theorem no_block {x : Fin 3} {i : Nat} {B acc} :
    ¬ (trace d hd ns ts).CallAt x i (.fg (.block B acc)) :=
  fun h => by simpa using (callAt_iff.1 h).2.2

theorem no_sign {x : Fin 3} {i : Nat} {a} : ¬ (trace d hd ns ts).SignAt x i a :=
  fun ⟨_, h⟩ => by simpa using (callAt_iff.1 h).2.2

/-- **On `T1` the lower-bound clause fails**: `x` admits `a` at `2`; at `y`'s call at `4`
there is no processing in `[2, 4)`. -/
theorem earlierReceipt_lowerBound_fails : ¬ LowerBoundAttClause T1 2 := by
  intro h
  have hadm : T1.SendOrAdmitAttAt 2 1 (att 2 (by decide)) := by
    refine Or.inr ⟨_, callAt_iff.2 ⟨by decide, rfl, rfl⟩, ?_, by simp [T1, trace, holding]⟩
    simp [T1, trace, Trace.state, Node.init, Store.init]
  obtain ⟨k, hk, hlo, hp, hlt⟩ := h 2 (by simp [H]) 1 _ hadm 1 (by simp [H]) 2
    ⟨_, callAt_iff.2 ⟨by decide, rfl, rfl⟩⟩ (by simp [T1, deadline_eq, time_lt])
  obtain ⟨hk3, hn, -⟩ := processAttAt_iff.1 hp
  simp only [T1, deadline_eq, time_lt hk3, time_lt (show 1 < 3 by decide)] at hlo hlt
  interval_cases k <;> simp_all

/-- **On `T2` the lower-bound clause fails**: `x` admits `a` at `1`; `y`'s first processing
is at `3 = 1 + Δ_F`, not strictly before it. -/
theorem bundledAdmission_lowerBound_fails : ¬ LowerBoundAttClause T2 2 := by
  intro h
  have hadm : T2.SendOrAdmitAttAt 2 0 (att 3 (by decide)) := by
    refine Or.inr ⟨_, callAt_iff.2 ⟨by decide, rfl, rfl⟩, ?_, by simp [T2, trace, holding]⟩
    simp [T2, trace, Trace.state, Node.init, Store.init]
  obtain ⟨k, hk, hlo, hp, hlt⟩ := h 2 (by simp [H]) 0 _ hadm 1 (by simp [H]) 1
    ⟨_, callAt_iff.2 ⟨by decide, rfl, rfl⟩⟩ (by simp [T2, deadline_eq, time_lt])
  obtain ⟨hk3, hn, -⟩ := processAttAt_iff.1 hp
  simp only [T2, deadline_eq, time_lt hk3, time_lt (show 0 < 3 by decide)] at hlo hlt
  interval_cases k <;> simp_all

/-- The message, block and relay clauses of `SyncOn` hold on every such trace (nothing is sent,
proposed or accepted). -/
theorem syncOn_of_attestation {W Wr : Time → Prop} {eff : Time → Time} {ΔF : Time}
    (hΔF : 0 < ΔF) (hle : (P d hd).Δ ≤ ΔF)
    (hatt : ∀ x ∈ H, ∀ i a, (trace d hd ns ts).SendOrAdmitAttAt x i a →
      W ((trace d hd ns ts).time i) → ∀ y ∈ H, ∀ j, (trace d hd ns ts).IsCall y j →
        (trace d hd ns ts).deadline y j (eff ((trace d hd ns ts).time i)) ΔF ≤
          (trace d hd ns ts).time j →
        (trace d hd ns ts).AttDeliveredBy y j (eff ((trace d hd ns ts).time i)) ΔF a) :
    (trace d hd ns ts).SyncOn H ΔF W Wr eff where
  deltaF := hΔF
  delta_le := hle
  message x _ i m h := by
    obtain ⟨ℓ, hc, -⟩ := h
    exact absurd hc no_ac
  block x _ i B h := by
    rcases h with h | ⟨⟨_, h⟩, -⟩ <;> exact absurd h no_block
  relay x _ i B h := absurd h no_block
  attestation := hatt

/-- An admission in such a trace is of `a`, at a cut `i < 3`. -/
theorem admit_spec {x : Fin 3} {i : Nat} {a : FG.Att 3}
    (h : (trace d hd ns ts).SendOrAdmitAttAt x i a) : i < 3 ∧ a = att d hd := by
  rcases h with h | ⟨ℓ, hc, -, hin⟩
  · exact absurd h no_sign
  · refine ⟨(callAt_iff.1 hc).1, ?_⟩
    simpa [trace, holding] using hin

/-- The clause holds when each honest node's first call `f y` processes `a` before every
call of it, at a time earlier than every cut time plus `Δ_F`. -/
theorem att_clause {ΔF : Time} (f : Fin 3 → Nat)
    (hf : ∀ y ∈ H, f y < 3 ∧ ns (f y) = y ∧ ∀ j, j < 3 → ns j = y → f y ≤ j)
    (htime : ∀ y ∈ H, ∀ i < 3, ts (f y) < ts i + ΔF) (hpos : ∀ i < 3, 0 ≤ ts i)
    {x : Fin 3} {i : Nat} {a : FG.Att 3} (h : (trace d hd ns ts).SendOrAdmitAttAt x i a)
    {y : Fin 3} (hy : y ∈ H) {j : Nat} (hj : (trace d hd ns ts).IsCall y j) :
    (trace d hd ns ts).AttDeliveredBy y j (max ((trace d hd ns ts).time i) 0) ΔF a := by
  obtain ⟨hi, rfl⟩ := admit_spec h
  obtain ⟨c, hc⟩ := hj
  obtain ⟨hj3, hjy, -⟩ := callAt_iff.1 hc
  obtain ⟨hf3, hfy, hmin⟩ := hf y hy
  refine ⟨f y, hmin j hj3 hjy, processAttAt_iff.2 ⟨hf3, hfy, rfl⟩, ?_⟩
  rw [deadline_eq, time_lt hf3, time_lt hi, max_eq_left (hpos i hi)]
  exact htime y hy i hi

/-- **`T1` no longer refutes `GST(0)`**: `y`'s processing at `1` counts for `x`'s admission
at `2`. -/
theorem earlierReceipt_gstRun : T1.GSTRun H 2 0 :=
  syncOn_of_attestation (by decide) le_rfl fun _ _ _ _ h _ _ hy _ hj _ =>
    att_clause (fun y => if y = 2 then 1 else 0)
      (by intro y hy; simp only [H, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with rfl | rfl <;> refine ⟨by decide, by decide, fun j hj hn => ?_⟩ <;>
            interval_cases j <;> simp_all)
      (by intro y hy i hi; simp only [H, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with rfl | rfl <;> interval_cases i <;> decide)
      (by intro i hi; interval_cases i <;> decide) h hy hj

/-- **`T2` is excluded at `Δ_F = 2 < Δ = 3`**: `GST(0)` now carries `Δ ≤ Δ_F`. -/
theorem bundledAdmission_not_gstRun : ¬ T2.GSTRun H 2 0 := fun h => absurd h.delta_le (by decide)

/-- **`T2` satisfies `GST(0)` at `Δ_F = Δ = 3`.** -/
theorem bundledAdmission_gstRun_at_delta : T2.GSTRun H 3 0 :=
  syncOn_of_attestation (by decide) le_rfl fun _ _ _ _ h _ _ hy _ hj _ =>
    att_clause (fun y => if y = 2 then 0 else 1)
      (by intro y hy; simp only [H, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with rfl | rfl <;> refine ⟨by decide, by decide, fun j hj hn => ?_⟩ <;>
            interval_cases j <;> simp_all)
      (by intro y hy i hi; simp only [H, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with rfl | rfl <;> interval_cases i <;> decide)
      (by intro i hi; interval_cases i <;> decide) h hy hj

end Consensus.Goldilocks.Test.AttPremise

end

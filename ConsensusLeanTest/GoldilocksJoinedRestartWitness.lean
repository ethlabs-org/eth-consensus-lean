module
public import ConsensusLeanTest.GoldilocksAC
@[expose] public section

/-! # Witnesses for F.1 (c) `JoinedAwake` and A0.7 `JoinedKeepsVotes` over a restart

Both statements quantify over the restarts of a node that is joined after a call. The existing
runs do not meet that quantifier with content: the tick run and the asleep run have no restart,
and in `GoldilocksRestartWitness` the restart is the node's first cut, so the pools it erases are
empty (A0.7's conclusion is vacuous there). Here the node holds a vote when it restarts.

On `GoldilocksAC`'s parameters (one validator `v0`, `Δ = 1`, `t_s = 4s`, `k = c = 2`, the genesis
frame `Φ₀` inside `{genesis}`), the AC trace `trJR` (each post-state the call's literal output):

| cut | time | call | effect |
|---|---|---|---|
| 0 | `4 = t_1` | `ac_on_message(m1)` | admits the vote `m1 = (v0, 1, genesis)`; no own vote |
| 1 | `10` | `ac_restart` | after a sleep on `(6, 10)`: erases the pool, `restart_time = 10` |
| 2 | `19` | `ac_on_tick` | slot `4`, joined (`10 ≤ t_3 = 12`); nothing due |

`v0` is awake on `[0, 6]` and from `10` on. Labelled by kind (CONTRIBUTING "Statements"):

* (a) `localRun_JR`: `trJR` satisfies the AC trace contract `ACLocalRun`.
* (a) `joinedAwake_witness`: at the joined tick (cut `2`) the node has been awake on
  `[t_3, 19] = [12, 19]`, and its restart (cut `1`, time `10`) is at or before `t_3`.
* (a) `joinedKeepsVotes_witness`: the restart erased the slot-`1` vote `m1`, and
  `1 < slot(19) − 1 = 3`.
* (r) `joined_premise_needed`: at the restart cut itself (time `10`, not joined:
  `10 > t_1 = 4`) both conclusions fail: `v0` was asleep at `8 ∈ [4, 10]`, the restart is after
  `t_1`, and the erased vote's slot `1` is not below `slot(10) − 1 = 1`.
* `joinedAwake_applies`, `joinedKeepsVotes_applies`: each statement, assumed, applies to `trJR` at
  the joined tick with these premises. -/

namespace Consensus.Goldilocks.SA.Test.JoinedRestart

open Consensus.Goldilocks.SA.Test

theorem slot_4 : sp1.slot 4 = 1 := by decide
theorem slot_10 : sp1.slot 10 = 2 := by decide
theorem slot_19 : sp1.slot 19 = 4 := by decide

/-- The slot-`1` vote of `v0` on genesis. -/
def m1 : Vote sp1.n := ⟨v0, 1, 0⟩

/-- Cut `0`: `ac_on_message(m1)` at `4` from the initial state. -/
noncomputable def c0 : SAState sp1.n × List (Em sp1 Unit) :=
  (GA1).step v0 (GA1).initial Φ₀ 4 (.message m1)

/-- Cut `1`: `ac_restart` at `10`. -/
noncomputable def c1 : SAState sp1.n × List (Em sp1 Unit) := (GA1).step v0 c0.1 Φ₀ 10 .restart

/-- Cut `2`: `ac_on_tick` at `19`. -/
noncomputable def c2 : SAState sp1.n × List (Em sp1 Unit) := (GA1).step v0 c1.1 Φ₀ 19 .tick

noncomputable def ℓ0 : ACLabel GA1 := ⟨.message m1, Φ₀, c0.2⟩
noncomputable def ℓ1 : ACLabel GA1 := ⟨.restart, Φ₀, c1.2⟩
noncomputable def ℓ2 : ACLabel GA1 := ⟨.tick, Φ₀, c2.2⟩

/-- The restart trace: one validator, awake on `[0, 6]` and from `10` on. -/
noncomputable def trJR : SATrace sp1 Unit ro1 where
  init := fun _ => SAState.initial 0
  node := fun _ => v0
  time := fun i => if i = 0 then 4 else if i = 1 then 10 else 19
  event := fun i => i
  pos := fun _ => 0
  label := fun i => match i with
    | 0 => some ℓ0
    | 1 => some ℓ1
    | 2 => some ℓ2
    | _ => none
  post := fun i => match i with
    | 0 => c0.1
    | 1 => c1.1
    | _ => c2.1
  awake := fun _ u => u ≤ 6 ∨ 10 ≤ u

theorem trJR_label {i : Nat} {ℓ : ACLabel GA1} (h : trJR.label i = some ℓ) :
    (i = 0 ∧ ℓ = ℓ0) ∨ (i = 1 ∧ ℓ = ℓ1) ∨ (i = 2 ∧ ℓ = ℓ2) := by
  rcases i with _ | _ | _ | i <;> simp [trJR] at h <;> simp [h]

theorem trJR_callAt {y : Fin sp1.n} {i : Nat} {ℓ : ACLabel GA1} (h : trJR.label i = some ℓ) :
    trJR.CallAt y i ℓ :=
  ⟨Subsingleton.elim _ _, h⟩

theorem trJR_time_mono : Monotone trJR.time := by
  intro a b h
  simp only [trJR]
  split_ifs <;> first | omega | decide

theorem trJR_state_succ (y : Fin sp1.n) {i : Nat} (hi : i ≤ 2) :
    trJR.state y (i + 1) = trJR.post i := by
  simp only [Trace.state]
  rw [ite_eq_left ⟨Subsingleton.elim _ _, by
    rcases i with _ | _ | _ | i <;> first | omega | simp [trJR]⟩]

theorem trJR_restartAt {y : Fin sp1.n} {j : Nat} (h : trJR.RestartAt y j) : j = 1 := by
  obtain ⟨ℓ, ⟨-, hl⟩, hc⟩ := h
  rcases trJR_label hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · cases hc
  · rfl
  · cases hc

theorem restartAt_1 : trJR.RestartAt v0 1 := ⟨ℓ1, trJR_callAt rfl, rfl⟩

/-! ## The states -/

/-- Before `t_1 + Δ` and with no slot-`1` proposal in the genesis frame, `try_vote` waits. -/
theorem tryVote_4 (A : SAState sp1.n) : tryVote sp1 v0 A Φ₀ 4 = (A, []) := by
  have hr : ¬ voteReady sp1 Φ₀ 1 := by
    rintro ⟨B, hB, hs, -⟩
    rw [Set.mem_singleton_iff.mp hB] at hs
    simp [g] at hs
  unfold tryVote
  dsimp only
  rw [slot_4]
  split_ifs with h1 h2
  all_goals first | rfl | exact absurd ⟨by decide, Or.inr hr⟩ h2

/-- The optimistic confirmation writes only the locks and the record. -/
theorem optimisticConfirmation_eq (A : SAState sp1.n) (Ψ : Frm sp1.n Unit) (t : Time) :
    ∃ L r, optimisticConfirmation sp1 A Ψ t = { A with locks := L, latestConfirmed := r } := by
  unfold optimisticConfirmation
  split
  · exact ⟨A.locks, A.latestConfirmed, rfl⟩
  · unfold updateLatestConfirmed
    split_ifs
    · exact ⟨_, A.latestConfirmed, rfl⟩
    · exact ⟨_, _, rfl⟩

/-- After cut `0`, the pools hold exactly `m1`, in the slot-`1` pool. -/
theorem c0_pool (σ : Nat) : c0.1.pool σ = if σ = 1 then [m1] else [] := by
  change (acOnMessage sp1 v0 (SAState.initial 0) Φ₀ 4 m1).1.pool σ = _
  unfold acOnMessage
  rw [tryVote_4]
  obtain ⟨L, r, h⟩ := optimisticConfirmation_eq (admitVote sp1 (SAState.initial 0) 4 m1) Φ₀ 4
  rw [h]
  change (admitVote sp1 (SAState.initial 0) 4 m1).pool σ = _
  unfold admitVote
  rw [ite_eq_right (by rw [slot_4]; simp [m1, SAState.initial]),
    ite_eq_right (by simp [SAState.initial])]
  change Function.update (fun _ => []) 1 ([] ++ [m1]) σ = _
  by_cases hσ : σ = 1
  · rw [hσ, Function.update_self]; rfl
  · rw [Function.update_of_ne hσ, ite_eq_right hσ]

/-- The restart at `10` replays nothing: the genesis frame has no other block. -/
theorem order_Φ₀ : ro1.order 10 Φ₀ = [] := by
  have hpo := ro1.parentOrder 10 Φ₀ ⟨[], List.nodup_nil, fun B => by
    simp only [List.not_mem_nil, false_iff, not_and, not_not]
    intro hB; rw [Set.mem_singleton_iff.mp hB]; rfl, fun i _ hi => absurd hi (Nat.not_lt_zero i)⟩
  refine List.eq_nil_iff_forall_not_mem.2 fun B hB => ?_
  obtain ⟨hB', hr⟩ := (hpo.2.1 B).1 hB
  rw [Set.mem_singleton_iff.mp hB'] at hr
  exact hr rfl

/-- After the restart, `restart_time = 10`. -/
theorem c1_restartTime : c1.1.restartTime = ((10 : Time) : WithBot Time) := by
  change (acRestart sp1 ro1 v0 c0.1 Φ₀ 10).1.restartTime = _
  unfold acRestart
  rw [order_Φ₀]
  rfl

/-- At `19` (slot `4`), the restarted node is joined: `10 ≤ t_3 = 12`. -/
theorem joined_c1_19 : joined sp1 c1.1 19 := by
  rw [joined, c1_restartTime, slot_19]
  exact WithBot.coe_le_coe.2 (by decide)

/-- The tick at `19` (neither `t_4 + Δ` nor `t_4 + 2Δ`) changes nothing. -/
theorem c2_eq : c2 = (c1.1, []) := by
  change acOnTick sp1 v0 c1.1 Φ₀ 19 = _
  unfold acOnTick
  dsimp only
  rw [slot_19, ite_eq_right (not_not.2 joined_c1_19),
    ite_eq_right (show ¬ ((19 : Time) = sp1.ts ((4 : Nat) : Int) + sp1.Δ) by decide),
    ite_eq_right (show ¬ ((19 : Time) = sp1.ts ((4 : Nat) : Int) + 2 * sp1.Δ ∧ 0 < 4) by decide)]

/-! ## The trace contract -/

/-- `{genesis}` with the genesis frame: the frame law's `FrameIn`. -/
theorem frameIn_Φ₀ : (GA1).FrameIn ({g} : Set (Blk sp1.n Unit)) Φ₀ := ⟨frameOK_Φ₀, le_rfl⟩

/-- (a) The restart trace satisfies the AC trace contract for the honest set `{v0}` inside
`{genesis}`. -/
theorem localRun_JR : ACLocalRun GA1 Set.univ ({g} : Set (Blk sp1.n Unit)) trJR where
  coherent := coherent_g
  init := fun _ _ => rfl
  exec := fun i ℓ h _ => by
    rcases trJR_label h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    all_goals rw [trJR_state_succ _ (by decide)]; rfl
  frameLaw := fun y _ i ℓ h => by
    rcases trJR_label h.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨fun k _ hk => absurd hk (Nat.not_lt_zero k), Φ₀, ⟨rfl, rfl, rfl, rfl, rfl⟩,
        frameIn_Φ₀, frameIn_Φ₀, rfl, trivial⟩
    · exact Or.inr ⟨0, ℓ0, by decide, trJR_callAt rfl, fun k hk hk' => absurd hk' (by omega),
        frameIn_Φ₀, rfl⟩
    · exact Or.inr ⟨1, ℓ1, by decide, trJR_callAt rfl, fun k hk hk' => absurd hk' (by omega),
        frameIn_Φ₀, rfl⟩
  time_nonneg := fun i => by simp only [trJR]; split_ifs <;> decide
  time_mono := trJR_time_mono
  awake_of_call := fun y _ i ℓ h => by
    rcases trJR_label h.2 with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Or.inl (by decide)
    · exact Or.inr (by decide)
    · exact Or.inr (by decide)
  restart_of_sleep := fun y _ i ℓ u h hu0 hut hu hprev => by
    change ¬ (u ≤ 6 ∨ 10 ≤ u) at hu
    obtain ⟨h6, h10⟩ := not_or.1 hu
    rcases trJR_label h.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · change u < (4 : Time) at hut
      exact absurd (le_of_lt (lt_trans hut (by decide))) h6
    · rfl
    · have := hprev 1 (by decide) ℓ1 (trJR_callAt rfl)
      change (10 : Time) < u at this
      exact absurd (le_of_lt this) h10
  restart_at_wake := fun y _ u v hu0 huv hu hv => by
    change ¬ (u ≤ 6 ∨ 10 ≤ u) at hu
    change v ≤ 6 ∨ 10 ≤ v at hv
    obtain ⟨h6, h10⟩ := not_or.1 hu
    refine ⟨1, ⟨ℓ1, trJR_callAt rfl, rfl⟩, ?_, ?_⟩
    · change u < (10 : Time); exact lt_of_not_ge h10
    · change (10 : Time) ≤ v
      rcases hv with hv | hv
      · exact absurd (le_of_lt (lt_of_lt_of_le huv hv)) h6
      · exact hv
  sleep_of_restart := fun y _ i ℓ h hr => by
    rcases trJR_label h.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hr
    · refine ⟨8, by decide, by decide, by simp [trJR], fun j hj ℓ' hj' => ?_⟩
      obtain rfl : j = 0 := by omega
      decide
    · cases hr

/-! ## F.1 (c) `JoinedAwake` -/

/-- (a) **`JoinedAwake` witness.** After the tick at `19` the node is joined; it has been awake on
`[max 0 t_3, 19] = [12, 19]`, and its restart (cut `1`, time `10`) is at or before `t_3 = 12`. -/
theorem joinedAwake_witness :
    ACLocalRun GA1 Set.univ ({g} : Set (Blk sp1.n Unit)) trJR ∧ trJR.CallAt v0 2 ℓ2 ∧
    joined sp1 (trJR.post 2) (trJR.time 2) ∧ trJR.RestartAt v0 1 ∧
    (∀ u : Time, max 0 (sp1.ts ((sp1.slot (trJR.time 2) : Int) - 1)) ≤ u → u ≤ trJR.time 2 →
      trJR.awake v0 u) ∧
    ∀ j ≤ 2, trJR.RestartAt v0 j → trJR.time j ≤ sp1.ts ((sp1.slot (trJR.time 2) : Int) - 1) := by
  have ht : trJR.time 2 = 19 := rfl
  have hp : trJR.post 2 = c1.1 := by change c2.1 = c1.1; rw [c2_eq]
  refine ⟨localRun_JR, trJR_callAt rfl, by rw [hp, ht]; exact joined_c1_19, restartAt_1,
    fun u hu _ => Or.inr ?_, fun j _ hj => ?_⟩
  · rw [ht, slot_19, show sp1.ts (((4 : Nat) : Int) - 1) = 12 by decide] at hu
    exact le_trans (by decide) (le_of_max_le_right hu)
  · rw [trJR_restartAt hj, ht, slot_19]
    decide

/-! ## A0.7 `JoinedKeepsVotes` -/

/-- The state before the restart holds the slot-`1` vote `m1`, and only it. -/
theorem state_1_pool (σ : Nat) : (trJR.state v0 1).pool σ = if σ = 1 then [m1] else [] := by
  rw [trJR_state_succ v0 (by decide)]
  exact c0_pool σ

/-- (a) **`JoinedKeepsVotes` witness.** The restart (cut `1`) erased the vote `m1` of slot `1`, and
at the joined tick at `19`, `1 < slot(19) − 1 = 3`. -/
theorem joinedKeepsVotes_witness :
    trJR.CallAt v0 2 ℓ2 ∧ joined sp1 (trJR.post 2) (trJR.time 2) ∧ trJR.RestartAt v0 1 ∧
    m1 ∈ (trJR.state v0 1).pool 1 ∧
    ∀ j ≤ 2, trJR.RestartAt v0 j → ∀ σ, ∀ x ∈ (trJR.state v0 j : SAState sp1.n).pool σ,
      (x.slot : Int) < (sp1.slot (trJR.time 2) : Int) - 1 := by
  refine ⟨joinedAwake_witness.2.1, joinedAwake_witness.2.2.1, restartAt_1,
    by rw [state_1_pool]; exact List.mem_singleton.2 rfl, fun j _ hj σ x hx => ?_⟩
  rw [trJR_restartAt hj, state_1_pool] at hx
  split_ifs at hx
  · rw [List.mem_singleton.1 hx, show trJR.time 2 = 19 from rfl, slot_19]
    decide
  · cases hx

/-! ## Rejection: the joined premise -/

/-- (r) **The joined premise is needed.** At the restart cut itself (time `10`), the node is not
joined (`10 > t_1 = 4`), and both conclusions fail there: `v0` was asleep at `8 ∈ [4, 10]`, its
restart at `10` is after `t_1`, and the erased vote's slot `1` is not below `slot(10) − 1 = 1`. -/
theorem joined_premise_needed :
    trJR.CallAt v0 1 ℓ1 ∧ ¬ joined sp1 (trJR.post 1) (trJR.time 1) ∧
    ¬ (∀ u : Time, max 0 (sp1.ts ((sp1.slot (trJR.time 1) : Int) - 1)) ≤ u → u ≤ trJR.time 1 →
      trJR.awake v0 u) ∧
    ¬ (trJR.time 1 ≤ sp1.ts ((sp1.slot (trJR.time 1) : Int) - 1)) ∧
    ¬ (∀ σ, ∀ x ∈ (trJR.state v0 1 : SAState sp1.n).pool σ,
      (x.slot : Int) < (sp1.slot (trJR.time 1) : Int) - 1) := by
  have ht : trJR.time 1 = 10 := rfl
  refine ⟨trJR_callAt rfl, ?_, fun h => ?_, by rw [ht, slot_10]; decide, fun h => ?_⟩
  · change ¬ joined sp1 c1.1 10
    rw [joined, c1_restartTime, slot_10]
    exact fun h => absurd (WithBot.coe_le_coe.1 h) (by decide)
  · have := h 8 (by rw [ht, slot_10]; decide) (by rw [ht]; decide)
    simp [trJR] at this
  · have := h 1 m1 (by rw [state_1_pool]; exact List.mem_singleton.2 rfl)
    rw [ht, slot_10] at this
    exact absurd this (by decide)

/-! ## The statements reach the witnesses -/

theorem joinedAwake_applies (h : JoinedAwake sp1) :
    (∀ u : Time, max 0 (sp1.ts ((sp1.slot (trJR.time 2) : Int) - 1)) ≤ u → u ≤ trJR.time 2 →
      trJR.awake v0 u) ∧
    ∀ j ≤ 2, trJR.RestartAt v0 j → trJR.time j ≤ sp1.ts ((sp1.slot (trJR.time 2) : Int) - 1) :=
  h Unit ro1 Set.univ {g} trJR localRun_JR v0 trivial 2 ℓ2 (trJR_callAt rfl)
    joinedAwake_witness.2.2.1

theorem joinedKeepsVotes_applies (h : JoinedKeepsVotes sp1) :
    ∀ j ≤ 2, trJR.RestartAt v0 j → ∀ σ, ∀ x ∈ (trJR.state v0 j : SAState sp1.n).pool σ,
      (x.slot : Int) < (sp1.slot (trJR.time 2) : Int) - 1 :=
  h Unit ro1 Set.univ {g} trJR localRun_JR v0 trivial 2 ℓ2 (trJR_callAt rfl)
    joinedAwake_witness.2.2.1

end Consensus.Goldilocks.SA.Test.JoinedRestart

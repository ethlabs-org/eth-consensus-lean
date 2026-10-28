module
public import ConsensusShapeTests.Controls

@[expose] public section
namespace Consensus.Shape.Tests.Iteration3
open Model Run

/-- A single awake honest source suffices; the other honest nodes need not
receive any local submission. -/
def oneSource : EnvPoint Bool :=
  ⟨⟨3, by decide, 4, fun _ _ => true⟩, Finset.univ, 20,
    fun v t => if v = true ∧ t = 0 then [42] else []⟩

theorem oneSource_submitted : oneSource.SubmittedToSome 42 0 :=
  ⟨true, Finset.mem_univ _, 0, le_rfl, le_rfl, rfl, by simp [oneSource]⟩

theorem other_node_no_submission (t : Time) : oneSource.submit false t = [] := by
  simp [oneSource]

def sleepingSource : EnvPoint Bool :=
  { oneSource with env := ⟨3, by decide, 4, fun _ _ => false⟩ }

theorem sleeping_source_not_submitted : ¬ sleepingSource.SubmittedToSome 42 0 := by
  rintro ⟨v, _, τ, _, _, haw, _⟩
  cases haw

/-- Only finalized-to-stable nesting is broken. Stable-to-confirmed alone
would miss this counterexample, including at the initial cut. -/
def badNesting : Trace Bool Tx :=
  ⟨oneSource, 0, fun _ => 0, fun g _ _ => if g = .finalized then [42] else []⟩

theorem stable_confirmed_nested : badNesting.Nested .stable .confirmed := by
  intro v hv i hi
  exact List.prefix_refl _

theorem finalized_stable_not_nested : ¬ badNesting.Nested .finalized .stable := by
  intro h
  have := h true (Finset.mem_univ _) 0 (Nat.zero_le _)
  change [42] <+: [] at this
  simp at this

/-- Ingress can inject an unsubmitted transaction. The cumulative inbox
survives restarts and is available to the next clock. -/
def relayedRun :=
  Model.mkRun (F := compiled (family true false false)) (E := env)
    Finset.univ 5 seat (fun _ _ => [])
    (fun _ t => if t = 2 then [42] else []) goodHash [.restart 0 3]

theorem injected_held : relayedRun.TxHeld 0 42 3 := by
  exact ⟨2, by decide, by decide, by simp [relayedRun, Model.mkRun, Model.Run.inbox]⟩

theorem held_strict_deadline : ¬ relayedRun.TxHeld 0 42 2 := by
  rintro ⟨τ, hτ, hτd, hx⟩
  have hne : τ ≠ 2 := ne_of_lt hτd
  simp [relayedRun, Model.mkRun, Model.Run.inbox, hne] at hx

theorem relayed_mempool_after_restart : 42 ∈ Model.mempool relayedRun.inbox 0 5 := by
  apply txHeld_mem_mempool relayedRun
  exact ⟨2, by decide, by decide,
    by simp [relayedRun, Model.mkRun, Model.Run.inbox]⟩

theorem injected_not_submitted : ¬ relayedRun.point.SubmittedToSome 42 5 := by
  rintro ⟨v, _, τ, _, _, _, hx⟩
  cases hx

/-- With Δ = 3, zero catch-up would permit a proposer whose awake
history is too short for the delivery interval. -/
def shortHistory : EnvPoint Bool :=
  ⟨⟨3, by decide, 0, fun _ t => decide (5 ≤ t)⟩, Finset.univ, 6,
    fun _ _ => []⟩

theorem shortHistory_ready : shortHistory.Ready 0 true 6 := by
  refine ⟨Finset.mem_univ _, ?_⟩
  intro t ht _
  change decide (5 ≤ t) = true
  apply decide_eq_true
  simpa using ht

theorem shortHistory_not_awake_delta : ¬ AwakeOn shortHistory.env true (6 - 3) 6 := by
  intro h
  have := h 3 (by decide) (by decide)
  cases this

/-- Ready proposers now always have at least one Δ of catch-up. -/
theorem zero_catchUp_invalid (C : Constants) (hz : C.catchUp = 0) : ¬ C.Valid := by
  intro h
  have := h.catchUp_pos
  omega

end Consensus.Shape.Tests.Iteration3
end

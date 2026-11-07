module
public import ConsensusLean.Spec.Problem.CorrectProtocol
public import ConsensusLean.Lemmas.Problem.DerivedFacts
public import ConsensusLean.Lemmas.Problem.Facts.Atoms
public import ConsensusLean.Lemmas.Problem.Facts.Transfer
public import ConsensusLean.Lemmas.Problem.Facts.Network
public import ConsensusLean.Lemmas.Problem.Facts.Properties
public import ConsensusLean.Lemmas.Problem.Facts.Regimes
public import ConsensusLean.Lemmas.Problem.Facts.CorrectProtocol
public import ConsensusLean.Lemmas.Problem.Constant
@[expose] public section

/-! # L0 tests: properties have teeth

Small traces that violate each property, the `InCuts` fix at cut 0, the
transaction-relay vocabulary, nesting across three outputs, catch-up, and
local accountability: evidence that exists somewhere in the run is not enough. -/

namespace Consensus.Shape.Tests.Problem

def point : EnvPoint Bool :=
  ⟨⟨1, by decide, 1, by decide, fun _ _ => true⟩, fun _ => ∅, monotone_const, 2,
    fun _ t => if t = 0 then [42] else []⟩

def incompatible : Trace Bool Nat Unit :=
  ⟨point, 2, fun i => (i : Int), fun _ v _ => if v then [1] else [2]⟩

def rollback : Trace Bool Nat Unit :=
  ⟨point, 2, fun i => (i : Int), fun _ _ i => if i = 1 then [1] else []⟩

def omitted : Trace Bool Tx Unit :=
  ⟨point, 2, fun i => (i : Int), fun _ _ _ => []⟩

theorem incompatible_laws : incompatible.Laws := by
  constructor
  · rfl
  · intro i j hij _; change (i : Int) ≤ j; exact_mod_cast hij
  · intro i hi; change (i : Int) ≤ 2; change i ≤ 2 at hi; exact_mod_cast hi

theorem rollback_laws : rollback.Laws :=
  ⟨incompatible_laws.1, incompatible_laws.2, incompatible_laws.3⟩

theorem omitted_laws : omitted.Laws :=
  ⟨incompatible_laws.1, incompatible_laws.2, incompatible_laws.3⟩

theorem incompatible_not_agree : ¬ incompatible.Agree () 0 := by
  intro h
  have hc := h true false 1 1
    (by unfold Trace.InCuts incompatible; decide)
    (by unfold Trace.InCuts incompatible; decide)
    (by simp [EnvPoint.HonestAt, incompatible, point])
    (by simp [EnvPoint.HonestAt, incompatible, point])
  change Compatible [1] [2] at hc
  simp [Compatible] at hc

theorem rollback_not_monotone : ¬ rollback.Monotone () 0 := by
  intro h
  have hp := h true 1 2 (by unfold Trace.InCuts rollback; decide) (by decide)
    (by unfold Trace.InCuts rollback; decide)
    (by simp [EnvPoint.HonestAt, rollback, point])
    (by simp [EnvPoint.HonestAt, rollback, point])
  change [1] <+: [] at hp
  simp at hp

theorem omitted_not_txLive : ¬ omitted.TxLive 0 () 0 1 := by
  intro h
  have hs : point.SubmittedToSome 42 0 := by
    exact ⟨true, 0, le_rfl, le_rfl, by simp [EnvPoint.HonestAt, point],
      rfl, by simp [point]⟩
  have hr : point.Ready 0 true 2 := by
    exact ⟨by simp [EnvPoint.HonestAt, point], fun _ _ _ => rfl⟩
  have hx := h 42 0 2 hs (by decide) (by decide) true hr
  change 42 ∈ [] at hx
  cases hx

/-! ## The `InCuts` fix: cut 0 counts from time 0 -/

/-- On a lawful trace, the initial cut is in the cuts from time 0. -/
theorem inCuts_zero {V α Id : Type} (tr : Trace V α Id) (h : tr.Laws) : tr.InCuts 0 0 :=
  ⟨Nat.zero_le _, h.cutTime_zero.symm.le⟩

/-- A trace whose read at cut 0 is `[1]` and at cut 1 is `[]`. -/
def initRollback : Trace Bool Nat Unit :=
  ⟨point, 2, fun i => (i : Int), fun _ _ i => if i = 0 then [1] else []⟩

/-- A rollback from the initial cut violates monotonicity from time 0 (the
cut-0 fix: before it, cut 0 was not in `InCuts 0`). -/
theorem init_rollback_not_monotone : ¬ initRollback.Monotone () 0 := by
  intro h
  have hp := h true 0 1 (by unfold Trace.InCuts initRollback; decide)
    (by decide) (by unfold Trace.InCuts initRollback; decide)
    (by simp [EnvPoint.HonestAt, initRollback, point])
    (by simp [EnvPoint.HonestAt, initRollback, point])
  change [1] <+: [] at hp
  simp at hp

/-! ## Transaction relay: one awake honest source -/

/-- A single awake honest source suffices; the other honest nodes need not
receive any local submission. -/
def oneSource : EnvPoint Bool :=
  ⟨⟨3, by decide, 3, by decide, fun _ _ => true⟩, fun _ => ∅, monotone_const, 20,
    fun v t => if v = true ∧ t = 0 then [42] else []⟩

theorem oneSource_submitted : oneSource.SubmittedToSome 42 0 :=
  ⟨true, 0, le_rfl, le_rfl, by simp [EnvPoint.HonestAt, oneSource],
    rfl, by simp [oneSource]⟩

theorem other_node_no_submission (t : Time) : oneSource.submit false t = [] := by
  simp [oneSource]

def sleepingSource : EnvPoint Bool :=
  { oneSource with env := ⟨3, by decide, 3, by decide, fun _ _ => false⟩ }

theorem sleeping_source_not_submitted : ¬ sleepingSource.SubmittedToSome 42 0 := by
  rintro ⟨v, τ, _, _, _, haw, _⟩
  cases haw

/-! ## Nesting across three outputs -/

/-- Three output identifiers (confirmed, stable, finalized). -/
inductive G3 where
  | c
  | s
  | f
  deriving DecidableEq

/-- Only finalized-to-stable nesting is broken. Stable-to-confirmed alone
would miss this counterexample, including at the initial cut. -/
def badNesting : Trace Bool Tx G3 :=
  ⟨oneSource, 0, fun _ => 0, fun g _ _ => if g = .f then [42] else []⟩

theorem stable_confirmed_nested : badNesting.Nested .s .c := by
  intro v i hi hv
  exact List.prefix_refl _

theorem finalized_stable_not_nested : ¬ badNesting.Nested .f .s := by
  intro h
  have := h true 0 (Nat.zero_le _) (by simp [EnvPoint.HonestAt, badNesting, oneSource])
  change [42] <+: [] at this
  simp at this

/-! ## Catch-up -/

/-- With Δ = 3, zero catch-up would permit a reader whose awake history is
shorter than one `Δ`. -/
def shortHistory : EnvPoint Bool :=
  ⟨⟨3, by decide, 3, by decide, fun _ t => decide (5 ≤ t)⟩, fun _ => ∅,
    monotone_const, 6, fun _ _ => []⟩

theorem shortHistory_ready : shortHistory.Ready 0 true 6 := by
  refine ⟨by simp [EnvPoint.HonestAt, shortHistory], ?_⟩
  intro t ht _
  change decide (5 ≤ t) = true
  apply decide_eq_true
  simpa using ht

/-- Awake throughout the half-open interval `[a, b)` (moved from L0: only this
test uses it). -/
def AwakeOn {V : Type} (E : Env V) (v : V) (a b : Time) : Prop :=
  ∀ u, a ≤ u → u < b → E.awake v u = true

theorem shortHistory_not_awake_delta : ¬ AwakeOn shortHistory.env true (6 - 3) 6 := by
  intro h
  have := h 3 (by decide) (by decide)
  cases this

/-! ## Local accountability has teeth -/

/-- One output; a single-run system on three validators (validator 2 faulty)
whose honest readers conflict at cut 0, where nothing is seen yet; by the end
of the run the honest evidence convicts validator 2. -/
def localGlobal : System (Fin 3) where
  schema := ⟨Unit, fun _ => some ()⟩
  Run := Unit
  trace _ := ⟨⟨⟨1, by decide, 1, by decide, fun _ _ => true⟩,
    fun _ => {2}, monotone_const, 0, fun _ _ => []⟩, 1,
    fun _ => 0, fun _ v _ => if v = 0 then [1] else [2]⟩
  Valid _ := True
  Obs := Unit
  log _ := ⟨fun _ _ _ => False, fun _ _ _ => False, fun _ _ => [], fun _ => False⟩
  view _ _ i := if i = 0 then ∅ else Set.univ
  convicts _ A x := () ∈ A ∧ x = 2
  Excuse _ := False

/-- The whole honest evidence of the run convicts one third (validator 2),
honest validators are not framed, yet local accountability for one third
fails: the conflicting reads at cut 0 carry no evidence of their own. So
accountability is local: global slashability would not satisfy it. -/
theorem local_accountability_teeth :
    (Fintype.card (Fin 3) : ℚ) * (1 / 3) ≤
        (Consensus.convicted (localGlobal.convicts ()) (localGlobal.honestEvidenceBy () 0)).card ∧
      localGlobal.NonFraming () ∧
      ¬ localGlobal.AccountablySafe () (1 / 3) () 0 := by
  classical
  have hfull :
      Consensus.convicted (localGlobal.convicts ()) (localGlobal.honestEvidenceBy () 0) = {2} := by
    ext x
    simp only [Consensus.convicted, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_singleton]
    refine ⟨fun h => h.2, fun h => ⟨⟨0, 1, by decide, le_rfl,
      by simp [EnvPoint.HonestAt, localGlobal], ?_⟩, h⟩⟩
    exact Set.mem_univ (α := Unit) ()
  have hempty : Consensus.convicted (localGlobal.convicts ())
      (localGlobal.view () 0 0 ∪ localGlobal.view () 1 0) = ∅ := by
    ext x
    simp only [Consensus.convicted, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.notMem_empty, iff_false]
    rintro ⟨h | h, _⟩ <;> exact absurd h (Set.notMem_empty _)
  refine ⟨?_, ?_, ?_⟩
  · rw [hfull]
    simp
  · intro v d hv hc
    have hv2 : v = 2 := hc.2
    subst hv2
    exact hv (Finset.mem_singleton_self _)
  · intro h
    rcases h 0 1 0 0 ⟨Nat.zero_le _, le_rfl⟩ ⟨Nat.zero_le _, le_rfl⟩
      (by simp [EnvPoint.HonestAt, localGlobal])
      (by simp [EnvPoint.HonestAt, localGlobal]) with hc | hc
    · change Compatible [1] [2] at hc
      simp [Compatible] at hc
    · change (Fintype.card (Fin 3) : ℚ) * (1 / 3) ≤
        (Consensus.convicted (localGlobal.convicts ())
          (localGlobal.view () 0 0 ∪ localGlobal.view () 1 0)).card at hc
      rw [hempty] at hc
      norm_num at hc

end Consensus.Shape.Tests.Problem
end

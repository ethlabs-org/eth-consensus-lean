module
public import ConsensusLean.Instances.Goldilocks.Refinement.Defs
public import ConsensusLean.Spec.Shape.Accepted
public import ConsensusLean.Lemmas.Problem.Facts.Regimes
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Transport

public section

/-! # Acceptance assembly with finite guarantee witnesses

The assumptions are fixed before choosing guarantees. The three named coefficient
holes and five direct adapter holes are joint obligations, not independent arbitrary
choices. They do not prove acceptance. Do not import into Main/Solution.
The local pattern is a fixed function of Setup's timeout; no legacy consecutive-run
formula or dependence of timeout on the outer gap is imposed here.
-/

namespace Consensus.Goldilocks.Refinement

open Blocks Shape

/-- Four-anchor window for the one-delivery-bound model, cF=2 and δt≥4.
First-descendant row service, inherited progress and cache joins remain OPEN. -/
def finalWindow (S : Setup) : Pattern :=
  ⟨[0, S.δt - 1, S.δt + 1, S.δt + 3], by simp⟩

/-- Fixed timeout and outage assumptions. The pattern is determined by Setup,
not chosen by a caller; outer gaps never enter the timeout bound. -/
structure AcceptanceAssumptions (S : Setup) where
  timeout : 4 ≤ S.δt
  lookback : ℕ+

/-- Only guarantees are chosen: positive finite catch-up and finite heal/latency
coefficients at every capability and outer gap. -/
structure AcceptanceCoefficients where
  catchUp : ℕ+
  heal : Capability → ℕ+ → Nat
  latency : Capability → ℕ+ → Nat

/-- OPEN numeric witness, chosen jointly with the adapter proofs below. -/
noncomputable def accepted_catchUp (S : Setup) (A : AcceptanceAssumptions S) : ℕ+ := by
  sorry

/-- OPEN finite healing witness; no whole-run progress premise may be added. -/
noncomputable def accepted_heal (S : Setup) (A : AcceptanceAssumptions S) :
    Capability → ℕ+ → Nat := by
  sorry

/-- OPEN finite latency witness, at every outer gap, independent of timeout. -/
noncomputable def accepted_latency (S : Setup) (A : AcceptanceAssumptions S) :
    Capability → ℕ+ → Nat := by
  sorry

/-- The same three witnesses are used by every adapter. -/
noncomputable def accepted_coefficients (S : Setup) (A : AcceptanceAssumptions S) :
    AcceptanceCoefficients :=
  ⟨accepted_catchUp S A, accepted_heal S A, accepted_latency S A⟩

/-- Standard fixed resilience fractions; only guarantee coefficients vary.
Final progress is the chosen local pattern at every positive outer gap.
An abbreviation exposes the index type for the adapter signatures. -/
abbrev acceptanceContract {S : Setup} (A : AcceptanceAssumptions S)
    (C : AcceptanceCoefficients) : Contract ProgressReq where
  Idx := ℕ+
  idx_nonempty := ⟨1⟩
  params := { Params.standard C.catchUp (4 * S.k - 4)
    (min A.lookback (4 * S.k - 5)) C.heal C.latency with η := A.lookback }
  progress := fun cap X => .recur ⟨if cap = .final then finalWindow S else Pattern.single, X⟩

theorem acceptanceContract_params_eq {S : Setup} (A : AcceptanceAssumptions S)
    (C : AcceptanceCoefficients) :
    (acceptanceContract A C).params =
      { Params.standard C.catchUp (4 * S.k - 4)
        (min A.lookback (4 * S.k - 5)) C.heal C.latency with η := A.lookback } := by rfl

theorem accepted_coefficients_catchUp (S : Setup) (A : AcceptanceAssumptions S) :
    (accepted_coefficients S A).catchUp = accepted_catchUp S A := by rfl

noncomputable abbrev K (S : Setup) (A : AcceptanceAssumptions S) :=
  acceptanceContract A (accepted_coefficients S A)

variable (S : Setup) (A : AcceptanceAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- R8, claims C0.1/C0.2/F.2, node outputs_valid. NO PAPER PROOF for
engine/read transport; replacement endpoint: engine_outputValid. -/
theorem accepted_outputValid : (Sys (family S) V).HoldsAlways fun r =>
    ∀ c g, schema.output c = some g → OutputValid r.2 g := by
  exact shape_outputValid V S

/-- R8, claims C0.1/C0.2/F.2, node outputs_nested. NO PAPER PROOF for
engine chain transport; replacement endpoint: engine_nested. -/
theorem accepted_nested : ∀ c₁ c₂ g₁ g₂, c₁.rank < c₂.rank →
    schema.output c₁ = some g₁ → schema.output c₂ = some g₂ →
    (Sys (family S) V).HoldsAlways fun r => (chainTrace r.2).Nested g₁ g₂ := by
  exact shape_nested V S

/-- R8, claims F.2, node finalized_monotone. NO PAPER PROOF for engine
read transport; replacement endpoint: engine_finalMonotone. -/
theorem accepted_finalMonotone : ∀ g, schema.output .final = some g →
    (Sys (family S) V).HoldsAlways fun r => (chainTrace r.2).Monotone g 0 := by
  exact shape_finalMonotone V S

/-- R7, claims G0.5 and G1.1–G1.5, node final_accountable.
NO PAPER PROOF for held-tree evidence/view and collision transport. Raw
GenesisFresh is not a premise here: the encoding must discharge root separation. -/
theorem accepted_finalAccountable : ∀ g, schema.output .final = some g →
    (Sys (family S) V).Holds (fun _ => True) fun r =>
      (chainTrace r.2).AccountablySafe r.2.ViewIdx r.2.Slashable
        (K S A).params.α g 0 := by
  exact shape_finalAccountable V S (K S A) (by norm_num [Params.standard])

/-- R3 available/stable inclusion; R4 FinalInclude for final.
NO PAPER PROOF for exact contract gHeal, bounded recurrence→node progress,
or repaired engine timing transport. See generic-r3-bridge-audit.md.
This field must not acquire whole-run progress before ready as a premise. -/
theorem accepted_healthyLive : ∀ cap g, schema.output cap = some g →
    ∀ (i : (K S A).Idx) (gst : Time), (Sys (family S) V).Holds
      (fun r => (Sys (family S) V).Healthy (K S A) gst r ∧
        (Sys (family S) V).prog (shapeProgress (family S) V) (K S A) cap i
          ((Sys (family S) V).ready (K S A) gst r)
          ((Sys (family S) V).pt r).horizon r)
      fun r => ProposalLiveReady r.2 ((Sys (family S) V).cDur (K S A) r)
        g ((Sys (family S) V).heal (K S A) cap i gst r) ((K S A).params.latency cap i) := by
  sorry

/-- R1, sleepy-record-invariant.md §§2–5.1 and sleepy-proposal-adoption.md
§§2–4 (conditional S1–S4 package). NO PAPER PROOF for engine network,
readiness and read-cut transport. Node route: sleepy_invariant and ready reads. -/
theorem accepted_sleepySafe : ∀ cap g, (cap = .available ∨ cap = .stable) →
    schema.output cap = some g → (Sys (family S) V).Holds
      ((Sys (family S) V).Sleepy (K S A)) fun r =>
        (chainTrace r.2).ReadySafe ((Sys (family S) V).cDur (K S A) r) g 0 := by
  sorry

/-- R2 inclusion/growth, node sleepy_statements. NO PAPER PROOF yet pinned
for the exact recurrence/readiness/deadline transport; keep this gap explicit. -/
theorem accepted_sleepyLive : ∀ cap g, (cap = .available ∨ cap = .stable) →
    schema.output cap = some g → ∀ i : (K S A).Idx,
      (Sys (family S) V).Holds
        (fun r => (Sys (family S) V).Sleepy (K S A) r ∧
          (Sys (family S) V).prog (shapeProgress (family S) V) (K S A) cap i
            0 ((Sys (family S) V).pt r).horizon r)
        fun r => ProposalLiveReady r.2 ((Sys (family S) V).cDur (K S A) r)
          g 0 ((K S A).params.latency cap i) := by
  sorry

/-- R3 healed safety. NO PAPER PROOF for bounded [ready,heal] recurrence
to current whole-run HealedPremises or the target gHeal bound. RecRet also
has no completed proof (rc-recret-induction.md §6). -/
theorem accepted_healedSafe : ∀ cap g, (cap = .available ∨ cap = .stable) →
    schema.output cap = some g → ∀ (i : (K S A).Idx) (gst : Time),
      (Sys (family S) V).Holds
        (fun r => (Sys (family S) V).Healthy (K S A) gst r ∧
          (Sys (family S) V).prog (shapeProgress (family S) V) (K S A) cap i
            ((Sys (family S) V).ready (K S A) gst r)
            ((Sys (family S) V).heal (K S A) cap i gst r) r)
        fun r => (chainTrace r.2).ReadySafe ((Sys (family S) V).cDur (K S A) r)
          g ((Sys (family S) V).heal (K S A) cap i gst r) := by
  sorry

/-- R5 OC1–OC4: NO PAPER PROOF for composed-node outage continuation.
Blocked by lifetime (4k−1 versus 4k−2) and finite pre-outage network scope:
SyncUntil b₀ does not give unrestricted late-wake SyncRun calls. Do not
insert that false implication as an intermediate lemma. -/
theorem accepted_persists : ∀ g, schema.output .stable = some g → ∀ T b₀ b₁,
    (Sys (family S) V).Holds ((Sys (family S) V).Outage (K S A) T b₀ b₁)
      fun r => (chainTrace r.2).ProtectedThrough
        ((Sys (family S) V).cDur (K S A) r) g (resilienceTarget schema g) T b₀ b₁ := by
  sorry

/-- Exact nine-field assembly; the named gaps above are not a blanket claims assumption. -/
theorem accepted_claims : ShapeClaims (family S) (K S A) := by
  intro V _ _
  exact {
    outputValid := accepted_outputValid S V
    nested := accepted_nested S V
    finalMonotone := accepted_finalMonotone S V
    finalAccountable := accepted_finalAccountable S A V
    healthyLive := accepted_healthyLive S A V
    sleepySafe := accepted_sleepySafe S A V
    sleepyLive := accepted_sleepyLive S A V
    healedSafe := accepted_healedSafe S A V
    persists := accepted_persists S A V }

/-- Selection-aware singleton duties make every recurrence fit. -/
theorem accepted_progressFits : ProgressFits (K S A) (family S) := by
  intro cap i pub s
  rfl

/-- At an outer gap beyond the local span there is room for a bad slot. -/
theorem accepted_progressTolerant : ProgressTolerant schema (K S A) := by
  intro cap _ N
  let P := if cap = .final then finalWindow S else Pattern.single
  exact ⟨⟨P.span + 2, by omega⟩, Nat.le_refl _⟩

/-- Fixed thresholds and positive finite catch-up/budget are admissible. -/
theorem accepted_admissible : (K S A).params.Admissible := by
  rw [acceptanceContract_params_eq]
  exact {
    catchUp_pos := (accepted_coefficients S A).catchUp.pos
    θ_range := by norm_num [Params.standard]
    β_range := by norm_num [Params.standard]
    cover_range := by norm_num [Params.standard]
    α_range := by norm_num [Params.standard]
    budget_pos := by have := A.lookback.pos; have := S.two_le_k; dsimp [Params.standard]; omega }

/-- Concrete existential endpoint. Every gap is a named numeric or adapter
leaf; no simulation, GenesisFresh, or desired safety premise is added. -/
theorem accepted : ∃ C : AcceptanceCoefficients,
    Accepted (family S) (acceptanceContract A C) := by
  refine ⟨accepted_coefficients S A, ?_⟩
  exact {
    claims := accepted_claims S A
    admissible := accepted_admissible S A
    serves := by simp [OutputSchema.Serves, schema]
    progressFits := accepted_progressFits S A
    progressTolerant := accepted_progressTolerant S A }

end Consensus.Goldilocks.Refinement

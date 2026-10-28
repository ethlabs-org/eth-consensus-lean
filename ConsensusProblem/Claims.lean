module
public import ConsensusProblem.Atoms

@[expose] public section

/-! # Contracts and claims (layer 0)

A protocol advertises a `Contract`: for each capability it provides, a
specification (`CapSpec`) made of premises in the closed premise language and
Δ-coefficients. `ProblemClaims S X K` is the headline statement: the system
`S`, with execution atoms interpreted by `X`, meets every claim of contract
`K`. Its meaning depends only on this layer: what a protocol must prove is
fixed here, for every protocol.

Claims hold on valid runs whose premise holds, unless the run's excuse holds
(an observed hash collision in the execution model). Safety and the safety
half of recovery may also be escaped by global slashability of a fraction `α`
when the contract says so; liveness is never escaped. Local accountability
is unconditional: two conflicting honest reads convict `α` from their own
evidence. -/

namespace Consensus

namespace System

variable {V : Type} [Fintype V] [DecidableEq V]

/-- On valid runs satisfying `A`, `P` holds or the excuse holds. -/
def Holds (S : System V) (A P : S.Run → Prop) : Prop :=
  ∀ r, S.Valid r → A r → P r ∨ S.Excuse r

/-- On valid runs, `P` holds. -/
def HoldsAlways (S : System V) (P : S.Run → Prop) : Prop :=
  ∀ r, S.Valid r → P r

/-- The escaped form: on valid runs satisfying `A`, `P` holds, or the excuse
holds, or (if the escape is `some α`) the run is globally slashable for `α`. -/
def HoldsEsc (S : System V) (esc : Option ℚ) (A P : S.Run → Prop) : Prop :=
  ∀ r, S.Valid r → A r → P r ∨ S.Excuse r ∨ ∃ α, esc = some α ∧ S.GloballySlashable α r

/-- The duration `k · Δ` in run `r`. -/
def dur (S : System V) (r : S.Run) (k : Nat) : Time := ((k : Nat) : Time) * (S.trace r).point.env.Δ

end System

/-- A safety specification: its premise and an optional global-slashing
escape fraction. -/
structure SafetySpec (Prog : Type) where
  premise : Premise Prog
  escape : Option ℚ := none

/-- A liveness specification, indexed by `Idx`: premise, start time and
latency (a Δ-coefficient). -/
structure LiveSpec (Prog Idx : Type) where
  premise : Idx → Premise Prog
  start : Idx → TimeExpr
  latency : Idx → Nat

/-- A recovery specification, indexed by `Idx`: premise, recovery point (from
which ready readers are safe and transactions live), latency, and an optional
escape on the safety half only. -/
structure RecoverySpec (Prog Idx : Type) where
  premise : Idx → Premise Prog
  start : Idx → TimeExpr
  latency : Idx → Nat
  escape : Option ℚ := none

/-- What a protocol claims for one capability: safety, liveness, optionally
local accountability (unconditional, collision excuse only), resilience
(premise over parameters `σ 0 = T`, `σ 1 = b₀`, `σ 2 = b₁`) and recovery. -/
structure CapSpec (Prog Idx : Type) where
  safety : SafetySpec Prog
  live : LiveSpec Prog Idx
  accountable : Option ℚ := none
  resilience : Option (Premise Prog) := none
  recovery : Option (RecoverySpec Prog Idx) := none

/-- What a protocol advertises: an index type for liveness and recovery
specs (nonempty), one catch-up coefficient shared by every claim (the
readers' eligibility), and a specification per provided capability. -/
structure Contract (O : OutputSchema) (Prog : Type) where
  Idx : Type
  idx_nonempty : Nonempty Idx
  catchUp : Nat
  spec : Capability → Option (CapSpec Prog Idx)

/-- Mandatory parts: a stable capability has a resilience premise and a
recovery spec. -/
def CapSpec.Complete {Prog Idx : Type} (c : Capability) (s : CapSpec Prog Idx) : Prop :=
  c = .stable → s.resilience.isSome ∧ s.recovery.isSome

/-- An optional fraction is absent or in `(0, 1]`. -/
def FracWF (e : Option ℚ) : Prop := ∀ α, e = some α → 0 < α ∧ α ≤ 1

/-- Structural well-formedness of a capability spec: every premise is
well-formed (which also excludes horizon and parameter caps), every start is
horizon-free, every escape and accountable fraction is in `(0, 1]`. -/
structure CapSpec.WellFormed {Prog Idx : Type} (s : CapSpec Prog Idx) : Prop where
  safety : s.safety.premise.WellFormed
  safetyEscape : FracWF s.safety.escape
  live : ∀ i, (s.live.premise i).WellFormed
  accountable : FracWF s.accountable
  resilience : ∀ P, s.resilience = some P → P.WellFormed
  recovery : ∀ R, s.recovery = some R → (∀ i, (R.premise i).WellFormed) ∧ FracWF R.escape
  /-- Liveness starts do not depend on the horizon (a start at the horizon
  would make liveness vacuous). -/
  liveStart : ∀ i, (s.live.start i).HorizonFree
  /-- Recovery points do not depend on the horizon. -/
  recoveryStart : ∀ R, s.recovery = some R → ∀ i, (R.start i).HorizonFree

/-- Structural well-formedness of a contract (fraction ranges, no horizon or
parameter caps, horizon-free starts). This is not a non-vacuity certificate: a
well-formed contract may still have unsatisfiable premises. -/
structure Contract.WellFormed {O : OutputSchema} {Prog : Type} (K : Contract O Prog) : Prop where
  caps : ∀ c s, K.spec c = some s → s.WellFormed

/-- The output resilience is measured against: the available output if
provided, else the same output. -/
def resilienceTarget (O : OutputSchema) (g : O.Id) : O.Id := (O.output .available).getD g

/-- Schema package: a final output is provided. -/
def OutputSchema.BFTCore (O : OutputSchema) : Prop := (O.output .final).isSome

/-- Schema package: an available output and no final output. -/
def OutputSchema.DACore (O : OutputSchema) : Prop :=
  (O.output .available).isSome ∧ O.output .final = none

/-- The schema serves a ledger: it is a `BFTCore` (a final output, possibly
with others) or a `DACore` (an available output without a final one). A schema
that provides neither (no output at all, or only a stable one) is not a
consensus service; acceptance (`Shape.Accepted`) requires this. -/
def OutputSchema.Serves (O : OutputSchema) : Prop := O.BFTCore ∨ O.DACore

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The claims for one provided capability served by output `g`. -/
structure CapClaims {Prog : Type} (S : System V) (X : ExecProfile S Prog)
    (K : Contract S.schema Prog) (g : S.schema.Id) (s : CapSpec Prog K.Idx) : Prop where
  /-- Safety from time 0 (or escape). -/
  safe : ∀ σ, S.HoldsEsc s.safety.escape (fun r => s.safety.premise.eval S X K.catchUp σ r)
    (fun r => (S.trace r).Safe g 0)
  /-- Transaction liveness for ready readers. -/
  live : ∀ i σ, S.Holds (fun r => (s.live.premise i).eval S X K.catchUp σ r)
    (fun r => (S.trace r).TxLive (S.dur r K.catchUp) g
      ((s.live.start i).eval (S.trace r).point σ) (S.dur r (s.live.latency i)))
  /-- Local accountability: conflicting honest reads convict `α` from their
  own evidence. -/
  accountable : ∀ α, s.accountable = some α →
    S.Holds (fun _ => True) (fun r => S.AccountablySafe r α g 0)
  /-- Resilience: parameters `σ 0 = T` (protectedAt), `σ 1 = b₀`
  (outageStart); the premise may also use `σ 2 = b₁` (outageEnd). -/
  persists : ∀ P, s.resilience = some P → ∀ σ,
    S.Holds (fun r => P.eval S X K.catchUp σ r)
      (fun r => (S.trace r).ProtectedThrough (S.dur r K.catchUp) g
        (resilienceTarget S.schema g) (σ 0) (σ 1) (σ 2))
  /-- Recovery, safety half: ready readers are safe from the recovery point
  (or escape). -/
  recoverySafe : ∀ R, s.recovery = some R → ∀ i σ,
    S.HoldsEsc R.escape (fun r => (R.premise i).eval S X K.catchUp σ r)
      (fun r => (S.trace r).ReadySafe (S.dur r K.catchUp) g
        ((R.start i).eval (S.trace r).point σ))
  /-- Recovery, liveness half. -/
  recoveryLive : ∀ R, s.recovery = some R → ∀ i σ,
    S.Holds (fun r => (R.premise i).eval S X K.catchUp σ r)
      (fun r => (S.trace r).TxLive (S.dur r K.catchUp) g
        ((R.start i).eval (S.trace r).point σ) (S.dur r (R.latency i)))

/-- The headline: system `S`, with execution atoms interpreted by `X`, meets
contract `K`. -/
structure ProblemClaims {Prog : Type} (S : System V) (X : ExecProfile S Prog)
    (K : Contract S.schema Prog) : Prop where
  /-- The contract is structurally well-formed. -/
  wf : K.WellFormed
  /-- The system's laws. -/
  laws : S.Laws
  /-- A capability is provided exactly when it is specified. -/
  provided : ∀ c, (S.schema.output c).isSome = (K.spec c).isSome
  /-- Every spec has its mandatory parts. -/
  complete : ∀ c s, K.spec c = some s → s.Complete c
  /-- Honest validators are never convicted by honest evidence. -/
  nonFraming : S.HoldsAlways S.NonFraming
  /-- Lower-rank outputs are prefixes of higher-rank ones, unconditionally. -/
  nested : ∀ c₁ c₂ g₁ g₂, c₁.rank < c₂.rank → S.schema.output c₁ = some g₁ →
    S.schema.output c₂ = some g₂ → S.HoldsAlways (fun r => (S.trace r).Nested g₁ g₂)
  /-- The final output never rolls back, unconditionally. -/
  finalMonotone : ∀ g, S.schema.output .final = some g →
    S.HoldsAlways (fun r => (S.trace r).Monotone g 0)
  /-- The claims of every provided capability. -/
  caps : ∀ c g s, S.schema.output c = some g → K.spec c = some s → CapClaims S X K g s

namespace System

/-- Accountable safety, non-framing and faults below the accountable fraction give
agreement of `g`. -/
theorem agree_of_accountable (S : System V) (hL : S.Laws) (r : S.Run) {g : S.schema.Id}
    {t₀ : Time} {α : ℚ} (hacc : S.AccountablySafe r α g t₀) (hnf : S.NonFraming r)
    (hb : (S.trace r).point.FaultsBelow α) : (S.trace r).Agree g t₀ := by
  classical
  intro u hu v hv i j hi hj
  rcases hacc u hu v hv i j hi hj with hc | hcard
  · exact hc
  · exfalso
    have hsub : S.convicted r (S.view r u i ∪ S.view r v j) ⊆ (S.trace r).point.faulty := by
      intro x hx
      have hx' : S.convicts r (S.view r u i ∪ S.view r v j) x := by
        unfold convicted Consensus.convicted at hx; simpa using hx
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, fun hxh => hnf x hxh ?_⟩
      refine hL.convicts_mono r _ _ x ?_ hx'
      rintro o (ho | ho)
      · exact ⟨u, hu, hL.view_mono r u i _ hi.1 ho⟩
      · exact ⟨v, hv, hL.view_mono r v j _ hj.1 ho⟩
    change (Fintype.card V : ℚ) * α ≤
      (S.convicted r (S.view r u i ∪ S.view r v j)).card at hcard
    have hc : ((S.convicted r (S.view r u i ∪ S.view r v j)).card : ℚ) ≤
        (S.trace r).point.faulty.card := by exact_mod_cast Finset.card_le_card hsub
    unfold EnvPoint.FaultsBelow at hb
    linarith

/-- Non-framing and a strict fault cap exclude the global slashing escape. -/
theorem not_globallySlashable_of_nonFraming (S : System V) (r : S.Run) {α : ℚ}
    (hnf : S.NonFraming r) (hb : (S.trace r).point.FaultsBelow α) :
    ¬ S.GloballySlashable α r := by
  classical
  have hsub : S.convicted r (S.honestEvidence r) ⊆ (S.trace r).point.faulty := by
    intro v hv
    have hc : S.convicts r (S.honestEvidence r) v := (Finset.mem_filter.mp hv).2
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hh => hnf v hh hc⟩
  have hc : ((S.convicted r (S.honestEvidence r)).card : ℚ) ≤
      (S.trace r).point.faulty.card := by exact_mod_cast Finset.card_le_card hsub
  unfold GloballySlashable EnvPoint.FaultsBelow at *
  intro hs
  linarith

/-- An escaped claim with escape `α`, under non-framing and faults below `α`, is
an unescaped claim. -/
theorem safe_of_escape {S : System V} {α : ℚ} {A P : S.Run → Prop}
    (hc : S.HoldsEsc (some α) A P) (hnf : S.HoldsAlways S.NonFraming) (r : S.Run)
    (hv : S.Valid r) (hA : A r) (hb : (S.trace r).point.FaultsBelow α) : P r ∨ S.Excuse r := by
  rcases hc r hv hA with h | h | ⟨β, hβ, hs⟩
  · exact Or.inl h
  · exact Or.inr h
  · cases hβ
    exact False.elim (not_globallySlashable_of_nonFraming S r (hnf r hv) hb hs)

omit [Fintype V] [DecidableEq V] in
/-- A weaker premise: a claim under `A` holds under any `B` implying `A`. -/
theorem Holds.mono_premise {S : System V} {A B P : S.Run → Prop} (h : S.Holds A P)
    (hAB : ∀ r, B r → A r) : S.Holds B P :=
  fun r hv hb => h r hv (hAB r hb)

end System

/-- Local accountability, non-framing and faults below the accountable fraction give
agreement of the capability's output. -/
theorem ProblemClaims.agree_of_accountable {Prog : Type} {S : System V} {X : ExecProfile S Prog}
    {K : Contract S.schema Prog} (hc : ProblemClaims S X K) {c : Capability} {g : S.schema.Id}
    {s : CapSpec Prog K.Idx} {α : ℚ}
    (hg : S.schema.output c = some g) (hs : K.spec c = some s) (ha : s.accountable = some α)
    (r : S.Run) (hv : S.Valid r) (hb : (S.trace r).point.FaultsBelow α) :
    (S.trace r).Agree g 0 ∨ S.Excuse r :=
  ((hc.caps c g s hg hs).accountable α ha r hv trivial).imp
    (fun h => S.agree_of_accountable hc.laws r h (hc.nonFraming r hv) hb) id

end Consensus

end

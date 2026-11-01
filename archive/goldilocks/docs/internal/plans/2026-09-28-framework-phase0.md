# Framework Phase 0 (compiled prototype) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build a compiled prototype of the framework core (instances, claim specs, certificates, profiles, the core floor, a Pareto comparison, a registry and a catalog lock) on the current v1 engine. The prototype tests the approved interfaces with the Lean compiler before Phases 1–2 freeze them.

**Architecture:** There are two new Lake libraries. `AvailableChainFramework` holds the layers L1–L3, the core kit and the Pareto code, and imports only `AvailableChainModel` and `AvailableChainStatements`. `AvailableChainRegistry` holds the L4 instances (Sanity, a Grid CO hooks variant, a toy Counter protocol), their certificates and refutations, and the tests. Two scripts (`lake env lean --run`) generate the registry table and the catalog lock. Existing libraries do not change.

**Tech Stack:** Lean 4 v4.30.0-rc2, Mathlib v4.30.0-rc2, Lake. The existing sources use the module system (`module`, `public import`, `@[expose] public section`).

**Spec:** `docs/FRAMEWORK-DESIGN.md` v7 (§0–§6 approved by the user on 2026-09-28). Read §2 E4, §3, §4, §5 and §8 before you start.

## Global Constraints

- Toolchain and Mathlib v4.30.0-rc2. Do not run `lake update`. `.lake/packages` is a clone; keep it.
- Committed proofs use no `sorry`, no `admit`, no project axioms and no `native_decide`. Kernel checks use `decide`, `decide_cbv` or `rfl`.
- The Mac `lean` is throttled (LEAN_SLOTS = 3). Before you conclude that a build is slow, check `ps -o etime,%cpu` on the `lean` processes.
- Build check for this plan: `lake build --wfail AvailableChainFramework AvailableChainRegistry`. The full check before handoff: `lake build --wfail` (all default targets).
- L0–L3 do not import L4–L6: no file in `AvailableChainFramework/` imports `AvailableChainRegistry`, `AvailableChainGridCO`, `AvailableChainSA`, `AvailableChainSAPC`, `AvailableChainLStar` or `AvailableChainWitnesses`.
- Existing files do not change, with two exceptions: `lakefile.toml` (new libraries) and `docs/MAP.md` (new rows).
- Commit ONLY on a user request (repository rule). Each task ends at a CHECKPOINT: the build is green and the task's files are listed in the report. Do not run `git commit`.
- Prose in comments and docs: ASD-STE100 Simplified Technical English.
- Namespace for new code: `AvailableChain.Framework` (L1–L3, kit) and `AvailableChain.Registry` (L4).
- Claim ids are immutable `Lean.Name`s with a version suffix, for example `` `core.safe.confirmed.v1 ``.

## Deviations from the spec (for the user to confirm)

1. §5 "checked attributes (`@[cert]`, `@[refutes]`)" become a TYPE-SCANNING registry script. Every constant whose type is `Cert c I`, `Refutation c I` or `RefutationFamily c I` is a certificate or refutation by its type. A constant whose type is `∀ …, Cert c I` is reported as CONDITIONAL and never as a certificate. This gives the same guarantee without attribute metaprogramming in `module` files.
2. §8 Phase 0 "E4 and Deliverable checked for Grid CO" becomes "E4 hooks (`HooksSound`) checked for a Grid CO variant with the new `excludes`". `Deliverable`, `RelayFeasible` and `WindowMargin` for Grid CO go to Phase 1, together with the change of `excludes` in `gridCO` itself.
3. §8 Phase 0 "the run-extension theorem for a toy spec" is proved FROM GENESIS (the canonical synchronous run exists for every horizon and is in the Sleepy regime). The general form, from every valid prefix, is `Kit.Engine` in Phase 1.
4. `ClaimSpec.needs` (§4) is not a field. Facets are type classes over `Instance` (Task 6 tests that a new facet is an addition). The v1 `Interface` is the one facet that every Phase 0 instance carries as a field.

## Review Focus

1. A certificate whose regime has no run: `Cert.inhabited` must be a real run of the instance, with horizon ≥ every H. Test: Task 4 builds `inhabited` from `exampleSleepy`, and Task 9 from the canonical Counter run.
2. The `le` direction: `le k k'` means that `k'` is AT LEAST AS WEAK as `k`. Pareto keeps the STRONGEST constants. Test: Task 5 checks a two-constant example where the direction matters.
3. A wrong `excludes` for Grid CO that excludes an object that the node would accept. Test: Task 7 proves `excludes → process st o = st` and checks one in-window HEAD that is not excluded.
4. A catalog lock hash that is not deterministic, or that changes when a new claim is added. Test: Task 6 runs the lock twice and after an addition, and compares.
5. The core floor used wrongly: an instance with a refuted core claim must not be a candidate. Test: Task 4 proves `¬ Candidate sanity`.

---

## File structure

```text
┌──────────────────────────────────────────────┬─────────────────────────────────────────┐
│ File                                         │ Responsibility                          │
├──────────────────────────────────────────────┼─────────────────────────────────────────┤
│ lakefile.toml                                │ two new libraries, default targets      │
│ AvailableChainFramework.lean                 │ library root                            │
│ AvailableChainFramework/Hooks.lean           │ E4: Outcome, classify, HooksSound (v1)  │
│ AvailableChainFramework/Instance.lean        │ Validators, Instance                    │
│ AvailableChainFramework/Claim.lean           │ RefutationKind, ClaimSpec, holds,       │
│                                              │ inhabited                               │
│ AvailableChainFramework/Cert.lean            │ Cert, Refutation, RefutationFamily      │
│ AvailableChainFramework/Profile.lean         │ Profile, ProfileCert                    │
│ AvailableChainFramework/Catalog/Core.lean    │ four core claims, profile `core`,       │
│                                              │ Candidate                               │
│ AvailableChainFramework/Kit/Core.lean        │ includedPersist lemma                   │
│ AvailableChainFramework/Pareto.lean          │ stronger, pareto, their lemmas          │
│ AvailableChainFramework/Engine/V2Sketch.lean │ toy E5/E6 step and isolation laws       │
│ AvailableChainRegistry.lean                  │ library root                            │
│ AvailableChainRegistry/Sanity.lean           │ Sanity instance, certs, refutation      │
│ AvailableChainRegistry/GridCOHooks.lean      │ gridCOx (new excludes), HooksSound      │
│ AvailableChainRegistry/Counter.lean          │ toy Counter spec and instance           │
│ AvailableChainRegistry/CounterRun.lean       │ canonical run, run extension, certs     │
│ AvailableChainRegistry/Tests/Pareto.lean     │ two-constant toy claim, Pareto checks   │
│ AvailableChainRegistry/Tests/NewFacet.lean   │ extensibility test (new facet + claim)  │
│ scripts/Registry.lean                        │ writes docs/REGISTRY.md                 │
│ scripts/CatalogLock.lean                     │ writes or checks docs/catalog.lock      │
│ docs/catalog.lock, docs/REGISTRY.md          │ generated                               │
└──────────────────────────────────────────────┴─────────────────────────────────────────┘
```

Every new `.lean` file under the two libraries starts with this header (use the imports that the task gives):

```lean
module
public import <imports>

@[expose] public section

namespace <namespace>
```

and ends with `end <namespace>` then `end`.

---

### Task 1: Libraries and E4 hooks

**Files:**
- Modify: `lakefile.toml`
- Create: `AvailableChainFramework.lean`, `AvailableChainFramework/Hooks.lean`
- Create: `AvailableChainRegistry.lean`, `AvailableChainRegistry/Sanity.lean` (hooks part only)

**Interfaces:**
- Produces: `AvailableChain.Framework.Outcome`, `classify`, `HooksSound`, `AvailableChain.Registry.Sanity.hooks : HooksSound (alwaysGenesis 1)`.

- [ ] **Step 1: Add the libraries.** Append to `lakefile.toml`, and add both names to `defaultTargets`:

```toml
# Framework prototype (Phase 0): hooks, instances, claim catalog, certificates.
[[lean_lib]]
name = "AvailableChainFramework"

# Instances with certificates and refutations over the framework (L4), and tests.
[[lean_lib]]
name = "AvailableChainRegistry"
```

- [ ] **Step 2: Write the failing test.** Create `AvailableChainRegistry/Sanity.lean` with imports `AvailableChainFramework` and `AvailableChainWitnesses.Sanity`, namespace `AvailableChain.Registry.Sanity`, and:

```lean
open AvailableChain AvailableChain.Generic AvailableChain.Framework
open AvailableChain.Witnesses.Sanity

theorem hooks : HooksSound (alwaysGenesis 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro st o _; rfl
  · intro V _ _ E rho _ v o i j _ _; rfl
  · intro V _ _ E rho _ v o i j _ h; exact h
  · intro st o o' h; exact Or.inl h
```

Create the roots: `AvailableChainFramework.lean` with `public import AvailableChainFramework.Hooks`, and `AvailableChainRegistry.lean` with `public import AvailableChainRegistry.Sanity`.

- [ ] **Step 3: Run it; it fails.** Run: `lake build AvailableChainRegistry`. Expected: FAIL, `unknown identifier 'HooksSound'` (or an unknown module).

- [ ] **Step 4: Write `AvailableChainFramework/Hooks.lean`.** Imports: `AvailableChainStatements.Generic.Conditions`. Namespace `AvailableChain.Framework`.

```lean
open AvailableChain.Generic AvailableChain.Statements.Generic

variable {n : Nat}

/-- The effect of one handler call on one handled object (design E4). -/
inductive Outcome where
  /-- `processed` changes from false to true. -/
  | accepted
  /-- `excludes` holds after the call; it holds for the rest of the epoch. -/
  | rejected
  /-- No change for the object, and it is not excluded. -/
  | refused
  deriving DecidableEq, Repr

/-- The effect of the call `process st o` on the handled object `o'`. -/
def classify (P : ProtocolSpec n) (st : P.State) (o o' : P.Object) : Outcome :=
  if P.processed st o' = false ∧ P.processed (P.process st o) o' = true then .accepted
  else if P.excludes (P.process st o) o' = true then .rejected
  else .refused

/-- E4 obligations on the v1 engine. The v1 engine has no restart, so a run
is one epoch. Stability is stated along runs, because `clock` can move back
in time on states that no run reaches. -/
structure HooksSound (P : ProtocolSpec n) : Prop where
  /-- An excluded object does not change the state. -/
  excludes_inert : ∀ st o, P.excludes st o = true → P.process st o = st
  /-- Exclusion is stable along a run. -/
  excludes_stable : ∀ {V : Type} [DecidableEq V] [Fintype V] (E : Env V)
    (rho : Run V P), ScheduleWellFormed E rho → ∀ v o i j, i ≤ j →
      P.excludes (Run.stateBefore P rho i v) o = true →
      P.excludes (Run.stateBefore P rho j v) o = true
  /-- `processed` is monotone along a run. -/
  processed_stable : ∀ {V : Type} [DecidableEq V] [Fintype V] (E : Env V)
    (rho : Run V P), ScheduleWellFormed E rho → ∀ v o i j, i ≤ j →
      P.processed (Run.stateBefore P rho i v) o = true →
      P.processed (Run.stateBefore P rho j v) o = true
  /-- A handled object is the delivered object or one that it carries. -/
  handles_carries : ∀ st o o', P.handles st o o' → o = o' ∨ P.carries o o'
```

`classify` is a definition, not a field: no protocol can override the E4
classification.

- [ ] **Step 5: Run it; it passes.** Run: `lake build --wfail AvailableChainFramework AvailableChainRegistry`. Expected: PASS. If `ScheduleWellFormed` does not take `[Fintype V]`, remove that binder in both fields.

- [ ] **Step 6: CHECKPOINT.** The build is green. Report the files. Do not commit.

---

### Task 2: Instance, ClaimSpec, certificates

**Files:**
- Create: `AvailableChainFramework/Instance.lean`, `AvailableChainFramework/Claim.lean`, `AvailableChainFramework/Cert.lean`
- Modify: `AvailableChainFramework.lean` (add the three imports)
- Test: `AvailableChainRegistry/Sanity.lean` (append)

**Interfaces:**
- Consumes: `HooksSound` (Task 1).
- Produces:
  - `Validators` with fields `V`, `dec`, `fin`;
  - `Instance` with fields `n`, `P`, `Δ`, `iface`, `hooks`;
  - `ClaimSpec` with fields `id`, `Const`, `valid`, `le`, `le_refl`, `le_trans`, `Point`, `regime`, `conclusion`, `trigger`, `transport`, `refutable`;
  - `ClaimSpec.holds`, `ClaimSpec.inhabited`;
  - `Cert`, `Refutation`, `RefutationFamily`, `Cert.weaken`, `Cert.not_refuted`, `Refutation.family_of`.

- [ ] **Step 1: Write the failing test.** Append to `AvailableChainRegistry/Sanity.lean`:

```lean
/-- The Sanity protocol as an instance. -/
def sanity : Instance where
  n := 1
  P := alwaysGenesis 1
  Δ := 1
  iface := interface 1
  hooks := hooks

example : sanity.Δ = exampleEnv.Δ := rfl
```

- [ ] **Step 2: Run it; it fails.** Run: `lake build AvailableChainRegistry`. Expected: FAIL, `unknown identifier 'Instance'`.

- [ ] **Step 3: Write `AvailableChainFramework/Instance.lean`.** Imports: `AvailableChainFramework.Hooks`, `AvailableChainStatements.Generic.Interface`.

```lean
open AvailableChain.Generic AvailableChain.Statements.Generic

/-- A finite validator type, bundled so that claims can quantify over it. -/
structure Validators where
  V : Type
  dec : DecidableEq V
  fin : Fintype V

attribute [instance] Validators.dec Validators.fin

/-- A protocol instance (design §3): the protocol, its protocol parameters,
and its facets, bound once. Claim constants are not here; they belong to
certificates. Phase 0 carries the v1 `Interface` as the one field facet;
other facets are type classes over `Instance`. -/
structure Instance where
  n : Nat
  P : ProtocolSpec n
  /-- Every certified environment has this Δ. -/
  Δ : Time
  iface : Interface P
  hooks : HooksSound P
```

- [ ] **Step 4: Write `AvailableChainFramework/Claim.lean`.** Imports: `AvailableChainFramework.Instance`.

```lean
open AvailableChain.Generic

/-- How a claim can be refuted. -/
inductive RefutationKind where
  /-- One finite run for one constant. -/
  | run
  /-- A parameterized family: no valid constant works. -/
  | family
  /-- The claim has no refutation form. -/
  | none
  deriving DecidableEq, Repr

/-- A catalog claim (design §4). `le k k'` means that `k'` is at least as
weak as `k`. `Point` holds the run parameters that the claim quantifies
over (for example `t₀`, or `T`, `b₀`, `b₁`). -/
structure ClaimSpec where
  id : Lean.Name
  Const : Type
  valid : Const → Prop
  le : Const → Const → Bool
  le_refl : ∀ k, le k k = true
  le_trans : ∀ a b c, le a b = true → le b c = true → le a c = true
  Point : Type
  /-- The runs that the claim speaks about. -/
  regime : (I : Instance) → Const → (W : Validators) → Env W.V →
    Run W.V I.P → Point → Prop
  /-- What the claim states about such a run. -/
  conclusion : (I : Instance) → Const → (W : Validators) → Env W.V →
    Run W.V I.P → Point → Prop
  /-- The event that makes the claim non-vacuous in a run (design §5). -/
  trigger : (I : Instance) → Const → (W : Validators) → Env W.V →
    Run W.V I.P → Point → Prop
  /-- A weaker constant keeps the claim. A proof, not metadata. -/
  transport : ∀ (I : Instance) (k k' : Const), valid k → valid k' →
    le k k' = true →
    (∀ (W : Validators) (E : Env W.V), E.Δ = I.Δ → ∀ rho x,
      regime I k W E rho x → conclusion I k W E rho x) →
    (∀ (W : Validators) (E : Env W.V), E.Δ = I.Δ → ∀ rho x,
      regime I k' W E rho x → conclusion I k' W E rho x)
  refutable : RefutationKind

namespace ClaimSpec

/-- The claim holds for an instance at a constant. -/
def holds (c : ClaimSpec) (I : Instance) (k : c.Const) : Prop :=
  ∀ (W : Validators) (E : Env W.V), E.Δ = I.Δ → ∀ rho x,
    c.regime I k W E rho x → c.conclusion I k W E rho x

/-- For every horizon bound, the regime has a run of the instance, with a
larger horizon, in which the trigger occurs (design §5). -/
def inhabited (c : ClaimSpec) (I : Instance) (k : c.Const) : Prop :=
  ∀ H : Time, ∃ (W : Validators) (E : Env W.V) (rho : Run W.V I.P) (x : c.Point),
    E.Δ = I.Δ ∧ H ≤ rho.horizon ∧ c.regime I k W E rho x ∧ c.trigger I k W E rho x

end ClaimSpec
```

- [ ] **Step 5: Write `AvailableChainFramework/Cert.lean`.** Imports: `AvailableChainFramework.Claim`.

```lean
/-- A certificate: one instance satisfies one claim at one constant, and the
claim's trigger occurs in its regime. -/
structure Cert (c : ClaimSpec) (I : Instance) where
  const : c.Const
  valid : c.valid const
  inhabited : c.inhabited I const
  proof : c.holds I const

/-- A refutation at one constant. -/
structure Refutation (c : ClaimSpec) (I : Instance) where
  const : c.Const
  valid : c.valid const
  proof : ¬ c.holds I const

/-- No valid constant works. -/
structure RefutationFamily (c : ClaimSpec) (I : Instance) : Prop where
  proof : ∀ k, c.valid k → ¬ c.holds I k

variable {c : ClaimSpec} {I : Instance}

/-- Move a certificate to a weaker constant. Inhabitation does not transport,
so the caller supplies it. -/
def Cert.weaken (x : Cert c I) (k' : c.Const) (hv : c.valid k')
    (hle : c.le x.const k' = true) (hi : c.inhabited I k') : Cert c I where
  const := k'
  valid := hv
  inhabited := hi
  proof := c.transport I x.const k' x.valid hv hle x.proof

theorem Cert.not_refuted (x : Cert c I) (r : RefutationFamily c I) : False :=
  r.proof x.const x.valid x.proof

theorem Refutation.family_of (r : Refutation c I)
    (h : ∀ k, c.valid k → c.holds I k → c.holds I r.const) :
    RefutationFamily c I :=
  ⟨fun k hk hh => r.proof (h k hk hh)⟩
```

- [ ] **Step 6: Run it; it passes.** Add the three modules to `AvailableChainFramework.lean`. Run: `lake build --wfail AvailableChainFramework AvailableChainRegistry`. Expected: PASS.

- [ ] **Step 7: CHECKPOINT.** Do not commit.

---

### Task 3: Core catalog, profiles, floor, includedPersist

**Files:**
- Create: `AvailableChainFramework/Profile.lean`, `AvailableChainFramework/Catalog/Core.lean`, `AvailableChainFramework/Kit/Core.lean`
- Modify: `AvailableChainFramework.lean`

**Interfaces:**
- Consumes: Task 2.
- Produces:
  - `Profile` with fields `id` and `claims : List ClaimSpec`;
  - `ProfileCert (p : Profile) (I : Instance) := ∀ c ∈ p.claims, Cert c I`;
  - `Catalog.safeConfirmed`, `Catalog.safeStable`, `Catalog.prefixOrder` and `Catalog.includedConfirmed : ClaimSpec`;
  - `Catalog.core : Profile`;
  - `Catalog.Candidate I := ProfileCert Catalog.core I`;
  - `Catalog.not_candidate_of_family`;
  - `Kit.includedPersist_of_safe`.

- [ ] **Step 1: Write the failing test.** Create `AvailableChainFramework/Kit/Core.lean` (imports `AvailableChainStatements.Generic.Properties`; namespace `AvailableChain.Framework.Kit`) with the statement first. It fails until `block_preceq_trans` exists:

```lean
open AvailableChain AvailableChain.Generic AvailableChain.Statements.Generic

variable {V : Type} [DecidableEq V] {n : Nat} {P : ProtocolSpec n}

theorem block_preceq_trans (A B C : Block) :
    Block.Preceq A B → Block.Preceq B C → Block.Preceq A C := by
  intro hAB hBC
  induction C with
  | genesis =>
      have hB : B = .genesis := by simpa [Block.Preceq, Block.preceq] using hBC
      subst hB; exact hAB
  | node p s r ih =>
      unfold Block.Preceq Block.preceq at hBC
      rcases Bool.or_eq_true_iff.mp hBC with h | h
      · have : B = .node p s r := of_decide_eq_true h
        subst this; exact hAB
      · have := ih h
        unfold Block.Preceq Block.preceq
        exact Bool.or_eq_true_iff.mpr (Or.inr this)

/-- Persistent inclusion follows from safety and exact-time inclusion with
the same `D` (design §4, derived lemma; user decision 2026-09-28). -/
theorem includedPersist_of_safe (E : Env V) (I : Interface P) (rho : Run V P)
    (g : Output P) (t₀ D : Time) (hsafe : SafeFrom P rho g t₀)
    (hinc : IncludedFrom P E I rho g t₀ D) :
    ∀ s : Slot, t₀ < P.proposalTime s → HonestAwakeProposer E rho s →
      P.proposalTime s + D ≤ rho.horizon → 0 ≤ D →
      ∃ B, HonestProposalAt E I rho s B ∧
        ∀ t, P.proposalTime s + D ≤ t → t ≤ rho.horizon → InBy P rho g B t := by
  intro s hs hp hh hD
  obtain ⟨B, hB, hin⟩ := hinc s hs hp hh
  refine ⟨B, hB, fun t ht htH v hv => ?_⟩
  exact block_preceq_trans _ _ _ (hin v hv)
    (hsafe.monotone v hv _ _ (by linarith) ht htH)
```

Proof guide: if `block_preceq_trans` does not close as written, copy the proof of `block_preceq_trans` in `AvailableChainGridCO/Proofs/Map.lean:25` (it is private there; do not import it). `linarith` needs `Mathlib.Tactic.Linarith`; add `public import Mathlib.Tactic.Linarith` if it is not in scope.

- [ ] **Step 2: Run it.** Run: `lake build AvailableChainFramework.Kit.Core`. Expected: PASS, or a local proof error that you fix without a change to the statements.

- [ ] **Step 3: Write `AvailableChainFramework/Profile.lean`.** Imports: `AvailableChainFramework.Cert`.

```lean
/-- A named set of catalog claims (design §4, profiles). -/
structure Profile where
  id : Lean.Name
  claims : List ClaimSpec

/-- One certificate per claim of the profile, all for one instance. Shared
constant names are Phase 1 (`ac-4.3` needs them). -/
def ProfileCert (p : Profile) (I : Instance) : Type :=
  ∀ c ∈ p.claims, Cert c I
```

- [ ] **Step 4: Write `AvailableChainFramework/Catalog/Core.lean`.** Imports: `AvailableChainFramework.Profile`, `AvailableChainStatements.Generic.Regimes`. Namespace `AvailableChain.Framework.Catalog`.

```lean
open AvailableChain AvailableChain.Generic AvailableChain.Statements.Generic

/-- The Sleepy regime of an instance. -/
def sleepy (I : Instance) (W : Validators) (E : Env W.V) (rho : Run W.V I.P)
    (t₀ : Time) : Prop :=
  SleepyRegime I.P E I.iface rho t₀

/-- Safety of one output in the Sleepy regime. No constant. -/
def safeOf (id : Lean.Name) (g : (I : Instance) → Output I.P) : ClaimSpec where
  id := id
  Const := Unit
  valid := fun _ => True
  le := fun _ _ => true
  le_refl := fun _ => rfl
  le_trans := fun _ _ _ _ _ => rfl
  Point := Time
  regime := fun I _ W E rho t₀ => sleepy I W E rho t₀
  conclusion := fun I _ _ _ rho t₀ => SafeFrom I.P rho (g I) t₀
  trigger := fun _ _ _ _ _ _ => True
  transport := by
    intro I k k' _ _ _ h
    cases k; cases k'; exact h
  refutable := .run

def safeConfirmed : ClaimSpec :=
  safeOf `core.safe.confirmed.v1 (fun I => I.iface.confirmed)

def safeStable : ClaimSpec :=
  safeOf `core.safe.stable.v1 (fun I => I.iface.stable)

/-- `stable ⪯ confirmed` at every honest node and time, in every run. -/
def prefixOrder : ClaimSpec where
  id := `core.prefix.stableConfirmed.v1
  Const := Unit
  valid := fun _ => True
  le := fun _ _ => true
  le_refl := fun _ => rfl
  le_trans := fun _ _ _ _ _ => rfl
  Point := Unit
  regime := fun _ _ _ _ _ _ => True
  conclusion := fun I _ _ _ rho _ => OutputOrder I.P I.iface rho
  trigger := fun _ _ _ _ _ _ => True
  transport := by
    intro I k k' _ _ _ h
    cases k; cases k'; exact h
  refutable := .run

/-- Exact-time inclusion of honest proposals in `confirmed`, Sleepy regime.
`D` is fixed: `le` is equality (design §4). -/
def includedConfirmed : ClaimSpec where
  id := `core.included.confirmed.v1
  Const := Time
  valid := fun D => 0 ≤ D
  le := fun a b => decide (a = b)
  le_refl := fun _ => decide_eq_true rfl
  le_trans := by
    intro a b c hab hbc
    have h1 := of_decide_eq_true hab
    have h2 := of_decide_eq_true hbc
    exact decide_eq_true (h1.trans h2)
  Point := Time
  regime := fun I _ W E rho t₀ => sleepy I W E rho t₀
  conclusion := fun I D _ E rho t₀ =>
    IncludedFrom I.P E I.iface rho I.iface.confirmed t₀ D
  trigger := fun I D _ E rho t₀ =>
    ∃ s : Slot, t₀ < I.P.proposalTime s ∧ HonestAwakeProposer E rho s ∧
      I.P.proposalTime s + D ≤ rho.horizon
  transport := by
    intro I k k' _ _ hle h
    have : k = k' := of_decide_eq_true hle
    subst this; exact h
  refutable := .family

/-- The core floor (design §4): every candidate certifies all four. -/
def core : Profile where
  id := `core.v1
  claims := [safeConfirmed, safeStable, prefixOrder, includedConfirmed]

/-- A candidate protocol passes the core floor. -/
def Candidate (I : Instance) : Type := ProfileCert core I

/-- A refutation family of a core claim rejects the instance. -/
theorem not_candidate_of_family {I : Instance} {c : ClaimSpec}
    (hc : c ∈ core.claims) (r : RefutationFamily c I) : Candidate I → False :=
  fun h => (h c hc).not_refuted r
```

- [ ] **Step 5: Run it; it passes.** Add `Profile`, `Catalog.Core` and `Kit.Core` to `AvailableChainFramework.lean`. Run: `lake build --wfail AvailableChainFramework`. Expected: PASS.

- [ ] **Step 6: CHECKPOINT.** Do not commit.

---

### Task 4: Sanity: three certificates, one refutation family, not a candidate

**Files:**
- Modify: `AvailableChainRegistry/Sanity.lean`

**Interfaces:**
- Consumes: Tasks 2–3; `AvailableChain.Witnesses.Sanity` (`alwaysGenesis`, `interface`, `safe`, `nested`, `exampleEnv`, `exampleRun`, `exampleSleepy`, `confirmedIncluded_fails`).
- Produces: `certSafeConfirmed`, `certSafeStable`, `certPrefix : Cert _ sanity`, `refutedIncluded : RefutationFamily Catalog.includedConfirmed sanity`, `not_candidate : Catalog.Candidate sanity → False`.

- [ ] **Step 1: Write the statements (failing).** Append:

```lean
open AvailableChain.Framework.Catalog

/-- The Sleepy regime of Sanity has runs of every horizon. -/
theorem sleepyInhabited (H : Time) :
    ∃ (W : Validators) (E : Env W.V) (rho : Run W.V sanity.P) (t₀ : Time),
      E.Δ = sanity.Δ ∧ H ≤ rho.horizon ∧ sleepy sanity W E rho t₀ := by
  refine ⟨⟨Fin 1, inferInstance, inferInstance⟩, exampleEnv, exampleRun (max H 0),
    0, rfl, ?_, exampleSleepy (max H 0)⟩
  change H ≤ max 1 (1 + max H 0)
  omega

def certSafeConfirmed : Cert safeConfirmed sanity where
  const := ()
  valid := trivial
  inhabited := by
    intro H
    obtain ⟨W, E, rho, t₀, hΔ, hH, hs⟩ := sleepyInhabited H
    exact ⟨W, E, rho, t₀, hΔ, hH, hs, trivial⟩
  proof := by
    intro W E _ rho t₀ _
    exact safe 1 W.V rho t₀

def certSafeStable : Cert safeStable sanity where
  const := ()
  valid := trivial
  inhabited := by
    intro H
    obtain ⟨W, E, rho, t₀, hΔ, hH, hs⟩ := sleepyInhabited H
    exact ⟨W, E, rho, t₀, hΔ, hH, hs, trivial⟩
  proof := by
    intro W E _ rho t₀ _
    exact safe 1 W.V rho t₀

def certPrefix : Cert prefixOrder sanity where
  const := ()
  valid := trivial
  inhabited := by
    intro H
    exact ⟨⟨Fin 1, inferInstance, inferInstance⟩, exampleEnv, exampleRun (max H 0),
      (), rfl, by change H ≤ max 1 (1 + max H 0); omega, trivial, trivial⟩
  proof := by
    intro W E _ rho _ _
    exact nested 1 W.V rho

theorem refutedIncluded : RefutationFamily includedConfirmed sanity := by
  refine ⟨fun D _ h => ?_⟩
  exact confirmedIncluded_fails D
    (h ⟨Fin 1, inferInstance, inferInstance⟩ exampleEnv rfl (exampleRun D) 0
      (exampleSleepy D))

theorem not_candidate : Candidate sanity → False :=
  not_candidate_of_family (by simp [core]) refutedIncluded
```

- [ ] **Step 2: Run it.** Run: `lake build --wfail AvailableChainRegistry`. Expected: PASS. Proof guide for local errors:
  - `safe` has the signature `safe (n : Nat) (V : Type) [DecidableEq V] (rho) (t₀)`.
  - The `Validators` instance fields must resolve `DecidableEq W.V` through `attribute [instance] Validators.dec`.
  - If `omega` does not see through `max`, use `simp only [max_def]; split_ifs <;> omega`.
  - Do NOT change a statement to make a proof pass. Report instead.

- [ ] **Step 3: Axiom check.** Append:

```lean
#print axioms certSafeConfirmed
#print axioms not_candidate
```

Run the build. Expected: the output lists only `propext`, `Classical.choice` and `Quot.sound` (or a subset). Then delete the two `#print` lines (they add build noise).

- [ ] **Step 4: CHECKPOINT.** Do not commit.

---

### Task 5: Pareto comparison

**Files:**
- Create: `AvailableChainFramework/Pareto.lean`, `AvailableChainRegistry/Tests/Pareto.lean`
- Modify: both library roots

**Interfaces:**
- Consumes: `ClaimSpec` (Task 2).
- Produces:
  - `ClaimSpec.stronger (c) (k k' : c.Const) : Bool`;
  - `ClaimSpec.pareto (c) (ks : List c.Const) : List c.Const`;
  - `pareto_sub`;
  - `pareto_covers`.

- [ ] **Step 1: Write the failing test.** Create `AvailableChainRegistry/Tests/Pareto.lean` (imports `AvailableChainFramework`; namespace `AvailableChain.Registry.Tests`). It is a toy two-constant claim, with an arming lag A (smaller is stronger) and a budget Π (larger is stronger), and no regime:

```lean
open AvailableChain AvailableChain.Framework

def armedToy : ClaimSpec where
  id := `test.armedToy.v1
  Const := Time × Time
  valid := fun _ => True
  le := fun a b => decide (a.1 ≤ b.1 ∧ b.2 ≤ a.2)
  le_refl := fun _ => decide_eq_true ⟨le_rfl, le_rfl⟩
  le_trans := by
    intro a b c hab hbc
    have h1 := of_decide_eq_true hab
    have h2 := of_decide_eq_true hbc
    exact decide_eq_true ⟨h1.1.trans h2.1, h2.2.trans h1.2⟩
  Point := Unit
  regime := fun _ _ _ _ _ _ => True
  conclusion := fun _ _ _ _ _ _ => True
  trigger := fun _ _ _ _ _ _ => True
  transport := by intro _ _ _ _ _ _ _ W E hΔ rho x _; trivial
  refutable := .none

-- (4,10) beats (5,10) and (4,8); (6,20) is incomparable with (4,10).
example : armedToy.pareto [(5, 10), (4, 10), (6, 20), (4, 8)] = [(4, 10), (6, 20)] := by
  decide
-- The direction matters: a weaker constant never removes a stronger one.
example : armedToy.pareto [(4, 10), (5, 9)] = [(4, 10)] := by decide
```

- [ ] **Step 2: Run it; it fails.** Run: `lake build AvailableChainRegistry`. Expected: FAIL, `unknown constant 'ClaimSpec.pareto'`.

- [ ] **Step 3: Write `AvailableChainFramework/Pareto.lean`.** Imports: `AvailableChainFramework.Claim`.

```lean
namespace ClaimSpec

/-- `k` is strictly stronger than `k'`. -/
def stronger (c : ClaimSpec) (k k' : c.Const) : Bool :=
  c.le k k' && !c.le k' k

/-- The constants that no constant in the list beats (the strongest ones). -/
def pareto (c : ClaimSpec) (ks : List c.Const) : List c.Const :=
  ks.filter (fun k => !ks.any (fun k' => c.stronger k' k))

theorem pareto_sub (c : ClaimSpec) (ks : List c.Const) :
    ∀ k ∈ c.pareto ks, k ∈ ks := fun _ hk => (List.mem_filter.mp hk).1

/-- Every listed constant is at least as weak as some Pareto constant. -/
theorem pareto_covers (c : ClaimSpec) (ks : List c.Const) :
    ∀ k ∈ ks, ∃ k' ∈ c.pareto ks, c.le k' k = true := by
  sorry -- see proof guide; the committed file has no sorry

end ClaimSpec
```

Proof guide for `pareto_covers`: use strong induction on the number of elements of `ks` that are strictly stronger than `k`, `(ks.filter (fun k' => c.stronger k' k)).length`. If this number is zero, `k` itself is in `pareto ks` and `le_refl` closes the goal. If not, take `k₁ ∈ ks` with `stronger k₁ k`. The set of elements strictly stronger than `k₁` is a strict subset of those strictly stronger than `k`: it is a subset by `le_trans`, and `k₁` is in the second set but not in the first. Apply the induction hypothesis to `k₁` to get `k'` with `le k' k₁`, then `le_trans` gives `le k' k`. Replace the `sorry` before the checkpoint.

- [ ] **Step 4: Run it; it passes.** Run: `lake build --wfail AvailableChainFramework AvailableChainRegistry`. Expected: PASS. If `decide` fails on the `Int` list examples, use `decide_cbv`. Do not use `native_decide`.

- [ ] **Step 5: CHECKPOINT.** Check: `grep -rn sorry AvailableChainFramework AvailableChainRegistry` prints nothing. Do not commit.

---

### Task 6: Registry and catalog lock scripts; extensibility test

**Files:**
- Create: `scripts/Registry.lean`, `scripts/CatalogLock.lean`, `AvailableChainRegistry/Tests/NewFacet.lean`
- Generate: `docs/REGISTRY.md`, `docs/catalog.lock`

**Interfaces:**
- Consumes: every constant of type `Cert c I`, `Refutation c I` or `RefutationFamily c I` in `AvailableChainRegistry`.
- Produces:
  - two command-line tools, each run as `lake env lean --run scripts/<name>.lean [args]`;
  - `docs/catalog.lock`: one line per declaration, in the form `<declaration name> <16 hex digits>`, sorted by name.

- [ ] **Step 1: Write `scripts/Registry.lean`.**

```lean
import AvailableChainRegistry
open Lean

/-- The head constant after all leading binders, and whether binders exist. -/
partial def headOf (e : Expr) (binders : Bool := false) : Option Name × Bool :=
  match e with
  | .forallE _ _ b _ => headOf b true
  | _ => (e.getAppFn.constName?, binders)

def kinds : List (Name × String) :=
  [(``AvailableChain.Framework.Cert, "cert"),
   (``AvailableChain.Framework.Refutation, "refutation"),
   (``AvailableChain.Framework.RefutationFamily, "refutation-family")]

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `AvailableChainRegistry }] {}
  let mut rows : Array String := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let (h, conditional) := headOf ci.type
    match h.bind (fun h => kinds.lookup h) with
    | some kind =>
        let args := (ci.type.getForallBody).getAppArgs
        let claim := toString (args[0]!.getAppFn.constName?.getD `?)
        let inst := toString (args[1]!.getAppFn.constName?.getD `?)
        let status := if conditional then "CONDITIONAL (not a certificate)" else "LEAN"
        rows := rows.push s!"│ {n} │ {kind} │ {claim} │ {inst} │ {status} │"
    | none => pure ()
  let rows := rows.qsort (· < ·)
  IO.FS.writeFile "docs/REGISTRY.md"
    ("# Registry (generated by scripts/Registry.lean; do not edit)\n\n```text\n" ++
      "│ Declaration │ Kind │ Claim │ Instance │ Status │\n" ++
      String.intercalate "\n" rows.toList ++ "\n```\n")
```

`getForallBody` strips the binders so that a conditional theorem still shows its claim and instance. If it is not in this toolchain, use the loop `match e with | .forallE _ _ b _ => strip b | e => e`. The table is aligned by hand later; a missing alignment is not an error.

- [ ] **Step 2: Run it.** Run: `lake build AvailableChainRegistry && lake env lean --run scripts/Registry.lean && cat docs/REGISTRY.md`. Expected: rows for `certSafeConfirmed`, `certSafeStable`, `certPrefix` (cert, LEAN) and `refutedIncluded` (refutation-family, LEAN).

- [ ] **Step 3: Write `scripts/CatalogLock.lean`.**

```lean
import AvailableChainFramework
open Lean

/-- Declarations under these prefixes are locked (L1–L3 and the LM/L0
definitions that they use are reached through the closure). -/
def roots : List Name :=
  [`AvailableChain.Framework.Catalog, `AvailableChain.Framework.ClaimSpec,
   `AvailableChain.Framework.Cert, `AvailableChain.Framework.Instance,
   `AvailableChain.Framework.HooksSound]

def ownHash (ci : ConstantInfo) : UInt64 :=
  let base := mixHash (hash ci.name) (hash ci.type)
  match ci with
  | .defnInfo d => mixHash base (hash d.value)
  | .opaqueInfo d => mixHash base (hash d.value)
  | .inductInfo d => d.ctors.foldl (fun h c => mixHash h (hash c)) base
  | _ => base  -- theorems: the statement only; a new proof keeps the hash

partial def closureHash (env : Environment) (n : Name)
    (memo : Std.HashMap Name UInt64) : Except String (UInt64 × Std.HashMap Name UInt64) := do
  if let some h := memo[n]? then return (h, memo)
  let some ci := env.find? n | throw s!"missing body: {n}"
  let memo := memo.insert n (ownHash ci)  -- breaks cycles through recursors
  let deps := (ci.getUsedConstantsAsSet.toList.filter (· != n)).toArray.qsort Name.lt
  let mut h := ownHash ci
  let mut memo := memo
  for d in deps do
    let (hd, m) ← closureHash env d memo
    memo := m
    h := mixHash h hd
  return (h, memo.insert n h)

def hex (u : UInt64) : String :=
  let s := String.mk (Nat.toDigits 16 u.toNat)
  "".pushn '0' (16 - s.length) ++ s

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `AvailableChainFramework }] {}
  let names := (env.constants.toList.map (·.1)).filter (fun n =>
    !n.isInternal && roots.any (fun r => r.isPrefixOf n))
  let names := names.toArray.qsort Name.lt
  let mut memo : Std.HashMap Name UInt64 := {}
  let mut lines : Array String := #[]
  for n in names do
    match closureHash env n memo with
    | .ok (h, m) => memo := m; lines := lines.push s!"{n} {hex h}"
    | .error e => IO.eprintln e; return 2
  let text := String.intercalate "\n" lines.toList ++ "\n"
  match args with
  | ["--write"] => IO.FS.writeFile "docs/catalog.lock" text; return 0
  | ["--check"] =>
      let old ← IO.FS.readFile "docs/catalog.lock"
      if old == text then return 0
      IO.eprintln "catalog.lock differs"; return 1
  | _ => IO.eprintln "usage: --write | --check"; return 2
```

Memo note: the first insert (own hash) ends recursion on cycles. The final entry replaces it. A declaration that the recursion reaches during a cycle keeps a hash that does not include the rest of the cycle. This is deterministic, which is all that the lock needs.

- [ ] **Step 4: Determinism test.** Run: `lake env lean --run scripts/CatalogLock.lean --write && cp docs/catalog.lock /tmp/lock1 && lake env lean --run scripts/CatalogLock.lean --check; echo $?`. Expected: `0`.

- [ ] **Step 5: Extensibility test.** Create `AvailableChainRegistry/Tests/NewFacet.lean` (imports `AvailableChainFramework`; namespace `AvailableChain.Registry.Tests`). It adds a facet as a class and a claim that needs it, outside the locked namespaces:

```lean
open AvailableChain AvailableChain.Generic AvailableChain.Framework

/-- A new facet: a third output. Adding it changes no existing declaration. -/
class HasStrong (I : Instance) where
  strong : I.P.State → Block

def safeStrong (I : Instance) [HasStrong I] : Prop :=
  ∀ (W : Validators) (E : Env W.V) (rho : Run W.V I.P) (t₀ : Time),
    Catalog.sleepy I W E rho t₀ →
    AvailableChain.Statements.Generic.SafeFrom I.P rho (HasStrong.strong (I := I)) t₀
```

Add it to `AvailableChainRegistry.lean`. Then run: `lake build AvailableChainRegistry && lake env lean --run scripts/CatalogLock.lean --check; echo $?`. Expected: `0` (the lock covers only `AvailableChainFramework`, and the new facet did not change it).

Then prove that the check detects a change. Temporarily change `includedConfirmed.valid` to `fun D => 0 < D`, rebuild `AvailableChainFramework`, and run `--check`. Expected: `1`. Revert the change, rebuild, and run `--check`. Expected: `0`.

- [ ] **Step 6: CHECKPOINT.** `docs/catalog.lock` and `docs/REGISTRY.md` exist. Do not commit.

---

### Task 7: Grid CO E4 hooks with the new `excludes`

**Files:**
- Create: `AvailableChainRegistry/GridCOHooks.lean`
- Modify: `AvailableChainRegistry.lean`

**Interfaces:**
- Consumes:
  - `AvailableChain.GridCO.gridCO`, `admitVote`, `process`, `processed`, `handles`, `carries`, `votesAt`, `equivocates` (`AvailableChainGridCO/Model/Protocol.lean`);
  - `stateBefore_now_mono` (`AvailableChainGridCO/Proofs/ClockBounds.lean:70`).
- Produces:
  - `gridExcludes (p : Params) : State p.n → Wire p.n → Bool`;
  - `gridCOx (p : Params) : ProtocolSpec p.n`;
  - `gridCOx_hooks : HooksSound (gridCOx p)`.

- [ ] **Step 1: Read the code first.** Read `Model/Protocol.lean` lines 120–140 (`votesAt`, `equivocates`), 300–370 (admission, `process`, `processed`, `handles`) and 480–500 (`clock`, `expire`). Record whether `expire` or `clock` ever removes an entry from `st.votes`. If it does, the equivocation case is NOT stable. Then drop the equivocation disjunct from `gridExcludes` below, and state that change in the report.

- [ ] **Step 2: Write the definitions and the failing statements.**

```lean
module
public import AvailableChainFramework
public import AvailableChainGridCO.Proofs.ClockBounds

@[expose] public section

namespace AvailableChain.Registry.GridCO

open AvailableChain AvailableChain.Generic AvailableChain.Framework AvailableChain.GridCO
open AvailableChain.Statements.Generic

/-- Permanent rejection (design E4): a HEAD for label `r` after slot `r+1`
(the clock only goes forward), or a new HEAD from a seat that already
equivocates at `r`. Both make `admitVote` return the state unchanged. -/
def gridExcludes (p : Params) {n : Nat} (st : State n) (o : Wire n) : Bool :=
  match o.auth, o.payload with
  | .seat r i, .head _ =>
      decide (r + 1 < (st.now / (4 * p.Δ)).toNat) ||
        (!decide (o ∈ st.votes) && equivocates (votesAt st r) i)
  | _, _ => false

/-- Grid CO with the E4 `excludes`. Every other field is `gridCO`'s. -/
def gridCOx [LeasePolicy] (p : Params) : ProtocolSpec p.n :=
  { gridCO p with excludes := gridExcludes p }

variable [LeasePolicy]

theorem gridExcludes_inert (p : Params) (st : State p.n) (o : Wire p.n)
    (h : gridExcludes p st o = true) : process p st o = st := by
  sorry -- proof guide below

theorem gridCOx_hooks (p : Params) : HooksSound (gridCOx p) := by
  sorry -- proof guide below

/-- Review Focus 3: an in-window, new, non-equivocating HEAD is not excluded. -/
theorem inWindow_not_excluded (p : Params) (st : State p.n) (r : Slot)
    (i : Fin p.n) (x) (hr : (st.now / (4 * p.Δ)).toNat ≤ r + 1)
    (heq : equivocates (votesAt st r) i = false) :
    gridExcludes p st ⟨.seat r i, .head x⟩ = false := by
  simp [gridExcludes, heq, Nat.not_lt.mpr hr]
```

Match the constructor name `.head x` and the `equivocates` argument order to the code that you read in Step 1.

- [ ] **Step 3: Prove `gridExcludes_inert`.** Proof guide: unfold `gridExcludes` and `process`, then split on `o.auth` and `o.payload`. For `.seat r i, .head _`, unfold `admitVote`. The refusal guard is `r < current - 1 || current < r || decide (o ∈ st.votes) || equivocates (votesAt st r) i`:
  - The first disjunct of `gridExcludes` gives `r < current - 1` (`omega`, using `r + 1 < current`).
  - The second disjunct gives the `equivocates` guard.

  Every other case of `gridExcludes` is `false`, which contradicts `h`.

- [ ] **Step 4: Prove `gridCOx_hooks`.** There are four fields:
  - `excludes_inert` is `gridExcludes_inert`.
  - `excludes_stable`: use induction on `j` from `i`. `World.step` either runs `clock` (`now` does not decrease along the run: `stateBefore_now_mono`, stated for `gridCO p`; `gridCOx` has the same `State`, `clock` and `process`, so transfer the lemma through `rfl` on `stateBefore`) or runs `process` (`votes` only grows, so `o ∉ votes` stays; `admitVote` refuses `o` when `equivocates`, so `o` never enters `votes` while it is excluded, and `equivocates` of a longer list stays true).
  - `processed_stable`: `votes` and `blocks` only grow (the same Step 1 check covers `clock`).
  - `handles_carries`: unfold `handles` and `carries`. The first disjunct is `o = o'`; the proposal case gives `child ∈ raw.map fromHead`, which is the left disjunct of `carries`.

  If `stateBefore` for `gridCOx` is not definitionally equal to `stateBefore` for `gridCO`, prove it once by `rfl` or `simp [Run.stateBefore, World.step, gridCOx]`, and state it as a lemma `stateBefore_x`.

- [ ] **Step 5: Run it; it passes.** Run: `lake build --wfail AvailableChainRegistry`, then `grep -n sorry AvailableChainRegistry/GridCOHooks.lean`. Expected: PASS, no output.

- [ ] **Step 6: CHECKPOINT.** Report the result of Step 1 (does `clock` or `expire` remove votes?). Do not commit.

---

### Task 8: E5/E6 toy step (engine v2 sketch)

**Files:**
- Create: `AvailableChainFramework/Engine/V2Sketch.lean`
- Modify: `AvailableChainFramework.lean`

**Interfaces:**
- Produces:
  - `SpecV2`, `Isolated`, `Restorable`;
  - `tickV2`, `restartV2`;
  - `output_tick`, `base_restart`, `toyV2`, `toyV2_isolated`.

  Nothing in Phases 0–1 consumes these. Phase 2 replaces them with the real engine v2.

- [ ] **Step 1: Write the definitions and the statements.** Imports: `AvailableChainModel.Objects.Blocks`, `AvailableChainModel.Objects.Time`. Namespace `AvailableChain.Framework.V2Sketch`.

```lean
open AvailableChain

/-- The part of a v2 spec that E5 and E6 need. -/
structure SpecV2 where
  State : Type
  Base : Type
  Object : Type
  Durable : Type
  DBase : Type
  base : State → Base
  clock : State → Time → State
  process : State → Object → State
  recordOwn : State → Object → State
  selfVisible : Object → Bool
  durable : State → Durable
  restore : Durable → State
  /-- The base-visible part of durable data. -/
  dbase : Durable → DBase
  output : State → Block

/-- E5 isolation laws. -/
structure Isolated (S : SpecV2) : Prop where
  clock_base : ∃ f : S.Base → Time → S.Base, ∀ st t, S.base (S.clock st t) = f (S.base st) t
  process_base : ∃ g : S.Base → S.Object → S.Base,
    ∀ st o, S.base (S.process st o) = g (S.base st) o
  recordOwn_base : ∀ st o, S.base (S.recordOwn st o) = S.base st
  output_base : ∃ h : S.Base → Block, ∀ st, S.output st = h (S.base st)

/-- E6 restore law: the base after a restart depends only on the
base-visible durable part, and that part only on the base. -/
structure Restorable (S : SpecV2) : Prop where
  restore_base : ∃ r : S.DBase → S.Base, ∀ d, S.base (S.restore d) = r (S.dbase d)
  durable_base : ∃ k : S.Base → S.DBase, ∀ st, S.dbase (S.durable st) = k (S.base st)

/-- The atomic tick: clock, then the own record over the self-visible
emitted objects in list order. Emission itself is outside this sketch. -/
def tickV2 (S : SpecV2) (st : S.State) (t : Time) (emitted : List S.Object) : S.State :=
  (emitted.filter S.selfVisible).foldl S.recordOwn (S.clock st t)

def restartV2 (S : SpecV2) (st : S.State) : S.State := S.restore (S.durable st)

/-- The own record never changes an output. -/
theorem output_tick (S : SpecV2) (h : Isolated S) (st : S.State) (t : Time)
    (os : List S.Object) : S.output (tickV2 S st t os) = S.output (S.clock st t) := by
  obtain ⟨hb, hh⟩ := h.output_base
  rw [hh, hh]
  unfold tickV2
  generalize S.clock st t = s0
  induction (os.filter S.selfVisible) generalizing s0 with
  | nil => rfl
  | cons o rest ih => simp only [List.foldl_cons]; rw [ih]; exact h.recordOwn_base s0 o

/-- Two states with the same base have the same base after a restart. -/
theorem base_restart (S : SpecV2) (h : Restorable S) (a b : S.State)
    (hab : S.base a = S.base b) : S.base (restartV2 S a) = S.base (restartV2 S b) := by
  obtain ⟨r, hr⟩ := h.restore_base
  obtain ⟨k, hk⟩ := h.durable_base
  simp only [restartV2, hr, hk, hab]
```

- [ ] **Step 2: A toy instance.** Append a toy whose record is a self-visible seat index, which must not reach the base (audit V11):

```lean
/-- State: (height, recorded seat index). Base: height. -/
def toyV2 : SpecV2 where
  State := Nat × Nat
  Base := Nat
  Object := Nat × Bool       -- (value, self-visible)
  Durable := Nat × Nat
  DBase := Nat
  base := fun st => st.1
  clock := fun st _ => st
  process := fun st o => (max st.1 o.1, st.2)
  recordOwn := fun st o => (st.1, o.1)
  selfVisible := fun o => o.2
  durable := fun st => st
  restore := fun d => (d.1, 0)
  dbase := fun d => d.1
  output := fun st => (List.range st.1).foldl (fun b k => .node b k ⟨k + 1⟩) .genesis

theorem toyV2_isolated : Isolated toyV2 :=
  ⟨⟨fun b _ => b, fun _ _ => rfl⟩, ⟨fun b o => max b o.1, fun _ _ => rfl⟩,
    fun _ _ => rfl, ⟨fun b => (List.range b).foldl (fun c k => .node c k ⟨k + 1⟩) .genesis,
      fun _ => rfl⟩⟩

theorem toyV2_restorable : Restorable toyV2 :=
  ⟨⟨fun d => d, fun _ => rfl⟩, ⟨fun b => b, fun _ => rfl⟩⟩
```

- [ ] **Step 3: Run it; it passes.** Run: `lake build --wfail AvailableChainFramework`. Expected: PASS. If the `induction … generalizing` form does not elaborate, prove `output_tick` with a helper lemma `foldl_recordOwn_base : ∀ l s, S.base (l.foldl S.recordOwn s) = S.base s`, by `List.foldl` induction.

- [ ] **Step 4: CHECKPOINT.** Do not commit.

---

### Task 9: Counter toy: run extension from genesis and certificates

**Files:**
- Create: `AvailableChainRegistry/Counter.lean`, `AvailableChainRegistry/CounterRun.lean`
- Modify: `AvailableChainRegistry.lean`

**Interfaces:**
- Consumes: Tasks 1–4; `ExecutionValid`, `PartialSynchrony`, `AcceptedObjectRelay`, `SleepyRegime`.
- Produces:
  - `counter : ProtocolSpec 1`, `counterInst : Instance`, `counterEnv`;
  - `canonical (k : Nat) (H : Nat) : Run (Fin k.succ) counter`;
  - `canonical_sleepy`;
  - `certSafeConfirmed`, `certSafeStable`, `certPrefix : Cert _ counterInst`.

This task is the hardest. It is the only one whose proofs are long, so give it to the strongest lane.

- [ ] **Step 1: Write `Counter.lean`.** Namespace `AvailableChain.Registry.Counter`. Imports: `AvailableChainFramework`, `Mathlib.Tactic`.

```lean
open AvailableChain AvailableChain.Generic AvailableChain.Framework
open AvailableChain.Statements.Generic

/-- The chain of height `k`: a fixed block for every height. -/
def chain : Nat → Block
  | 0 => .genesis
  | k + 1 => .node (chain k) k ⟨k + 1⟩

/-- Each proposer proposes the next height; a node accepts exactly the next
height. Payload `k` depends on height `k - 1`. -/
def counter : ProtocolSpec 1 where
  State := Nat
  Label := Empty
  Payload := Nat
  init := 0
  clock := fun st _ => st
  actTime := fun ℓ => ℓ.elim
  duties := fun _ => []
  duties_spec := fun ℓ _ => ℓ.elim
  duties_nodup := fun _ => List.nodup_nil
  act := fun _ ℓ => ℓ.elim
  proposalTime := fun s => s
  slotsAt := fun t => if 0 ≤ t then [t.toNat] else []
  slotsAt_spec := by
    intro s t
    change (s ∈ if 0 ≤ t then [t.toNat] else []) ↔ (s : Int) = t
    split_ifs with h <;> simp <;> omega
  slotsAt_nodup := by intro t; split_ifs <;> simp
  propose := fun st _ => some (st + 1)
  gossip := fun _ _ => []
  process := fun st o => if o.payload = st + 1 then st + 1 else st
  wellFormed := fun _ => true
  depsPresent := fun st o => decide (o.payload ≤ st + 1)
  processed := fun st o => decide (o.payload ≤ st)
  excludes := fun _ _ => false
  handles := fun _ o o' => o = o'
  carries := fun _ _ => False

def counterIface : Interface counter where
  confirmed := fun st => chain st
  stable := fun st => chain st
  block := fun k => some (chain k)
  opening := fun _ => True

theorem counter_hooks : HooksSound counter := by
  refine ⟨fun _ _ h => by simp [counter] at h, ?_, ?_, fun _ _ _ h => Or.inl h⟩
  · intro V _ _ E rho _ v o i j _ h; simp [counter] at h
  · sorry -- processed_stable: the state only grows (proof guide)

def counterInst : Instance where
  n := 1
  P := counter
  Δ := 1
  iface := counterIface
  hooks := counter_hooks
```

Proof guide for `processed_stable`: first prove `step_mono : st ≤ (World.step w e) v` for every event (`clock` is the identity; `process` returns `st` or `st + 1`). Then prove `stateBefore_mono : i ≤ j → stateBefore i v ≤ stateBefore j v` by induction on `j`, with `List.take_succ` and `List.foldl_append`. `decide (o.payload ≤ a) = true` and `a ≤ b` give `decide (o.payload ≤ b) = true`. `ScheduleWellFormed` is not needed.

- [ ] **Step 2: Write `CounterRun.lean` with the statements.** Namespace `AvailableChain.Registry.Counter`. The canonical synchronous run has `k+1` honest nodes, horizon `H`, and all nodes awake. At each time `t = 0 … H`, it has the ticks of all nodes (in `Fin` order), then the delivery of `⟨.proposer t, t+1⟩` to all nodes. The proposer of every slot is node 0.

```lean
def counterEnv (k : Nat) : Env (Fin k.succ) where
  Δ := 1
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := le_rfl
  awake := fun _ _ => true

def eventsAt (k t : Nat) : List (Event (Fin k.succ) counter.Object) :=
  (List.finRange k.succ).map (fun v => .tick v (t : Time)) ++
    (List.finRange k.succ).map (fun v => .deliver v ⟨.proposer t, t + 1⟩ (t : Time))

def canonical (k H : Nat) : Run (Fin k.succ) counter where
  honest := Finset.univ
  horizon := H
  events := (List.range (H + 1)).flatMap (eventsAt k)
  seatOf := fun ℓ => ℓ.elim
  proposerOf := fun _ => 0

/-- Every node has accepted heights `1 … t` before time `t`. -/
theorem stateBeforeTime_eq (k H t : Nat) (ht : t ≤ H + 1) (v : Fin k.succ) :
    Run.stateBeforeTime counter (canonical k H) t v = t := by
  sorry

/-- Run extension from genesis for the toy spec (design §8, Phase 0):
for every horizon, the canonical synchronous run is valid, meets both
relay conditions, and is in the Sleepy regime from 0. -/
theorem canonical_sleepy (k H : Nat) :
    SleepyRegime counter (counterEnv k) counterIface (canonical k H) 0 := by
  sorry
```

Proof guide:
- Write `seatOf := fun ℓ => ℓ.elim` as `fun ℓ => Empty.elim ℓ` if the elaborator needs it.
- `stateBeforeTime_eq`: induction on `t`. The events before time `t+1` are the events before `t` plus `eventsAt k t`. The ticks leave the state unchanged. The delivery of `t+1` to `v` moves `v` from `t` to `t+1` and does not touch other nodes (`Function.update`).
- `canonical_sleepy` has seven fields:
  - `execution`: sorted (keys `(t,0)` before `(t,1)`, times increase), no duplicates, times in `[0,H]`, all nodes honest, ticks at every integer time (`PublicTime` with `Δ = 1`). Delivery checks: `wellFormed` is true; for deps and freshness, the state before the delivery of `t+1` is `t` (use `stateBefore` at the index, and prove an index version of `stateBeforeTime_eq`). Unforgeable: the holder of `.proposer t` is node 0, which emits `⟨.proposer t, t+1⟩` at its tick at `t`, since its state after the clock is `t` and it is awake.
  - `rootInjective`: all named blocks are `chain m`, and `(chain m).root = ⟨m⟩` for `m ≥ 1`.
  - `partialSynchrony` and `acceptedRelay`: each emission at `t` is delivered to every node at `t < t + 1`, and it is accepted there.
  - `gst_zero`, `start_zero`: `rfl`.
  - `participation`: no faulty node, and at least one awake node.

- [ ] **Step 3: The certificates.** Append:

```lean
open AvailableChain.Framework.Catalog

theorem counter_safe (W : Validators) (rho : Run W.V counter) (t₀ : Time) :
    SafeFrom counter rho counterIface.confirmed t₀ := by
  sorry
```

Proof guide: every honest read is `chain m` for some `m`. `chain a ⪯ chain b` when `a ≤ b` (induction on `b`), so every two reads are compatible. Per-node monotonicity follows from `stateBefore_mono` (Task 9, Step 1) through `readAt`.

Then build the three `Cert`s as in Task 4. Use `inhabited` from `canonical_sleepy`, with `H := max H₀ 0` converted to `Nat` (`Int.toNat`), and horizon `≥ H₀` by `Int.self_le_toNat`. `certPrefix` uses `OutputOrder` with `stable = confirmed`, which is `Block.Preceq x x` (`decide` on `preceq` for equal blocks: prove `preceq_refl` by cases).

- [ ] **Step 4: Run it; it passes.** Run: `lake build --wfail AvailableChainRegistry`, then `grep -rn sorry AvailableChainRegistry`. Expected: PASS, no output. Then run `lake env lean --run scripts/Registry.lean` and check that `docs/REGISTRY.md` lists the three Counter certificates.

- [ ] **Step 5: Stretch goal, optional in Phase 0: `included(confirmed)` for Counter at `D = 1`.** If it is done, Counter is the first instance that passes the floor (`Candidate counterInst`). If it is not done, record it as an open item in the report. It is not a Phase 0 acceptance item.

- [ ] **Step 6: CHECKPOINT.** Do not commit.

---

### Task 10: Documents and handoff

**Files:**
- Modify: `docs/MAP.md` (rows for the new libraries), `log.md`, `state.md`
- Modify: `docs/FRAMEWORK-DESIGN.md` §8 (Phase 0 row: record the deviations that the user accepted)

- [ ] **Step 1: Full build.** Run: `lake build --wfail`. Expected: PASS with the same job count as before, plus the new modules. Run `grep -rn 'sorry\|admit\|native_decide' AvailableChainFramework AvailableChainRegistry scripts`. Expected: no output.
- [ ] **Step 2: Lock and registry.** Run `lake env lean --run scripts/CatalogLock.lean --check` (expected `0`) and `lake env lean --run scripts/Registry.lean`.
- [ ] **Step 3: Write the report.** Include:
  - what the prototype showed about each interface: `Validators` bundling, `Point`, type-class facets, `Cert` as data;
  - every statement that you had to change, and why;
  - the Grid CO `expire` finding from Task 7, Step 1;
  - the open items for the Phase 1–2 plan.

  Append the report to `log.md`, and update `state.md` (30 lines or fewer).
- [ ] **Step 4: CHECKPOINT.** Stop. The user decides about commits and the Phase 1–2 plan.

---

## After Phase 0

Phases 1–2 get their own plan after this prototype. Phase 0 exists to change the interfaces (§3 says Phase 0 selects the facet and constant representations), so a detailed Phase 1–2 plan now would be rewritten. Phase 1 will include:
- the full v1 catalog;
- the `ac-4.3` and `strong-1` equivalences, with shared constants;
- the `excludes` change in `gridCO`, SA and SA-PC;
- the exempt `AcceptedObjectRelay`, with the check of every `acceptedRelay` use;
- `WindowMargin`, `Deliverable` and `RelayFeasible` per instance;
- `Kit.Engine` run extension from every valid prefix;
- `MATRIX.md`;
- the §9 rule text in `CONTRACT.md`.

Phase 2 is engine v2 and the lift, and the §9 rule text in `AGENTS.md`.

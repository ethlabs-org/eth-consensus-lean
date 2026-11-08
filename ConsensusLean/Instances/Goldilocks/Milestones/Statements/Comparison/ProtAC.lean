module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Comparison.ProtACEnv

@[expose] public section

/-! # Tier A protection: the class, the claim and the profile (statements)

Tier A restates the protection profile (`Comparison/Protection`, K6) over AC traces of the
Goldilocks SA. The parameter type, its order and its feasibility predicates are K6's (`ProtQ`);
the class is its own (`ProtClassAC0`): an infinite-trace AC specialisation of K6's class without
its arming premise, for a static honest set `H` (`Hᶜ` faulty) and trivial frames, over the
vocabulary of `ProtACEnv`. No equivalence with K6's `ProtClass` is claimed.

* `ProtClassAC0 q T b₀ b₁`: the outage times (`0 ≤ T`, `b₀ ≤ b₁ ≤ b₀ + β·Δ`), service before
  `b₀` cut at the deadline and from `b₁`, the tick duty, time progress, trivial frames,
  η-sleepiness from `0`, no sleep and the cohort margin on the no-sleep window, a cohort of at
  least `A` and at most `fcap` faulty validators.
* `ProtectedReadyAC c T t₀`: every read of a validator ready at `T` is below every read of a
  validator ready at a time `t ≥ t₀`.
* Protection is a property of a lock rule's retention, not of every lawful unlock stage (the
  unlock relation alone keeps no lock), so the profile is per candidate: `ProtProfileAC0 Run ℓ rec`
  over the runs `Run` of the candidate, with named run predicates (`parentRunAC`; the
  evidence-release runs at a write mode follow once their projection is in Milestones).
* `protLagAC0`, `protRecAC0`: the defaults at the Goldilocks contract's numbers (lag `4k + 6`,
  recovery `9`) at the points inside the contract's outage windows, `⊤` elsewhere.

Static, trivial frames, infinite traces; no claim about growing faults or Tier R. Coverage is not
stated here. Statements only. -/

namespace Consensus.Goldilocks.Comparison

open SA Consensus.Comparison

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}

/-- **Tier A's protection class at point `q`**, for the outage `[b₀, b₁)` and a read at `T`
(without the arming premise `T + ℓ·Δ ≤ b₀`). -/
def ProtClassAC0 (q : ProtQ) (T b₀ b₁ : Time) (tr : SATrace sp FGP ro) (H : Set (Fin sp.n))
    (U : Set (Blk sp.n FGP)) : Prop :=
  0 ≤ T ∧ b₀ ≤ b₁ ∧ b₁ ≤ b₀ + (q.β : Time) * sp.Δ ∧
    SyncUntilAC tr H U b₀ ∧ PSyncAC tr H U b₁ ∧
    TickDuty tr H ∧ TimeProgressAC tr ∧ TrivialFrames tr H ∧
    EtaSleepyAC tr H q.θ ((q.η : Time) * sp.Δ) ((q.catchUp : Time) * sp.Δ) ∧
    NoSleepOnAC tr H (protStartAC sp q b₀) (protEndAC sp q b₁) ∧
    CohortOnAC tr H (protStartAC sp q b₀) (protEndAC sp q b₁) ∧
    q.A ≤ (awakeAtAC tr H (protStartAC sp q b₀)).ncard ∧ Hᶜ.ncard ≤ q.fcap

/-- **Protection of the ready reads at `T` from `t₀` on**: for readiness with catch-up `c`, every
read of a validator ready at `T` is an ancestor (inside `U`) of every read of a validator ready at
any `t ≥ t₀`. -/
def ProtectedReadyAC (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (c T t₀ : Time) : Prop :=
  ∀ v B, ReadyAC tr H c v T → ReadAC tr v T B →
    ∀ w t B', t₀ ≤ t → ReadyAC tr H c w t → ReadAC tr w t B' → Anc U B B'

/-- **The parent's runs**: AC traces of the Goldilocks SA with its contract and the honest-object
facts for some proposer schedule. -/
def parentRunAC (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP)) : Prop :=
  ∃ proposer, ACRun proposer tr H U

/-- **The Tier A protection profile** of the candidate whose runs are `Run`: monotone lag and
recovery bounds `ℓ`, `rec`, and at every point `q` with `ℓ q = c` and `rec q = d`, on every run of
the class with `T + c·Δ ≤ b₀`, the ready reads at `T` are protected from `b₁ + d·Δ` on. -/
def ProtProfileAC0 (Run : SATrace sp FGP ro → Set (Fin sp.n) → Set (Blk sp.n FGP) → Prop)
    (ℓ rec : Bound ProtQ) : Prop :=
  AdverseMonotone ℓ ∧ AdverseMonotone rec ∧
    ∀ q (c d : ℕ), ℓ q = c → rec q = d → ∀ tr H U (T b₀ b₁ : Time),
      Run tr H U → ProtClassAC0 q T b₀ b₁ tr H U → T + (c : Time) * sp.Δ ≤ b₀ →
        ProtectedReadyAC tr H U ((q.catchUp : Time) * sp.Δ) T (b₁ + (d : Time) * sp.Δ)

variable (sp) in
/-- **The points inside the Goldilocks contract's outage** (K6's `PersistsPoint` read at the
contract's numbers: budget `4k − 5`, `η = 0`, `ahead = 5`, `noSleep = 4k + 6`, `cohortAhead = 0`,
`θ = 1/2`, `catchUp = 19`), at either source output: the AC's confirmed tip is both its stable and
its available output. At `θ ≥ 1` the class is empty, so a finite default there is a vacuous
implication; no coverage or ranking is claimed at any point. -/
def ProtPointAC0 (q : ProtQ) : Prop :=
  q.β ≤ 4 * sp.k - 5 ∧ 5 ≤ q.ahead ∧ 4 * sp.k + 6 ≤ q.noSleep ∧
    q.noSleep + q.cohortAhead = 4 * sp.k + 6 ∧ (1 / 2 : ℚ) ≤ q.θ ∧ 19 ≤ q.catchUp

instance (q : ProtQ) : Decidable (ProtPointAC0 sp q) := by
  unfold ProtPointAC0; infer_instance

variable (sp) in
/-- The default lag: `4k + 6` inside the contract's outage, `⊤` elsewhere. -/
def protLagAC0 : Bound ProtQ := fun q =>
  if ProtPointAC0 sp q then ((4 * sp.k + 6 : ℕ) : WithTop ℕ) else ⊤

variable (sp) in
/-- The default recovery: `9` inside the contract's outage, `⊤` elsewhere. -/
def protRecAC0 : Bound ProtQ := fun q => if ProtPointAC0 sp q then ((9 : ℕ) : WithTop ℕ) else ⊤

end Consensus.Goldilocks.Comparison

end

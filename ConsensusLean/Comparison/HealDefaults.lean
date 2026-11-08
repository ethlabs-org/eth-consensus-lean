module
public import ConsensusLean.Comparison.HealProfile

@[expose] public section

/-! # Slice 1: the defaults from the contract (statements)

Implication fields only, from the L0 property table (`Behaviour`, so from every `CorrectProtocol`);
coverage is a separate obligation.

* `healHsDefault`, `healHlDefault`, `healLatDefault`: at `(cap, i)`, the contract's heal coefficient
  (`hs` for `cap` available or stable, `hl` for every capability) and latency coefficient (`lat`),
  at every point with `fcap < β·n` whose readiness is at least the contract's (`K.catchUp ≤
  q.catchUp`, `K.θ ≤ q.θ`), whatever `L`, `hpre`, `hpost`, `m` and the class; `⊤` elsewhere (and
  `hs = ⊤` for final).
* `HealDefault`: every model system with the L0 property table has the Slice 1 heal profile
  `(healHsDefault, healHlDefault, healLatDefault)` at every capability, index and role floors. The
  proof instantiates `healedSafe` and `healthyLive` at GST `b₁`: the class with `fcap < β·n` is in
  `Healthy b₁` (`IncidentNet` gives `PSync b₁`; `HonestAwakeAfter b₁` is `HealthyOn`'s
  participation clause; the class carries the FG delay bound); healed safety needs progress only up
  to the heal point, which progress to the horizon gives when the heal point is within the
  horizon, and when it is past the horizon ready-reader safety from it is vacuous (every cut is
  within the horizon); a reader ready with catch-up `q.catchUp·ΔAC ≥ catchUp·ΔAC` is ready with the
  contract's catch-up, so the contract's claims cover the point's readers. -/

namespace Consensus.Comparison

open Consensus.Model

variable {V : Type} [Fintype V] {Prog : Type}

/-- The point's readiness is at least the contract's: catch-up at least `K.catchUp` (fewer
readers) and ratio at least `K.θ`. -/
abbrev ReadinessAtLeast (K : Contract Prog) (q : HealQ V) : Prop :=
  K.params.catchUp ≤ q.catchUp ∧ K.params.θ ≤ q.θ

/-- The default safety-heal bound at `(cap, i)`: the contract's heal coefficient for an available
or stable `cap` at points with `fcap < β·n` and readiness at least the contract's; `⊤`
elsewhere. -/
noncomputable def healHsDefault (K : Contract Prog) (cap : Capability) (i : K.Idx) :
    Bound (HealQ V) := fun q =>
  if (cap = .available ∨ cap = .stable) ∧ (q.fcap : ℚ) < K.params.β * Fintype.card V ∧
      ReadinessAtLeast K q then
    (K.params.heal cap i : WithTop ℕ) else ⊤

/-- The default liveness-heal bound at `(cap, i)`: the contract's heal coefficient at points with
`fcap < β·n` and readiness at least the contract's; `⊤` elsewhere. -/
noncomputable def healHlDefault (K : Contract Prog) (cap : Capability) (i : K.Idx) :
    Bound (HealQ V) := fun q =>
  if (q.fcap : ℚ) < K.params.β * Fintype.card V ∧ ReadinessAtLeast K q then
    (K.params.heal cap i : WithTop ℕ) else ⊤

/-- The default latency bound after the heal point at `(cap, i)`: the contract's latency
coefficient at points with `fcap < β·n` and readiness at least the contract's; `⊤` elsewhere. -/
noncomputable def healLatDefault (K : Contract Prog) (cap : Capability) (i : K.Idx) :
    Bound (HealQ V) := fun q =>
  if (q.fcap : ℚ) < K.params.β * Fintype.card V ∧ ReadinessAtLeast K q then
    (K.params.latency cap i : WithTop ℕ) else ⊤

/-- **The Slice 1 heal defaults** (`HealDefault`): every model system with the L0 property table has
the Slice 1 heal profile `(healHsDefault, healHlDefault, healLatDefault)` at every capability,
index and role floors. -/
def HealDefault : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (O : OutputSchema) (F : ProtocolFamily O)
    (fl : RoleFloor F V) (Prog : Type) (X : Progress (sysOf O F V) Prog) (K : Contract Prog),
    Behaviour (sysOf O F V) X K → ∀ cap (i : K.Idx),
      HealProfile F X K fl cap i (healHsDefault K cap i) (healHlDefault K cap i)
        (healLatDefault K cap i)

end Consensus.Comparison

end

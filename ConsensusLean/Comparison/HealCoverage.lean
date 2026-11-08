module
public import ConsensusLean.Comparison.Coverage
public import ConsensusLean.Comparison.HealProfile

@[expose] public section

/-! # Slice 1 heal coverage for chain shapes (statements)

`HealDomainCoverage` and `HealBoundaryCoverage` ask, for every point of the coverage domain with a
finite claim, for a valid, excuse-free witness run of the Slice 1 class (with the profile's progress
premise and every finite claim active at the point's readers); the boundary form also asks the
witness to attain the environment parameters (`Attains`): exact incident length, exactly `hpre`
validators active before the end of the incident and exactly `hpost` after it, exactly `fcap`
compromised, exactly `max m fcap` that cannot vote, the class exercised. These statements say which
bounds of a chain shape family are covered.

* `ForgeableRole F`: a compromised key can sign an object that the selection admits: a message, and
  either the poll role admits a selection containing every given set of keys, or some committee
  kind admits a selection containing any one key (at each slot). The exact-activity witnesses
  deliver one such forged object per active key and window to an honest node; a family where no
  compromised key can hold a credential has no run with positive activity.
* `HealDomainSupport`: at every point of the coverage domain with a finite heal claim, the progress
  requirement admits `fcap` compromised validators, and positive activity needs `ForgeableRole`.
* `HealBoundarySupport`: moreover a split class (held or not) has `fcap < β·n`: the witness needs an
  honest message sent during the incident and held across the groups, and in a chain shape the only
  send the contract guarantees is an honest proposal, from healthy liveness, which needs the healthy
  fault bound.
* `ShapeHealDomainCoverage`, `ShapeHealBoundaryCoverage`: the two Slice 1 coverage packages for
  chain shape families, at the shape's role floors (`shapeRoleFloor`), under the progress fit of the
  contract, an FG delay of at least one `ΔAC` and the provided output; the boundary package also
  takes the chain-level claims and proposals that are not FG attestations (for the exercised
  message). -/

namespace Consensus.Comparison

open Shape Blocks
open Consensus.Model (Obj Msg)

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]

/-- **A compromised key can hold a credential**: at every public parameter, there is a message
to sign, and either the poll role admits a selection containing every given set of keys, or some
committee kind admits a selection containing any one key. -/
def ForgeableRole (F : ChainShapeFamily O Info) : Prop :=
  ∀ pub : Model.Public, Nonempty (Msg (Header Info) (F pub).Body) ∧
    ((∀ T : Finset (Fin pub.n), ∃ S, (F pub).skel.pollSel.Admits S ∧ T ⊆ S) ∨
      ∃ k₀ : (F pub).skel.Kind, ∀ j : Fin pub.n, ∃ S, ((F pub).skel.kindSel k₀).Admits S ∧ j ∈ S)

variable {V : Type} [Fintype V]

/-- **Domain support of the Slice 1 heal bounds** at `(cap, i)`: at every point of the coverage
domain with a finite safety claim, or finite liveness and latency claims, the progress requirement
of `(cap, i)` admits `fcap` compromised validators, and positive activity needs a forgeable
role. -/
def HealDomainSupport (F : ChainShapeFamily O Info) (K : Contract ProgressReq) (cap : Capability)
    (i : K.Idx) (hs hl lat : Bound (HealQ V)) : Prop :=
  ∀ q : HealQ V, q.DomainFeasible → (hs q < ⊤ ∨ (hl q < ⊤ ∧ lat q < ⊤)) →
    AdmitsFaults (K.progress cap i) q.fcap ∧ (0 < q.hpre ∨ 0 < q.hpost → ForgeableRole F)

/-- **Boundary support of the Slice 1 heal bounds** at `(cap, i)`: the domain support, and at every
point of the coverage domain with a finite claim and a split class (held or not),
`fcap < β·n`. -/
def HealBoundarySupport (F : ChainShapeFamily O Info) (K : Contract ProgressReq)
    (cap : Capability) (i : K.Idx) (hs hl lat : Bound (HealQ V)) : Prop :=
  HealDomainSupport F K cap i hs hl lat ∧
    ∀ q : HealQ V, q.DomainFeasible → (hs q < ⊤ ∨ (hl q < ⊤ ∧ lat q < ⊤)) → q.a.IsSplit →
      (q.fcap : ℚ) < K.params.β * Fintype.card V

/-- **Slice 1 domain coverage for chain shapes**: a chain shape family with a fitting progress
requirement and an FG delay of at least one `ΔAC` has domain coverage, at its role floors, of every
Slice 1 heal profile `(hs, hl, lat)` at a provided output's `(cap, i)` whose finite claims lie in
the domain support. -/
def ShapeHealDomainCoverage : Prop :=
  ∀ {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]
    (F : ChainShapeFamily O Info) (K : Contract ProgressReq) (V : Type) [Fintype V] [DecidableEq V],
    ProgressFits K F → 1 ≤ K.params.fgDelay →
    ∀ (cap : Capability) (i : K.Idx) (hs hl lat : Bound (HealQ V)), (O.output cap).isSome →
      HealDomainSupport F K cap i hs hl lat →
      HealDomainCoverage (compiled F) (shapeProgress F V) K (shapeRoleFloor F V) cap i hs hl lat

/-- **Slice 1 boundary coverage for chain shapes**: a chain shape family with the chain-level
claims, a fitting progress requirement, proposals that are not FG attestations and an FG delay of at
least one `ΔAC` has boundary coverage, at its role floors, of every Slice 1 heal profile
`(hs, hl, lat)` at a provided output's `(cap, i)` whose finite claims lie in the boundary
support. -/
def ShapeHealBoundaryCoverage : Prop :=
  ∀ {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]
    (F : ChainShapeFamily O Info) (K : Contract ProgressReq) (V : Type) [Fintype V] [DecidableEq V],
    ShapeClaimsAt F K V → ProgressFits K F → ProposalsNotFGAtt F → 1 ≤ K.params.fgDelay →
    ∀ (cap : Capability) (i : K.Idx) (hs hl lat : Bound (HealQ V)), (O.output cap).isSome →
      HealBoundarySupport F K cap i hs hl lat →
      HealBoundaryCoverage (compiled F) (shapeProgress F V) K (shapeRoleFloor F V) cap i hs hl lat

end Consensus.Comparison

end

module
public import ConsensusLean.Comparison.Heal
public import ConsensusLean.Comparison.Activity

@[expose] public section

/-! # Slice 1 heal profile: activity, participation, readiness and the held split (statements)

Slice 1 adds to Slice 0's heal profile (`Heal.lean`) the coordinates that Slice 0 leaves out:
the adversary's **activity** before and after the incident, a **lower bound on the validators that
cannot vote** during the incident (faulty by the horizon, or honest and asleep throughout it), the
**held split** (a refinement of the split class in which no group receives, during the incident,
content that the other group first released honestly then), and the **readiness parameters**
`θ` and `catchUp`, so that one point means one set of ready readers for every protocol.

* `IncidentClass`: `any`, `split G`, `splitHeld G`, ordered `splitHeld G ≤ split G ≤ any`. Its
  delivery guarantee is Slice 0's (`IncidentClass.async`); `splitHeld G` adds the content-origin
  hold.
* `HonestAwakeAfter b₁`: every validator honest at a time of `[max b₁ 0, horizon]` is awake then
  (`HealthyOn`'s participation clause after the incident).
* `notAwakeHonest b₀ b₁`: compromised by the horizon, or honest and asleep at every time of a
  nonempty incident window `[max b₀ 0, b₁)`.
* `HealQ`: the parameters `⟨L, hpre, hpost, m, fcap, a, θ, catchUp⟩`, ordered coordinatewise
  toward more adverse points (`L`, `hpre`, `hpost`, `fcap` and the class increase; `m`, `θ` and
  `catchUp` decrease); `HealQ.DomainFeasible`, a conservative coverage subdomain.
* Over model systems `sysOf O F V` with role floors `fl` (activity and the hold read signatures by
  signer, which only L1 objects carry; both readings are the canonical ones of `Activity.lean`):
  * `HealClass`: the **bound-independent** run class: the incident geometry of the class (and the
    hold for `splitHeld`), the incident length, activity at most `hpre` on `[0, max b₁ 0)` and at
    most `hpost` on `[max b₁ 0, horizon]`, at least `m` validators that cannot vote, at most `fcap`
    compromised by the horizon, full participation after the incident, and the contract's FG delay
    bound; `HealClassMono` states that the order implies inclusion of the classes;
  * `HealProfile`: Slice 0's heal claims (ready-reader safety from `healAt b₁ (hs q)`, transaction
    liveness from `healAt b₁ (hl q)` with delay `lat q·ΔAC`) on `HealClass`, per capability and
    index, for the readers ready with catch-up `q.catchUp·ΔAC`;
  * `HealDomainCoverage` (a representative of the class with the output provided and every finite
    claim active) and `HealBoundaryCoverage` (the same, and the witness attains the environment
    parameters, `Attains`), both on `HealQ.DomainFeasible`.

Bound inputs are environment quantities only: the activity measure and the hold read the
adversary's signatures and the network's receipts and releases, never the protocol's admission or
outputs. -/

namespace Consensus.Comparison

/-- **The incident classes of Slice 1.** `any` and `split G` are Slice 0's (`AsyncClass`).
`splitHeld G` is `split G` plus the content-origin hold (`ContentOriginHold`): no honest node of one
group receives during the incident, by any route, content that a validator of the other group first
released honestly in a release not owed by the synchronous prefix. -/
inductive IncidentClass (V : Type) where
  | any
  | split (G : V → Bool)
  | splitHeld (G : V → Bool)

namespace IncidentClass

variable {V : Type}

/-- The delivery guarantee of a class (Slice 0's `AsyncClass`): `splitHeld G` has the in-group
synchrony of `split G`; the hold is a separate clause (`HoldOn`). -/
def async : IncidentClass V → AsyncClass V
  | .any => .any
  | .split G => .split G
  | .splitHeld G => .split G

/-- The class order, from least to most adverse: `splitHeld G ≤ split G ≤ any`; two split classes
(held or not) are comparable only with the same groups. -/
def Le : IncidentClass V → IncidentClass V → Prop
  | _, .any => True
  | .split G, .split G' => G = G'
  | .splitHeld G, .split G' => G = G'
  | .splitHeld G, .splitHeld G' => G = G'
  | _, _ => False

instance : LE (IncidentClass V) := ⟨Le⟩

theorem le_def (a a' : IncidentClass V) : a ≤ a' ↔ Le a a' := Iff.rfl

/-- The groups of a split class are both nonempty; `any` has no groups and no condition. -/
def TwoGroups : IncidentClass V → Prop
  | .any => True
  | .split G => (∃ v, G v = true) ∧ ∃ v, G v = false
  | .splitHeld G => (∃ v, G v = true) ∧ ∃ v, G v = false

/-- The class is a split class (held or not). -/
def IsSplit : IncidentClass V → Prop
  | .any => False
  | .split _ => True
  | .splitHeld _ => True

end IncidentClass

section Generic

variable {V : Type} (S : System V)

/-- **Full participation after the incident**: every validator honest at a time of
`[max b₁ 0, horizon]` is awake then (the participation clause of `HealthyOn` from GST `b₁`). -/
def HonestAwakeAfter (b₁ : Time) (r : S.Run) : Prop :=
  ∀ v t, max b₁ 0 ≤ t → t ≤ (S.pt r).horizon → (S.pt r).HonestAt v t →
    (S.pt r).env.awake v t = true

variable [Fintype V] [DecidableEq V]

/-- **The validators that cannot vote during the incident** `[max b₀ 0, b₁)`, counted on the run's
point: those compromised by the horizon, and those honest and asleep at every time of the incident
window, provided the window is nonempty (`max b₀ 0 < b₁`; without the guard every honest validator
would qualify on an empty window). A validator asleep for only part of the incident is not counted:
it votes in its other slots. On an empty window this is `faultyAt horizon`. Under growing faults a
validator compromised by the horizon may have voted honestly before its compromise: the count is
not a bound on the historical honest support. -/
noncomputable def notAwakeHonest (b₀ b₁ : Time) (r : S.Run) : Finset V := by
  classical
  exact Finset.univ.filter fun v => v ∈ (S.pt r).faultyAt (S.pt r).horizon ∨
    (max b₀ 0 < b₁ ∧ ∀ t, max b₀ 0 ≤ t → t < b₁ →
      (S.pt r).HonestAt v t ∧ (S.pt r).env.awake v t = false)

end Generic

variable {V : Type}

/-- **Slice 1 heal parameters**: the incident length `L` (`b₁ − b₀ ≤ L·ΔAC`), the activity bounds
`hpre` (on `[0, max b₁ 0)`) and `hpost` (on `[max b₁ 0, horizon]`), a **lower** bound `m` on the
validators that cannot vote during the incident (`notAwakeHonest`), the fault cap `fcap`
(`faultCount horizon ≤ fcap`, the regime cap), the incident class `a`, and the readiness
parameters: the participation ratio `θ` and the catch-up `catchUp` (readers are the validators
ready with catch-up `catchUp·ΔAC`). The readiness parameters are coordinates of the point, not the
contract's numbers, so two protocols at one point are ranked on the same ready readers; a default
from a contract `K` is finite only at `K.θ ≤ θ` and `K.catchUp ≤ catchUp`. No Slice 1 claim or
class reads `θ` (the heal class has no sleepy participation clause); it is a coordinate so that the
parameter points of all profiles carry the same readiness. -/
structure HealQ (V : Type) where
  L : ℕ
  hpre : ℕ
  hpost : ℕ
  m : ℕ
  fcap : ℕ
  a : IncidentClass V
  θ : ℚ
  catchUp : ℕ

namespace HealQ

/-- **The coordinatewise order**, toward more adverse points: `L`, `hpre`, `hpost` and `fcap`
increase; `m` decreases (a lower bound on the validators that cannot vote: a smaller `m` admits
more runs); the class increases (`splitHeld G ≤ split G ≤ any`); `θ` decreases (a smaller ratio is
a weaker participation premise wherever one is read; none is in Slice 1); `catchUp` decreases (a
shorter catch-up makes more validators ready, `EnvPoint.Ready`, so the claims cover more readers).
It is not defined as class inclusion; `HealClassMono` states that it implies it (`θ` and `catchUp`
enter no class, only the claims' readers). -/
instance : LE (HealQ V) :=
  ⟨fun q q' => q.L ≤ q'.L ∧ q.hpre ≤ q'.hpre ∧ q.hpost ≤ q'.hpost ∧ q'.m ≤ q.m ∧
    q.fcap ≤ q'.fcap ∧ q.a ≤ q'.a ∧ q'.θ ≤ q.θ ∧ q'.catchUp ≤ q.catchUp⟩

theorem le_def (q q' : HealQ V) :
    q ≤ q' ↔ q.L ≤ q'.L ∧ q.hpre ≤ q'.hpre ∧ q.hpost ≤ q'.hpost ∧ q'.m ≤ q.m ∧
      q.fcap ≤ q'.fcap ∧ q.a ≤ q'.a ∧ q'.θ ≤ q.θ ∧ q'.catchUp ≤ q.catchUp :=
  Iff.rfl

/-- The readers' catch-up duration at point `q` in run `r` of `S`: `catchUp·ΔAC`. -/
def readerDur (q : HealQ V) (S : System V) (r : S.Run) : Time :=
  (q.catchUp : Time) * (S.pt r).env.ΔAC

/-- **The coverage domain**, a conservative subdomain of the points whose class is nonempty (domain
and boundary coverage need a witness only here):
* `hpre ≤ fcap` and `hpost ≤ fcap` (only compromised keys are active; a key may be active in both
  windows, so the sum is not bounded);
* `max m fcap + 2 ≤ n`: at least two validators are neither faulty nor whole-incident sleepers, so
  two ready readers remain;
* `L = 0` (no incident, `b₀ = b₁`) only with `any`, and then `m ≤ fcap` (the window is empty and
  `notAwakeHonest` is `faultyAt horizon`);
* a split class (held or not) needs `L ≥ 1` and two nonempty groups.

Points outside it may still have nonempty classes (an activity or fault cap above what any run
attains admits the runs of a smaller cap); coverage does not ask for them. At the level of the
point, the boundary conditions (positive sleepers need `L ≥ 1`; `n − fcap − s ≥ 2` with
`s = max m fcap − fcap`; two nonempty honest groups) are these conditions, so one predicate serves
both coverages. -/
def DomainFeasible [Fintype V] (q : HealQ V) : Prop :=
  q.hpre ≤ q.fcap ∧ q.hpost ≤ q.fcap ∧ max q.m q.fcap + 2 ≤ Fintype.card V ∧
    (q.L = 0 → q.m ≤ q.fcap) ∧ (q.a.IsSplit → 1 ≤ q.L) ∧ q.a.TwoGroups

end HealQ

open Consensus.Model

variable [Fintype V] [DecidableEq V] {O : OutputSchema} (F : ProtocolFamily O) {Prog : Type}
  (X : Progress (sysOf O F V) Prog) (K : Contract Prog)

/-- The hold clause of a class: the canonical content-origin hold for `splitHeld G`; nothing for
the other classes. -/
def HoldOn : IncidentClass V → Time → Time → (sysOf O F V).Run → Prop
  | .splitHeld G, b₀, b₁, r => contentHold F r G b₀ b₁
  | .any, _, _, _ => True
  | .split _, _, _, _ => True

/-- **Slice 1's run class** at `q` with incident `[b₀, b₁)` and role floors `fl`: the incident
geometry of the class's delivery guarantee and, for `splitHeld`, the content-origin hold;
`b₀ ≤ b₁` and `b₁ − b₀ ≤ L·ΔAC`; activity at most `hpre` on `[0, max b₁ 0)` and at most `hpost` on
`[max b₁ 0, horizon]`; at least `m` validators that cannot vote during the incident; at most `fcap`
compromised by the horizon; every validator honest after the incident awake then; and the
contract's FG delay bound `ΔFG ≤ fgDelay·ΔAC`. It mentions no bound, and neither `θ` nor
`catchUp`. -/
def HealClass (fl : RoleFloor F V) (q : HealQ V) (b₀ b₁ : Time) (r : (sysOf O F V).Run) : Prop :=
  IncidentNet (sysOf O F V) q.a.async b₀ b₁ r ∧ HoldOn F q.a b₀ b₁ r ∧ b₀ ≤ b₁ ∧
    b₁ - b₀ ≤ (q.L : Time) * ((sysOf O F V).pt r).env.ΔAC ∧
    activity F fl r 0 (max b₁ 0) ≤ q.hpre ∧
    activity F fl r (max b₁ 0) (((sysOf O F V).pt r).horizon + 1) ≤ q.hpost ∧
    q.m ≤ (notAwakeHonest (sysOf O F V) b₀ b₁ r).card ∧
    ((sysOf O F V).pt r).faultCount ((sysOf O F V).pt r).horizon ≤ q.fcap ∧
    HonestAwakeAfter (sysOf O F V) b₁ r ∧
    ((sysOf O F V).pt r).env.ΔFG ≤ (K.params.fgDelay : Time) * ((sysOf O F V).pt r).env.ΔAC

/-- **The order implies class inclusion**: for every model system, role floors, contract and
incident, a run of the class at `q` is a run of the class at every `q' ≥ q`. -/
def HealClassMono : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (O : OutputSchema) (F : ProtocolFamily O)
    (fl : RoleFloor F V) (Prog : Type) (K : Contract Prog) (q q' : HealQ V) (b₀ b₁ : Time)
    (r : (sysOf O F V).Run),
    q ≤ q' → HealClass F K fl q b₀ b₁ r → HealClass F K fl q' b₀ b₁ r

/-- **The Slice 1 heal profile** of capability `cap` at index `i`, with role floors `fl`,
safety-heal bound `hs`, liveness-heal bound `hl` and latency bound `lat`. On valid runs of the
class at `q` with the progress premise of `(cap, i)` (the contract's requirement, at its own
catch-up) from `ready` (at GST `b₁`) to the horizon, unless the run's excuse holds: the readers of
`cap`'s output ready with catch-up `q.catchUp·ΔAC` are safe from `healAt b₁ (hs q)`, and every
transaction submitted to an honest awake node is in the read of every such reader from
`max t (healAt b₁ (hl q)) + ΔAC + lat q·ΔAC`. A `⊤` bound claims nothing; `hl` and `lat` claim
even when `hs = ⊤`. The bounds are monotone in the adverse parameters. -/
structure HealProfile (fl : RoleFloor F V) (cap : Capability) (i : K.Idx)
    (hs hl lat : Bound (HealQ V)) : Prop where
  mono : AdverseMonotone hs ∧ AdverseMonotone hl ∧ AdverseMonotone lat
  safe : ∀ q (c : ℕ), hs q = c → ∀ g, (sysOf O F V).schema.output cap = some g → ∀ b₀ b₁,
    (sysOf O F V).Holds (fun r => HealClass F K fl q b₀ b₁ r ∧
        (sysOf O F V).prog X K cap i ((sysOf O F V).ready K b₁ r) ((sysOf O F V).pt r).horizon r)
      (fun r => ((sysOf O F V).trace r).ReadySafe (q.readerDur (sysOf O F V) r) g
        (healAt (sysOf O F V) b₁ c r))
  live : ∀ q (c d : ℕ), hl q = c → lat q = d → ∀ g, (sysOf O F V).schema.output cap = some g →
    ∀ b₀ b₁,
    (sysOf O F V).Holds (fun r => HealClass F K fl q b₀ b₁ r ∧
        (sysOf O F V).prog X K cap i ((sysOf O F V).ready K b₁ r) ((sysOf O F V).pt r).horizon r)
      (fun r => ((sysOf O F V).trace r).TxLive (q.readerDur (sysOf O F V) r) g
        (healAt (sysOf O F V) b₁ c r) ((d : Time) * ((sysOf O F V).pt r).env.ΔAC))

/-- **The witness attains the environment parameters** of `q` (not the bound values): the incident
length is exactly `L·ΔAC`; the activity is exactly `hpre` on `[0, max b₁ 0)` and exactly `hpost` on
`[max b₁ 0, horizon]`; exactly `fcap` validators are compromised by the horizon; exactly
`max m fcap` validators cannot vote during the incident (`notAwakeHonest` contains
`faultyAt horizon`, so the attained count is `fcap` plus exactly `max m fcap − fcap` honest
whole-incident sleepers); and the class is exercised (`Exercised` of its delivery class: for a
split class, both groups have a validator honest at the horizon, and a cross-group message is held
until `b₁`). -/
def Attains (fl : RoleFloor F V) (q : HealQ V) (b₀ b₁ : Time) (r : (sysOf O F V).Run) : Prop :=
  b₁ - b₀ = (q.L : Time) * ((sysOf O F V).pt r).env.ΔAC ∧
    activity F fl r 0 (max b₁ 0) = q.hpre ∧
    activity F fl r (max b₁ 0) (((sysOf O F V).pt r).horizon + 1) = q.hpost ∧
    ((sysOf O F V).pt r).faultCount ((sysOf O F V).pt r).horizon = q.fcap ∧
    (notAwakeHonest (sysOf O F V) b₀ b₁ r).card = max q.m q.fcap ∧
    Exercised (sysOf O F V) q.a.async b₀ b₁ r

/-- **Slice 1 domain coverage** of `(hs, hl, lat)` at `(cap, i)` with role floors `fl`: for every
point of the coverage domain with a finite safety bound, or finite liveness and latency bounds,
`cap`'s output is provided and the class at the point has a representative: a valid, excuse-free
run of the class with the profile's progress premise that makes every finite claim active for the
point's readers (`SafeActive` from the safety heal point; `TxLiveActive` from the liveness heal
point with delay `lat·ΔAC`). Shared across protocols: it reads the protocol only through which
bounds are finite. -/
structure HealDomainCoverage (fl : RoleFloor F V) (cap : Capability) (i : K.Idx)
    (hs hl lat : Bound (HealQ V)) : Prop where
  covers : ∀ q : HealQ V, q.DomainFeasible → (hs q < ⊤ ∨ (hl q < ⊤ ∧ lat q < ⊤)) →
    ((sysOf O F V).schema.output cap).isSome ∧
    ∃ r b₀ b₁, (sysOf O F V).Valid r ∧ ¬ (sysOf O F V).Excuse r ∧ HealClass F K fl q b₀ b₁ r ∧
      (sysOf O F V).prog X K cap i ((sysOf O F V).ready K b₁ r) ((sysOf O F V).pt r).horizon r ∧
      (∀ c : ℕ, hs q = c → SafeActive (q.readerDur (sysOf O F V) r)
        (healAt (sysOf O F V) b₁ c r) ((sysOf O F V).pt r)) ∧
      (∀ c d : ℕ, hl q = c → lat q = d →
        ((sysOf O F V).pt r).TxLiveActive (q.readerDur (sysOf O F V) r)
          (healAt (sysOf O F V) b₁ c r) ((d : Time) * ((sysOf O F V).pt r).env.ΔAC))

/-- **Slice 1 boundary coverage** of `(hs, hl, lat)` at `(cap, i)` with role floors `fl`: as
`HealDomainCoverage`, on the same coverage domain, and the witness attains the environment
parameters (`Attains`). -/
structure HealBoundaryCoverage (fl : RoleFloor F V) (cap : Capability) (i : K.Idx)
    (hs hl lat : Bound (HealQ V)) : Prop where
  covers : ∀ q : HealQ V, q.DomainFeasible → (hs q < ⊤ ∨ (hl q < ⊤ ∧ lat q < ⊤)) →
    ((sysOf O F V).schema.output cap).isSome ∧
    ∃ r b₀ b₁, (sysOf O F V).Valid r ∧ ¬ (sysOf O F V).Excuse r ∧ HealClass F K fl q b₀ b₁ r ∧
      (sysOf O F V).prog X K cap i ((sysOf O F V).ready K b₁ r) ((sysOf O F V).pt r).horizon r ∧
      Attains F fl q b₀ b₁ r ∧
      (∀ c : ℕ, hs q = c → SafeActive (q.readerDur (sysOf O F V) r)
        (healAt (sysOf O F V) b₁ c r) ((sysOf O F V).pt r)) ∧
      (∀ c d : ℕ, hl q = c → lat q = d →
        ((sysOf O F V).pt r).TxLiveActive (q.readerDur (sysOf O F V) r)
          (healAt (sysOf O F V) b₁ c r) ((d : Time) * ((sysOf O F V).pt r).env.ΔAC))

end Consensus.Comparison

end

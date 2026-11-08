module
public import ConsensusLean.Comparison.Basic

@[expose] public section

/-! # Slice 0 heal profile and its coverage (statements)

Slice 0 answers: how fast does a protocol heal after an incident of length `L` (asynchrony of class
`a` on `[b₀, b₁)`, `b₁ − b₀ ≤ L·ΔAC`) with at most `fcap` validators compromised by the horizon,
everyone awake (`FullAwake`)? It has no activity measure, no sleepers and no participation
parameter.

* `Slice0Q`: the parameters `⟨L, fcap, a⟩`, ordered coordinatewise (`L` and `fcap` increase, `split`
  below `any`); a larger point admits more runs (`Slice0ClassMono`, `Defaults.lean`).
* `Slice0Class`: the **bound-independent** run class (geometry, the fault cap, full participation
  and the contract's FG delay bound); no bound value enters it, so two bound functions are always
  compared on the same runs.
* `HealProfile0 S X K cap i hs hl lat`: at the contract's capability `cap` and index `i`, with the
  progress premise of `(cap, i)` from `ready` to the horizon, ready readers of `cap`'s output are
  safe from `healAt b₁ (hs q)` (`ReadySafe`), and transactions are live from `healAt b₁ (hl q)` with
  delay `lat q·ΔAC` (`TxLive`). The bounds are monotone in the adverse parameters.
* `HealCoverage0`: for every feasible point with a finite claim, the output is provided and a
  valid, excuse-free run
  attains the environment parameters (exact incident length, exact fault count, the class
  exercised) with the progress premise and every finite claim active (`SafeActive`,
  `TxLiveActive`). Coverage is a separate obligation, not a field of the profile.

The profile is per capability and index because the contract's heal points are
(`K.params.heal cap i`); a bound shared by every index would have no finite default for a contract
whose heal coefficient grows with the index. -/

namespace Consensus.Comparison

variable {V : Type}

/-- Slice 0 parameters: the incident length `L` (`b₁ − b₀ ≤ L·ΔAC`), the fault cap `fcap`
(`faultCount horizon ≤ fcap`) and the asynchrony class `a`. -/
structure Slice0Q (V : Type) where
  L : ℕ
  fcap : ℕ
  a : AsyncClass V

namespace Slice0Q

/-- The coordinatewise order: `L` and `fcap` increase, the class increases (`split` below
`any`). -/
instance : LE (Slice0Q V) := ⟨fun q q' => q.L ≤ q'.L ∧ q.fcap ≤ q'.fcap ∧ q.a ≤ q'.a⟩

theorem le_def (q q' : Slice0Q V) : q ≤ q' ↔ q.L ≤ q'.L ∧ q.fcap ≤ q'.fcap ∧ q.a ≤ q'.a :=
  Iff.rfl

variable [Fintype V]

/-- **Feasible points**: at least two validators stay honest (`fcap ≤ n − 2`, so two ready readers
remain for `SafeActive`); `split G` needs a positive incident length and two nonempty groups (so
`L = 0` only with `any`). Infeasible points need no coverage witness. -/
def Feasible (q : Slice0Q V) : Prop :=
  q.fcap + 2 ≤ Fintype.card V ∧
    match q.a with
    | .any => True
    | .split G => 1 ≤ q.L ∧ (∃ v, G v = true) ∧ ∃ v, G v = false

end Slice0Q

variable [Fintype V] [DecidableEq V] {Prog : Type} (S : System V) (X : Progress S Prog)
  (K : Contract Prog)

/-- **Slice 0's run class** at `q` with incident `[b₀, b₁)`: the incident geometry of class `q.a`,
`b₀ ≤ b₁` and `b₁ − b₀ ≤ L·ΔAC`, at most `fcap` validators compromised by the horizon, full
participation, and the contract's FG delay bound `ΔFG ≤ fgDelay·ΔAC`. It mentions no bound. -/
def Slice0Class (q : Slice0Q V) (b₀ b₁ : Time) (r : S.Run) : Prop :=
  IncidentNet S q.a b₀ b₁ r ∧ b₀ ≤ b₁ ∧ b₁ - b₀ ≤ (q.L : Time) * (S.pt r).env.ΔAC ∧
    (S.pt r).faultCount (S.pt r).horizon ≤ q.fcap ∧ FullAwake S r ∧
    (S.pt r).env.ΔFG ≤ (K.params.fgDelay : Time) * (S.pt r).env.ΔAC

/-- **The Slice 0 heal profile** of capability `cap` at index `i`, with safety-heal bound `hs`,
liveness-heal bound `hl` and latency bound `lat`. On valid runs of the class at `q` with the
progress premise of `(cap, i)` from `ready` (at GST `b₁`) to the horizon, unless the run's excuse
holds: ready readers of `cap`'s output are safe from `healAt b₁ (hs q)`, and every transaction
submitted to an honest awake node is in every ready read from
`max t (healAt b₁ (hl q)) + ΔAC + lat q·ΔAC`. A `⊤` bound claims nothing; `hl` and `lat` claim even
when `hs = ⊤`. -/
structure HealProfile0 (cap : Capability) (i : K.Idx) (hs hl lat : Bound (Slice0Q V)) : Prop where
  mono : AdverseMonotone hs ∧ AdverseMonotone hl ∧ AdverseMonotone lat
  safe : ∀ q (c : ℕ), hs q = c → ∀ g, S.schema.output cap = some g → ∀ b₀ b₁,
    S.Holds (fun r => Slice0Class S K q b₀ b₁ r ∧
        S.prog X K cap i (S.ready K b₁ r) (S.pt r).horizon r)
      (fun r => (S.trace r).ReadySafe (S.cDur K r) g (healAt S b₁ c r))
  live : ∀ q (c d : ℕ), hl q = c → lat q = d → ∀ g, S.schema.output cap = some g → ∀ b₀ b₁,
    S.Holds (fun r => Slice0Class S K q b₀ b₁ r ∧
        S.prog X K cap i (S.ready K b₁ r) (S.pt r).horizon r)
      (fun r => (S.trace r).TxLive (S.cDur K r) g (healAt S b₁ c r) ((d : Time) * (S.pt r).env.ΔAC))

/-- **The class is exercised** on run `r` with incident `[b₀, b₁)`. `any`: nothing beyond the exact
geometry (asked separately). `split G`: both groups have a validator honest at the horizon, and a
message is genuinely held across groups until `b₁`: a send at `t ∈ [b₀, b₁)` with
`t + ΔAC ≤ b₁`, by a node honest at `t`, of a message that is not an FG attestation, to a node of
the other group honest at `b₁` and awake throughout `[t, b₁]` that holds it at no time before
`b₁`. -/
def Exercised (a : AsyncClass V) (b₀ b₁ : Time) (r : S.Run) : Prop :=
  match a with
  | .any => True
  | .split G =>
    (∃ u, G u = true ∧ (S.pt r).HonestAt u (S.pt r).horizon) ∧
    (∃ u, G u = false ∧ (S.pt r).HonestAt u (S.pt r).horizon) ∧
    ∃ v w m t, G v ≠ G w ∧ (S.log r).sent v m t ∧ (S.pt r).HonestAt v t ∧ ¬ (S.log r).fgAtt m ∧
      b₀ ≤ t ∧ t + (S.pt r).env.ΔAC ≤ b₁ ∧ (S.pt r).HonestAt w b₁ ∧
      (S.pt r).AwakeOnClosed w t b₁ ∧ ∀ d, d < b₁ → ¬ (S.log r).Held (S.pt r) w m d

/-- **Slice 0 heal coverage** of `(hs, hl, lat)` at `(cap, i)`: for every feasible point with a
finite safety bound, or finite liveness and latency bounds, `cap`'s output is provided (a finite
claim about an absent output is vacuous, so it is never covered), and there is a valid, excuse-free
run of the class with the profile's progress premise that **attains the environment parameters**
(incident length exactly `L·ΔAC`, exactly `fcap` validators compromised by the horizon, the class
exercised) and makes every finite claim active: `SafeActive` from the safety heal point, and
`TxLiveActive` from the liveness heal point with delay `lat·ΔAC` (its deadline is
`max t start + ΔAC + D`, one `ΔAC` past `D`). Shared across protocols: it reads the protocol only
through which bounds are finite. -/
structure HealCoverage0 (cap : Capability) (i : K.Idx) (hs hl lat : Bound (Slice0Q V)) : Prop where
  covers : ∀ q : Slice0Q V, q.Feasible → (hs q < ⊤ ∨ (hl q < ⊤ ∧ lat q < ⊤)) →
    (S.schema.output cap).isSome ∧ ∃ r b₀ b₁, S.Valid r ∧ ¬ S.Excuse r ∧
      Slice0Class S K q b₀ b₁ r ∧
      S.prog X K cap i (S.ready K b₁ r) (S.pt r).horizon r ∧
      b₁ - b₀ = (q.L : Time) * (S.pt r).env.ΔAC ∧
      (S.pt r).faultCount (S.pt r).horizon = q.fcap ∧ Exercised S q.a b₀ b₁ r ∧
      (∀ c : ℕ, hs q = c → SafeActive (S.cDur K r) (healAt S b₁ c r) (S.pt r)) ∧
      (∀ c d : ℕ, hl q = c → lat q = d →
        (S.pt r).TxLiveActive (S.cDur K r) (healAt S b₁ c r) ((d : Time) * (S.pt r).env.ΔAC))

end Consensus.Comparison

end

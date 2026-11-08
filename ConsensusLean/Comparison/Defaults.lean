module
public import ConsensusLean.Comparison.Heal
public import ConsensusLean.Comparison.Latency

@[expose] public section

/-! # Slice 0: the order lemma and the defaults from the contract (statements)

* `Slice0ClassMono`: the coordinatewise order of `Slice0Q` implies inclusion of the run classes, so
  `AdverseMonotone` reads "a point admitting more runs never has a better bound".
* **Defaults** from the L0 property table (`Behaviour`, so from every `CorrectProtocol`):
  implication fields only; coverage is a separate obligation.
  * `HealDefault0`: at `(cap, i)`, `hs = K.params.heal cap i` for `cap` available or stable,
    `hl = K.params.heal cap i` and `lat = K.params.latency cap i` for every capability, at every
    point with `fcap < β·n` whatever `L` and the class; `⊤` elsewhere (and `hs = ⊤` for final). The
    proof instantiates `healedSafe` and `healthyLive` at GST `b₁`; healed safety needs progress only
    up to the heal point, which progress to the horizon gives when the heal point is within the
    horizon, and when it is past the horizon ready-reader safety from it is vacuous (every cut is
    within the horizon).
  * `TxLatencyDefault0`: from `sleepyLive`, `lat = K.params.latency cap i` for `cap` available or
    stable at every cap `f` with `θ·n < n − f` (full participation makes every validator honest at
    the look-ahead ready); `⊤` elsewhere. `sleepyLive` gives no proposal latency default. -/

namespace Consensus.Comparison

/-- **The order implies class inclusion**: a run of the class at `q` is a run of the class at every
`q' ≥ q`, for every system, contract and incident. -/
def Slice0ClassMono : Prop :=
  ∀ (V : Type) [Fintype V] (Prog : Type) (S : System V) (K : Contract Prog) (q q' : Slice0Q V)
    (b₀ b₁ : Time) (r : S.Run), q ≤ q' → Slice0Class S K q b₀ b₁ r → Slice0Class S K q' b₀ b₁ r

/-- **The synchronous class is monotone in the cap**: `f ≤ f'` includes the class at `f` in the
class at `f'`. -/
def Sync0ClassMono : Prop :=
  ∀ (V : Type) [Fintype V] (S : System V) (f f' : ℕ) (r : S.Run),
    f ≤ f' → Sync0Class S f r → Sync0Class S f' r

variable {V : Type} [Fintype V] {Prog : Type}

/-- The default safety-heal bound at `(cap, i)`: the contract's heal coefficient for an available
or stable `cap` at points with `fcap < β·n`; `⊤` elsewhere. -/
noncomputable def hsDefault (K : Contract Prog) (cap : Capability) (i : K.Idx) :
    Bound (Slice0Q V) := fun q =>
  if (cap = .available ∨ cap = .stable) ∧ (q.fcap : ℚ) < K.params.β * Fintype.card V then
    (K.params.heal cap i : WithTop ℕ) else ⊤

/-- The default liveness-heal bound at `(cap, i)`: the contract's heal coefficient at points with
`fcap < β·n`; `⊤` elsewhere. -/
noncomputable def hlDefault (K : Contract Prog) (cap : Capability) (i : K.Idx) :
    Bound (Slice0Q V) := fun q =>
  if (q.fcap : ℚ) < K.params.β * Fintype.card V then (K.params.heal cap i : WithTop ℕ) else ⊤

/-- The default latency bound after the heal point at `(cap, i)`: the contract's latency
coefficient at points with `fcap < β·n`; `⊤` elsewhere. -/
noncomputable def latDefault (K : Contract Prog) (cap : Capability) (i : K.Idx) :
    Bound (Slice0Q V) := fun q =>
  if (q.fcap : ℚ) < K.params.β * Fintype.card V then (K.params.latency cap i : WithTop ℕ) else ⊤

variable (V) in
/-- The default transaction latency at `(cap, i)`: the contract's latency coefficient for an
available or stable `cap` at caps `f` with `θ·n < n − f`; `⊤` elsewhere. -/
noncomputable def txLatDefault (K : Contract Prog) (cap : Capability) (i : K.Idx) : Bound ℕ :=
  fun f =>
    if (cap = .available ∨ cap = .stable) ∧
        K.params.θ * Fintype.card V < (Fintype.card V : ℚ) - f then
      (K.params.latency cap i : WithTop ℕ) else ⊤

/-- **The heal defaults** (`HealDefault0`): every system with the L0 property table has the Slice 0
heal profile `(hsDefault, hlDefault, latDefault)` at every capability and index. -/
def HealDefault0 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (Prog : Type) (S : System V) (X : Progress S Prog)
    (K : Contract Prog), Behaviour S X K → ∀ cap (i : K.Idx),
      HealProfile0 S X K cap i (hsDefault K cap i) (hlDefault K cap i) (latDefault K cap i)

/-- **The transaction latency default** (`TxLatencyDefault0`): every system with the L0 property
table has the Slice 0 transaction latency `txLatDefault` at every capability and index. -/
def TxLatencyDefault0 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (Prog : Type) (S : System V) (X : Progress S Prog)
    (K : Contract Prog), Behaviour S X K → ∀ cap (i : K.Idx),
      TxLatency0 S X K cap i (txLatDefault V K cap i)

end Consensus.Comparison

end

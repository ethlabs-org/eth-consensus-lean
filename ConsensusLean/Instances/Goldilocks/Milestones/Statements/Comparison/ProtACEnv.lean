module
public import ConsensusLean.Comparison.Protection
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.ACU

@[expose] public section

/-! # Tier A protection: the trace vocabulary (statements)

The environment of Tier A's protection class over AC traces of the Goldilocks SA
(`Comparison/ProtAC`), for a static honest set `H` (every validator outside `H` is faulty) on an
infinite trace (no horizon):

* service before `b₀`, cut at the receiver's deadline (`SyncUntilAC`): the AC counterpart of the
  delivery rule `Delivers (a + Δ − 1) b₀` (`Spec/Problem/Network`), owed only when the receiver's
  deadline is at most `b₀ + 1`, with messages processed since the receiver's latest restart;
* service from `b₁` (`PSyncAC`): `HealthyACCore`'s message and relay clauses at `g := b₁`
  verbatim, the relay from `b₁` of blocks accepted before it (`OlderRelayAC`) and the re-service of
  messages after restarts (`RewakeServiceAC`); no awake clause;
* the tick duty (`TickDuty`, `Driven.tick`'s shape) and time progress (`TimeProgressAC`);
* participation (`awakeAtAC`, `awakeInAC`, `lateWakersAC`, `NoSleepOnAC`, `CohortOnAC`,
  `ReadyAC`, `EtaSleepyAC`): `EnvPoint`'s predicates (`Spec/Problem/Basic`, `Regimes`) with the
  faulty set `Hᶜ` at every time, so `retain` is the identity; the windows `protStartAC`,
  `protEndAC` are K6's `protStart`, `protEnd` without the horizon clamps (the infinite-trace
  specialisation, not a consequence of static faults);
* the read of a validator at time `T` (`LastCallAt`, `ReadAC`): its confirmed tip from the state
  after its last call at or before `T`, with that call's frame, evaluated at `T`.

No equivalence with the generic `OutageNet` or `ProtClass` is claimed. Definitions only. -/

namespace Consensus.Goldilocks.Comparison

open SA Consensus.Comparison

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}

/-! ### Service -/

/-- **Service before `b₀`, cut at the deadline**: every AC message an honest `x` sends or admits
is processed by every honest `y` before `y`'s deadline and since `y`'s latest restart (no restart
of `y` between the processing and the call that reads it), and every block it accepts is accepted
by every honest `y` (inside `U` above `y`'s finalized tip) before `y`'s deadline, whenever that
deadline is at most `b₀ + 1`; read at every call of `y` at or after the deadline. A restart resets
the AC's pools but not the frame, so blocks need no re-acceptance after it (under trivial frames
the tree is genesis and every block accepted so far). -/
structure SyncUntilAC (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (b₀ : Time) : Prop where
  message : ∀ x ∈ H, ∀ i m, tr.SendOrAdmit x i m →
    ∀ y ∈ H, ∀ j ℓ, tr.CallAt y j ℓ → tr.deadline y j (tr.time i) ≤ tr.time j →
      tr.deadline y j (tr.time i) ≤ b₀ + 1 →
      ∃ k ≤ j, tr.time i ≤ tr.time k ∧ tr.ProcessAt y k m ∧
        tr.time k < tr.deadline y k (tr.time i) ∧ ∀ r, k < r → r ≤ j → ¬ tr.RestartAt y r
  relay : ∀ x ∈ H, ∀ i B, tr.AcceptAt x i B →
    ∀ y ∈ H, ∀ j ℓ, tr.CallAt y j ℓ → tr.deadline y j (tr.time i) ≤ tr.time j →
      tr.deadline y j (tr.time i) ≤ b₀ + 1 → Anc U ℓ.frame.F B →
      ∃ k ≤ j, tr.AcceptAt y k B ∧ tr.time k < tr.deadline y k (tr.time i)

/-- **The relay from `b₁` of older blocks**: every block an honest `x` accepted before `b₁` is
accepted by every honest `y` (inside `U` above its finalized tip) before `y`'s deadline from
`b₁`. -/
def OlderRelayAC (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (b₁ : Time) : Prop :=
  ∀ x ∈ H, ∀ i B, tr.AcceptAt x i B → tr.time i < b₁ →
    ∀ y ∈ H, ∀ j ℓ, tr.CallAt y j ℓ → tr.deadline y j b₁ ≤ tr.time j → Anc U ℓ.frame.F B →
      ∃ k ≤ j, tr.AcceptAt y k B ∧ tr.time k < tr.deadline y k b₁

/-- **Re-service of messages from `b₁` after restarts**: `HealthyACCore`'s message clause at
`g := b₁` with the processing since `y`'s latest restart (no restart of `y` between the
processing and the call that reads it). -/
def RewakeServiceAC (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (b₁ : Time) : Prop :=
  ∀ x ∈ H, ∀ i m, tr.SendOrAdmit x i m →
    ∀ y ∈ H, ∀ j ℓ, tr.CallAt y j ℓ → tr.deadline y j (max (tr.time i) b₁) ≤ tr.time j →
      ∃ k ≤ j, tr.time i ≤ tr.time k ∧ tr.ProcessAt y k m ∧
        tr.time k < tr.deadline y k (max (tr.time i) b₁) ∧
        ∀ r, k < r → r ≤ j → ¬ tr.RestartAt y r

/-- **Service from `b₁`**: `HealthyACCore`'s message and relay clauses at `g := b₁` (verbatim),
the relay from `b₁` of the blocks accepted before it, and the re-service of messages after
restarts. No awake clause. -/
structure PSyncAC (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (b₁ : Time) : Prop where
  message : ∀ x ∈ H, ∀ i m, tr.SendOrAdmit x i m →
    ∀ y ∈ H, ∀ j ℓ, tr.CallAt y j ℓ → tr.deadline y j (max (tr.time i) b₁) ≤ tr.time j →
      ∃ k ≤ j, tr.time i ≤ tr.time k ∧ tr.ProcessAt y k m ∧
        tr.time k < tr.deadline y k (max (tr.time i) b₁)
  relay : ∀ x ∈ H, ∀ i B, tr.AcceptAt x i B → b₁ ≤ tr.time i →
    ∀ y ∈ H, ∀ j ℓ, tr.CallAt y j ℓ → tr.deadline y j (tr.time i) ≤ tr.time j →
      Anc U ℓ.frame.F B → ∃ k ≤ j, tr.AcceptAt y k B ∧ tr.time k < tr.deadline y k (tr.time i)
  older : OlderRelayAC tr H U b₁
  rewake : RewakeServiceAC tr H b₁

/-! ### Driver and time -/

/-- **The tick duty** (`Driven.tick`): every honest node awake at a public time `t ≥ 0` runs its
tick at `t`. -/
def TickDuty (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) : Prop :=
  ∀ y ∈ H, ∀ t, 0 ≤ t → sp.toParams.IsPublic t → tr.awake y t →
    ∃ i ℓ, tr.CallAt y i ℓ ∧ ℓ.call = .tick ∧ tr.time i = t

/-- **Time progresses**: every time is exceeded by some cut (the infinite-trace
specialisation). With monotone cut times, which every run supplies (`ACLocalRun.time_mono`),
only finitely many cuts are then at or before any time. -/
def TimeProgressAC (tr : SATrace sp FGP ro) : Prop := ∀ t, ∃ i, t < tr.time i

/-! ### Participation (static faults) -/

/-- The start `a` of the no-sleep window: `noSleep·Δ` before `b₀`, at least `0`. -/
def protStartAC (sp : SAParams) (q : ProtQ) (b₀ : Time) : Time :=
  max 0 (b₀ - (q.noSleep : Time) * sp.Δ)

/-- The end `z` of the no-sleep window: `noSleep·Δ` after `b₁`. -/
def protEndAC (sp : SAParams) (q : ProtQ) (b₁ : Time) : Time := b₁ + (q.noSleep : Time) * sp.Δ

/-- The honest validators awake at `t`. -/
def awakeAtAC (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (t : Time) : Set (Fin sp.n) :=
  {y | y ∈ H ∧ tr.awake y t}

/-- The honest validators awake at some time of `[a, b]`. -/
def awakeInAC (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (a b : Time) : Set (Fin sp.n) :=
  {y | y ∈ H ∧ ∃ u, a ≤ u ∧ u ≤ b ∧ tr.awake y u}

/-- **The late wakers** of `[a, b]`: honest, awake in `[a, b]`, asleep at `a`. -/
def lateWakersAC (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (a b : Time) : Set (Fin sp.n) :=
  awakeInAC tr H a b \ awakeAtAC tr H a

/-- **No sleep on `[a, b]`**: an honest validator awake at `t ∈ [a, b]` stays awake through `b`. -/
def NoSleepOnAC (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (a b : Time) : Prop :=
  ∀ y ∈ H, ∀ t, a ≤ t → t ≤ b → tr.awake y t → ∀ u, t ≤ u → u ≤ b → tr.awake y u

/-- **The cohort margin**: the faulty validators and the late wakers of `[a, b]` are fewer than
the honest validators awake at `a`. -/
def CohortOnAC (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (a b : Time) : Prop :=
  (Hᶜ ∪ lateWakersAC tr H a b).ncard < (awakeAtAC tr H a).ncard

/-- **Ready at `t` with catch-up `c`**: honest, and awake throughout `[max 0 (t − c − 1), t]`
(`EnvPoint.Ready`). -/
def ReadyAC (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (c : Time) (y : Fin sp.n) (t : Time) :
    Prop :=
  y ∈ H ∧ ∀ τ, max 0 (t - c - 1) ≤ τ → τ ≤ t → tr.awake y τ

/-- The ready validators at `t`. -/
def readyAtAC (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (c t : Time) : Set (Fin sp.n) :=
  {y | ReadyAC tr H c y t}

/-- **η-sleepy from `0`** (`EnvPoint.EtaSleepyOn θ η c W 0 ⊤` with the faulty set `Hᶜ`): at every
`t ≥ 0`, the ready validators exceed fraction `θ` of the ready ones, the faulty ones and (for
`η > 0`) the honest validators awake in `[max 0 (t − η), t]`. -/
def EtaSleepyAC (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (θ : ℚ) (η c : Time) : Prop :=
  ∀ t, 0 ≤ t →
    if η ≤ 0 then
      θ * (((readyAtAC tr H c t).ncard + Hᶜ.ncard : ℕ) : ℚ) < (readyAtAC tr H c t).ncard
    else
      θ * ((readyAtAC tr H c t ∪ awakeInAC tr H (max 0 (t - η)) t ∪ Hᶜ).ncard : ℚ) <
        (readyAtAC tr H c t).ncard

/-! ### The read -/

/-- **`y`'s last call at or before `T`** is at cut `j`. -/
def LastCallAt (tr : SATrace sp FGP ro) (y : Fin sp.n) (j : Nat) (T : Time) : Prop :=
  (∃ ℓ, tr.CallAt y j ℓ) ∧ tr.time j ≤ T ∧
    ∀ j' ℓ', j < j' → tr.CallAt y j' ℓ' → T < tr.time j'

/-- **`y` reads `B` at time `T`**: `B` is the confirmed tip of `y`'s state after its last call at
or before `T`, with that call's frame, evaluated at `T`. A validator with no call by `T` reads
nothing; a ready one at a point with `catchUp ≥ 1` has a tick by `T` (`TickDuty`), and with time
progress its last call exists (a Lemmas fact, not part of this definition). -/
def ReadAC (tr : SATrace sp FGP ro) (y : Fin sp.n) (T : Time) (B : Blk sp.n FGP) : Prop :=
  ∃ j ℓ, LastCallAt tr y j T ∧ tr.CallAt y j ℓ ∧ B = acConfirmed sp (tr.post j) ℓ.frame T

end Consensus.Goldilocks.Comparison

end

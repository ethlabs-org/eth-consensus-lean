module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.Trace
public import ConsensusLean.Instances.Goldilocks.Spec.SA.Instance

@[expose] public section

/-! # Goldilocks SA: premises over SA traces

The premises of the AC step statements that read the SA's votes and its joining rule
(goldilocks-claims.tex §"Premises", §"L1: components / Available chain"), over an AC trace of
`goldilocksSA`:

* `JoinedAt tr y t`: `y` is joined at `t` (its latest restart at or before `t` is at or before
  `t_{slot(t)−1}`, or it never restarted); `honestAwakeJoined tr H t` counts the honest
  validators awake and joined at `t` (`h_t`), and `FaultBound tr H t` is `f < h_t` with `f` the
  number of faulty validators.
* `CarryAt` and `Carry`: `Carry_y(s, S, B)` for the votes `CV` counted for `B` in slot `s` (one
  counted vote per validator of `S`) and an honest `y` that votes in slot `s + 1`: `y` is awake
  and joined at its vote; before `t_s + 3Δ` it accepted the heads of the counted votes and their
  ancestors (inside `U`); and at its vote it holds, received before `t_s + 3Δ`, each counted vote
  or two other slot-`s` votes of that validator. `Carry(s, S, B)`: every honest vote of slot
  `s + 1` satisfies it.

The AC starts of the run records (`ACRun`, `ACRunU`, their growing forms, `GoldilocksRun`) are
starts up to the vote permission (`VoteStart`): the initial state with some own-role vote
permission installed; the initial state is one (`voteStart_initial`). -/

namespace Consensus.Goldilocks.SA

/-- **A start up to the vote permission**: the initial state `SAState.initial g` with some own-role
vote permission `m` installed (`VoteBinding.installVote` touches only `mayVote`). -/
def VoteStart {n : Nat} (g : Nat) (s : SAState n) : Prop :=
  ∃ m, s = { SAState.initial g with mayVote := m }

/-- The initial state is a start up to the vote permission. -/
theorem voteStart_initial {n : Nat} (g : Nat) : VoteStart g (SAState.initial g : SAState n) :=
  ⟨(SAState.initial g : SAState n).mayVote, rfl⟩

variable {FGP : Type} (sp : SAParams)

/-- An AC trace of the Goldilocks SA with the replay order `ro`. -/
abbrev SATrace (sp : SAParams) (FGP : Type) (ro : ReplayOrder sp FGP) :=
  ACTrace (goldilocksSA sp FGP ro)

variable {sp} {ro : ReplayOrder sp FGP}

/-- The vote emission `e` of `y` at cut `i`. -/
def VoteAt (tr : SATrace sp FGP ro) (y : Fin sp.n) (i : Nat) (e : Em sp FGP) : Prop :=
  ∃ ℓ, tr.CallAt y i ℓ ∧ e ∈ ℓ.emits

/-- `y` is joined at `t`: every restart of `y` at or before `t` is at or before
`t_{slot(t)−1}`. -/
def JoinedAt (tr : SATrace sp FGP ro) (y : Fin sp.n) (t : Time) : Prop :=
  ∀ k, tr.RestartAt y k → tr.time k ≤ t → tr.time k ≤ sp.ts ((sp.slot t : Int) - 1)

/-- `h_t`: the number of honest validators awake and joined at `t`. -/
noncomputable def honestAwakeJoined (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (t : Time) :
    Nat :=
  {y | y ∈ H ∧ tr.awake y t ∧ JoinedAt tr y t}.ncard

/-- `f < h_t`, with `f` the number of faulty (non-honest) validators. -/
def FaultBound (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (t : Time) : Prop :=
  Hᶜ.ncard < honestAwakeJoined tr H t

/-- `y` accepted `X` before `T`: `X` is genesis, or `y` accepted it at a cut before `T`. -/
def AcceptedBefore (tr : SATrace sp FGP ro) (y : Fin sp.n) (X : Blk sp.n FGP) (T : Time) : Prop :=
  X.root = sp.genesisRoot ∨ ∃ k, tr.AcceptAt y k X ∧ tr.time k < T

/-- The state `A` holds the vote `v`, received (or carried) before `T`. -/
def HeldBefore (A : SAState sp.n) (v : Vote sp.n) (T : Time) : Prop :=
  v ∈ A.pool v.slot ∧ A.voteStamp v < ETime.of T

/-- **`Carry_y(s, S, B)`** at the vote emission `e` of `y` at cut `i`, for the votes `CV`
counted in slot `s` (one per counted validator). -/
structure CarryAt (tr : SATrace sp FGP ro) (U : Set (Blk sp.n FGP)) (y : Fin sp.n) (i : Nat)
    (e : Em sp FGP) (s : Nat) (CV : Set (Vote sp.n)) : Prop where
  /-- `y` is awake at its vote. -/
  awake : tr.awake y (tr.time i)
  /-- `y` is joined at its vote. -/
  joined : joined sp e.readPoint (tr.time i)
  /-- Before `t_s + 3Δ`, `y` accepted the head of each counted vote and its ancestors. -/
  heads : ∀ v ∈ CV, ∃ Hv ∈ U, Hv.root = v.head ∧
    ∀ X, Anc U X Hv → AcceptedBefore tr y X (sp.ts s + 3 * sp.Δ)
  /-- At its vote, `y` holds, received before `t_s + 3Δ`, each counted vote or two other
  slot-`s` votes of its validator. -/
  holds : ∀ v ∈ CV, HeldBefore e.readPoint v (sp.ts s + 3 * sp.Δ) ∨
    ∃ v₁ v₂, v₁ ≠ v₂ ∧ v₁ ≠ v ∧ v₂ ≠ v ∧ v₁.val = v.val ∧ v₂.val = v.val ∧
      v₁.slot = s ∧ v₂.slot = s ∧
      HeldBefore e.readPoint v₁ (sp.ts s + 3 * sp.Δ) ∧
      HeldBefore e.readPoint v₂ (sp.ts s + 3 * sp.Δ)

/-- **`Carry(s, S, B)`**: `Carry_y(s, S, B)` at every honest vote of slot `s + 1`. -/
def Carry (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP)) (s : Nat)
    (CV : Set (Vote sp.n)) : Prop :=
  ∀ y ∈ H, ∀ i e, VoteAt tr y i e → e.msg.slot = s + 1 → CarryAt tr U y i e s CV

end Consensus.Goldilocks.SA

end

module
public import ConsensusLean.Comparison.Basic

@[expose] public section

/-! # Frontier lemmas: the overlap lemmas (statements)

Generic lower bounds on the heal point, over any `System`, so for every protocol at once. A protocol
that protects a ready source read `X` (every ready read of the target output from `t₀` on extends
`X`) cannot be safe for ready readers from a time `≤ t` if some ready reader reads, at a time `t`,
a ledger incompatible with `X`: a later ready read of the target extends `X`, and the incompatible
read conflicts with it. So the heal point is after `t`.

* `OverlapSameRun`: one run carries both claims, protection (`ProtectedReadyFrom` of `src` into
  `dst` from `t₀`, a ProtectionProfile's claim) and safety (`ReadySafe` of `dst` from
  `healAt b₁ k`, a HealProfile's claim); a ready source read at `T`, a ready reader whose read at a
  cut of time `t` is incompatible with it, and a ready target reader at `t′ ≥ max t₀ t`, within
  the horizon, give `t < healAt b₁ k`.
* `TargetObsThrough`: the common observation of a target reader in two runs: the same reads of
  every output and the same readiness at every time through `t′`.
* `OverlapTwoRun`: the transfer version, with the roles separated. Protection holds in `r₁`, where
  the source reader is ready at `T`; safety holds in `r₂`, where the divergent reader is ready at
  its read (it may be faulty in `r₁`); the target reader is ready in `r₁` at `t′` and observes the
  same in both runs through `t′` (so it is ready, hence honest, in `r₂` at `t′` too). Then
  `t < healAt b₁ k` in `r₂`. Equal reads alone do not transfer readiness, so the common
  observation includes it.

The lemmas take the profiles' claims, not their classes: whatever classes give protection in one
run and safety in the other, a run in both (or a twin pair) bounds the heal coefficient from below.
The twins themselves (the runs and the common observation, e.g. from a deterministic protocol on
equal inputs) are protocol-specific premises.

**Reads at cuts.** Safety reads at event cuts, checking each reader at its cut's time; protection
reads at the end of a time (`readAt`). The divergent read is at a cut `j` of time `t`. The target's
end-of-`t′` read is the read at the last cut at or before `t′`, so `t′` is required to be that
cut's time (some event occurs at `t′`): a reader that becomes ready between two events reads at
the end of `t′` the read of a cut at which it was not ready, and safety says nothing about it.
`t ≥ b₁` is not a premise: below `b₁` the conclusion holds anyway (`b₁ ≤ healAt b₁ k`, since
`ΔAC > 0`).

Statements only: the proofs are in `Proofs/Comparison`. -/

namespace Consensus.Comparison

/-- **Common observation of target reader `w` through `t′`** in runs `r₁` and `r₂` (catch-up
durations `c₁`, `c₂`): at every time `s ≤ t′`, `w` reads the same ledger of every output at the
end of `s` in both runs, and is ready at `s` in `r₁` iff it is ready at `s` in `r₂`. -/
def TargetObsThrough {V : Type} (S : System V) (c₁ c₂ : Time) (w : V) (t' : Time)
    (r₁ r₂ : S.Run) : Prop :=
  (∀ g s, s ≤ t' → (S.trace r₁).readAt g w s = (S.trace r₂).readAt g w s) ∧
    ∀ s, s ≤ t' → ((S.pt r₁).Ready c₁ w s ↔ (S.pt r₂).Ready c₂ w s)

/-- **Overlap lemma, same run.** For every system and run `r`, with catch-up duration `c`: if
every ready read of `dst` at times in `[t₀, horizon]` extends every ready read of `src` at `T`
(`ProtectedReadyFrom`), ready readers of `dst` are safe from `healAt b₁ k` (`ReadySafe`), `v` is
ready at `T`, `u` is ready at the time `t` of cut `j` and its read of `dst` there is incompatible
with `v`'s read of `src` at the end of `T`, and a target `w` is ready at a time `t′` with
`t₀ ≤ t′`, `t ≤ t′` and `t′ ≤ horizon` that is the time of its end-of-`t′` cut, then the heal point
is after `t`: `t < healAt b₁ k`. -/
def OverlapSameRun : Prop :=
  ∀ (V : Type) (S : System V) (r : S.Run) (c : Time) (src dst : S.schema.Id) (T t₀ b₁ : Time)
    (k : ℕ) (v u w : V) (j : ℕ) (t t' : Time),
    (S.trace r).ProtectedReadyFrom c src dst T t₀ →
    (S.trace r).ReadySafe c dst (healAt S b₁ k r) →
    (S.pt r).Ready c v T →
    j ≤ (S.trace r).cuts → (S.trace r).cutTime j = t → (S.pt r).Ready c u t →
    ¬ Compatible ((S.trace r).readAt src v T) ((S.trace r).read dst u j) →
    t₀ ≤ t' → t ≤ t' → t' ≤ (S.pt r).horizon → (S.pt r).Ready c w t' →
    (S.trace r).cutTime ((S.trace r).endCut t') = t' →
    t < healAt S b₁ k r

/-- **Overlap lemma, two runs, roles separated.** For every system and runs `r₁`, `r₂` (catch-up
durations `c₁`, `c₂`): if in `r₁` every ready read of `dst` at times in `[t₀, horizon]` extends
every ready read of `src` at `T` and the source reader `v` is ready at `T`; in `r₂` ready readers
of `dst` are safe from `healAt b₁ k`, and the divergent reader `u` is ready at the time `t` of cut
`j`, where its read of `dst` is incompatible with `v`'s read of `src` at the end of `T` in `r₁`;
and the target `w` is ready in `r₁` at a time `t′` with `t₀ ≤ t′`, `t ≤ t′` and `t′ ≤` the horizon
of `r₁`, has the same observation in both runs through `t′` (`TargetObsThrough`), and `t′` is the
time of its end-of-`t′` cut in `r₂`; then the heal point of `r₂` is after `t`:
`t < healAt b₁ k`. Nothing is assumed about `u` in `r₁` or about `v` in `r₂`. -/
def OverlapTwoRun : Prop :=
  ∀ (V : Type) (S : System V) (r₁ r₂ : S.Run) (c₁ c₂ : Time) (src dst : S.schema.Id)
    (T t₀ b₁ : Time) (k : ℕ) (v u w : V) (j : ℕ) (t t' : Time),
    (S.trace r₁).ProtectedReadyFrom c₁ src dst T t₀ →
    (S.pt r₁).Ready c₁ v T →
    (S.trace r₂).ReadySafe c₂ dst (healAt S b₁ k r₂) →
    j ≤ (S.trace r₂).cuts → (S.trace r₂).cutTime j = t → (S.pt r₂).Ready c₂ u t →
    ¬ Compatible ((S.trace r₁).readAt src v T) ((S.trace r₂).read dst u j) →
    t₀ ≤ t' → t ≤ t' → t' ≤ (S.pt r₁).horizon → (S.pt r₁).Ready c₁ w t' →
    TargetObsThrough S c₁ c₂ w t' r₁ r₂ →
    (S.trace r₂).cutTime ((S.trace r₂).endCut t') = t' →
    t < healAt S b₁ k r₂

end Consensus.Comparison

end

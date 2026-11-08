module
public import ConsensusLean.Instances.Goldilocks.Spec.WeightedLocks.Evidence

@[expose] public section

/-! # The one release: an unlock stage with the release threshold capped at half the committee

A candidate unlock stage on weighted locks (`wlockStore`): a lock of a slot below `s` whose parent
unlock target is `T` moves to the deepest block `Y ⪯ T` of the tree with
`|evidence(Y)| < min(W(Y), μ_r)`, or to `Φ.F` when there is none (`oneReleaseTarget`), where `W`
is the lock's weight and `μ_r = ⌈n/2⌉` (`releaseMu`, the committee is all of `V`). It is
evidence-release's target (`evidenceTarget`) for the lock with its weight capped at `μ_r`
(`capWeight`), so the evidence, the weights and the fallback are evidence-release's.

**Reading of the rule.** The rule is written as a stage after the parent's unlock
(`LockStore.unlockWith`), as every stage is. The code it reads replaces the parent's unlock: it
scans the ancestors of the lock's block `B` for the deepest `Y` with the condition. The two
agree: the opponents of `Y` are evidence against it, so `|evidence(Y)| < ⌈n/2⌉` gives
`2·|opponents(Y)| < n`, every such `Y ⪯ B` passes the parent's test, and so lies at or above the
parent's target `T`. That the deepest such `Y ⪯ B` is `oneReleaseTarget … T` is a lemma
(`Lemmas/Candidates/PreConfirmations`), not a definition.

Definitions only; the stage's laws (`UnlockStage.Lawful`, `UnlockStage.Fixes`) are proved in
`Lemmas/Candidates/PreConfirmations`. -/

namespace Consensus.Goldilocks.PreConfirmations

open SA EvidenceRelease

variable (sp : SAParams) {FGP : Type}

/-- The release threshold `μ_r = ⌈n/2⌉` of the one release (full committees). -/
def releaseMu : Nat := (sp.n + 1) / 2

/-- A weighted lock with its weight capped at `μ`, by block root. -/
def capWeight (μ : Nat) (w : WLock) : WLock :=
  { w with weight := fun r => min (w.weight r) μ }

/-- Where the one release moves a lock of weight `w` from `T`: the deepest block `Y ⪯ T` of the
tree with `|evidence(Y)| < min(W(Y), μ_r)`, or `Φ.F`. -/
noncomputable def oneReleaseTarget (Φ : Frm sp.n FGP) (V : View sp.n) (s : Int) (w : WLock)
    (T : Blk sp.n FGP) : Blk sp.n FGP :=
  evidenceTarget sp Φ V s (capWeight (releaseMu sp) w) T

/-- The one release as an unlock stage (no context). -/
noncomputable def oneReleaseStage : UnlockStage sp wlockStore Unit where
  target _ Φ V s w T := oneReleaseTarget sp Φ V s w T

end Consensus.Goldilocks.PreConfirmations

end

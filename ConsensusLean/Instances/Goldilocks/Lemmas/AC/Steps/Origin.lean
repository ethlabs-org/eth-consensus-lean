module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission

public section

/-! # Goldilocks SA: where every lock comes from

Like `Steps/Provenance` (fast locks), for every lock, fast or slow, and also at a vote's read
point: every lock sits below (inside `U`) the block of a lock of its slot that the node wrote by
an optimistic confirmation (`OptimisticLockAt`) or by the update of that slot (`UpdateAt`, at
`t_s + 6Δ`), at a cut no later than the vote's. The lock functions only move locks back (A0.4
(c)), a restart keeps them (A0.7), and the optimistic check and the update are the only writers.
A1.3's lock analysis reads it: a lock of slot `m` or `m + 1` at a slot-`(m+1)` vote is an
optimistic one. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}

/-- `x` writes a lock of slot `s` on `D` at cut `j`: by an optimistic confirmation, or by the
update of slot `s` (which writes its fast and slow locks on blocks of the result's path). -/
def LockOrigin (tr : SATrace sp FGP ro) (x : Fin sp.n) (j s : Nat) (D : Blk sp.n FGP) : Prop :=
  (∃ CV, OptimisticLockAt tr x j s D CV) ∨ ∃ ℓ, UpdateAt tr x j s ℓ

/-- **Lock origin at a vote.** Every lock at the read point of an honest vote sits below the
block of a lock of its slot that the voter wrote at a cut no later than the vote's. -/
theorem lock_origin_readPoint (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    {e : Em sp FGP} (hc : CastAt tr y i ℓ e) :
    ∀ l ∈ e.readPoint.locks, ∃ j ≤ i, ∃ D, LockOrigin tr y j l.slot D ∧
      ∃ L ∈ U, L.root = l.block ∧ Anc U L D := by
  sorry

end Consensus.Goldilocks.SA

end

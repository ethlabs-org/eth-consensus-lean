module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain

public section

/-! # Goldilocks SA: when `unlock` leaves a lock in place

`unlockTarget(Φ, V, s, B)` is the deepest ancestor `B'` of `B` in the tree with
`2 · |opponents(Φ, V, s, B')| < committeeSize`, or `Φ.F`. So:

* `unlockTarget_eq_self`: if `B` has fewer than half the committee as opponents, the target is `B`;
* `unlockTarget_eq_self_of_subset`: the same when the opponents lie in a set smaller than
  half the committee.

`opponents` contains the equivocators of `V.votes`, and `V` is arbitrary, so a hypothesis
`∀ V, unlockTarget sp Φ V s B = B` can hold only for `B = Φ.F` in general (a view where every
validator equivocates has no block with few opponents). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {Φ : Frm sp.n FGP}

/-- **`unlock` keeps a block with few opponents.** If `B` is in the tree and fewer than half of
the committee oppose `B` in `V` against the slot-`s` votes, then `unlockTarget` of `B` is `B`. -/
theorem unlockTarget_eq_self (hΦ : FrameOK Φ) (V : View sp.n) (s : Int) {B : Blk sp.n FGP}
    (hB : B ∈ Φ.tree) (hopp : 2 * (opponents sp Φ V s B).ncard < sp.committeeSize) :
    unlockTarget sp Φ V s B = B := by
  have hS : {B' | B' ∈ Φ.tree ∧ Φ.Anc B' B ∧ 2 * (opponents sp Φ V s B').ncard < sp.committeeSize} ⊆
      Φ.tree := fun X hX => hX.1
  have hBS : B ∈
      {B' | B' ∈ Φ.tree ∧ Φ.Anc B' B ∧ 2 * (opponents sp Φ V s B').ncard < sp.committeeSize} :=
    ⟨hB, .refl, hopp⟩
  obtain ⟨D, hD⟩ := exists_deepest hΦ hS ⟨B, hBS⟩
  have hBD := anc_deepest hΦ hS (fun X hX C hC => anc_total hΦ.coherent hX.2.1 hC.2.1) hD B
    hBS
  unfold unlockTarget
  rw [hD, Option.getD_some]
  exact Anc.antisymm hΦ.coherent (deepest_mem hD).1.2.1 hBD

/-- `unlockTarget_eq_self` when the opponents of `B` in `V` lie in a set `O` with
`2 · |O| < committeeSize`. -/
theorem unlockTarget_eq_self_of_subset (hΦ : FrameOK Φ) (V : View sp.n) (s : Int)
    {B : Blk sp.n FGP} (hB : B ∈ Φ.tree) {O : Set (Fin sp.n)}
    (hO : opponents sp Φ V s B ⊆ O) (hOn : 2 * O.ncard < sp.committeeSize) :
    unlockTarget sp Φ V s B = B :=
  unlockTarget_eq_self hΦ V s hB
    (lt_of_le_of_lt (Nat.mul_le_mul_left 2 (Set.ncard_le_ncard hO O.toFinite)) hOn)

end Consensus.Goldilocks.SA

end

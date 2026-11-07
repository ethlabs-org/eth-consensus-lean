module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.LeftEntry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.LowFinalized
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HalfCommittee
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HeldRoots

public section

/-! # Frozen growing interface of the retained-origin transports

The growing forms of the retention transports of `Healing/Retention/{Boot,Prefix,Finality}`
that the clean cluster and its consumers read, frozen under their final names (static name +
`_at`). Each node is honest at its own cut; a reader of a held state is honest at an observation
time `t` after the state's cuts. Beyond the static statements, they add only the fault-count
bounds `≤ b`, because growing faults are counted only through the horizon:

* `low_finalized_below_origin_at` (`left_entry_origin_at` is proved in `Clean/LeftEntry`);
* `high_J_root_of_held_at_call_before_at`, `low_root_of_held_seed_at_call_at`;
* `high_floor_signed_source_of_row_bound_at`;
* `half_committee_at`: the voters of slot `m` honest at a later observation `t ≤ b` are half
  the committee.

Each theorem here is an open `sorry`; this module is deleted when the proofs land. -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- **A high floor has a signed source below a bounded row label**: for a reader honest at
`t ≤ b`, a high origin under the reader's head-height floor yields a high origin, of a label
below `u`, above an entry at or past the floor, signed by the origin's writer after the write. -/
theorem high_floor_signed_source_of_row_bound_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x y : Fin sp.n} {i j k : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) {t : Time} (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t)
    (hy : y ∈ H t) (htb : t ≤ b) {u : Nat}
    (hrow : ∀ W ∈ (tr.state y k).fg.tree, ∀ att ∈ W.fgPayload,
      ∀ v d, v ∈ H (tr.time d) → tr.SignAt v d att → d < k → ∀ r l O,
        r < d → HighOrigin tr H g v r l O → l < u)
    (hpair : ∀ v r l O, r < k → HighOrigin tr H g v r l O →
      ∀ v' r' l' O', r' < k → HighOrigin tr H g v' r' l' O' →
      Compatible (tr.HonestBlocksAt H) O O')
    (hcomp : ∀ v r l O, r < k → HighOrigin tr H g v r l O →
      Compatible (tr.HonestBlocksAt H) B O)
    (hfloor : ((tr.state x i).fg.σ B.root).h < (tr.state y k).fg.headHeightFloor) :
    ∃ v r l O E, r < k ∧ HighOrigin tr H g v r l O ∧ l < u ∧
      E ∈ (tr.state y k).fg.tree ∧ Anc (tr.HonestBlocksAt H) E O ∧
      Anc (tr.HonestBlocksAt H) B O ∧
      (tr.state y k).fg.headHeightFloor ≤ ((tr.state y k).fg.σ E.root).h ∧
      ∃ d att, r < d ∧ d < k ∧ v ∈ H (tr.time d) ∧ tr.SignAt v d att ∧ att.T = E.root := by
  sorry

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end

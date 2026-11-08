module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Healed

public section

/-! # The healed record cover (continuation vocabulary)

After a hand-over at `T`, the sleepy invariant from genesis is false: before GST, honest
confirmations, locks and FG attestations can sit on conflicting branches. The continuation proof
carries a frontier relative to two label floors instead: the healed family of
`Lemmas/Growing/Sleepy/Node/Healed` (`HealedOrigin`, `OnHealedChain`, `HealedOriginsBelow`,
`HealedVotesBelow`), with the lock floor `rL = cleanLabel a + k + 2` and the origin floor
`rO = rL + k − 1 = cleanLabel a + 2k + 1` for the reset `a` (`Healing.cleanLabel`).

* `HealedRecordCoverAt`: a record is the reader's finalized block, or an ancestor of an origin of
  label `≥ rO` written before the read.

**Why two floors.** Up to the reset's healthy bound, the reset premises have every later honest
vote extend a lock write of label `≥ cleanLabel + k + 2` (`fast_source_votes_before_at`,
`slow_source_votes_before_at`), because its whole slow window is clean. A result is extended by
every later honest vote only from `cleanLabel + 2k + 1` on (`clean_result_prefix_votes_before_at`),
and two origins compare only from there (`clean_sources_compatible_at`). -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
variable (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))

/-- **The healed record cover** at the origin floor `rO`: the record `R` of `y` before cut `n`,
read at `t`, is its finalized block, or an ancestor (inside the blocks held while honest) of a
result or optimistic selection of label `≥ rO` by a node honest at its cut, before `n` and no later
than `t`. -/
def HealedRecordCoverAt (rO : Nat) (y : Fin sp.n) (n : Nat) (t : Time)
    (R : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  R = (tr.state y n).fg.F ∨ ∃ x q s C CV, x ∈ H (tr.time q) ∧ q < n ∧ tr.time q ≤ t ∧ rO ≤ s ∧
    (SA.ResultAt tr.projAC x q s C CV ∨ SA.OptimisticLockAt tr.projAC x q s C CV) ∧
    Anc (tr.HonestBlocksAt H) R C

variable {tr H}

theorem healedRecordCoverAt_iff {rO : Nat} {y : Fin sp.n} {n : Nat} {t : Time}
    {R : SA.Blk sp.n (List (FG.Att sp.n))} :
    HealedRecordCoverAt tr H rO y n t R ↔
      R = (tr.state y n).fg.F ∨ ∃ x q s C CV, x ∈ H (tr.time q) ∧ q < n ∧ tr.time q ≤ t ∧ rO ≤ s ∧
        (SA.ResultAt tr.projAC x q s C CV ∨ SA.OptimisticLockAt tr.projAC x q s C CV) ∧
        Anc (tr.HonestBlocksAt H) R C :=
  Iff.rfl

end Consensus.Goldilocks.Compose.Growing

end

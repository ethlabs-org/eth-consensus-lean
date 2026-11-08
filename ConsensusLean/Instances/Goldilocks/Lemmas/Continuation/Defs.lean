module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Healed
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Growing.Run
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.AC

public section

/-! # The healed family (continuation vocabulary)

After a hand-over at `T`, the sleepy invariant from genesis is false: before GST, honest
confirmations, locks and FG attestations can sit on conflicting branches. The continuation proof
carries a frontier relative to two label floors instead: a lock floor `rL` and an origin floor
`rO`. At the hand-over, `rL = cleanLabel a + k + 2` and `rO = rL + k − 1 = cleanLabel a + 2k + 1`
for the reset `a` (`Healing.cleanLabel`). From genesis both floors are `0`.

* `LockWithin` (`Sleepy/Node/Healed`): a fast or slow lock write of label `s` on a block, by a
  writer honest at its write, at a time `≤ b`.
* `HealedOrigin g rL rO C s b`, **the healed family**: an origin (`OriginWithin`) of label
  `≥ rO`, a lock write of label `≥ rL`, or the block of a high origin
  (`Healing.Growing.HighOrigin`) of label `s` written at a time `≤ b`.
* `OnHealedChain`: an ancestor, inside the blocks held while honest, of a family member.
* `HealedOriginsBelow` (`P_s`) and `HealedVotesBelow` (`V_s`) from the floors, up to `b`.
* `HealedRecordCoverAt`: a record is the reader's finalized block, or an ancestor of an origin of
  label `≥ rO` written before the read.

**Why two floors.** Up to the reset's healthy bound, the reset premises have every later honest
vote extend a lock write of label `≥ cleanLabel + k + 2` (`fast_source_votes_before_at`,
`slow_source_votes_before_at`), because its whole slow window is clean. A result is extended by
every later honest vote only from `cleanLabel + 2k + 1` on (`clean_result_prefix_votes_before_at`),
and two origins compare only from there (`clean_sources_compatible_at`). The first transfer of a
result of label `s` needs every lock live at the slot-`(s+1)` vote to compare with the result. Those
locks have labels down to `s + 1 − k`, and from the lock floor on they are known to compare. A
result's confirmation may conflict with locks, so a result gets no lower floor. A lock of label
`≥ rO` is a prefix of an origin of its label, so above `rO` the lock members add no constraint.
-/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
variable (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))

/-- **The healed family** of label `s` within `b`, from the lock floor `rL` and the origin floor
`rO`: an origin of label `≥ rO`, a lock write of label `≥ rL`, or the block of a high origin of
label `s` written at a time `≤ b`. At the hand-over `rO = rL + k − 1`. A result's later honest
votes respect the locks live at them, whose labels reach `k` below the vote, and only from the lock
floor on are those locks known to compare with the result. -/
def HealedOrigin (g : Time) (rL rO : Nat) (C : SA.Blk sp.n (List (FG.Att sp.n))) (s : Nat)
    (b : Time) : Prop :=
  (rO ≤ s ∧ OriginWithin tr H C s b) ∨ (rL ≤ s ∧ LockWithin tr H C s b) ∨
    ∃ x i, tr.time i ≤ b ∧ Healing.Growing.HighOrigin tr H g x i s C

/-- `B` is an ancestor, inside the blocks held while honest, of a member of the healed family
within `b`. -/
def OnHealedChain (g : Time) (rL rO : Nat) (B : SA.Blk sp.n (List (FG.Att sp.n))) (b : Time) :
    Prop :=
  ∃ C s, HealedOrigin tr H g rL rO C s b ∧ Anc (tr.HonestBlocksAt H) B C

/-- **`P_s` from the floors `rL`, `rO` up to `b`**: members of the healed family within `b` of
labels below `s` are pairwise compatible. -/
def HealedOriginsBelow (g : Time) (rL rO s : Nat) (b : Time) : Prop :=
  ∀ C j C' j', j < s → j' < s → HealedOrigin tr H g rL rO C j b →
    HealedOrigin tr H g rL rO C' j' b → Compatible (tr.HonestBlocksAt H) C C'

/-- **`V_s` from the floors `rL`, `rO` up to `b`**: every honest vote at a time `≤ b` of a slot
`m` with `j < m ≤ s` extends every member of the healed family within `b` of label `j`. -/
def HealedVotesBelow (g : Time) (rL rO s : Nat) (b : Time) : Prop :=
  ∀ C j, HealedOrigin tr H g rL rO C j b → ∀ y i e, HVoteAt tr H y i e → tr.time i ≤ b →
    j < e.msg.slot → e.msg.slot ≤ s → SA.VoteExtends (tr.HonestBlocksAt H) e.msg C

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

theorem healedOrigin_iff {g : Time} {rL rO : Nat} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    {s : Nat} {b : Time} :
    HealedOrigin tr H g rL rO C s b ↔
      (rO ≤ s ∧ OriginWithin tr H C s b) ∨ (rL ≤ s ∧ LockWithin tr H C s b) ∨
        ∃ x i, tr.time i ≤ b ∧ Healing.Growing.HighOrigin tr H g x i s C :=
  Iff.rfl

theorem onHealedChain_iff {g : Time} {rL rO : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    {b : Time} :
    OnHealedChain tr H g rL rO B b ↔
      ∃ C s, HealedOrigin tr H g rL rO C s b ∧ Anc (tr.HonestBlocksAt H) B C :=
  Iff.rfl

theorem healedOriginsBelow_iff {g : Time} {rL rO s : Nat} {b : Time} :
    HealedOriginsBelow tr H g rL rO s b ↔
      ∀ C j C' j', j < s → j' < s → HealedOrigin tr H g rL rO C j b →
        HealedOrigin tr H g rL rO C' j' b → Compatible (tr.HonestBlocksAt H) C C' :=
  Iff.rfl

theorem healedVotesBelow_iff {g : Time} {rL rO s : Nat} {b : Time} :
    HealedVotesBelow tr H g rL rO s b ↔
      ∀ C j, HealedOrigin tr H g rL rO C j b → ∀ y i e, HVoteAt tr H y i e → tr.time i ≤ b →
        j < e.msg.slot → e.msg.slot ≤ s → SA.VoteExtends (tr.HonestBlocksAt H) e.msg C :=
  Iff.rfl

theorem healedRecordCoverAt_iff {rO : Nat} {y : Fin sp.n} {n : Nat} {t : Time}
    {R : SA.Blk sp.n (List (FG.Att sp.n))} :
    HealedRecordCoverAt tr H rO y n t R ↔
      R = (tr.state y n).fg.F ∨ ∃ x q s C CV, x ∈ H (tr.time q) ∧ q < n ∧ tr.time q ≤ t ∧ rO ≤ s ∧
        (SA.ResultAt tr.projAC x q s C CV ∨ SA.OptimisticLockAt tr.projAC x q s C CV) ∧
        Anc (tr.HonestBlocksAt H) R C :=
  Iff.rfl

theorem HealedOrigin.mono {g : Time} {rL rO : Nat} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    {s : Nat} {b b' : Time} (h : HealedOrigin tr H g rL rO C s b) (hb : b ≤ b') :
    HealedOrigin tr H g rL rO C s b' := by
  rcases h with ⟨hs, h⟩ | ⟨hs, h⟩ | ⟨x, i, hi, h⟩
  · exact Or.inl ⟨hs, h.mono hb⟩
  · exact Or.inr (Or.inl ⟨hs, h.mono hb⟩)
  · exact Or.inr (Or.inr ⟨x, i, hi.trans hb, h⟩)

/-- An origin of label at least the origin floor is in the healed family. -/
theorem HealedOrigin.of_origin {g : Time} {rL rO : Nat} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    {s : Nat} {b : Time} (hs : rO ≤ s) (h : OriginWithin tr H C s b) :
    HealedOrigin tr H g rL rO C s b :=
  Or.inl ⟨hs, h⟩

/-- A lock write of label at least the lock floor is in the healed family. -/
theorem HealedOrigin.of_lock {g : Time} {rL rO : Nat} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    {s : Nat} {b : Time} (hs : rL ≤ s) (h : LockWithin tr H C s b) :
    HealedOrigin tr H g rL rO C s b :=
  Or.inr (Or.inl ⟨hs, h⟩)

/-- A high origin written at a time `≤ b` is in the healed family, at all floors. -/
theorem HealedOrigin.of_high {g : Time} {rL rO : Nat} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    {s : Nat} {b : Time} {x : Fin sp.n} {i : Nat} (hi : tr.time i ≤ b)
    (h : Healing.Growing.HighOrigin tr H g x i s C) : HealedOrigin tr H g rL rO C s b :=
  Or.inr (Or.inr ⟨x, i, hi, h⟩)

end Consensus.Goldilocks.Compose.Growing

end

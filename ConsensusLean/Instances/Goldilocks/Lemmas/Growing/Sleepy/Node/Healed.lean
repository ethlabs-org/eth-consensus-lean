module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.AC
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Growing.Run

public section

/-! # Goldilocks under `Sleepy` with growing faults: the healed family

The label induction of the sleepy proof, over a family of blocks that starts at two label floors:
a lock floor `rL` and an origin floor `rO`. From genesis both floors are `0`; after a hand-over
(`Lemmas/Continuation`), `rL = cleanLabel a + k + 2` and `rO = rL + k − 1` for the reset `a`.

* `LockWithin`: a fast or slow lock write of label `s` on a block, by a writer honest at its
  write, at a time `≤ b`. Every stored lock of an honest node sits below its own lock write of the
  lock's slot (`lock_write_at`, `Node/Lift`), and each lock write sits below an origin of its label
  written at the same cut (`lock_below_origin_at`).
* `HealedOrigin g rL rO C s b`, **the healed family**: an origin (`OriginWithin`) of label `≥ rO`,
  a lock write of label `≥ rL`, or the block of a high origin (`Healing.Growing.HighOrigin`) of
  label `s` written at a time `≤ b`.
* `OnHealedChain`: an ancestor, inside the blocks held while honest, of a family member.
* `HealedOriginsBelow` (`P_s`) and `HealedVotesBelow` (`V_s`) from the floors, up to `b`.

**Why two floors.** A live lock at a vote is compared through its writer's lock write, whose label
is the lock's slot; the drain bounds that label from below, so lock writes enter the family from
`rL`. A result's first transfer needs every lock live at the next vote to compare with it, and
those locks reach `k` labels below the vote; so results enter only from `rO = rL + k − 1`. A lock
of label `≥ rO` is a prefix of an origin of its label, so above `rO` the lock members add no
constraint. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
variable (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))

/-- **A lock write within `b`**: a fast lock (a fast update or an optimistic selection) or a slow
lock of label `s` on the block `C`, written at cut `i` by a writer `x` honest at that cut, at a
time `≤ b`. -/
def LockWithin (C : SA.Blk sp.n (List (FG.Att sp.n))) (s : Nat) (b : Time) : Prop :=
  ∃ x i, x ∈ H (tr.time i) ∧ tr.time i ≤ b ∧
    ((∃ CV, SA.FastLockAt tr.projAC x i s C CV) ∨ SA.SlowLockAt tr.projAC x i s C)

/-- **The healed family** of label `s` within `b`, from the lock floor `rL` and the origin floor
`rO`: an origin of label `≥ rO`, a lock write of label `≥ rL`, or the block of a high origin of
label `s` written at a time `≤ b`. -/
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

variable {tr H}

theorem lockWithin_iff {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} {b : Time} :
    LockWithin tr H C s b ↔ ∃ x i, x ∈ H (tr.time i) ∧ tr.time i ≤ b ∧
      ((∃ CV, SA.FastLockAt tr.projAC x i s C CV) ∨ SA.SlowLockAt tr.projAC x i s C) :=
  Iff.rfl

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

theorem LockWithin.mono {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} {b b' : Time}
    (h : LockWithin tr H C s b) (hb : b ≤ b') : LockWithin tr H C s b' :=
  let ⟨x, i, hx, hi, h⟩ := h
  ⟨x, i, hx, hi.trans hb, h⟩

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

/-- `P_s` gives `P_{s'}` for every `s' ≤ s`. -/
theorem HealedOriginsBelow.of_le {g : Time} {rL rO s s' : Nat} {b : Time}
    (h : HealedOriginsBelow tr H g rL rO s b) (hs : s' ≤ s) :
    HealedOriginsBelow tr H g rL rO s' b :=
  fun C j C' j' hj hj' => h C j C' j' (by omega) (by omega)

/-- `V_s` gives `V_{s'}` for every `s' ≤ s`. -/
theorem HealedVotesBelow.of_le {g : Time} {rL rO s s' : Nat} {b : Time}
    (h : HealedVotesBelow tr H g rL rO s b) (hs : s' ≤ s) :
    HealedVotesBelow tr H g rL rO s' b :=
  fun C j hC y i e hv hib hj hm => h C j hC y i e hv hib hj (by omega)

end Consensus.Goldilocks.Compose.Growing

end

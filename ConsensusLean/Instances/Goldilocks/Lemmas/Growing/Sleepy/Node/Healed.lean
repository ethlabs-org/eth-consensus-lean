module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.AC

public section

/-! # Goldilocks under `Sleepy` with growing faults: lock writes

`LockWithin`: a fast or slow lock write of label `s` on a block, by a writer honest at its write,
at a time `≤ b`. Every stored lock of an honest node sits below its own lock write of the lock's
slot (`lock_write_at`, `Node/Lift`), and each lock write sits below an origin of its label written
at the same cut (`lock_below_origin_at`). Comparing a live lock through its write rather than
through that origin keeps the comparison inside a family of blocks that starts at a label floor:
the write's label is the lock's slot, which the drain bounds from below. -/

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

variable {tr H}

theorem lockWithin_iff {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} {b : Time} :
    LockWithin tr H C s b ↔ ∃ x i, x ∈ H (tr.time i) ∧ tr.time i ≤ b ∧
      ((∃ CV, SA.FastLockAt tr.projAC x i s C CV) ∨ SA.SlowLockAt tr.projAC x i s C) :=
  Iff.rfl

theorem LockWithin.mono {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} {b b' : Time}
    (h : LockWithin tr H C s b) (hb : b ≤ b') : LockWithin tr H C s b' :=
  let ⟨x, i, hx, hi, h⟩ := h
  ⟨x, i, hx, hi.trans hb, h⟩

end Consensus.Goldilocks.Compose.Growing

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LockKeepGlobal
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockFloorStep
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees

public section

/-! # Goldilocks: every honest node keeps a lock above `B₀` over an interval

The floor form of global lock keeping. The invariant is "each honest
`x` holds a lock of slot `js x`, with expiry at least `m`, on a block `⪰ B₀` of its frame's tree"
(`FloorAt`). The lock may move (`live_locks` to its viable ancestor, `unlock` to its unlock
target); it stays `⪰ B₀` when `B₀` is its own viable ancestor and `unlock` keeps `B₀`
(`SA.exists_step_locks_floor`). The moved lock keeps its slot and expiry, so the premise
`slot(t_j) ≤ m` bounds the interval.
The frame changes between cuts: the honest tree only grows, so a block `⪰ B₀` stays in the
frame's tree and `⪰ B₀` when `B₀` stays in the tree (`floor_frame_transport`). The vote
condition of `UnlockKeeps` for `B₀` holds because each honest cast reads its own floor
lock, a live lock block `⪰ B₀` (`SA.exists_readPoint_liveLockBlocks_floor`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- The floor at node `y`, cut `i`: a lock of slot `j` and expiry at least `m` on a block `⪰ B₀`
of the frame's tree. -/
abbrev FloorAt (tr : GoldilocksTrace sp ro) (y : Fin sp.n) (i : Nat)
    (B₀ : SA.Blk sp.n (List (FG.Att sp.n))) (j m : Nat) : Prop :=
  ∃ l ∈ (tr.state y i).ac.locks, l.slot = j ∧ m ≤ l.expiry ∧
    ∃ B ∈ (tr.state y i).fg.toFrame.tree, B.root = l.block ∧ (tr.state y i).fg.toFrame.Anc B₀ B

/-- **A block above `B₀` stays above `B₀` in a later frame** that still holds `B₀`. -/
theorem floor_frame_transport {ini} (hrun : GoldilocksRun proposer dg H tr ini) {y : Fin sp.n}
    (hy : y ∈ H) {i i' : Nat} (hii' : i ≤ i') {B₀ B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB0 : B₀ ∈ (tr.state y i').fg.toFrame.tree) (hB : B ∈ (tr.state y i).fg.toFrame.tree)
    (h : (tr.state y i).fg.toFrame.Anc B₀ B) :
    B ∈ (tr.state y i').fg.toFrame.tree ∧ (tr.state y i').fg.toFrame.Anc B₀ B := by
  have hsub := tree_mono hrun.toLocalRun hy hii'
  have h1 : Anc (tr.state y i').fg.tree B₀ B := (h.mono fun X hX => hX.1).mono hsub
  exact ⟨⟨hsub hB.1, hB0.2.trans h1⟩, Anc.restrict hB0.2 h1⟩

/-- **The floor over one cut.** At an honest `y`, cut `i`: the floor, no expiry, `B₀` in the
trees at `i` and `i + 1` and its own viable ancestor at `i`, and `unlock` at the AC call's view
keeping `B₀` (or `slot(t_i) − 1 ≤ j`) give the floor at `i + 1`. -/
theorem floor_run_view {ini} (hrun : GoldilocksRun proposer dg H tr ini) {y : Fin sp.n} (hy : y ∈ H)
    (i : Nat) {B₀ : SA.Blk sp.n (List (FG.Att sp.n))} {j m : Nat} (hfl : FloorAt tr y i B₀ j m)
    (hk : sp.slot (tr.time i) ≤ m) (hB0 : B₀ ∈ (tr.state y i).fg.toFrame.tree)
    (hB0' : B₀ ∈ (tr.state y (i + 1)).fg.toFrame.tree)
    (hva0 : (tr.state y i).fg.toFrame.viableAncestor B₀ = B₀)
    (hu : ∀ ℓ, tr.CallAt y i (.ac ℓ) → (sp.slot (tr.time i) : Int) - 1 ≤ j ∨
      SA.unlockTarget sp (Node.frame (tr.state y i))
        (SA.unlockView (ro := ro) (tr.state y i).ac (Node.frame (tr.state y i)) (tr.time i)
          ℓ.call) ((sp.slot (tr.time i) : Int) - 1) B₀ = B₀) :
    FloorAt tr y (i + 1) B₀ j m := by
  have hold : ∃ l ∈ (tr.state y (i + 1)).ac.locks, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ (tr.state y i).fg.toFrame.tree, B.root = l.block ∧
        (tr.state y i).fg.toFrame.Anc B₀ B := by
    by_cases hc : ∃ c, tr.CallAt y i c
    · obtain ⟨c, hc⟩ := hc
      have hlaw := hrun.cutLaw y hy i c hc
      rw [tr.state_succ_of_call hc]
      cases c with
      | ac ℓ =>
        obtain ⟨hfr, hstep, -, -⟩ := hlaw
        rw [hfr] at hstep
        have := SA.exists_step_locks_floor (ro := ro) y ℓ.call
          (frameOK_state hrun.toLocalRun hy i) (hrun.time_nonneg i) hB0 hva0 hk (hu ℓ hc) hfl
        rw [hstep] at this
        exact this
      | fg ℓ =>
        cases ℓ with
        | block C acc =>
          cases acc with
          | true => rw [hlaw.2.2.1]; exact hfl
          | false => rw [hlaw.2]; exact hfl
        | attestation a => rw [hlaw.2.1]; exact hfl
        | attest C s =>
          cases s with
          | none => rw [hlaw.2]; exact hfl
          | some a => rw [hlaw.2.2]; exact hfl
    · rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩]
      exact hfl
  obtain ⟨l, hl, hj, he, B, hB, hBr, hB0B⟩ := hold
  obtain ⟨hB', hB0B'⟩ := floor_frame_transport hrun hy (Nat.le_succ i) hB0' hB hB0B
  exact ⟨l, hl, hj, he, B, hB', hBr, hB0B'⟩

end Consensus.Goldilocks.Compose

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain

public section

/-! # Goldilocks under `Sleepy` with growing faults: stored locks do not veto origins

Every lock stored by a node honest at a call through `b` names a block on the chain of the origins
within `b` (S1), so the block of the call's frame at its root is compatible with every origin
within `b` held while honest (`stored_lock_compatible`), and no live lock conflicts with such an
origin in the call's frame (`origin_not_conflicts_at`): the veto argument shared by the update's
result (`result_not_vetoed_at`) and the optimistic check (`proposal_not_conflicts_point_at`).

Every step is proved. -/

namespace Consensus.Goldilocks.Compose.Growing

open AC (ACParams ReplayOrder Vote Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- No live lock of a set conflicts with a block `C` of a frame of blocks held while honest when the
blocks of the frame at the set's lock roots are compatible with `C`. -/
theorem not_conflicts_of_compatible {ini}
    (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {Φ : AC.Frm sp.n (List (FG.Att sp.n))} (hΦ : FrameOK Φ)
    (hHB : Φ.tree ⊆ tr.HonestBlocksAt H) {L : Set AC.Lock} {C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hCt : C ∈ Φ.tree)
    (h : ∀ l ∈ L, ∀ B ∈ Φ.tree, B.root = l.block → Compatible (tr.HonestBlocksAt H) C B)
    (t : Time) : ¬ AC.conflictsWithLock sp L Φ t C := by
  have hcoh := honestBlocksAt_coherent hrun hnc
  apply AC.not_conflictsWithLock_of_forall
  intro V hV
  obtain ⟨l, hl, B₀, hB₀, hB₀r, -, rfl⟩ := AC.mem_liveLockBlocks hΦ hV
  obtain ⟨hVt, hVB⟩ := AC.viableAncestor_anc hΦ hB₀
  have hVB' := hVB.mono hHB
  have hCV : Compatible (tr.HonestBlocksAt H) C (Φ.viableAncestor B₀) := by
    rcases h l hl B₀ hB₀ hB₀r with h | h
    · exact AC.anc_total hcoh h hVB'
    · exact Or.inr (hVB'.trans h)
  rcases hCV with h | h
  · exact Or.inl (AC.anc_tree_of_anc_U hcoh hΦ hHB hCt h hVt)
  · exact Or.inr (AC.anc_tree_of_anc_U hcoh hΦ hHB hVt h hCt)

/-- The block of a call's frame at the root of a lock stored by a node honest at the call, through
`b`, is compatible with every origin within `b` held while honest (S1). -/
theorem stored_lock_compatible {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {b : Time} (hb0 : 0 ≤ b) (hinv : SleepyInvariantUpTo tr H b)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j)) {ℓ : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y j ℓ) (hb : tr.time j ≤ b) {C : AC.Blk sp.n (List (FG.Att sp.n))}
    {s : Nat} (hCo : OriginWithin tr H C s b) (hCt : C ∈ ℓ.frame.tree) :
    ∀ l ∈ (tr.state y j).ac.locks, ∀ B ∈ ℓ.frame.tree, B.root = l.block →
      Compatible (tr.HonestBlocksAt H) C B := by
  have hcoh := honestBlocksAt_coherent hrun hnc
  have hHB := (frameIn_at hrun hnc hy hc).2
  intro l hl B₀ hB₀ hB₀r
  obtain ⟨L, hL, hLr, hch⟩ := hinv.locks_at_cut hrun hb0 hy
    (fun k hk => (hrun.time_mono hk.le).trans hb) l hl
  obtain rfl : L = B₀ := hcoh.1 (mem_honestBlocksAt hrun hy hL) (hHB hB₀) (hLr.trans hB₀r.symm)
  exact OnOriginChainWithin.compatible hrun hnc hinv.origins_compatible
    (hHB hCt) (hHB hB₀)
    (onOriginChainWithin_iff.2 (Or.inr ⟨C, s, hCo, Relation.ReflTransGen.refl⟩)) hch

/-- **No live lock of a node honest at a call conflicts with an origin within `b`** held in the
call's frame, at any time: every stored lock is on the origin chain (S1). -/
theorem origin_not_conflicts_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {b : Time} (hb0 : 0 ≤ b) (hinv : SleepyInvariantUpTo tr H b)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j)) {ℓ : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y j ℓ) (hb : tr.time j ≤ b) {C : AC.Blk sp.n (List (FG.Att sp.n))}
    {s : Nat} (hCo : OriginWithin tr H C s b) (hCt : C ∈ ℓ.frame.tree) (t : Time) :
    ¬ AC.conflictsWithLock sp (tr.state y j).ac.locks ℓ.frame t C :=
  have hΦ := frameIn_at hrun hnc hy hc
  not_conflicts_of_compatible hrun hnc hΦ.1 hΦ.2 hCt
    (stored_lock_compatible hrun hnc hb0 hinv hy hc hb hCo hCt) t

end Consensus.Goldilocks.Compose.Growing

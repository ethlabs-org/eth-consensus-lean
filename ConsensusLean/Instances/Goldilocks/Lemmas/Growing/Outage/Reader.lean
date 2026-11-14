module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Inv
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Local
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Candidate
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Sources
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record

public section

/-! # Outage under growing faults: consumers of the invariant at a reader

Consumers of the lock invariant at a reader, for a node
read at a time `t ≥ 0` at which it is honest, after every cut before the cut read (`_by`), and
at the cut's own time (`_at`):

* `liveLockBlocks_compatible_by` ((i) at the reader): the live lock blocks of the stored locks, in
  the node's frame, are compatible with every block `B ⪯ P`;
* `lockInv_state_by`, `liveBlocks_chain_by`: the stored lock invariant in the node's frame, and the
  live lock blocks on one chain (the static facts on the prefix through `t`);
* `reader_frame_by`, `reader_frame_at`: `fc_root` is compatible with every `B ⪯ P`, and `B`, when
  in the frame, is below the anchor or in the full viable tree. The candidate count is
  `2 f_t < n` at the read time.

The read-point form of (i) at a cast is in `Outage/S5Step`. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **The lock invariant at every honest cut**, in the cut's own frame: the stored record names a
block of the node's tree above every stored lock block (`lockInv_of_reachable` at the last AC
call, or none at the initial state), and the record is in the frame once `Σ.F` is below it. -/
theorem lockInv_state {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) (m : Nat) :
    SA.LockInv (tr.HonestBlocks H) (tr.state y m).ac (Node.frame (tr.state y m)) := by
  have hr := (goldilocks_ac_projection_from hrun hnc).localRun
  have hU := hr.coherent
  have hst := projAC_state hrun.toLocalRun hy m
  obtain ⟨E, hEt, hEr, -⟩ := record_origin hrun hnc hy m
  have hEU : E ∈ tr.HonestBlocks H := ⟨y, hy, m, hEt⟩
  refine SA.lockInv_iff.2 ⟨E, hEU, hEr,
    fun hFE => ⟨hEt, honest_held_anc hrun hnc hy hFE hEt⟩, fun l hl X hX hXr => ?_⟩
  rw [← hst] at hl
  rcases SA.state_reachable sp hr hy m with h0 | ⟨Φ, t, hreach, -⟩
  · obtain ⟨_, hs⟩ := SA.voteStart_iff.1 (hrun.vstart y)
    rw [h0, hs] at hl
    exact absurd hl (Set.notMem_empty l)
  · obtain ⟨-, -, hli⟩ := SA.lockInv_of_reachable_from hU (hrun.vstart y) hreach
    obtain ⟨E', hE'U, hE'r, -, hlE⟩ := SA.lockInv_iff.1 hli
    obtain rfl : E' = E := hU.1 hE'U hEU (hE'r.trans (by rw [hst]; exact hEr.symm))
    exact hlE l hl X hX hXr

end Consensus.Goldilocks.Compose

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}
  {ini : Fin sp.n → (goldilocksNode sp ro).State}
  {D : OutageLockPremises tr H proposer dg ini}

/-- **(i) at a reader**: for a node read at `t` (honest then, every cut before `m` at a time
`≤ t`), the live lock blocks of its stored locks in its frame are compatible with every block
`B ⪯ P`. -/
theorem liveLockBlocks_compatible_by (hinv : ∀ i, OutageLockInv D i) {y : Fin sp.n} {m : Nat}
    {t : Time} (ht0 : 0 ≤ t) (hm : ∀ k < m, tr.time k ≤ t) (hy : y ∈ H t) (τ : Time)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBP : Anc (tr.HonestBlocksAt H) B D.P) :
    ∀ X ∈ SA.liveLockBlocks sp (tr.state y m).ac.locks (Node.frame (tr.state y m)) τ,
      Compatible (tr.HonestBlocksAt H) X B := by
  intro X hX
  have hU := D.coherent
  have hΦ := frameOK_at D.hrun ht0 hy hm
  have hΦU : (Node.frame (tr.state y m)).tree ⊆ tr.HonestBlocksAt H :=
    fun Z hZ => tree_held_at ht0 hy hm hZ.1
  obtain ⟨l, hl, B₀, hB₀, hB₀r, -, rfl⟩ := SA.mem_liveLockBlocks hΦ hX
  obtain ⟨L, hL, hLr, hLP⟩ := (hinv m).locks y m t le_rfl ht0 hm hy l hl
  obtain rfl : B₀ = L := hU.1 (hΦU hB₀) (tree_held_at ht0 hy hm hL) (hB₀r.trans hLr.symm)
  exact compatible_of_anc_right hU hBP
    (compatible_of_head_anc hU ((SA.viableAncestor_anc hΦ hB₀).2.mono hΦU) hLP)

/-- **The lock invariant at a reader**, in the node's frame: the static `lockInv_state` on the
prefix through the read time `t`. -/
theorem lockInv_state_by (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {m : Nat} {t : Time} (ht0 : 0 ≤ t)
    (hm : ∀ k < m, tr.time k ≤ t) (hy : y ∈ H t) :
    SA.LockInv (tr.HonestBlocksAt H) (tr.state y m).ac (Node.frame (tr.state y m)) := by
  have hU := honestBlocksAt_coherent hrun hnc
  have hsub := upTo_subset hrun ht0
  have hst := Trace.upTo_state tr y hm
  have h := lockInv_state (hrun.upTo ht0) (hnc.upTo t) hy m
  rw [hst] at h
  obtain ⟨E, hEU, hEr, hEt, hlE⟩ := SA.lockInv_iff.1 h
  refine SA.lockInv_iff.2 ⟨E, hsub hEU, hEr,
    fun hFE => hEt (RunTrace.anc_upTo_of_right hrun.toLocalRun hnc ht0 hEU hFE),
    fun l hl X hX hXr => ?_⟩
  obtain ⟨L, hL, hLr, -⟩ := lock_origin (hrun.upTo ht0) (hnc.upTo _) hy m l (by rw [hst]; exact hl)
  have hLU : L ∈ (tr.upTo t).HonestBlocks (H t) := ⟨y, hy, m, hL⟩
  obtain rfl : X = L := hU.1 hX (hsub hLU) (hXr.trans hLr.symm)
  exact (hlE l hl X hLU hXr).mono hsub

/-- **The live lock blocks of a reader lie on one chain** in its frame. -/
theorem liveBlocks_chain_by (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {m : Nat} {t : Time} (ht0 : 0 ≤ t)
    (hm : ∀ k < m, tr.time k ≤ t) (hy : y ∈ H t) (τ : Time) :
    ∀ X ∈ SA.liveLockBlocks sp (tr.state y m).ac.locks (Node.frame (tr.state y m)) τ,
      ∀ Y ∈ SA.liveLockBlocks sp (tr.state y m).ac.locks (Node.frame (tr.state y m)) τ,
        Compatible (Node.frame (tr.state y m)).tree X Y :=
  (lockInv_state_by hrun hnc ht0 hm hy).liveBlocks_chain (honestBlocksAt_coherent hrun hnc)
    (frameOK_at hrun ht0 hy hm) fun _ hX => tree_held_at ht0 hy hm hX.1

/-- **The reader frame**: for a node read at `t` (honest then, every cut before `m` at a time
`≤ t`, `2 f_t < n`) and every block `B ⪯ P`, `fc_root` is compatible with `B`, and `B`, when in
the frame, is below the anchor or in the full viable tree. -/
theorem reader_frame_by (hinv : ∀ i, OutageLockInv D i) {y : Fin sp.n} {m : Nat} {t : Time}
    (ht0 : 0 ≤ t) (hm : ∀ k < m, tr.time k ≤ t) (hy : y ∈ H t)
    (hf : 2 * (H t)ᶜ.ncard < sp.n) (τ : Time) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBP : Anc (tr.HonestBlocksAt H) B D.P) :
    Compatible (tr.HonestBlocksAt H) (Node.frame (tr.state y m)).fcRoot B ∧
      (B ∈ (Node.frame (tr.state y m)).tree →
        (Node.frame (tr.state y m)).Anc B
            (SA.getAnchor sp (tr.state y m).ac (Node.frame (tr.state y m)) τ) ∨
          B ∈ (Node.frame (tr.state y m)).viableTree (Node.frame (tr.state y m)).tree) := by
  have hU := D.coherent
  have hΦ := frameOK_at D.hrun ht0 hy hm
  have hcaches := (hinv m).caches y m t le_rfl ht0 hm hy
  refine ⟨?_, fun hBt => ?_⟩
  · change Compatible _ (tr.state y m).fg.fcRoot B
    unfold Store.fcRoot
    split_ifs
    · exact compatible_of_anc_right hU hBP hcaches.2
    · exact compatible_of_anc_right hU hBP hcaches.1
  have hsrc := rows_sourced_by D.hrun D.hnc (B := D.P)
    (fun x k hk hx => (hinv m).sources x k hk hx) ht0 hm hy
  rcases held_candidate_of_rows_by D.hrun D.hnc ht0 hm hy hf hsrc
    (fun _ h => compatible_of_anc_right hU hBP h) hBt with h | h
  · exact Or.inl (h.trans ((SA.anc_getAnchor hΦ
      (liveBlocks_chain_by D.hrun D.hnc ht0 hm hy τ)).2 _ (Or.inr rfl)))
  · exact Or.inr h

/-- **The reader frame at a cut**: `reader_frame_by` read at the cut's own time. -/
theorem reader_frame_at (hinv : ∀ i, OutageLockInv D i) {y : Fin sp.n} {m : Nat}
    (hy : y ∈ H (tr.time m)) (hf : 2 * (H (tr.time m))ᶜ.ncard < sp.n) (τ : Time)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBP : Anc (tr.HonestBlocksAt H) B D.P) :
    Compatible (tr.HonestBlocksAt H) (Node.frame (tr.state y m)).fcRoot B ∧
      (B ∈ (Node.frame (tr.state y m)).tree →
        (Node.frame (tr.state y m)).Anc B
            (SA.getAnchor sp (tr.state y m).ac (Node.frame (tr.state y m)) τ) ∨
          B ∈ (Node.frame (tr.state y m)).viableTree (Node.frame (tr.state y m)).tree) :=
  reader_frame_by hinv (D.hrun.time_nonneg m) (fun _ hk => D.hrun.time_mono hk.le) hy hf τ hBP

end Consensus.Goldilocks.Compose.Growing

end

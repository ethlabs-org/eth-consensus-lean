module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameLabels
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee

public section

/-! # Goldilocks under `Sleepy` with growing faults: origins and frames of the prefix

The origins of the prefix `tr.upTo d` for the validators honest at `d` are origins of the run
(`originWithin_of_upTo`; `originBefore_of_upTo` and `lock_write_at` are in `Node/Lift`), and their
blocks are in the prefix's honest blocks (`origin_mem_upTo`). With these, an origin held at a cut
is at or below `fc_root` or fully viable (`held_origin_viable_at`, with `2 f_d < n` at the reading
cut). -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {d : Time}

/-- The result of an update is a block of the update's frame. -/
theorem resultAt_mem_frame {FGP : Type} {ro' : ReplayOrder sp FGP} {trS : SA.SATrace sp FGP ro'}
    {X : Fin sp.n} {i s : Nat} {C : SA.Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (h : SA.ResultAt trS X i s C CV) : ∃ ℓ, trS.CallAt X i ℓ ∧ C ∈ ℓ.frame.tree := by
  obtain ⟨ℓ, hu, hC, -⟩ := h
  exact ⟨ℓ, hu.1, (SA.deepest_mem hC).1.1⟩

/-- The block of an origin event at a time `≤ d` by a node honest at `d` is in the prefix's honest
blocks through `d`. -/
theorem origin_mem_upTo {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    {x : Fin sp.n} (hx : x ∈ H d) {k s : Nat} (hkd : tr.time k ≤ d)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (h : SA.ResultAt tr.projAC x k s C CV ∨ SA.OptimisticLockAt tr.projAC x k s C CV) :
    C ∈ (tr.upTo d).HonestBlocks (H d) := by
  rcases h with h | h
  · obtain ⟨ℓ, hc, hC⟩ := resultAt_mem_frame h
    exact mem_upTo_of_frame hrun hx hkd hc hC
  · obtain ⟨ℓ, A, hpt, -, hsel, -⟩ := h
    exact mem_upTo_of_frame hrun hx hkd hpt.1 (SA.optimisticSelect_mem_tree hsel)

/-- An origin of the prefix within `d'` is an origin of the run within `d'`. -/
theorem originWithin_of_upTo {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} {d' : Time}
    (h : Compose.OriginWithin (tr.upTo d) (H d) C s d') : OriginWithin tr H C s d' := by
  obtain ⟨x, hx, k, CV, hk, hO⟩ := Compose.originWithin_iff.1 h
  rw [RunTrace.upTo_projAC] at hO
  rcases hO with hO | hO
  · obtain ⟨hkd, hO⟩ := (sa_resultAt_upTo hrun.time_mono).mp hO
    exact OriginWithin.of_result (hrun.antitone hkd hx) hk hO
  · obtain ⟨hkd, hO⟩ := (sa_optimisticLockAt_upTo hrun.time_mono).mp hO
    exact OriginWithin.of_optimistic (hrun.antitone hkd hx) hk hO

/-- The block of an origin of the prefix is in the prefix's honest blocks. -/
theorem originWithin_upTo_mem {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (h : Compose.OriginWithin (tr.upTo d) (H d) C s d) : C ∈ (tr.upTo d).HonestBlocks (H d) := by
  obtain ⟨x, hx, k, CV, hk, hO⟩ := Compose.originWithin_iff.1 h
  rw [RunTrace.upTo_projAC] at hO
  refine origin_mem_upTo hrun hx hk (s := s) (CV := CV) ?_
  rcases hO with hO | hO
  · exact Or.inl ((sa_resultAt_upTo hrun.time_mono).mp hO).2
  · exact Or.inr ((sa_optimisticLockAt_upTo hrun.time_mono).mp hO).2

/-- **S3 at a held origin** (`held_origin_viable_before` at the cut's time `d = tr.time i`, with
`2 f_d < n`): at a cut of a node honest then, a block `B` it holds that is compatible with every
origin before the cut, when the origins within `d` are pairwise compatible, is at or below
`fc_root` or in the full viable tree. -/
theorem held_origin_viable_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    (hf : 2 * (H (tr.time i))ᶜ.ncard < sp.n)
    (hP : ∀ C s C' s', OriginWithin tr H C s (tr.time i) → OriginWithin tr H C' s' (tr.time i) →
      Compatible (tr.HonestBlocksAt H) C C')
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBc : ∀ C s, OriginBefore tr H C s i → Compatible (tr.HonestBlocksAt H) B C)
    (hBt : B ∈ (Node.frame (tr.state y i)).tree) :
    (Node.frame (tr.state y i)).Anc B (Node.frame (tr.state y i)).fcRoot ∨
      B ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree := by
  have hd := hrun.time_nonneg i
  have hst := RunTrace.upTo_state_of_le (y := y) hrun.time_mono (le_refl (tr.time i))
  have hBU : B ∈ (tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)) :=
    ⟨y, hy, i, by rw [hst]; exact hBt.1⟩
  have h := held_origin_viable_before (hrun.upTo hd) (hnc.upTo _) (b := tr.time i) hf
    (fun _ => Compose.originsBelowUpTo_iff.2 fun C j C' j' _ _ hC hC' =>
      compatible_upTo hrun hnc hd (originWithin_upTo_mem hrun hC)
        (originWithin_upTo_mem hrun hC')
        (hP C j C' j' (originWithin_of_upTo hrun hC) (originWithin_of_upTo hrun hC')))
    hy i (fun k hk => hrun.time_mono hk.le)
    (fun C s hC => by
      have hCw := hC.within (b := tr.time i) fun k hk => hrun.time_mono hk.le
      exact compatible_upTo hrun hnc hd hBU (originWithin_upTo_mem hrun hCw)
        (hBc C s (originBefore_of_upTo hrun hC)))
    (by rw [hst]; exact hBt)
  rwa [hst] at h

end Consensus.Goldilocks.Compose.Growing

end

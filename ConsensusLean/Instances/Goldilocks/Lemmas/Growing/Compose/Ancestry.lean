module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees

public section

/-! # Ancestry below a block held in a retained prefix

Root injectivity identifies each parent in the historical universe with the parent held in
the reader's tree. Thus ancestry descends into that tree even if other observers were later
compromised. Coherence belongs to the Compose layer, above generic run retention.
-/

namespace Consensus.Goldilocks.RunTrace

variable {P : Params} {A : NodeAC P} {tr : RunTrace A} {d : Time}

/-- Ancestry below a retained block needs no common honest observation horizon. -/
theorem anc_upTo_of_right {proposer : Nat → Fin P.n} {dg : Digest (List (FG.Att P.n)) A.Payload}
    {H : Time → Set (Fin P.n)} {sg : A.Msg → Fin P.n}
    {ini} (_hrun : Growing.LocalRun proposer dg H sg tr ini) (_hnc : Compose.NoCollRun dg tr)
    (_hd : 0 ≤ d)
    {B C : A.Blk} (_hC : C ∈ (tr.upTo d).HonestBlocks (H d))
    (_h : Anc (tr.HonestBlocksAt H) B C) : Anc ((tr.upTo d).HonestBlocks (H d)) B C := by
  have hrun := _hrun
  have hnc := _hnc
  have hd := _hd
  have hC := _hC
  have h := _h
  clear _hC _h
  obtain ⟨y, hy, i, hC⟩ := hC
  have hr := hrun.upTo hd
  have hcoh := Compose.Growing.honest_blocks_coherent_local hrun hnc
  have hsub : ((tr.upTo d).state y i).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ hX => RunTrace.honestBlocks_upTo_subset hrun.time_mono hd ⟨y, hy, i, hX⟩
  suffices Anc ((tr.upTo d).state y i).fg.tree B C from
    Anc.mono (fun _ hX => ⟨y, hy, i, hX⟩) this
  induction h with
  | refl => exact .refl
  | @tail X Y _ hXY ih =>
    have hroot := (Store.accepted_tree P A.Payload A.genesisPayload _
      (Compose.fg_reachable hr hy i)).2.2.2 Y hC
    rcases hroot.cases_tail with heq | ⟨Z, _, hZ⟩
    · rw [heq] at hXY
      cases hXY.2.2
    · obtain rfl : Z = X := hcoh.1 (hsub hZ.1) hXY.1
        (Option.some.inj (hZ.2.2.symm.trans hXY.2.2))
      exact (ih hZ.1).tail hZ

/-- Inside the blocks the prefix's nodes honest at `d` hold, ancestry is the run's ancestry inside
the blocks held while honest (the converse direction is `anc_upTo_of_right`). -/
theorem anc_upTo_iff {proposer : Nat → Fin P.n} {dg : Digest (List (FG.Att P.n)) A.Payload}
    {H : Time → Set (Fin P.n)} {sg : A.Msg → Fin P.n}
    (hrun : Growing.LocalRun proposer dg H sg tr) (hnc : Compose.NoCollRun dg tr) (hd : 0 ≤ d)
    {B C : A.Blk} (_hB : B ∈ (tr.upTo d).HonestBlocks (H d))
    (hC : C ∈ (tr.upTo d).HonestBlocks (H d)) :
    Anc ((tr.upTo d).HonestBlocks (H d)) B C ↔ Anc (tr.HonestBlocksAt H) B C :=
  ⟨Anc.mono (honestBlocks_upTo_subset hrun.time_mono hd), anc_upTo_of_right hrun hnc hd hC⟩

end Consensus.Goldilocks.RunTrace

end

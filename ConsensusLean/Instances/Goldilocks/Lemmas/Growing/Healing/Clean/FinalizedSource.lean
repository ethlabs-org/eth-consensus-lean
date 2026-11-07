module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.SourceOrigin
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.LeftEntry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.LowFinalized
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Seed
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees

public section

/-! # Finalization compared with a clean raw source

The reader is honest at the supplied observation; only completed cuts are bounded by it.
-/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- Finalization of a reader honest at `t ≤ b` compares with a clean raw source. -/
theorem finalized_compatible_clean_source_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} {r s n : Nat} {t : Time} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (SA.Vote sp.n)} (hx : x ∈ H (tr.time r))
    (hC : SA.ResultAt tr.projAC x r s C CV ∨ SA.OptimisticLockAt tr.projAC x r s C CV)
    (hs : cleanLabel sp a + 2 * sp.k + 1 ≤ s) (hrb : tr.time r ≤ b)
    (ht : 0 ≤ t) (hle : ∀ q < n, tr.time q ≤ t) (hy : y ∈ H t) (htb : t ≤ b) :
    Compatible (tr.HonestBlocksAt H) (tr.state y n).fg.F C := by
  have hU := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  have hr := fg_reachable_at hp.run ht hle hy
  have hsub : (tr.state y n).fg.tree ⊆ tr.HonestBlocksAt H := fun _ h =>
    ⟨y, n, t, ht, hle, hy, h⟩
  by_cases hh : HZ tr H g + 1 ≤ (tr.state y n).fg.hj
  · obtain ⟨_, hJm, hFJ, ⟨W, hW, hWJ, _⟩, _⟩ := Store.cache_invariants _ _ _ _ hr
    obtain ⟨E, hE, hEr, hEW, hcase⟩ := Store.J_entry_of_reachable hr hW
    obtain rfl : E = (tr.state y n).fg.J := hU.1 (hsub hE) (hsub hJm) (hEr.trans hWJ)
    rcases hcase with hg | ⟨hJh, hJT⟩
    · have hCx : C ∈ (tr.state x r).fg.tree := by
        rcases hC with ⟨ell, hu, hconf, _⟩ | hop
        · exact (frame_tree_subset_at hp.run hp.noColl hx hu.1).2 (SA.deepest_mem hconf).1.1
        · exact (hp.optimistic_supporter_at hx hrb hop).1
      have hrx := fg_reachable_at hp.run (hp.run.time_nonneg r)
        (fun _ hq => hp.run.time_mono hq.le) hx
      have subx : (tr.state x r).fg.tree ⊆ tr.HonestBlocksAt H := fun _ h =>
        ⟨x, r, tr.time r, hp.run.time_nonneg r, fun _ hq => hp.run.time_mono hq.le, hx, h⟩
      have hgen := (Store.accepted_tree _ _ _ _ hrx).2.2.1
      have he := hU.1 (hsub hJm) (subx hgen) (congrArg (·.root) hg)
      have hJC := ((Store.accepted_tree _ _ _ _ hrx).2.2.2 C hCx).mono subx
      rw [← he] at hJC
      exact Or.inl ((hFJ.mono hsub).trans hJC)
    · obtain ⟨_, _, _, _, v, d, _, hdn, _, _, q, hqd, u, D, ho, hJD⟩ :=
        hp.left_entry_origin_at ht hle hy htb hJm hJT (by omega) hEW
          (by have := Store.hj_lt_h hr hW; omega)
      have hFD := (hFJ.mono hsub).trans hJD
      have hcomp := hp.clean_source_compatible_high_origin_at hc hx hC hs hrb ho
        ((hle q (by omega)).trans htb)
      rcases hcomp with h | h
      · exact SA.anc_total hU hFD h
      · exact Or.inl (hFD.trans h)
  · obtain ⟨v, q, u, D, ho, hqa, _⟩ := hp.reset_seed_at
    have hqb := hqa.trans hp.reset_le
    have hFD := hp.low_finalized_below_origin_at ht hle hy htb (by omega) ho hqb
    rcases hp.clean_source_compatible_high_origin_at hc hx hC hs hrb ho hqb with h | h
    · exact SA.anc_total hU hFD h
    · exact Or.inl (hFD.trans h)

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end

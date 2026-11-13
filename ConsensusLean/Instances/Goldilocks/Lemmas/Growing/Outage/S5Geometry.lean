module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Sources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Local
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant

public section

/-! # Outage under growing faults: the Hi geometry

A node is **Hi** at a cut (`HiAt`) when its justification cache `Σ.J` is strictly above the
protected block `P`.

* `above_of_hi_height_at` (G3′): under Hi at cut `k`, read at a time `t` at which the node is
  honest after every cut before `k`, with `2 f_t < n`, every block of the node's tree at state
  height at least `h_j + 1` is strictly above `P`. Its height-`h_j` entry has a source, held while
  honest at `t`, compatible with `P` (lock safety's (SRC)), so it is compatible with `P`; it is
  `Σ.J` or a distinct entry of the same height, which cannot be below `P ≺ Σ.J`. The store is read
  on the prefix through `t`. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}
  {ini : Fin sp.n → (goldilocksNode sp ro).State}

/-- Strictly above `P` in the node's justification cache. -/
def HiAt (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (P : SA.Blk sp.n (List (FG.Att sp.n))) (y : Fin sp.n) (i : Nat) : Prop :=
  Anc (tr.HonestBlocksAt H) P (tr.state y i).fg.J ∧ (tr.state y i).fg.J.root ≠ P.root

theorem hiAt_iff {P : SA.Blk sp.n (List (FG.Att sp.n))} {y : Fin sp.n} {i : Nat} :
    HiAt tr H P y i ↔
      Anc (tr.HonestBlocksAt H) P (tr.state y i).fg.J ∧ (tr.state y i).fg.J.root ≠ P.root :=
  Iff.rfl

variable (D : OutageLockPremises tr H proposer dg ini)

/-- **G3′** at a read time: under Hi at cut `k ≤ i`, every block of the node's tree at state
height at least `h_j + 1` is strictly above `P`. -/
theorem above_of_hi_height_at {i : Nat} (hinv : OutageLockInv D i) {y : Fin sp.n} {k : Nat}
    {t : Time} (hk : k ≤ i) (ht0 : 0 ≤ t) (ht : ∀ k' < k, tr.time k' ≤ t) (hy : y ∈ H t)
    (hf : 2 * (H t)ᶜ.ncard < sp.n) (hHi : HiAt tr H D.P y k)
    {X : SA.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state y k).fg.tree)
    (hh : (tr.state y k).fg.hj + 1 ≤ ((tr.state y k).fg.σ X.root).h) :
    Anc (tr.HonestBlocksAt H) D.P X ∧ X.root ≠ D.P.root := by
  have hU := D.coherent
  have hr := D.hrun.upTo ht0
  have hnc' := D.hnc.upTo t
  have hsub := upTo_subset D.hrun ht0
  have hst := Trace.upTo_state tr y ht
  obtain ⟨hPJ, hJP⟩ := hiAt_iff.1 hHi
  rw [← hst] at hX hh hPJ hJP
  obtain ⟨-, hJt, -, -⟩ := Store.cache_invariants _ _ _ _ (fg_reachable hr.toLocalRun hy k)
  -- `h_j ≥ 1`: at `h_j = 0`, `Σ.J` is genesis, and nothing is strictly below genesis
  have hj1 : 1 ≤ ((tr.upTo t).state y k).fg.hj := by
    by_contra h0
    have hJg := justified_genesis hr (i := k) (by omega) hy
    by_cases hPJe : D.P = ((tr.upTo t).state y k).fg.J
    · exact hJP (by rw [hPJe])
    have := (Anc.slot_le hU hPJ).2 hPJe
    rw [hJg] at this
    exact Nat.not_lt_zero _ this
  -- the height-`h_j` entry below `X`, with a source compatible with `P`, held while honest at `t`
  have hsrc := (rows_sourced_by D.hrun D.hnc (B := D.P) (n := k)
    (fun x k' hk' hx => hinv.sources x k' (by omega) hx) ht0 ht hy).upTo_held ht
  obtain ⟨E, hEt, hEX, hEh, hET, D', ⟨hD'P, -⟩, hD's⟩ :=
    frame_crossing_source_before hr hnc' hf hy hsrc hX hj1 (Nat.lt_of_succ_le hh)
  have hEU : E ∈ (tr.upTo t).HonestBlocks (H t) := fg_tree_subset_honest hy k hEt
  obtain ⟨x, hx, k', -, -, hED', -, -⟩ := honest_source_entry hr hnc' hD's hEU rfl
  have hED : Anc (tr.HonestBlocksAt H) E D' :=
    hED'.mono ((fg_tree_subset_honest hx k').trans hsub)
  have hEP : Compatible (tr.HonestBlocksAt H) E D.P := by
    rcases hD'P with h | h
    · exact Or.inl (hED.trans h)
    · exact Anc.total hU hED h
  have hEXU : Anc (tr.HonestBlocksAt H) E X := hEX.mono ((fg_tree_subset_honest hy k).trans hsub)
  -- `E` is not below `P`: else `E ⪯ Σ.J`, two entries of height `h_j` below `Σ.J`, so `E = Σ.J`
  have hnot : ¬ Anc (tr.HonestBlocksAt H) E D.P := by
    intro hE
    have hEJ := honest_held_anc hr hnc' hy (RunTrace.anc_upTo_of_right D.hrun.toLocalRun D.hnc ht0
      ⟨y, hy, k, hJt⟩ (hE.trans hPJ)) hJt
    obtain ⟨hJh, hJT, -⟩ := justified_honest_source_before hr hnc' hf hy hsrc hj1
    have hEJe : E = ((tr.upTo t).state y k).fg.J :=
      held_entry_unique hr hnc' hy hJt hEJ Relation.ReflTransGen.refl (hEh.trans hJh.symm)
        hET hJT
    subst hEJe
    exact hJP (congrArg (·.root) (Anc.antisymm hU hE hPJ))
  have hPE : Anc (tr.HonestBlocksAt H) D.P E := hEP.resolve_left hnot
  refine ⟨hPE.trans hEXU, fun hXr => hnot ?_⟩
  have hXP : X = D.P := hU.1 (hsub (fg_tree_subset_honest hy k hX)) D.hP.1 hXr
  exact hXP ▸ hEXU

end Consensus.Goldilocks.Compose.Growing

end

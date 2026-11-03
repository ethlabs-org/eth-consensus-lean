module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.OutageLockSafety.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.OutageLockSafety.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.OutageLockSafety.Sources
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameKey
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic

public section

/-! # Outage S5: the Hi geometry (S5 card §9.3, §12.2, §12.5 A1)

Workbench `repos/consensus-lean/notes/outage/outage_restoration_s5.md`. A node is **Hi** at a
cut (`HiAt`) when its justification cache `Σ.J` is strictly above the protected block `P`.

* `above_of_hi_height` (G3′): under Hi, every block of the node's tree at state height at least
  `h_j + 1` is strictly above `P`. Its height-`h_j` entry has an honest source compatible with `P`
  (lock safety's (SRC)), so it is compatible with `P`; it is `Σ.J` or a distinct entry of the same
  height, which cannot be below `P ≺ Σ.J`.
* `head_above_of_hi` (H1, reader form): under Hi, `ac_head` extends `P`. It walks the full viable
  tree (not a voter's vote domain). Below `Σ.F` or `fc_root` the head is above `P` at once;
  otherwise `fc_root = Σ.F ≺ P`, the head height floor is at least `h_j + 1`, every viable head is
  strictly above `P` (G3′), so the viable tree holds `P` and the only viable child of a block below
  `P` on the way to `P` is the child towards `P`, which is eligible since its parent, below `P`,
  is not a viable head. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- Strictly above `P` in the node's justification cache. -/
def HiAt (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (P : SA.Blk sp.n (List (FG.Att sp.n)))
    (y : Fin sp.n) (i : Nat) : Prop :=
  Anc (tr.HonestBlocks H) P (tr.state y i).fg.J ∧ (tr.state y i).fg.J.root ≠ P.root

theorem hiAt_iff {P : SA.Blk sp.n (List (FG.Att sp.n))} {y : Fin sp.n} {i : Nat} :
    HiAt tr H P y i ↔
      Anc (tr.HonestBlocks H) P (tr.state y i).fg.J ∧ (tr.state y i).fg.J.root ≠ P.root :=
  Iff.rfl

/-- Two blocks of one coherent set with the same parent root: one below the other is the other. -/
private theorem eq_of_anc_sibling {S : Set (SA.Blk sp.n (List (FG.Att sp.n)))} (hS : Coherent S)
    {Y Y' : SA.Blk sp.n (List (FG.Att sp.n))} (hY' : Y' ∈ S) (hpar : Y'.parent = Y.parent)
    (h : Anc S Y' Y) : Y' = Y := by
  obtain rfl | ⟨Z, hY'Z, hZY⟩ := (Relation.ReflTransGen.cases_tail_iff _ _ _).1 h
  · rfl
  have hZ : Z ∈ S := hZY.1
  have h₁ := (Anc.slot_le hS hY'Z).1
  have h₂ := hS.2 Z hZ Y' hY' (hpar.trans hZY.2.2)
  omega

variable (D : OutageLockPremises tr H proposer dg)

/-- **G3′**: under Hi at cut `k ≤ i`, every block of the node's tree at state height at least
`h_j + 1` is strictly above `P`. -/
theorem above_of_hi_height {i : Nat} (hinv : OutageLockInv D i) {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} (hk : k ≤ i) (hHi : HiAt tr H D.P y k) {X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : X ∈ (tr.state y k).fg.tree)
    (hh : (tr.state y k).fg.hj + 1 ≤ ((tr.state y k).fg.σ X.root).h) :
    Anc (tr.HonestBlocks H) D.P X ∧ X.root ≠ D.P.root := by
  have hU := D.coherent
  obtain ⟨hPJ, hJP⟩ := hiAt_iff.1 hHi
  have hR := fg_reachable D.hrun.toLocalRun hy k
  obtain ⟨-, hJt, -, -⟩ := Store.cache_invariants _ _ _ _ hR
  -- `h_j ≥ 1`: at `h_j = 0`, `Σ.J` is genesis, and nothing is strictly below genesis
  have hj1 : 1 ≤ (tr.state y k).fg.hj := by
    by_contra h0
    have hJg := justified_genesis D.hrun (i := k) (by omega) hy
    by_cases hPJe : D.P = (tr.state y k).fg.J
    · exact hJP (by rw [hPJe])
    have := (Anc.slot_le hU hPJ).2 hPJe
    rw [hJg] at this
    exact Nat.not_lt_zero _ this
  -- the height-`h_j` entry below `X`, with an honest source compatible with `P`
  have hsrc := rows_sourced D.hrun D.hnc (B := D.P) (n := k)
    (fun x hx k' hk' => hinv.sources x hx k' (by omega)) hy
  obtain ⟨E, hEt, hEX, hEh, hET, D', hD'P, hD's⟩ :=
    frame_crossing_source_before D.hrun D.hnc D.two_faults_lt hy (i := k) hsrc hX hj1 (by omega)
  have hEU : E ∈ tr.HonestBlocks H := fg_tree_subset_honest hy k hEt
  obtain ⟨x, hx, k', -, -, hED', -, -⟩ := honest_source_entry D.hrun D.hnc hD's hEU rfl
  have hEP : Compatible (tr.HonestBlocks H) E D.P :=
    compatible_of_anc hU (hED'.mono (fg_tree_subset_honest hx k')) hD'P
  have hEXU : Anc (tr.HonestBlocks H) E X := hEX.mono (fg_tree_subset_honest hy k)
  -- `E` is not below `P`: else `E ⪯ Σ.J`, two entries of height `h_j` below `Σ.J`, so `E = Σ.J`
  have hnot : ¬ Anc (tr.HonestBlocks H) E D.P := by
    intro hE
    have hEJ := honest_held_anc D.hrun D.hnc hy (hE.trans hPJ) hJt
    obtain ⟨hJh, hJT, -⟩ := justified_honest_source_before D.hrun D.hnc D.two_faults_lt hy hsrc hj1
    have hEJe : E = (tr.state y k).fg.J :=
      held_entry_unique D.hrun D.hnc hy hJt hEJ Relation.ReflTransGen.refl (hEh.trans hJh.symm)
        hET hJT
    subst hEJe
    exact hJP (congrArg (·.root) (Anc.antisymm hU hE hPJ))
  have hPE : Anc (tr.HonestBlocks H) D.P E := hEP.resolve_left hnot
  refine ⟨hPE.trans hEXU, fun hr => hnot ?_⟩
  have hXP : X = D.P := hU.1 (fg_tree_subset_honest hy k hX) D.hP.1 hr
  exact hXP ▸ hEXU

end Consensus.Goldilocks.Compose

end

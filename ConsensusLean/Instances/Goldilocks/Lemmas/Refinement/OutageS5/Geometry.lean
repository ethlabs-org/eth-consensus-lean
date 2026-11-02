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

/-- The live lock blocks of the node's stored locks are compatible with `P` (lock safety's (i)
at cut `i`). -/
private theorem liveLockBlocks_compatible_at {i : Nat} (hinv : OutageLockInv D i) {w : Fin sp.n}
    (hw : w ∈ H) (t : Time) :
    ∀ L ∈ SA.liveLockBlocks sp (tr.state w i).ac.locks (Node.frame (tr.state w i)) t,
      Compatible (tr.HonestBlocks H) L D.P := by
  intro L hL
  have hU := D.coherent
  have hΦ := frameOK_state D.hrun.toLocalRun hw i
  have hΦU : (Node.frame (tr.state w i)).tree ⊆ tr.HonestBlocks H := fun Z hZ => ⟨w, hw, i, hZ.1⟩
  obtain ⟨l, hl, B₀, hB₀, hB₀r, -, rfl⟩ := SA.mem_liveLockBlocks hΦ hL
  obtain ⟨L', hL', hL'r, hL'P⟩ := hinv.locks w hw i le_rfl l hl
  obtain rfl : B₀ = L' := hU.1 (hΦU hB₀) ⟨w, hw, i, hL'⟩ (hB₀r.trans hL'r.symm)
  exact compatible_of_anc hU ((SA.viableAncestor_anc hΦ hB₀).2.mono hΦU) hL'P

/-- **H1, reader form**: under Hi, `ac_head` extends `P`. -/
theorem head_above_of_hi {i : Nat} (hinv : OutageLockInv D i) {w : Fin sp.n} (hw : w ∈ H)
    (hHi : HiAt tr H D.P w i) (t : Time) :
    Anc (tr.HonestBlocks H) D.P
      (SA.acHead sp (tr.state w i).ac (Node.frame (tr.state w i)) t) := by
  have hU := D.coherent
  obtain ⟨hPJ, hJP⟩ := hiAt_iff.1 hHi
  set st := (tr.state w i).fg
  set Φ := Node.frame (tr.state w i)
  have hΦ : FrameOK Φ := frameOK_state D.hrun.toLocalRun hw i
  have hΦU : Φ.tree ⊆ tr.HonestBlocks H := fun Z hZ => ⟨w, hw, i, hZ.1⟩
  have hR := fg_reachable D.hrun.toLocalRun hw i
  obtain ⟨-, hJt, -, -, -, ⟨Bm, hBmt, hBmh⟩, -⟩ := Store.cache_invariants _ _ _ _ hR
  have hjm : st.hj < st.hmax := Healing.hj_lt_hmax D.hrun hw i
  replace hBmh : (st.σ Bm.root).h = st.hmax := hBmh
  unfold SA.acHead
  set A := (tr.state w i).ac
  set V := (SA.latestView sp A Φ t).1
  set s := (SA.latestView sp A Φ t).2
  -- below `Σ.F`: every block of the tree, the head among them, extends `Σ.F`
  by_cases hPF : Anc (tr.HonestBlocks H) D.P st.F
  · have hmem := SA.getHead_mem' hΦ (fun X hX => hX.1) A t V s (T := Φ.viableTree Φ.tree)
    exact hPF.trans ((hΦ.rooted.2 _ hmem).mono hΦU)
  have hFP : Anc (tr.HonestBlocks H) st.F D.P :=
    ((hinv.caches w hw i le_rfl).1).resolve_right hPF
  have hdomA : ∀ B ∈ Φ.tree, ∀ X, Φ.Anc X B → X ∈ Φ.tree := fun B hB X hX => SA.mem_of_anc hX hB
  have hlocks := liveLockBlocks_compatible_at D hinv hw t
  -- `P` is held above `Σ.F`, given a held block above it
  have hPΦ : ∀ W ∈ st.tree, Anc (tr.HonestBlocks H) D.P W → D.P ∈ Φ.tree := by
    intro W hWt hPW
    have h := honest_held_anc D.hrun D.hnc hw hPW hWt
    have hPt : D.P ∈ st.tree := by
      by_cases he : D.P = W
      · exact he ▸ hWt
      · exact (Anc.mem h he).1
    exact ⟨hPt, honest_held_anc D.hrun D.hnc hw hFP hPt⟩
  by_cases hcond : st.hmax = st.hj + 1 ∧ ¬ st.Contest
  · -- `fc_root = Σ.J ⪰ P`: no viable block is below `P`
    have hfc : Φ.fcRoot = st.J := Store.fcRoot_of_not_contest st hcond.1 hcond.2
    have hJΦ : st.J ∈ Φ.tree := hfc ▸ hΦ.fcRoot_mem
    have hPt := hPΦ st.J hJt hPJ
    refine Anc.mono hΦU (SA.anc_getHead hU hΦ hΦU A t V s (dom := Φ.tree) subset_rfl hdomA
      (Or.inr (hfc ▸ SA.anc_tree_of_anc_U hU hΦ hΦU hPt hPJ hJΦ)) hlocks ?_)
    intro X Cx hCx _ hCxP
    have hJP' : Anc (tr.HonestBlocks H) st.J D.P := Anc.mono hΦU ((hfc ▸ hCx.2.1).trans hCxP)
    exact absurd (congrArg (·.root) (Anc.antisymm hU hJP' hPJ)) hJP
  -- `fc_root = Σ.F ≺ P`, and the head height floor is at least `h_j + 1`
  have hfc : Φ.fcRoot = st.F := by
    change st.fcRoot = st.F
    unfold Store.fcRoot
    simp only [hcond, ↓reduceIte]
  have hfl : st.hj + 1 ≤ st.headHeightFloor := by
    unfold Store.headHeightFloor
    split_ifs with hc
    · omega
    · have : st.hmax ≠ st.hj + 1 := fun h => hcond ⟨h, hc⟩
      omega
  have hvh : ∀ W ∈ Φ.viableHeads, Anc (tr.HonestBlocks H) D.P W ∧ W.root ≠ D.P.root :=
    fun W hW => above_of_hi_height D hinv hw le_rfl hHi hW.1 (hfl.trans hW.2.2.2)
  -- the block of height `h_max` is a viable head above `P`
  have hPBm := (above_of_hi_height D hinv hw le_rfl hHi hBmt
    (show st.hj + 1 ≤ (st.σ Bm.root).h by omega)).1
  have hPt := hPΦ Bm hBmt hPBm
  have hFBm := honest_held_anc D.hrun D.hnc hw (hFP.trans hPBm) hBmt
  have hBmΦ : Bm ∈ Φ.tree := ⟨hBmt, hFBm⟩
  have hBmv : Bm ∈ Φ.viableHeads := by
    refine ⟨hBmt, hFBm, ?_, ?_⟩
    · change st.Anc st.fcRoot Bm
      rw [show st.fcRoot = st.F from hfc]
      exact hFBm
    · change st.headHeightFloor ≤ (st.σ Bm.root).h
      unfold Store.headHeightFloor
      split_ifs <;> omega
  have hFΦ : st.F ∈ Φ.tree := hfc ▸ hΦ.fcRoot_mem
  have hPv : D.P ∈ Φ.viableTree Φ.tree :=
    ⟨hPt, hfc ▸ SA.anc_tree_of_anc_U hU hΦ hΦU hFΦ hFP hPt, Bm, hBmΦ, hBmv,
      SA.anc_tree_of_anc_U hU hΦ hΦU hPt hPBm hBmΦ⟩
  refine Anc.mono hΦU (SA.anc_getHead hU hΦ hΦU A t V s (dom := Φ.tree) subset_rfl hdomA
    (Or.inl hPv) hlocks ?_)
  intro X Cx hCx hpar hCxP
  have hCxPU : Anc (tr.HonestBlocks H) Cx D.P := Anc.mono hΦU hCxP
  refine ⟨⟨hCx, hpar, Or.inl ?_⟩, fun D' hD' hne => absurd ?_ hne⟩
  · -- the parent of `Cx`, below `P`, is not a viable head
    rintro ⟨W, hW, hWp⟩
    have hWCx : Anc (tr.HonestBlocks H) W Cx :=
      Relation.ReflTransGen.single ⟨hΦU ⟨hW.1, hW.2.1⟩, hΦU hCx.1, hWp.trans rfl⟩
    obtain ⟨hPW, hWP⟩ := hvh W hW
    exact hWP (congrArg (·.root) (Anc.antisymm hU (hWCx.trans hCxPU) hPW))
  · -- a viable sibling `D'` of `Cx` is comparable with `P`, hence equal to `Cx`
    obtain ⟨⟨hD'Φ, -, W', -, hW'v, hD'W'⟩, hD'p, -⟩ := hD'
    have hpar' : D'.parent = Cx.parent := hD'p.trans hpar.symm
    rcases Anc.total hU (Anc.mono hΦU hD'W') (hvh W' hW'v).1 with hD'P | hPD'
    · rcases Anc.total hU hD'P hCxPU with h | h
      · exact eq_of_anc_sibling hU (hΦU hD'Φ) hpar' h
      · exact (eq_of_anc_sibling hU (hΦU hCx.1) hpar'.symm h).symm
    · exact (eq_of_anc_sibling hU (hΦU hCx.1) hpar'.symm (hCxPU.trans hPD')).symm

end Consensus.Goldilocks.Compose

end

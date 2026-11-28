module
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Store.View
public import ConsensusLean.Instances.Goldilocks.Spec.Node.State
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Core
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Order
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Honest
import ConsensusLean.Instances.Goldilocks.Lemmas.Frame.Ancestry
import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Tree
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # P-U shadow, V-B7: the S5Walk Hi case over the shadow frame

The stock `anc_getHead_of_hi` (`Growing/Outage/S5Walk`) splits on `Σ.hmax = Σ.hj + 1 ∧ ¬Contest`.
Under P-U every viable head of the Hi case lies strictly above `P`: by state height
`≥ hj + 1`, or by `P ≺ J ⪯ W` (`hi_viable_head_above'`). So the stock `hcond` branch (the walk
passes `fc_root = Σ.J`) collapses into the `F` branch: no `V3`, no `jTop`.

This file states the snapshot-level core `anc_getHead_of_hi'_core`: the stock proof with the
run-level facts it reads taken as explicit premises, in the form the run lemmas of the shadow run
(`GoldilocksRun'`) give them. -/

namespace Consensus.Goldilocks.Shadow.PU

open AC (ACParams Payload)

variable {sp : ACParams}

/-- Membership in the shadow frame tree (`Defs` does not expose `toFrame'`). -/
private theorem mem_tree {st : Store sp.toParams (Payload sp.n)}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} :
    B ∈ st.toFrame.tree ↔ B ∈ st.tree ∧ st.Anc st.F B := by
  rw [Store.toFrame_tree]; rfl

private theorem mem_heads {st : Store sp.toParams (Payload sp.n)}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} :
    B ∈ st.toFrame.viableHeads ↔ B ∈ st.tree ∧ st.Anc st.F B ∧ st.IsViable B := by
  rw [Store.toFrame_viableHeads]; rfl

/-- **Under Hi, every P-U viable head is strictly above `P`.** By height (`hmax ≤ σ(W).h`, or
`σ(W).h + 1 = hmax` with `hj + 1 < hmax`, both at least `hj + 1`, so G3′ applies) or by the J clause
(`P ≺ J ⪯ W`). -/
theorem hi_viable_head_above {U : Set (AC.Blk sp.n (List (FG.Att sp.n)))} (hU : Coherent U)
    {st : Store sp.toParams (Payload sp.n)} (hst : st.tree ⊆ U) (hjm : st.hj < st.hmax)
    {Pb : AC.Blk sp.n (List (FG.Att sp.n))} (hPJ : Anc U Pb st.J) (hJP : st.J.root ≠ Pb.root)
    (above : ∀ {X}, X ∈ st.tree → st.hj + 1 ≤ (st.σ X.root).h →
      Anc U Pb X ∧ X.root ≠ Pb.root)
    {W : AC.Blk sp.n (List (FG.Att sp.n))} (hW : W ∈ st.tree) (hv : st.IsViable W) :
    Anc U Pb W ∧ W.root ≠ Pb.root := by
  rcases (Store.isViable_iff st W).1 hv with h | ⟨h1, h2 | h2⟩
  · exact above hW (by omega)
  · exact above hW (by omega)
  · have hJW : Anc U st.J W := h2.mono hst
    refine ⟨hPJ.trans hJW, fun hr => hJP ?_⟩
    have hPne : Pb ≠ st.J := fun h => hJP (by rw [h])
    have hPU : Pb ∈ U := (Anc.mem hPJ hPne).1
    obtain rfl : W = Pb := hU.1 (hst hW) hPU hr
    exact congrArg (·.root) (Anc.antisymm hU hJW hPJ)

/-- Two blocks of one coherent set with the same parent root: one below the other is the other.
(A copy of the private lemma of `Growing/Outage/S5Walk`.) -/
private theorem eq_of_anc_sibling {S : Set (AC.Blk sp.n (List (FG.Att sp.n)))} (hS : Coherent S)
    {Y Y' : AC.Blk sp.n (List (FG.Att sp.n))} (hY' : Y' ∈ S) (hpar : Y'.parent = Y.parent)
    (h : Anc S Y' Y) : Y' = Y := by
  obtain rfl | ⟨Z, hY'Z, hZY⟩ := (Relation.ReflTransGen.cases_tail_iff _ _ _).1 h
  · rfl
  have hZ : Z ∈ S := hZY.1
  have h₁ := (Anc.slot_le hS hY'Z).1
  have h₂ := hS.2 Z hZ Y' hY' (hpar.trans hZY.2.2)
  omega

/-- **The Hi walk over the shadow frame (snapshot core).** Under Hi (`P ≺ Σ.J`) at a reachable
store whose shadow frame is well formed, a head walk over the viable tree of an ancestor-closed
domain extends `P`, when the live lock blocks of the walked state are compatible with `P` and the
domain's viable tree is nonempty or the domain is the whole tree.

The proof is the stock `anc_getHead_of_hi` without its `hcond` branch: `fc_root = Σ.F`, every
viable head is strictly above `P` (`hi_viable_head_above'`), and `P` lies in the viable tree. The
run-level facts the stock proof reads are premises: `hst` (the store tree is held), `hjm`
(`hj < hmax`), `hBm` (a block of state height `hmax`, the cache invariant), `above` (G3′),
`hcomp` (`Σ.F` and `P` are comparable), and `hheld` (held ancestry transfers to the store). -/
theorem anc_getHead_of_hi_core {U : Set (AC.Blk sp.n (List (FG.Att sp.n)))} (hU : Coherent U)
    {st : Store sp.toParams (Payload sp.n)} (hΦ : FrameOK st.toFrame)
    (hst : st.tree ⊆ U) (hjm : st.hj < st.hmax)
    (hBm : ∃ B ∈ st.tree, (st.σ B.root).h = st.hmax)
    {Pb : AC.Blk sp.n (List (FG.Att sp.n))} (hPJ : Anc U Pb st.J) (hJP : st.J.root ≠ Pb.root)
    (above : ∀ {X}, X ∈ st.tree → st.hj + 1 ≤ (st.σ X.root).h →
      Anc U Pb X ∧ X.root ≠ Pb.root)
    (hcomp : Compatible U st.F Pb)
    (hheld : ∀ {X Y}, Y ∈ st.tree → Anc U X Y → st.Anc X Y)
    (A : AC.ACState sp.n) (t : Time) (V : AC.View sp.n) (σ : Int)
    {dom : Set (AC.Blk sp.n (List (FG.Att sp.n)))}
    (hdom : dom ⊆ st.toFrame.tree) (hdomA : ∀ B ∈ dom, ∀ X, st.toFrame.Anc X B → X ∈ dom)
    (hne : (st.toFrame.viableTree dom).Nonempty ∨ st.toFrame.tree ⊆ dom)
    (hlocks : ∀ L ∈ AC.liveLockBlocks sp A.locks st.toFrame t, Compatible U L Pb) :
    Anc U Pb (AC.getHead sp A st.toFrame t (st.toFrame.viableTree dom) V σ) := by
  set Φ := st.toFrame with hΦdef
  have hΦU : Φ.tree ⊆ U := fun Z hZ => hst (mem_tree.1 hZ).1
  have hF : Φ.F = st.F := Store.toFrame_F st
  have hfc : Φ.fcRoot = st.F := Store.toFrame_fcRoot st
  obtain ⟨Bm, hBmt, hBmh⟩ := hBm
  -- below `Σ.F`: the head is a block of the tree, which extends `Σ.F`
  by_cases hPF : Anc U Pb st.F
  · have hmem := AC.getHead_mem hΦ (fun X hX => hdom hX.1) A t V σ (T := Φ.viableTree dom)
    have h := Anc.mono hΦU (hΦ.rooted.2 _ hmem)
    rw [hF] at h
    exact hPF.trans h
  have hFP : Anc U st.F Pb := hcomp.resolve_right hPF
  -- `P` is held above `Σ.F`, given a held block above it
  have hPΦ : ∀ W ∈ st.tree, Anc U Pb W → Pb ∈ Φ.tree := by
    intro W hWt hPW
    have h := hheld hWt hPW
    have hPt : Pb ∈ st.tree := by
      by_cases he : Pb = W
      · exact he ▸ hWt
      · exact (Anc.mem h he).1
    exact mem_tree.2 ⟨hPt, hheld hPt hFP⟩
  have hvh : ∀ W ∈ Φ.viableHeads, Anc U Pb W ∧ W.root ≠ Pb.root :=
    fun W hW => (by
      obtain ⟨h1, -, h3⟩ := mem_heads.1 hW
      exact hi_viable_head_above hU hst hjm hPJ hJP above h1 h3)
  have hFΦ : st.F ∈ Φ.tree := hfc ▸ hΦ.fcRoot_mem
  -- a viable head in the domain, strictly above `P`
  obtain ⟨W, hWd, hWv⟩ : ∃ W ∈ dom, W ∈ Φ.viableHeads := by
    rcases hne with ⟨X, -, -, W, hWd, hWv, -⟩ | hsub
    · exact ⟨W, hWd, hWv⟩
    · have hFBm := hheld hBmt (hFP.trans (above hBmt (by omega)).1)
      exact ⟨Bm, hsub (mem_tree.2 ⟨hBmt, hFBm⟩),
        mem_heads.2 ⟨hBmt, hFBm, (Store.isViable_iff st Bm).2 (Or.inl hBmh.ge)⟩⟩
  have hPW := (hvh W hWv).1
  have hWΦ : W ∈ Φ.tree := hdom hWd
  have hPt := hPΦ W (mem_tree.1 hWΦ).1 hPW
  have hPWΦ := AC.anc_tree_of_anc_U hU hΦ hΦU hPt hPW hWΦ
  have hPv : Pb ∈ Φ.viableTree dom :=
    ⟨hdomA W hWd _ hPWΦ, hfc ▸ AC.anc_tree_of_anc_U hU hΦ hΦU hFΦ hFP hPt, W, hWd, hWv, hPWΦ⟩
  refine Anc.mono hΦU (AC.anc_getHead hU hΦ hΦU A t V σ hdom hdomA (Or.inl hPv) hlocks ?_)
  intro X Cx hCx hpar hCxP
  have hCxPU : Anc U Cx Pb := Anc.mono hΦU hCxP
  have hCxΦ : Cx ∈ Φ.tree := hdom hCx.1
  refine ⟨⟨hCx, hpar, Or.inl ?_⟩, fun D' hD' hne => absurd ?_ hne⟩
  · -- the parent of `Cx`, below `P`, is not a viable head
    rintro ⟨W', hW', hW'p⟩
    have hW'Cx : Anc U W' Cx :=
      Relation.ReflTransGen.single ⟨hΦU (hΦ.viableHeads_subset hW'), hΦU hCxΦ, hW'p.trans rfl⟩
    obtain ⟨hPW', hW'P⟩ := hvh W' hW'
    exact hW'P (congrArg (·.root) (Anc.antisymm hU (hW'Cx.trans hCxPU) hPW'))
  · -- a viable sibling `D'` of `Cx` is comparable with `P`, hence equal to `Cx`
    obtain ⟨⟨hD'd, -, W', -, hW'v, hD'W'⟩, hD'p, -⟩ := hD'
    have hD'Φ : D' ∈ Φ.tree := hdom hD'd
    have hpar' : D'.parent = Cx.parent := hD'p.trans hpar.symm
    rcases Anc.total hU (Anc.mono hΦU hD'W') (hvh W' hW'v).1 with hD'P | hPD'
    · rcases Anc.total hU hD'P hCxPU with h | h
      · exact eq_of_anc_sibling hU (hΦU hD'Φ) hpar' h
      · exact (eq_of_anc_sibling hU (hΦU hCxΦ) hpar'.symm h).symm
    · exact (eq_of_anc_sibling hU (hΦU hCxΦ) hpar'.symm (hCxPU.trans hPD')).symm

/-- **The live lock blocks of a well-formed frame are compatible with `X` when the locked blocks
are.** A live lock block is the viable ancestor of a locked tree block (`mem_liveLockBlocks`),
which is below it; so compatibility passes down. This is the only place the stock hlocks callers
(`readPoint_liveLockBlocks_compatible_at`) read the frame, and it holds for every well-formed
frame, so projected locks that move in a P-U contest change nothing. -/
theorem liveLockBlocks_compatible_of_locked {U : Set (AC.Blk sp.n (List (FG.Att sp.n)))}
    (hU : Coherent U) {Φ : AC.Frm sp.n (List (FG.Att sp.n))} (hΦ : FrameOK Φ)
    (hΦU : Φ.tree ⊆ U) {locks : Set AC.Lock} {t : Time}
    {X : AC.Blk sp.n (List (FG.Att sp.n))}
    (h : ∀ l ∈ locks, ∀ B₀ ∈ Φ.tree, B₀.root = l.block → l.LiveAt sp t → Compatible U B₀ X) :
    ∀ L ∈ AC.liveLockBlocks sp locks Φ t, Compatible U L X := by
  intro L hL
  obtain ⟨l, hl, B₀, hB₀, hB₀r, hlive, rfl⟩ := AC.mem_liveLockBlocks hΦ hL
  exact Compose.Growing.compatible_of_head_anc hU
    ((AC.viableAncestor_anc hΦ hB₀).2.mono hΦU) (h l hl B₀ hB₀ hB₀r hlive)

end Consensus.Goldilocks.Shadow.PU

end

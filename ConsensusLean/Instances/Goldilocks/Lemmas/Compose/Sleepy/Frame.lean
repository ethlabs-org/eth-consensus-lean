module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FrameGeometry
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Window
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameSources

public section

/-! # Goldilocks under `Sleepy`: honest-store frame geometry

S3 of the Sleepy invariant. With the source origins relevant at a cut compatible with an origin `C`
and with each other, every target or progress quorum has an honest attestation (`q > f`), whose
named entry is on the origin chain; comparable sources of one height name one entry, so there is no
contest from genesis, the floor is `max(1, h_max − 1)`, and `fc_root` (`Σ.J` or `Σ.F`) is compatible
with `C`.

Both are stated for a block `B` with the hypotheses the argument uses, not only for origins, so
that the proposal-adoption bootstrap (S3P) applies them to the protected
proposal.

The store vocabulary (heights and entries along a held chain, the FG projection, the honest sources
`IsHonestSource`, `HonestRowsSourced`, `RowsAbove`) is in `FrameBase`, imported publicly; the
honest source of a crossing quorum and of `Σ.J` under `RowsAbove` (`frame_crossing_source_of`,
`justified_honest_source_of`) is in `FrameSources`, imported privately.

`FrameFrozen` proves the frozen witness and `FrameLabels` assembles the following consequences:

* **Full reads** (`held_origin_viable`): a held block compatible with every origin, above
  `fc_root`, is in the full viable tree: it is viable itself, or a maximal-height carrier extends
  the named entry of an honest crossing source above it.
* **Votes** (`vote_frame`): at an honest slot-`(s+1)` vote, a block compatible with the origins of
  labels `≤ s` and extended by an honest slot-`s` vote is in the viable tree of the voter block
  tree, or at or below `fc_root` (inside the honest blocks). The
  sources the voter's FG has seen have labels at most `s` (a label-`(s+1)` source is reported at
  the earliest in the tick at `t_{s+1} + Δ`, after the votes there), so `P_{s+1}` compares them;
  the frozen witness is an honest head (of a crossing source when the floor is above `B`, the
  honest slot-`s` head extending `B` otherwise), accepted before the freeze. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

private theorem held_σ_eq {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {y z : Fin sp.n}
    (hy : y ∈ H) (hz : z ∈ H) {i j : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBy : B ∈ (tr.state y i).fg.tree) (hBz : B ∈ (tr.state z j).fg.tree) :
    (tr.state y i).fg.σ B.root = (tr.state z j).fg.σ B.root := by
  rw [← store_eq hrun hy i] at hBy ⊢
  rw [← store_eq hrun hz j] at hBz ⊢
  exact Store.σ_eq_of_held (projFG_localRun hrun hnc) hy hz hBy hBz

/-! ### The store of an honest node whose honest attestations have compatible sources -/

section Geometry

variable {ini} (hrun : GoldilocksRun proposer dg H tr ini)
  (hnc : NoCollRun dg tr)
  (hf : 2 * Hᶜ.ncard < sp.n)
  {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}

include hrun hnc hy in
/-- **Comparable sources of one height name one entry.** -/
private theorem source_entry_eq {D D' E E' : SA.Blk sp.n (List (FG.Att sp.n))}
    (hDD' : Compatible (tr.HonestBlocks H) D D') (hD : IsHonestSource tr H D E.root)
    (hD' : IsHonestSource tr H D' E'.root) (hE : E ∈ (tr.state y i).fg.tree)
    (hE' : E' ∈ (tr.state y i).fg.tree)
    (hh : ((tr.state y i).fg.σ E.root).h = ((tr.state y i).fg.σ E'.root).h) : E = E' := by
  have key : ∀ {D D' E E' : SA.Blk sp.n (List (FG.Att sp.n))}, Anc (tr.HonestBlocks H) D D' →
      IsHonestSource tr H D E.root → IsHonestSource tr H D' E'.root → E ∈ (tr.state y i).fg.tree →
      E' ∈ (tr.state y i).fg.tree →
      ((tr.state y i).fg.σ E.root).h = ((tr.state y i).fg.σ E'.root).h → E = E' := by
    intro D D' E E' hDD hD hD' hE hE' hh
    obtain ⟨x, hx, k, -, hEt, hED, hEh, hET⟩ := honest_source_entry hrun hnc hD ⟨y, hy, i, hE⟩ rfl
    obtain ⟨x', hx', k', hD't, hE't, hE'D', hE'h, hE'T⟩ :=
      honest_source_entry hrun hnc hD' ⟨y, hy, i, hE'⟩ rfl
    have hED' : (tr.state x' k').fg.Anc E D' :=
      honest_held_anc hrun hnc hx' ((hED.mono (fg_tree_subset_honest hx k)).trans hDD) hD't
    have hEt' := anc_mem hED' hD't
    refine held_entry_unique hrun hnc hx' hD't hED' hE'D' ?_ ?_ hE'T
    · rw [held_σ_eq hrun hnc hx' hy hEt' hE, held_σ_eq hrun hnc hx' hy hE't hE']
      exact hh
    · rw [held_σ_eq hrun hnc hx' hx hEt' hEt]
      exact hET
  rcases hDD' with h | h
  · exact key h hD hD' hE hE' hh
  · exact (key h hD' hD hE' hE hh.symm).symm

include hrun hnc hy in
/-- A block held below a source's entry height is below the entry. -/
private theorem below_entry {B D E : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ (tr.state y i).fg.tree) (hE : E ∈ (tr.state y i).fg.tree)
    (hD : IsHonestSource tr H D E.root) (hDB : Compatible (tr.HonestBlocks H) D B)
    (hlt : ((tr.state y i).fg.σ B.root).h < ((tr.state y i).fg.σ E.root).h) :
    (tr.state y i).fg.Anc B E := by
  have hU := (projFG_localRun hrun hnc).coherent
  obtain ⟨x, hx, k, -, -, hED, -, -⟩ := honest_source_entry hrun hnc hD ⟨y, hy, i, hE⟩ rfl
  have hEDU : Anc (tr.HonestBlocks H) E D := hED.mono (fg_tree_subset_honest hx k)
  have no : ¬ Anc (tr.HonestBlocks H) E B := fun h => by
    have := (honest_held_height hrun hnc hy (honest_held_anc hrun hnc hy h hB)).1
    omega
  rcases hDB with h | h
  · exact absurd (hEDU.trans h) no
  · rcases Anc.total hU h hEDU with h' | h'
    · exact honest_held_anc hrun hnc hy h' hE
    · exact absurd h' no

include hrun in
/-- With `h_j = 0`, `Σ.J` is genesis. -/
theorem justified_genesis (h0 : (tr.state y i).fg.hj = 0) (hy : y ∈ H) :
    (tr.state y i).fg.J = sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload :=
  FrameGeometry.justified_genesis hrun.toLocalRun h0 hy

include hrun hnc hf hy in
/-- **No contest from genesis.** -/
private theorem frame_no_contest_of (hsrc : RowsAbove tr H G y i (tr.state y i).fg.hj)
    (hGG : ∀ D D', G D → G D' → Compatible (tr.HonestBlocks H) D D') :
    ¬ (tr.state y i).fg.Contest := by
  rintro ⟨hm, X, hX, -, hXh, hJX⟩
  have hR := fg_reachable hrun.toLocalRun hy i
  by_cases h0 : (tr.state y i).fg.hj = 0
  · rw [justified_genesis hrun h0 hy] at hJX
    exact hJX ((Store.accepted_tree _ _ _ _ hR).2.2.2 X hX)
  obtain ⟨hJh, hJT, D, hD, hDs⟩ := justified_honest_source_of hrun hnc hf hy hsrc (by omega)
  obtain ⟨E, hE, hEX, hEh, hET, D', hD', hD's⟩ :=
    frame_crossing_source_of hrun hnc hf hy hsrc hX (j := (tr.state y i).fg.hj) le_rfl (by omega)
      (by omega)
  have hJ := (Store.cache_invariants _ _ _ _ hR).2.1
  rw [source_entry_eq hrun hnc hy (hGG D D' hD hD') hDs hD's hJ hE (hJh.trans hEh.symm)] at hJX
  exact hJX hEX

include hrun hnc hf hy in
/-- **`Σ.J` is compatible with a block compatible with every source satisfying `G`.** -/
theorem J_compatible (hsrc : RowsAbove tr H G y i (tr.state y i).fg.hj)
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B) (hB : B ∈ tr.HonestBlocks H) :
    Compatible (tr.HonestBlocks H) (tr.state y i).fg.J B := by
  have hU := (projFG_localRun hrun hnc).coherent
  by_cases h0 : (tr.state y i).fg.hj = 0
  · rw [justified_genesis hrun h0 hy]
    obtain ⟨z, hz, j, hBt⟩ := hB
    exact Or.inl (((Store.accepted_tree _ _ _ _ (fg_reachable hrun.toLocalRun hz j)).2.2.2 B
      hBt).mono (fg_tree_subset_honest hz j))
  obtain ⟨-, -, D, hD, hDs⟩ := justified_honest_source_of hrun hnc hf hy hsrc (by omega)
  have hJ := (Store.cache_invariants _ _ _ _ (fg_reachable hrun.toLocalRun hy i)).2.1
  obtain ⟨x, hx, k, -, -, hJD, -, -⟩ := honest_source_entry hrun hnc hDs ⟨y, hy, i, hJ⟩ rfl
  have hJDU : Anc (tr.HonestBlocks H) (tr.state y i).fg.J D := hJD.mono (fg_tree_subset_honest hx k)
  rcases hGB D hD with h | h
  · exact Or.inl (hJDU.trans h)
  · exact Anc.total hU hJDU h

include hrun hnc hf hy in
/-- **The floor, or a crossing source above the block**: with no contest the floor is
`h_max − 1`; when it is above a held block `B`, a carrier of height `h_max` crossed it with an
honest source `D`, whose entry `E` of height `h_max − 1` extends `B`. -/
theorem floor_or_crossing_of (hsrc : RowsAbove tr H G y i (tr.state y i).fg.hj)
    (hGG : ∀ D D', G D → G D' → Compatible (tr.HonestBlocks H) D D')
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B) (hB : B ∈ (tr.state y i).fg.tree) :
    (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ B.root).h ∨
      ∃ D E X, G D ∧ IsHonestSource tr H D E.root ∧ E ∈ (tr.state y i).fg.tree ∧
        (tr.state y i).fg.Anc B E ∧
        ((tr.state y i).fg.σ E.root).h = (tr.state y i).fg.headHeightFloor ∧
        X ∈ (tr.state y i).fg.tree ∧ (tr.state y i).fg.Anc E X ∧ (tr.state y i).fg.IsViable X := by
  have hfl : (tr.state y i).fg.headHeightFloor = (tr.state y i).fg.hmax - 1 := by
    unfold Store.headHeightFloor
    split_ifs with h
    · exact absurd h (frame_no_contest_of hrun hnc hf hy hsrc hGG)
    · rfl
  by_cases hle : (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ B.root).h
  · exact Or.inl hle
  right
  obtain ⟨-, -, -, ⟨Z, hZ, -, hZj⟩, hZm, ⟨X, hX, hXh⟩, -⟩ :=
    Store.cache_invariants _ _ _ _ (fg_reachable hrun.toLocalRun hy i)
  have hB1 := (honest_held_chain hrun hy hB).1
  have hZ1 := (honest_held_chain hrun hy hZ).2.1
  have hZ2 := hZm Z hZ
  obtain ⟨E, hE, hEX, hEh, -, D, hD, hDs⟩ :=
    frame_crossing_source_of hrun hnc hf hy hsrc hX (j := (tr.state y i).fg.hmax - 1) (by omega)
      (by omega) (by omega)
  refine ⟨D, E, X, hD, hDs, hE, below_entry hrun hnc hy hB hE hDs (hGB D hD) (by omega),
    hEh.trans hfl.symm, hX, hEX, ?_⟩
  change (tr.state y i).fg.headHeightFloor ≤ _
  omega

end Geometry

/-- The scoped floor argument needs a fault bound, not the Sleepy regime. Only honest attestations
whose entry height is at least the reader's `h_j` need source witnesses. -/
theorem floor_or_crossing_scoped (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}
    (hsrc : ∀ X ∈ (tr.state y i).fg.tree, ∀ a ∈ X.fgPayload, a.val ∈ H →
      (tr.state y i).fg.hj ≤ ((tr.state y i).fg.σ a.T).h →
      ∃ D, G D ∧ IsHonestSource tr H D a.T)
    (hGG : ∀ D D', G D → G D' → Compatible (tr.HonestBlocks H) D D')
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B)
    (hB : B ∈ (tr.state y i).fg.tree) :
    (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ B.root).h ∨
      ∃ D E X, G D ∧ IsHonestSource tr H D E.root ∧ E ∈ (tr.state y i).fg.tree ∧
        (tr.state y i).fg.Anc B E ∧
        ((tr.state y i).fg.σ E.root).h = (tr.state y i).fg.headHeightFloor ∧
        X ∈ (tr.state y i).fg.tree ∧ (tr.state y i).fg.Anc E X ∧
        (tr.state y i).fg.IsViable X :=
  floor_or_crossing_of hrun hnc hf hy
    (rowsAbove_iff.2 fun X hX a ha hav _ h => hsrc X hX a ha hav h) hGG hGB hB

section Wrappers

variable (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr) (hsl : tr.SleepyRun H ΔF)
  {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}

/-- Justification provenance uses only the numerical fault bound and the supplied attestation
sources. -/
theorem justified_honest_source_before {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) (hf : 2 * Hᶜ.ncard < sp.n) {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}
    (hsrc : HonestRowsSourced tr H G y i)
    (hj : 1 ≤ (tr.state y i).fg.hj) :
    ((tr.state y i).fg.σ (tr.state y i).fg.J.root).h = (tr.state y i).fg.hj ∧
      ((tr.state y i).fg.σ (tr.state y i).fg.J.root).Th = (tr.state y i).fg.J.root ∧
      ∃ D, G D ∧ IsHonestSource tr H D (tr.state y i).fg.J.root :=
  justified_honest_source_of hrun hnc hf hy (hsrc.above _) hj

/-- `frame_crossing_source` with the numerical fault bound in place of `Sleepy`. -/
theorem frame_crossing_source_before {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) (hf : 2 * Hᶜ.ncard < sp.n) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop} (hsrc : HonestRowsSourced tr H G y i)
    {W : SA.Blk sp.n (List (FG.Att sp.n))} (hW : W ∈ (tr.state y i).fg.tree) {j : Nat}
    (hj1 : 1 ≤ j) (hj2 : j < ((tr.state y i).fg.σ W.root).h) :
    ∃ E ∈ (tr.state y i).fg.tree, (tr.state y i).fg.Anc E W ∧
      ((tr.state y i).fg.σ E.root).h = j ∧ ((tr.state y i).fg.σ E.root).Th = E.root ∧
      ∃ D, G D ∧ IsHonestSource tr H D E.root :=
  frame_crossing_source_of hrun hnc hf hy (hsrc.above 0) hW (Nat.zero_le j) hj1 hj2

end Wrappers

end Consensus.Goldilocks.Compose

end

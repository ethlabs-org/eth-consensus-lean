module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FrameSourceGeometry
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Window
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Invariants
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Cut

public section

/-! # Goldilocks under `Sleepy`: the honest-store vocabulary of the frame geometry

The facts of one honest store that the frame geometry (`Compose/Sleepy/Frame`) and its
source lemmas (`Compose/Sleepy/FrameSources`) read: ancestry and heights along a held chain, the
uniqueness of the entry block of one height below a held block, the FG projection of a run
(`projFG_localRun`, `store_eq`), and the honest sources an attestation names (`IsHonestSource`,
`HonestRowsSourced`, `RowsAbove`): the entry a source names is its ancestor
(`honest_source_entry`), and an honest attestation has a source below an origin whose event
precedes the signing (`attestation_source`). `Frame` imports this module publicly. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

/-! ### Chain geometry in one honest store -/

section Store

variable {P : Params} {ACP : Type} {acp₀ : ACP} {H₀ : Set (Fin P.n)} {U : Set (NodeBlock P ACP)}
  {ftr : FGTrace P ACP}

/-- An ancestor of a member is a member. -/
theorem anc_mem {S : Set (NodeBlock P ACP)} {A W : NodeBlock P ACP} (h : Anc S A W)
    (hW : W ∈ S) : A ∈ S :=
  FrameGeometry.anc_mem h hW

/-- One accepted block keeps the justification or justifies its parent's entry. -/
theorem step_J {gp : FG.FGParams} {σ σ' : FG.ChainState gp.n} {B : FG.FGBlock gp.n}
    (h : gp.stateTransition σ B = some σ') :
    (σ'.J = σ.J ∧ σ'.hj = σ.hj) ∨ (σ'.J = σ.Th ∧ σ'.hj = σ.h) :=
  FrameGeometry.step_J h

end Store

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-! ### The FG projection of a run -/

/-- The FG projection of a Goldilocks run is an FG local run inside the honest blocks. -/
theorem projFG_localRun {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) :
    FGLocalRun (goldilocksNode sp ro).genesisPayload H (tr.HonestBlocks H) tr.projFG :=
  fg_projection_from (fun y _ => requirements_from sp ro (hrun.vstart y)) hrun.genesis_root_ok
    hrun.toLocalRun hnc

theorem store_eq {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) :
    tr.projFG.store y i = (tr.state y i).fg :=
  FrameGeometry.store_eq hrun.toLocalRun hy i

/-- The tree of an honest node is among the honest blocks. -/
theorem fg_tree_subset_honest {y : Fin sp.n} (hy : y ∈ H) (i : Nat) :
    (tr.state y i).fg.tree ⊆ tr.HonestBlocks H :=
  FrameGeometry.fg_tree_subset_honest hy i

/-- Ancestry inside the honest blocks below a held block is ancestry in the holder's store. -/
theorem honest_held_anc {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {A W : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : Anc (tr.HonestBlocks H) A W) (hW : W ∈ (tr.state y i).fg.tree) :
    (tr.state y i).fg.Anc A W :=
  FrameGeometry.honest_held_anc hrun.toLocalRun (projFG_localRun hrun hnc) hy h hW

/-- State heights do not decrease along ancestry in an honest store, and equal heights have equal
`Th`. -/
theorem honest_held_height {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {A W : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : (tr.state y i).fg.Anc A W) :
    ((tr.state y i).fg.σ A.root).h ≤ ((tr.state y i).fg.σ W.root).h ∧
      (((tr.state y i).fg.σ W.root).h = ((tr.state y i).fg.σ A.root).h →
        ((tr.state y i).fg.σ W.root).Th = ((tr.state y i).fg.σ A.root).Th) :=
  FrameGeometry.honest_held_height hrun.toLocalRun (projFG_localRun hrun hnc) hy h

/-- Two entries of one state height below one held block are equal. -/
theorem held_entry_unique {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {E E' W : SA.Blk sp.n (List (FG.Att sp.n))}
    (hW : W ∈ (tr.state y i).fg.tree)
    (hE : (tr.state y i).fg.Anc E W) (hE' : (tr.state y i).fg.Anc E' W)
    (hh : ((tr.state y i).fg.σ E.root).h = ((tr.state y i).fg.σ E'.root).h)
    (hT : ((tr.state y i).fg.σ E.root).Th = E.root)
    (hT' : ((tr.state y i).fg.σ E'.root).Th = E'.root) : E = E' :=
  FrameGeometry.held_entry_unique hrun.toLocalRun (projFG_localRun hrun hnc) hy hW hE hE' hh hT hT'

/-- The chain invariants of a held block's state. -/
theorem honest_held_chain {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.state y i).fg.tree) :
    1 ≤ ((tr.state y i).fg.σ B.root).h ∧
      ((tr.state y i).fg.σ B.root).hj < ((tr.state y i).fg.σ B.root).h ∧
      (((tr.state y i).fg.σ B.root).hj = 0 → ((tr.state y i).fg.σ B.root).J = sp.genesisRoot) :=
  FrameGeometry.honest_held_chain hrun.toLocalRun hy hB

/-- An honest attestation on the chain of a held block was signed by its signer before the node
accepted the block, before the cut. -/
theorem honest_row_signed_before {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : X ∈ (tr.state y i).fg.tree) {a : FG.Att sp.n} (ha : a ∈ X.fgPayload) (hav : a.val ∈ H) :
    ∃ m < i, tr.AcceptAt y m X ∧ ∃ k < m, tr.SignAt a.val k a := by
  rw [← store_eq hrun hy i] at hX
  rcases Store.tree_accepted (projFG_localRun hrun hnc) hy hX with rfl | ⟨m, hm, hA⟩
  · simp [Params.genesisBlock] at ha
  · exact ⟨m, hm, projFG_callAt.1 hA,
      hrun.att_unforgeable y hy m a (Or.inr ⟨X, ⟨true, projFG_callAt.1 hA⟩, ha⟩) hav⟩

/-! ### Honest sources -/

/-- The target of an attestation that `create_attestation` signs is the entry of its entry
state. (As `Persist/Attest`'s `createAtt_T`.) -/
private theorem createAtt_T {n : Nat} {Λ Λ' : FG.Record} {v : Fin n} {σe : FG.ChainState n}
    {a : FG.Att n} (h : Λ.createAtt v σe = some (a, Λ')) : a.T = σe.Th := by
  unfold FG.Record.createAtt at h
  rcases hp : Λ.heightPair σe.h σe.Th with _ | ⟨h', T, τ⟩
  · rw [hp] at h; cases h
  · rw [hp] at h
    dsimp only at h
    split_ifs at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
    unfold FG.Record.heightPair at hp
    split_ifs at hp <;> cases hp <;> rfl

/-- `D` is an honest source naming the entry `T`: a block of an honest node's tree whose state
has the entry `T`. -/
def IsHonestSource (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))
    (D : SA.Blk sp.n (List (FG.Att sp.n))) (T : Nat) : Prop :=
  ∃ x ∈ H, ∃ k, D ∈ (tr.state x k).fg.tree ∧ ((tr.state x k).fg.σ D.root).Th = T

theorem isHonestSource_iff {D : SA.Blk sp.n (List (FG.Att sp.n))} {T : Nat} :
    IsHonestSource tr H D T ↔
      ∃ x ∈ H, ∃ k, D ∈ (tr.state x k).fg.tree ∧ ((tr.state x k).fg.σ D.root).Th = T :=
  Iff.rfl

/-- Every honest attestation on a block of `y`'s tree before cut `i` has a source satisfying `G`. -/
def HonestRowsSourced (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))
    (G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop) (y : Fin sp.n) (i : Nat) : Prop :=
  ∀ X ∈ (tr.state y i).fg.tree, ∀ a ∈ X.fgPayload, a.val ∈ H → ∃ D, G D ∧ IsHonestSource tr H D a.T

theorem honestRowsSourced_iff {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop} {y : Fin sp.n}
    {i : Nat} : HonestRowsSourced tr H G y i ↔
      ∀ X ∈ (tr.state y i).fg.tree, ∀ a ∈ X.fgPayload, a.val ∈ H →
        ∃ D, G D ∧ IsHonestSource tr H D a.T :=
  Iff.rfl

/-- Every honest attestation on a block of `y`'s tree before cut `i` that names a block of the tree
(its entry) of height at least `h₀` (in `y`'s states) has a source satisfying `G`: the
attestations the geometry reads at the crossing heights `≥ h₀`. An attestation may name a root
the reader does not hold (a finality-pair attestation of a longer chain); the geometry never
reads those. -/
def RowsAbove (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))
    (G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop) (y : Fin sp.n) (i h₀ : Nat) : Prop :=
  ∀ X ∈ (tr.state y i).fg.tree, ∀ a ∈ X.fgPayload, a.val ∈ H →
    (∃ E ∈ (tr.state y i).fg.tree, E.root = a.T) →
    h₀ ≤ ((tr.state y i).fg.σ a.T).h → ∃ D, G D ∧ IsHonestSource tr H D a.T

theorem rowsAbove_iff {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop} {y : Fin sp.n}
    {i h₀ : Nat} : RowsAbove tr H G y i h₀ ↔
      ∀ X ∈ (tr.state y i).fg.tree, ∀ a ∈ X.fgPayload, a.val ∈ H →
        (∃ E ∈ (tr.state y i).fg.tree, E.root = a.T) →
        h₀ ≤ ((tr.state y i).fg.σ a.T).h → ∃ D, G D ∧ IsHonestSource tr H D a.T :=
  Iff.rfl

theorem HonestRowsSourced.above {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}
    {y : Fin sp.n} {i : Nat} (h : HonestRowsSourced tr H G y i) (h₀ : Nat) :
    RowsAbove tr H G y i h₀ :=
  fun X hX a ha hav _ _ => h X hX a ha hav

/-- The entry an honest source names is its ancestor, an entry block of the source's height. -/
theorem honest_source_entry {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {D : SA.Blk sp.n (List (FG.Att sp.n))} {T : Nat} (hD : IsHonestSource tr H D T)
    {E : SA.Blk sp.n (List (FG.Att sp.n))} (hE : E ∈ tr.HonestBlocks H) (hET : E.root = T) :
    ∃ x ∈ H, ∃ k, D ∈ (tr.state x k).fg.tree ∧ E ∈ (tr.state x k).fg.tree ∧
      (tr.state x k).fg.Anc E D ∧
      ((tr.state x k).fg.σ E.root).h = ((tr.state x k).fg.σ D.root).h ∧
      ((tr.state x k).fg.σ E.root).Th = E.root := by
  apply FrameGeometry.honest_source_entry hrun.toLocalRun (projFG_localRun hrun hnc) _ hE hET
  exact FrameGeometry.isHonestSource_iff.2 (isHonestSource_iff.1 hD)

/-- **An honest attestation names the entry of its source**, a block of the signer's tree below
an origin whose event precedes the signing (the source is a live fast lock block,
`lock_origin`). -/
theorem attestation_source {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {x : Fin sp.n} (hx : x ∈ H) {k : Nat} {a : FG.Att sp.n} (h : tr.SignAt x k a) :
    ∃ D ∈ tr.HonestBlocks H, IsHonestSource tr H D a.T ∧
      ∃ C l, OriginBefore tr H C l k ∧ Anc (tr.HonestBlocks H) D C := by
  obtain ⟨src, hcall⟩ := h
  obtain ⟨j, rfl, ℓ, hcj, -, -, hC, hfg⟩ := attest_source hrun.toLocalRun hx hcall
  rw [(hrun.cutLaw x hx j _ hcj).1] at hC
  have hΦ : FrameOK (Node.frame (tr.state x j)) :=
    (Store.frame_realization _ _ _ _ (fg_reachable hrun.toLocalRun hx j)).1
  -- the source is the deepest candidate: the viable ancestor of a stored fast lock block
  have hcand : src ∈ SA.toFGCandidates sp (tr.state x j).ac (Node.frame (tr.state x j))
      (tr.time j) := by
    have hC' : (SA.acToFG sp (tr.state x j).ac (Node.frame (tr.state x j)) (tr.time j)).2 =
        some src := hC
    unfold SA.acToFG at hC'
    rcases hd : SA.deepest (Node.frame (tr.state x j))
      (SA.toFGCandidates sp (tr.state x j).ac (Node.frame (tr.state x j)) (tr.time j)) with
      _ | D
    · simp only [hd] at hC'
      split_ifs at hC'
    · simp only [hd] at hC'
      split_ifs at hC'
      cases hC'
      exact (SA.deepest_mem hd).1
  obtain ⟨hsv, l, hl, hlb, -, -⟩ := hcand
  obtain ⟨l₀, hl₀, B, hB, hBr, -, rfl⟩ := hl
  obtain ⟨hVt, hVB⟩ := SA.viableAncestor_anc hΦ hB
  obtain rfl : src = (Node.frame (tr.state x j)).viableAncestor B :=
    hΦ.coherent.1 hsv.1 hVt hlb.symm
  obtain ⟨L, hL, hLr, C, hCo, hLC⟩ := lock_origin hrun hnc hx j l₀ hl₀
  obtain rfl : L = B :=
    (projFG_localRun hrun hnc).coherent.1 ⟨x, hx, j, hL⟩ ⟨x, hx, j, hB.1⟩ (hLr.trans hBr.symm)
  -- the attestation names the entry of the source's state
  have hatt := (hrun.cutLaw x hx (j + 1) _ hcall).1
  have hT := createAtt_T hatt
  have hst : (Node.frame (tr.state x j)).viableAncestor L ∈ (tr.state x (j + 1)).fg.tree := by
    rw [hfg]; exact hVt.1
  obtain ⟨⟨E, -, hEr, -, -, hET⟩, -⟩ :=
    Store.entry_state_of_source _ _ _ _ (fg_reachable hrun.toLocalRun hx (j + 1)) _ hst
  rw [← hEr, hET] at hT
  obtain ⟨z, hz, c, hc, CV, ho⟩ := originBefore_iff.1 hCo
  exact ⟨_, ⟨x, hx, j, hVt.1⟩, ⟨x, hx, j + 1, hst, hT.symm⟩, C, l₀.slot,
    originBefore_iff.2 ⟨z, hz, c, by omega, CV, ho⟩,
    (Anc.mono (T := tr.HonestBlocks H) (fun _ hZ => ⟨x, hx, j, hZ.1⟩) hVB).trans hLC⟩

end Consensus.Goldilocks.Compose

end

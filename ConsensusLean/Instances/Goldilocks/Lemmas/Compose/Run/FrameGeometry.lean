module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Components
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Projection
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Cut
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Invariants

public section

/-! # Honest-store geometry over any AC

The node cut law identifies the actual FG stores with the FG projection. Store ancestry and
height facts then need only an `FGLocalRun` of that projection; no concrete AC law is used. -/

namespace Consensus.Goldilocks.Compose.FrameGeometry

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A}

/-- The FG projection and the node have the same honest stores. -/
theorem store_eq (hr : Node.LocalRun proposer dg H sg tr)
    {y : Fin P.n} (hy : y ∈ H) (i : Nat) :
    tr.projFG.store y i = (tr.state y i).fg := by
  change (tr.projFG.state y i).1 = _
  rw [projFG_state hr hy i]

/-- An honest node's tree contributes to the honest-block universe. -/
theorem fg_tree_subset_honest {y : Fin P.n} (hy : y ∈ H) (i : Nat) :
    (tr.state y i).fg.tree ⊆ tr.HonestBlocks H := fun _ hB => ⟨y, hy, i, hB⟩

/-- An ancestor of a member is a member. -/
theorem anc_mem {S : Set A.Blk} {B W : A.Blk} (h : Anc S B W) (hW : W ∈ S) : B ∈ S := by
  by_cases he : B = W
  · exact he ▸ hW
  · exact (Anc.mem h he).1

/-- Ancestry in the honest-block universe lifts below a held block. -/
theorem honest_held_anc (hr : Node.LocalRun proposer dg H sg tr)
    (hf : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    {y : Fin P.n} (hy : y ∈ H) {i : Nat} {B W : A.Blk}
    (h : Anc (tr.HonestBlocks H) B W) (hW : W ∈ (tr.state y i).fg.tree) :
    (tr.state y i).fg.Anc B W := by
  rw [← store_eq hr hy i] at hW ⊢
  exact Store.anc_of_U hf hy h hW

private theorem anc_height {ACP : Type} {acp₀ : ACP} {H₀ : Set (Fin P.n)}
    {U : Set (NodeBlock P ACP)} {ftr : FGTrace P ACP}
    (hr : FGLocalRun acp₀ H₀ U ftr) {y : Fin P.n} (hy : y ∈ H₀)
    {m : Nat} {B W : NodeBlock P ACP} (h : (ftr.store y m).Anc B W) :
    ((ftr.store y m).σ B.root).h ≤ ((ftr.store y m).σ W.root).h ∧
      (((ftr.store y m).σ W.root).h = ((ftr.store y m).σ B.root).h →
        ((ftr.store y m).σ W.root).Th = ((ftr.store y m).σ B.root).Th) := by
  induction h with
  | refl => exact ⟨le_rfl, fun _ => rfl⟩
  | tail _ hYW ih =>
    obtain ⟨c, -, -, -, hc⟩ := Store.chain_state_of_chain P ACP acp₀ _
      (Store.store_reachable hr hy m) _ hYW.1
    obtain ⟨h1, -, -, h4, -⟩ := FG.height_step P.fg _ _ _ _ hc (Store.step_σ hr hy hYW.2.1 hYW.2.2)
    have := ih.1
    rcases h1 with h1 | h1
    · exact ⟨by omega, fun _ => (h4 h1).1.trans (ih.2 (by omega))⟩
    · exact ⟨by omega, fun _ => by omega⟩

/-- Height is monotone along ancestry, with constant entries on height plateaus. -/
theorem honest_held_height (hr : Node.LocalRun proposer dg H sg tr)
    (hf : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    {y : Fin P.n} (hy : y ∈ H) {i : Nat} {B W : A.Blk}
    (h : (tr.state y i).fg.Anc B W) :
    ((tr.state y i).fg.σ B.root).h ≤ ((tr.state y i).fg.σ W.root).h ∧
      (((tr.state y i).fg.σ W.root).h = ((tr.state y i).fg.σ B.root).h →
        ((tr.state y i).fg.σ W.root).Th = ((tr.state y i).fg.σ B.root).Th) := by
  rw [← store_eq hr hy i] at h ⊢
  exact anc_height hf hy h

/-- Two entry blocks of one height below one held block coincide. -/
theorem held_entry_unique (hr : Node.LocalRun proposer dg H sg tr)
    (hf : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    {y : Fin P.n} (hy : y ∈ H) {i : Nat} {E E' W : A.Blk}
    (hW : W ∈ (tr.state y i).fg.tree)
    (hE : (tr.state y i).fg.Anc E W) (hE' : (tr.state y i).fg.Anc E' W)
    (hh : ((tr.state y i).fg.σ E.root).h = ((tr.state y i).fg.σ E'.root).h)
    (hT : ((tr.state y i).fg.σ E.root).Th = E.root)
    (hT' : ((tr.state y i).fg.σ E'.root).Th = E'.root) : E = E' := by
  have coh : Coherent (tr.state y i).fg.tree := hf.coherent.mono (fg_tree_subset_honest hy i)
  apply coh.1 (anc_mem hE hW) (anc_mem hE' hW)
  rcases Anc.total coh hE hE' with h | h
  · exact hT.symm.trans (((honest_held_height hr hf hy h).2 hh.symm).symm.trans hT')
  · exact hT.symm.trans (((honest_held_height hr hf hy h).2 hh).trans hT')

/-- The chain invariants of a held block need no AC projection law. -/
theorem honest_held_chain (hr : Node.LocalRun proposer dg H sg tr)
    {y : Fin P.n} (hy : y ∈ H) {i : Nat} {B : A.Blk}
    (hB : B ∈ (tr.state y i).fg.tree) :
    1 ≤ ((tr.state y i).fg.σ B.root).h ∧
      ((tr.state y i).fg.σ B.root).hj < ((tr.state y i).fg.σ B.root).h ∧
      (((tr.state y i).fg.σ B.root).hj = 0 → ((tr.state y i).fg.σ B.root).J = P.genesisRoot) := by
  obtain ⟨c, -, -, -, hc⟩ := Store.chain_state_of_chain _ _ _ _ (fg_reachable hr hy i) B hB
  obtain ⟨h1, -, h2, h3, -⟩ := FG.chain_invariants _ _ _ hc
  exact ⟨h1, h2, h3⟩

/-- Genesis is an ancestor of every honest block. -/
theorem honest_genesis_anc (hr : Node.LocalRun proposer dg H sg tr)
    {B : A.Blk} (hB : B ∈ tr.HonestBlocks H) :
    P.genesisBlock A.genesisPayload ∈ tr.HonestBlocks H ∧
      Anc (tr.HonestBlocks H) (P.genesisBlock A.genesisPayload) B := by
  obtain ⟨y, hy, i, hBt⟩ := hB
  obtain ⟨-, -, hg, hanc⟩ := Store.accepted_tree _ _ _ _ (fg_reachable hr hy i)
  exact ⟨⟨y, hy, i, hg⟩, (hanc B hBt).mono fun X hX => ⟨y, hy, i, hX⟩⟩

/-- Zero justified height names the actual genesis block. -/
theorem justified_genesis (hr : Node.LocalRun proposer dg H sg tr)
    {y : Fin P.n} {i : Nat} (h0 : (tr.state y i).fg.hj = 0) (hy : y ∈ H) :
    (tr.state y i).fg.J = P.genesisBlock A.genesisPayload := by
  have hR := fg_reachable hr hy i
  obtain ⟨-, hJ, -, ⟨Z, hZ, hZJ, hZj⟩, -⟩ := Store.cache_invariants _ _ _ _ hR
  obtain ⟨-, hcoh, hg, -⟩ := Store.accepted_tree _ _ _ _ hR
  exact hcoh.1 hJ hg (hZJ.symm.trans ((honest_held_chain hr hy hZ).2.2 (hZj.trans h0)))

end Consensus.Goldilocks.Compose.FrameGeometry

end

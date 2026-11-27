module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.CoreStock
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Store.Growing
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Store.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Cache
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Frame
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Coherence
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FrameSourceGeometry
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.FGProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Entries
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Invariants
import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Order
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # P-U shadow: the honest-store geometry and the source geometry over the shadow run

Ports of `Compose/Run/FrameGeometry`, `FrameSourceGeometry` and `FrameViability`
(`J_compatible`) to the shadow store (`Store.Reachable'`) and the shadow runs (`FGLocalRun'`,
`Node.LocalRun'`). None of these facts reads viability: they are facts about the accepted tree,
the state `σ` and its entries, which the shadow shares with the stock store except for the
finalized tip `F` and what acceptance requires of it. The store side is the `_with` lemmas of
`Shadow/PU/Cache`. -/

namespace Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}

/-- In a shadow-reachable store the state of a block is the transition of its parent's. -/
theorem step_σ' (h : st.Reachable acp₀) {W : NodeBlock P ACP} (hW : W ∈ st.tree) {pr : Nat}
    (hp : W.parent = some pr) :
    P.fg.stateTransition (st.σ pr) W.fgView = some (st.σ W.root) := by
  obtain ⟨-, -, -, ht⟩ := step_σ_with finalitySpec_updateFinality h.reachableWith hW hp
  exact ht

/-- The state of a block of a shadow-reachable store records the attestations of its chain
(`prog_rows`): each validator in the progress set signed an attestation on a held block below, for
the state's entry. -/
theorem prog_rows (h : st.Reachable acp₀) {W : NodeBlock P ACP} (hW : W ∈ st.tree) :
    ∀ v ∈ (st.σ W.root).prog, ∃ X ∈ st.tree, st.Anc X W ∧ ∃ a ∈ X.fgPayload, a.val = v ∧
      a.T = (st.σ W.root).Th := by
  have hu := finalitySpec_updateFinality (P := P) (ACP := ACP)
  have hr := h.reachableWith
  have hg := (accepted_tree_with hu hr).2.2.2 W hW
  clear hW
  induction hg with
  | refl =>
    rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, σ_genesis_with hu hr]
    intro v hv
    exact absurd hv (Finset.notMem_empty v)
  | @tail W' W _ hpar ih =>
    obtain ⟨h1, h2, hp⟩ := hpar
    obtain ⟨c, -, -, -, hc⟩ := chain_state_of_chain_with hu hr W' h1
    obtain ⟨-, p, hpv, hcase⟩ := Store.step_prog (step_σ' h h2 hp)
      (FG.chain_invariants P.fg _ _ hc).2.2.2.2.2.2.2.2.2
    rcases hcase with ⟨-, hT, hpe⟩ | ⟨-, he⟩
    · intro v hv
      rw [hpe] at hv
      rcases hpv v hv with hv | ⟨a, ha, hav, haT⟩
      · obtain ⟨X, hX, hXW, a, ha, hav, haT⟩ := ih v hv
        exact ⟨X, hX, hXW.tail ⟨h1, h2, hp⟩, a, ha, hav, haT.trans hT.symm⟩
      · exact ⟨W, h2, .refl, a, ha, hav, haT.trans hT.symm⟩
    · intro v hv
      rw [he] at hv
      exact absurd hv (Finset.notMem_empty v)

/-- **The crossing quorum** (`crossing_quorum`): below a block of a shadow-reachable store, each
height `j` below its own has an entry with a quorum of attestations naming it. -/
theorem crossing_quorum (h : st.Reachable acp₀) {W : NodeBlock P ACP} (hW : W ∈ st.tree) :
    ∀ j, 1 ≤ j → j < (st.σ W.root).h →
      ∃ E ∈ st.tree, st.Anc E W ∧ (st.σ E.root).h = j ∧ (st.σ E.root).Th = E.root ∧
        ∃ Q : Finset (Fin P.n), P.fg.q ≤ Q.card ∧ ∀ v ∈ Q, ∃ X ∈ st.tree,
          st.Anc X W ∧ ∃ a ∈ X.fgPayload, a.val = v ∧ a.T = E.root := by
  have hu := finalitySpec_updateFinality (P := P) (ACP := ACP)
  have hr := h.reachableWith
  have hg := (accepted_tree_with hu hr).2.2.2 W hW
  clear hW
  induction hg with
  | refl =>
    intro j h1 h2
    rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, σ_genesis_with hu hr] at h2
    simp [FG.ChainState.init] at h2
    omega
  | @tail W' W _ hpar ih =>
    obtain ⟨h1, h2, hp⟩ := hpar
    have hst := step_σ' h h2 hp
    obtain ⟨c, -, -, -, hc⟩ := chain_state_of_chain_with hu hr W' h1
    obtain ⟨hstep, -⟩ := FG.height_step P.fg _ _ _ _ hc hst
    have lift : ∀ X, st.Anc X W' → st.Anc X W := fun X hX => hX.tail ⟨h1, h2, hp⟩
    intro j hj1 hj2
    by_cases hlt : j < (st.σ W'.root).h
    · obtain ⟨E, hE, hEW, hEh, hET, Q, hQ, hv⟩ := ih j hj1 hlt
      exact ⟨E, hE, lift E hEW, hEh, hET, Q, hQ, fun v hv' =>
        let ⟨X, hX, hXW, a, ha, h⟩ := hv v hv'; ⟨X, hX, lift X hXW, a, ha, h⟩⟩
    · have hjeq : j = (st.σ W'.root).h := by rcases hstep with h | h <;> omega
      have hh : (st.σ W.root).h = (st.σ W'.root).h + 1 := by
        rcases hstep with h | h <;> omega
      obtain ⟨-, p, hpv, hcase⟩ := Store.step_prog hst
        (FG.chain_invariants P.fg _ _ hc).2.2.2.2.2.2.2.2.2
      have hq : P.fg.q ≤ p.card := by
        rcases hcase with ⟨he, -⟩ | ⟨hq, -⟩
        · omega
        · exact hq
      obtain ⟨⟨E, hE, hEr, hEW', hEh, hET⟩, -⟩ :=
        entry_state_of_source_with hu hr W' h1
      refine ⟨E, hE, lift E hEW', hEh.trans hjeq.symm, hET.trans hEr.symm, p, hq, fun v hv => ?_⟩
      rcases hpv v hv with hv | ⟨a, ha, hav, haT⟩
      · obtain ⟨X, hX, hXW, a, ha, hav, haT⟩ := prog_rows h h1 v hv
        exact ⟨X, hX, lift X hXW, a, ha, hav, haT.trans hEr.symm⟩
      · exact ⟨W, h2, .refl, a, ha, hav, haT.trans hEr.symm⟩

/-- The justification of a block of positive justified height names an entry (`J_entry`). -/
theorem J_entry (h : st.Reachable acp₀) {Z : NodeBlock P ACP} (hZ : Z ∈ st.tree)
    (hj : 1 ≤ (st.σ Z.root).hj) :
    ∃ E ∈ st.tree, E.root = (st.σ Z.root).J ∧ st.Anc E Z ∧
      (st.σ E.root).h = (st.σ Z.root).hj ∧ (st.σ E.root).Th = E.root := by
  obtain ⟨E, hE, hEr, hEZ, hcase⟩ := J_entry_hj_with finalitySpec_updateFinality h.reachableWith hZ
  rcases hcase with ⟨-, h0⟩ | ⟨h1, h2⟩
  · omega
  · exact ⟨E, hE, hEr, hEZ, h1, h2⟩

end Consensus.Goldilocks.Store

namespace Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type} {acp₀ : ACP} {H : Set (Fin P.n)} {U : Set (NodeBlock P ACP)}
  {tr : FGTrace P ACP}

/-- The store of an honest node before every cut of a shadow FG trace is `Reachable'`
(`store_reachable`). -/
theorem store_reachable' (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) (i : Nat) :
    (tr.store y i).Reachable acp₀ := by
  rw [reachable_eq]
  induction i with
  | zero =>
    change Relation.ReflTransGen Step (init acp₀) (tr.init y).1
    rw [hr.init y hy]
  | succ i ih =>
    rw [FGTrace.store, Trace.state]
    split_ifs with hnode
    · obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.1 hnode.2
      have hs : FGLabel.Step y (tr.state y i) ℓ (tr.post i) := by
        rw [← hnode.1]
        exact hr.exec i ℓ hℓ (hnode.1 ▸ hy)
      cases ℓ with
      | block B acc =>
        rcases (FGLabel.step_block _ _ _ _ _).1 hs with ⟨-, h, -⟩ | ⟨-, -, he⟩
        exacts [ih.tail ((step_iff _ _).2 (Or.inl ⟨B, h⟩)), he ▸ ih]
      | attestation a =>
        rw [(FGLabel.step_attestation _ _ _ _).1 hs]
        exact ih.tail ((step_iff _ _).2 (Or.inr ⟨a, rfl⟩))
      | attest src signed =>
        rw [((FGLabel.step_attest _ _ _ _ _).1 hs).1]
        exact ih
    · exact ih

/-- A block of an honest node's tree has its parent held (`parent_held`). -/
theorem parent_held' (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {B : NodeBlock P ACP} (hB : B ∈ (tr.store y i).tree) {r : Nat} (hp : B.parent = some r) :
    ∃ Y, ParentIn (tr.store y i).tree Y B := by
  have h := store_reachable' hr hy i
  rcases (accepted_tree_with finalitySpec_updateFinality h.reachableWith).2.2.2 B hB
    |>.cases_tail with rfl | ⟨Y, -, hY⟩
  · exact absurd hp (by simp [Params.genesisBlock])
  · exact ⟨Y, hY⟩

/-- `U`-ancestry below a held block is ancestry in the tree (`anc_of_U`). -/
theorem anc_of_U' (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {A C : NodeBlock P ACP} (h : Goldilocks.Anc U A C) (hC : C ∈ (tr.store y i).tree) :
    (tr.store y i).Anc A C := by
  induction h with
  | refl => exact .refl
  | tail _ hYC ih =>
    obtain ⟨Z, hZ⟩ := parent_held' hr hy hC hYC.2.2
    obtain rfl : Z = _ := hr.coherent.1 (hr.tree_subset y hy i hZ.1) hYC.1
      (Option.some.inj (hZ.2.2.symm.trans hYC.2.2))
    exact (ih hZ.1).tail hZ

end Consensus.Goldilocks.Store

namespace Consensus.Goldilocks.Compose.FrameGeometry

open Consensus.Goldilocks.Store

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

/-- The FG projection and the shadow node have the same honest stores (`store_eq`). -/
theorem store_eq' (hr : Node.LocalRun proposer dg H sg tr ini)
    {y : Fin P.n} (hy : y ∈ H) (i : Nat) :
    tr.projFG.store y i = (tr.state y i).fg := by
  change (tr.projFG.state y i).1 = _
  rw [projFG_state hr hy i]

/-- Ancestry in the honest-block universe lifts below a held block (`honest_held_anc`). -/
theorem honest_held_anc' (hr : Node.LocalRun proposer dg H sg tr ini)
    (hf : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    {y : Fin P.n} (hy : y ∈ H) {i : Nat} {B W : A.Blk}
    (h : Anc (tr.HonestBlocks H) B W) (hW : W ∈ (tr.state y i).fg.tree) :
    (tr.state y i).fg.Anc B W := by
  rw [← store_eq' hr hy i] at hW ⊢
  exact anc_of_U' hf hy h hW

/-- Height is monotone along ancestry, with constant entries on height plateaus
(`honest_held_height`). -/
theorem honest_held_height' (hr : Node.LocalRun proposer dg H sg tr ini)
    {y : Fin P.n} (hy : y ∈ H) {i : Nat} {B W : A.Blk}
    (h : (tr.state y i).fg.Anc B W) :
    ((tr.state y i).fg.σ B.root).h ≤ ((tr.state y i).fg.σ W.root).h ∧
      (((tr.state y i).fg.σ W.root).h = ((tr.state y i).fg.σ B.root).h →
        ((tr.state y i).fg.σ W.root).Th = ((tr.state y i).fg.σ B.root).Th) :=
  have hR := (Node.fg_reachable_at hr hy i).reachableWith
  ⟨h_le_of_store_anc_with finalitySpec_updateFinality hR h,
    fun he => Th_eq_of_anc_with finalitySpec_updateFinality hR h he⟩

/-- Two entry blocks of one height below one held block coincide (`held_entry_unique`). -/
theorem held_entry_unique' (hr : Node.LocalRun proposer dg H sg tr ini)
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
  · exact hT.symm.trans (((honest_held_height' hr hy h).2 hh.symm).symm.trans hT')
  · exact hT.symm.trans (((honest_held_height' hr hy h).2 hh).trans hT')

/-- The chain invariants of a held block (`honest_held_chain`). -/
theorem honest_held_chain' (hr : Node.LocalRun proposer dg H sg tr ini)
    {y : Fin P.n} (hy : y ∈ H) {i : Nat} {B : A.Blk}
    (hB : B ∈ (tr.state y i).fg.tree) :
    1 ≤ ((tr.state y i).fg.σ B.root).h ∧
      ((tr.state y i).fg.σ B.root).hj < ((tr.state y i).fg.σ B.root).h ∧
      (((tr.state y i).fg.σ B.root).hj = 0 → ((tr.state y i).fg.σ B.root).J = P.genesisRoot) := by
  have hR := (Node.fg_reachable_at hr hy i).reachableWith
  obtain ⟨c, -, -, -, hc⟩ := chain_state_of_chain_with finalitySpec_updateFinality hR B hB
  obtain ⟨h1, -, h2, h3, -⟩ := FG.chain_invariants _ _ _ hc
  exact ⟨h1, h2, h3⟩

/-- Genesis is an ancestor of every honest block (`honest_genesis_anc`). -/
theorem honest_genesis_anc' (hr : Node.LocalRun proposer dg H sg tr ini)
    {B : A.Blk} (hB : B ∈ tr.HonestBlocks H) :
    P.genesisBlock A.genesisPayload ∈ tr.HonestBlocks H ∧
      Anc (tr.HonestBlocks H) (P.genesisBlock A.genesisPayload) B := by
  obtain ⟨y, hy, i, hBt⟩ := hB
  obtain ⟨-, -, hg, hanc⟩ :=
    accepted_tree_with finalitySpec_updateFinality (Node.fg_reachable_at hr hy i).reachableWith
  exact ⟨⟨y, hy, i, hg⟩, (hanc B hBt).mono fun X hX => ⟨y, hy, i, hX⟩⟩

/-- Zero justified height names the actual genesis block (`justified_genesis`). -/
theorem justified_genesis' (hr : Node.LocalRun proposer dg H sg tr ini)
    {y : Fin P.n} {i : Nat} (h0 : (tr.state y i).fg.hj = 0) (hy : y ∈ H) :
    (tr.state y i).fg.J = P.genesisBlock A.genesisPayload := by
  have hR := Node.fg_reachable_at hr hy i
  obtain ⟨-, hJ, -, ⟨Z, hZ, hZJ, hZj⟩, -⟩ := cache_invariants _ _ _ _ hR
  obtain ⟨-, hcoh, hg, -⟩ := accepted_tree_with finalitySpec_updateFinality hR.reachableWith
  exact hcoh.1 hJ hg (hZJ.symm.trans ((honest_held_chain' hr hy hZ).2.2 (hZj.trans h0)))

/-- A source's named entry lies on its held chain (`honest_source_entry`). -/
theorem honest_source_entry' (hr : Node.LocalRun proposer dg H sg tr ini)
    (hf : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    {D : A.Blk} {T : Nat} (hD : IsHonestSource tr H D T)
    {E : A.Blk} (hE : E ∈ tr.HonestBlocks H) (hET : E.root = T) :
    ∃ x ∈ H, ∃ k, D ∈ (tr.state x k).fg.tree ∧ E ∈ (tr.state x k).fg.tree ∧
      (tr.state x k).fg.Anc E D ∧
      ((tr.state x k).fg.σ E.root).h = ((tr.state x k).fg.σ D.root).h ∧
      ((tr.state x k).fg.σ E.root).Th = E.root := by
  obtain ⟨x, hx, k, hDt, hDT⟩ := isHonestSource_iff.1 hD
  obtain ⟨⟨E', hE', hE'r, hE'D, hE'h, hE'T⟩, -⟩ :=
    entry_state_of_source_with finalitySpec_updateFinality
      (Node.fg_reachable_at hr hx k).reachableWith D hDt
  obtain rfl : E' = E := hf.coherent.1 ⟨x, hx, k, hE'⟩ hE (hE'r.trans (hDT.trans hET.symm))
  exact ⟨x, hx, k, hDt, hE', hE'D, hE'h, hE'T.trans hE'r.symm⟩

private theorem honest_mem (hf : 2 * Hᶜ.ncard < P.n) {Q : Finset (Fin P.n)}
    (hQ : P.fg.q ≤ Q.card) : ∃ v ∈ Q, v ∈ H := by
  by_contra hno
  have hsub : (↑Q : Set (Fin P.n)) ⊆ Hᶜ := fun v hv hvH => hno ⟨v, hv, hvH⟩
  have hc := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset] at hc
  have hq : P.fg.q = (2 * P.n + 2) / 3 := rfl
  omega

/-- A crossing quorum supplies an honest row at the crossing's entry
(`frame_crossing_source_of`). -/
theorem frame_crossing_source_of' (hr : Node.LocalRun proposer dg H sg tr ini)
    (hbound : 2 * Hᶜ.ncard < P.n) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {G : A.Blk → Prop} {h₀ : Nat} (hsrc : RowsAbove tr H G y i h₀)
    {W : A.Blk} (hW : W ∈ (tr.state y i).fg.tree) {j : Nat}
    (hj0 : h₀ ≤ j) (hj1 : 1 ≤ j) (hj2 : j < ((tr.state y i).fg.σ W.root).h) :
    ∃ E ∈ (tr.state y i).fg.tree, (tr.state y i).fg.Anc E W ∧
      ((tr.state y i).fg.σ E.root).h = j ∧ ((tr.state y i).fg.σ E.root).Th = E.root ∧
      ∃ D, G D ∧ IsHonestSource tr H D E.root := by
  obtain ⟨E, hE, hEW, hEh, hET, Q, hQ, hv⟩ :=
    crossing_quorum (Node.fg_reachable_at hr hy i) hW j hj1 hj2
  obtain ⟨v, hvQ, hvH⟩ := honest_mem hbound hQ
  obtain ⟨X, hX, -, a, ha, rfl, haT⟩ := hv v hvQ
  obtain ⟨D, hD, hDs⟩ :=
    rowsAbove_iff.1 hsrc X hX a ha hvH ⟨E, hE, haT.symm⟩ (by rw [haT, hEh]; exact hj0)
  exact ⟨E, hE, hEW, hEh, hET, D, hD, haT ▸ hDs⟩

/-- The justification entry has an honest source whenever its height is positive
(`justified_honest_source_of`). -/
theorem justified_honest_source_of' (hr : Node.LocalRun proposer dg H sg tr ini)
    (hf : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    (hbound : 2 * Hᶜ.ncard < P.n) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {G : A.Blk → Prop} (hsrc : RowsAbove tr H G y i (tr.state y i).fg.hj)
    (hj : 1 ≤ (tr.state y i).fg.hj) :
    ((tr.state y i).fg.σ (tr.state y i).fg.J.root).h = (tr.state y i).fg.hj ∧
      ((tr.state y i).fg.σ (tr.state y i).fg.J.root).Th = (tr.state y i).fg.J.root ∧
      ∃ D, G D ∧ IsHonestSource tr H D (tr.state y i).fg.J.root := by
  have hR := Node.fg_reachable_at hr hy i
  obtain ⟨-, hJ, -, ⟨Z, hZ, hZJ, hZj⟩, -⟩ := cache_invariants _ _ _ _ hR
  have hcoh := (accepted_tree_with finalitySpec_updateFinality hR.reachableWith).2.1
  obtain ⟨E, hE, hEr, hEZ, hEh, hET⟩ := J_entry hR hZ (by omega)
  have hEJ : E = (tr.state y i).fg.J := hcoh.1 hE hJ (hEr.trans hZJ)
  obtain ⟨E', -, hE'Z, hE'h, hE'T, D, hD, hDs⟩ :=
    frame_crossing_source_of' hr hbound hy hsrc hZ (j := ((tr.state y i).fg.σ Z.root).hj)
      hZj.ge (by omega) (honest_held_chain' hr hy hZ).2.1
  have hEE' : E = E' := held_entry_unique' hr hf hy hZ hEZ hE'Z (hEh.trans hE'h.symm) hET hE'T
  rw [← hEJ]
  exact ⟨hEh.trans hZj, hET, D, hD, hEE' ▸ hDs⟩

theorem justified_honest_source_before' (hr : Node.LocalRun proposer dg H sg tr ini)
    (hf : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    (hbound : 2 * Hᶜ.ncard < P.n) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {G : A.Blk → Prop} (hsrc : HonestRowsSourced tr H G y i) (hj : 1 ≤ (tr.state y i).fg.hj) :
    ((tr.state y i).fg.σ (tr.state y i).fg.J.root).h = (tr.state y i).fg.hj ∧
      ((tr.state y i).fg.σ (tr.state y i).fg.J.root).Th = (tr.state y i).fg.J.root ∧
      ∃ D, G D ∧ IsHonestSource tr H D (tr.state y i).fg.J.root :=
  justified_honest_source_of' hr hf hbound hy (hsrc.above _) hj

theorem frame_crossing_source_before' (hr : Node.LocalRun proposer dg H sg tr ini)
    (hbound : 2 * Hᶜ.ncard < P.n) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {G : A.Blk → Prop} (hsrc : HonestRowsSourced tr H G y i)
    {W : A.Blk} (hW : W ∈ (tr.state y i).fg.tree) {j : Nat}
    (hj1 : 1 ≤ j) (hj2 : j < ((tr.state y i).fg.σ W.root).h) :
    ∃ E ∈ (tr.state y i).fg.tree, (tr.state y i).fg.Anc E W ∧
      ((tr.state y i).fg.σ E.root).h = j ∧ ((tr.state y i).fg.σ E.root).Th = E.root ∧
      ∃ D, G D ∧ IsHonestSource tr H D E.root :=
  frame_crossing_source_of' hr hbound hy (hsrc.above 0) hW (Nat.zero_le _) hj1 hj2

/-- A held block compatible with a source's whole row lies below the source's entry when it is
lower (`below_entry`). -/
theorem below_entry (hr : Node.LocalRun proposer dg H sg tr ini)
    (hfg : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    {y : Fin P.n} (hy : y ∈ H) {i : Nat} {B D E : A.Blk}
    (hB : B ∈ (tr.state y i).fg.tree) (hE : E ∈ (tr.state y i).fg.tree)
    (hD : IsHonestSource tr H D E.root) (hDB : Compatible (tr.HonestBlocks H) D B)
    (hlt : ((tr.state y i).fg.σ B.root).h < ((tr.state y i).fg.σ E.root).h) :
    (tr.state y i).fg.Anc B E := by
  obtain ⟨x, hx, k, -, -, hED, -, -⟩ := honest_source_entry' hr hfg hD ⟨y, hy, i, hE⟩ rfl
  have hEDU : Anc (tr.HonestBlocks H) E D := hED.mono (fg_tree_subset_honest hx k)
  have no : ¬ Anc (tr.HonestBlocks H) E B := fun h => by
    have := (honest_held_height' hr hy (honest_held_anc' hr hfg hy h hB)).1
    omega
  rcases hDB with h | h
  · exact absurd (hEDU.trans h) no
  · rcases Anc.total hfg.coherent h hEDU with h' | h'
    · exact honest_held_anc' hr hfg hy h' hE
    · exact absurd h' no

/-- **A held block reaches the P-U floor or a source entry at the floor with a viable carrier**
(`floor_or_crossing_of`, with no contest case): the floor is `h_max − 1`, the carrier is a block
of height `h_max`, viable by height. The stock hypothesis `hGG` (sources pairwise compatible) is
only used by the stock proof to exclude a contest, and is not needed. -/
theorem floor_or_crossing_of' (hr : Node.LocalRun proposer dg H sg tr ini)
    (hfg : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    (hf : 2 * Hᶜ.ncard < P.n) {y : Fin P.n} (hy : y ∈ H) {i : Nat} {G : A.Blk → Prop}
    (hsrc : RowsAbove tr H G y i (tr.state y i).fg.hj)
    {B : A.Blk} (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B)
    (hB : B ∈ (tr.state y i).fg.tree) :
    (tr.state y i).fg.hmax - 1 ≤ ((tr.state y i).fg.σ B.root).h ∨
      ∃ D E X, G D ∧ IsHonestSource tr H D E.root ∧ E ∈ (tr.state y i).fg.tree ∧
        (tr.state y i).fg.Anc B E ∧
        ((tr.state y i).fg.σ E.root).h = (tr.state y i).fg.hmax - 1 ∧
        X ∈ (tr.state y i).fg.tree ∧ (tr.state y i).fg.Anc E X ∧ (tr.state y i).fg.IsViable X := by
  by_cases hle : (tr.state y i).fg.hmax - 1 ≤ ((tr.state y i).fg.σ B.root).h
  · exact Or.inl hle
  right
  obtain ⟨-, -, -, ⟨Z, hZ, -, hZj⟩, hZm, ⟨X, hX, hXh⟩, -⟩ :=
    cache_invariants _ _ _ _ (Node.fg_reachable_at hr hy i)
  have hB1 := (honest_held_chain' hr hy hB).1
  have hZ1 := (honest_held_chain' hr hy hZ).2.1
  have hZ2 := hZm Z hZ
  obtain ⟨E, hE, hEX, hEh, -, D, hD, hDs⟩ :=
    frame_crossing_source_of' hr hf hy hsrc hX (j := (tr.state y i).fg.hmax - 1) (by omega)
      (by omega) (by omega)
  exact ⟨D, E, X, hD, hDs, hE, below_entry hr hfg hy hB hE hDs (hGB D hD) (by omega), hEh, hX,
    hEX, Store.isViable_of_hmax_le (by omega)⟩

/-- **Compatibility with all relevant row sources implies compatibility with the justification**
(`J_compatible`; it does not read viability). -/
theorem J_compatible' (hr : Node.LocalRun proposer dg H sg tr ini)
    (hf : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    (hbound : 2 * Hᶜ.ncard < P.n) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {G : A.Blk → Prop} (hsrc : RowsAbove tr H G y i (tr.state y i).fg.hj)
    {B : A.Blk} (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B)
    (hB : B ∈ tr.HonestBlocks H) :
    Compatible (tr.HonestBlocks H) (tr.state y i).fg.J B := by
  by_cases h0 : (tr.state y i).fg.hj = 0
  · rw [justified_genesis' hr h0 hy]
    exact Or.inl (honest_genesis_anc' hr hB).2
  obtain ⟨-, -, D, hD, hDs⟩ := justified_honest_source_of' hr hf hbound hy hsrc (by omega)
  have hJ := (cache_invariants _ _ _ _ (Node.fg_reachable_at hr hy i)).2.1
  obtain ⟨x, hx, k, -, -, hJD, -, -⟩ := honest_source_entry' hr hf hDs ⟨y, hy, i, hJ⟩ rfl
  have hJDU : Anc (tr.HonestBlocks H) (tr.state y i).fg.J D :=
    hJD.mono (fg_tree_subset_honest hx k)
  rcases hGB D hD with h | h
  · exact Or.inl (hJDU.trans h)
  · exact Anc.total hf.coherent hJDU h


/-- **A held block compatible with every honest source stays a shadow candidate**
(`held_candidate_of_rows`): in the shadow frame, rooted at `F`, a block of the frame's tree
compatible with the row sources is in the viable tree. Over the shadow frame the viable heads are
the blocks of height `h_max`, or of height `h_max − 1` with `J ⪯` them or a gap above `h_j`, so the
stock case analysis on a contest is not needed: a block below the floor lies below the entry
at the floor of a maximal block (`floor_or_crossing_of'`), whose carrier has height `h_max`; a block
at the floor is viable, or compatible with `J` and strictly below it in a top frame, where `J` is a
viable head. -/
theorem held_candidate_of_rows' (hr : Node.LocalRun proposer dg H sg tr ini)
    (hfg : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    (hf : 2 * Hᶜ.ncard < P.n) {y : Fin P.n} (hy : y ∈ H) (i : Nat)
    {G : A.Blk → Prop} (hsrc : HonestRowsSourced tr H G y i) {B : A.Blk}
    (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B)
    (hBt : B ∈ (Node.frame (tr.state y i)).tree) :
    (Node.frame (tr.state y i)).Anc B (Node.frame (tr.state y i)).fcRoot ∨
      B ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree := by
  rw [Node.frame_eq] at hBt ⊢
  rw [Store.toFrame_tree] at hBt
  obtain ⟨hB, hFB⟩ := hBt
  right
  rw [Store.mem_viableTree_iff]
  refine ⟨hB, hFB, ?_⟩
  suffices h : ∃ W ∈ (tr.state y i).fg.tree, (tr.state y i).fg.Anc B W ∧
      (tr.state y i).fg.IsViable W by
    obtain ⟨W, hW, hBW, hv⟩ := h
    exact ⟨W, hW, hFB.trans hBW, hv, hBW⟩
  have hR := Node.fg_reachable_at hr hy i
  have hs := hR.puSnapshot
  have hjm := hs.hj_lt_hmax
  rcases floor_or_crossing_of' hr hfg hf hy (hsrc.above _) hGB hB with hpred |
      ⟨-, E, X, -, -, -, hBE, -, hX, hEX, hXv⟩
  swap
  · exact ⟨X, hX, hBE.trans hEX, hXv⟩
  by_cases hv : (tr.state y i).fg.IsViable B
  · exact ⟨B, hB, .refl, hv⟩
  have htop : (tr.state y i).fg.hmax = (tr.state y i).fg.hj + 1 := by
    by_contra hn
    refine hv (((tr.state y i).fg.isViable_iff B).2 ?_)
    by_cases hh : (tr.state y i).fg.hmax ≤ ((tr.state y i).fg.σ B.root).h
    · exact Or.inl hh
    · exact Or.inr ⟨by omega, Or.inl (by omega)⟩
  have hJB := J_compatible' hr hfg hf hy (hsrc.above _) hGB (fg_tree_subset_honest hy i hB)
  have hcomp : Compatible (tr.state y i).fg.tree (tr.state y i).fg.J B := by
    rcases hJB with h | h
    · exact Or.inl (honest_held_anc' hr hfg hy h hB)
    · exact Or.inr (honest_held_anc' hr hfg hy h hs.J_mem)
  obtain ⟨hBJ, -⟩ := (Store.isViable_or_lt_J_of_pred_le hpred hcomp).resolve_left hv
  refine ⟨_, hs.J_mem, hBJ, ?_⟩
  have := Store.J_mem_viableHeads hs htop
  rw [Store.toFrame_viableHeads] at this
  exact this.2.2

end Consensus.Goldilocks.Compose.FrameGeometry

namespace Consensus.Goldilocks.Compose

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ini : Fin sp.n → (goldilocksNode sp ro).State}

/-- **The FG projection of a shadow Goldilocks run is a shadow FG local run** inside the honest
blocks (`projFG_localRun`). Unresolved until `fg_projection_from'` (lane B0b) is proved. -/
theorem projFG_localRun' (hrun : GoldilocksRun proposer dg H tr ini) (hnc : NoCollRun dg tr) :
    FGLocalRun (goldilocksNode sp ro).genesisPayload H (tr.HonestBlocks H) tr.projFG :=
  fg_projection_from (fun y _ => requirements_from sp ro (hrun.vstart y)) hrun.genesis_root_ok
    hrun.toLocalRun hnc

end Consensus.Goldilocks.Compose

end

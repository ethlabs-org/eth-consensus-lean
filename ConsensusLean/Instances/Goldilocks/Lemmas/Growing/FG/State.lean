module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.FG.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Window
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Cut

public section

/-! # The FG state of a block at independently honest observations -/

namespace Consensus.Goldilocks.Store.Growing

variable {P : Params} {ACP : Type} {acp₀ : ACP} {H : Time → Set (Fin P.n)}
  {U : Set (NodeBlock P ACP)} {tr : FGTrace P ACP}

/-- Nodes need only be honest through their own observations, not through a common horizon. -/
theorem σ_eq_of_held (hr : Consensus.Goldilocks.Growing.FGLocalRun acp₀ H U tr)
    {y z : Fin P.n} {d e : Time} (hd : 0 ≤ d) (he : 0 ≤ e)
    (hy : y ∈ H d) (hz : z ∈ H e) {i j : Nat}
    (hi : ∀ k < i, tr.time k ≤ d) (hj : ∀ k < j, tr.time k ≤ e)
    {B : NodeBlock P ACP} (hBy : B ∈ (tr.store y i).tree)
    (hBz : B ∈ (tr.store z j).tree) : (tr.store y i).σ B.root = (tr.store z j).σ B.root := by
  have hsi := Trace.upTo_state tr y hi
  have hsj := Trace.upTo_state tr z hj
  have ry := hr.upTo hd
  have rz := hr.upTo he
  have hgz := (accepted_tree P ACP acp₀ _ (Store.store_reachable rz hz j)).2.2.2
  have hg := (accepted_tree P ACP acp₀ _ (Store.store_reachable ry hy i)).2.2.2
  have hBy' : B ∈ (FGTrace.store (tr.upTo d) y i).tree := by
    simpa only [FGTrace.store, hsi] using hBy
  have hBz' : B ∈ (FGTrace.store (tr.upTo e) z j).tree := by
    simpa only [FGTrace.store, hsj] using hBz
  suffices (FGTrace.store (tr.upTo d) y i).σ B.root =
      (FGTrace.store (tr.upTo e) z j).σ B.root by
    simpa only [FGTrace.store, hsi, hsj] using this
  have hchain := hg B hBy'
  clear hBy hBz hBy' hg
  induction hchain with
  | refl =>
    rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl,
      Store.σ_genesis ry hy, Store.σ_genesis rz hz]
  | @tail W' W _ hpar ih =>
    obtain ⟨h1, h2, hp⟩ := hpar
    have hW'z : W' ∈ (FGTrace.store (tr.upTo e) z j).tree := by
      rcases Relation.ReflTransGen.cases_tail (hgz W hBz') with heq | ⟨Z, -, hZ, -, hZp⟩
      · rw [heq] at hp
        cases hp
      · obtain rfl : Z = W' := hr.coherent.1 (rz.tree_subset z hz j hZ)
          (ry.tree_subset y hy i h1) (Option.some.inj (hZp.symm.trans hp))
        exact hZ
    have hs := Store.step_σ ry hy h2 hp
    rw [ih hW'z, Store.step_σ rz hz hBz' hp] at hs
    exact (Option.some.inj hs).symm

/-- Ancestry transfers between observations honest at their respective horizons. -/
theorem anc_transfer (hr : Consensus.Goldilocks.Growing.FGLocalRun acp₀ H U tr)
    {y z : Fin P.n} {d e : Time} (hd : 0 ≤ d) (he : 0 ≤ e)
    (hy : y ∈ H d) (hz : z ∈ H e) {i j : Nat}
    (hi : ∀ k < i, tr.time k ≤ d) (hj : ∀ k < j, tr.time k ≤ e)
    {A B : NodeBlock P ACP} (h : (tr.store y i).Anc A B)
    (hB : B ∈ (tr.store z j).tree) : (tr.store z j).Anc A B := by
  have ry := hr.upTo hd
  have rz := hr.upTo he
  have hsi := Trace.upTo_state tr y hi
  have hsj := Trace.upTo_state tr z hj
  have h' : (FGTrace.store (tr.upTo d) y i).Anc A B := by
    simpa only [FGTrace.store, hsi] using h
  have hB' : B ∈ (FGTrace.store (tr.upTo e) z j).tree := by
    simpa only [FGTrace.store, hsj] using hB
  suffices (FGTrace.store (tr.upTo e) z j).Anc A B by
    simpa only [FGTrace.store, hsj] using this
  clear h hB
  induction h' with
  | refl => exact .refl
  | tail _ hYB ih =>
    obtain ⟨Z, hZ⟩ := Store.parent_held rz hz hB' hYB.2.2
    obtain rfl : Z = _ := hr.coherent.1 (rz.tree_subset z hz j hZ.1)
      (ry.tree_subset y hy i hYB.1) (Option.some.inj (hZ.2.2.symm.trans hYB.2.2))
    exact (ih hZ.1).tail hZ

end Consensus.Goldilocks.Store.Growing

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameBase
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Window
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Invariants

public section

/-! # Goldilocks under `Sleepy`: honest sources of a crossing and of the justification

In the store of an honest node, with fewer than half of the validators faulty, every height that
a held block's chain crossed has an entry block and a quorum attesting it on the chain, of which
one attestation is honest; when the honest attestations naming held entries of height `≥ h₀` have
sources satisfying `G` (`RowsAbove`), that entry has such a source
(`frame_crossing_source_of`). At `h_j ≥ 1`, `Σ.J` is the entry block of height `h_j` below the
block that justified it, so it has such a source too (`justified_honest_source_of`).

The frame geometry (`Compose/Sleepy/Frame`) imports this module privately; readers that supply
their own `RowsAbove` import it directly. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

section Store

variable {P : Params} {ACP : Type} {acp₀ : ACP} {H₀ : Set (Fin P.n)} {U : Set (NodeBlock P ACP)}
  {ftr : FGTrace P ACP}

/-- Every progress bit of a held block's state has its attestation on the block's chain, naming the
entry. -/
private theorem prog_rows (hr : FGLocalRun acp₀ H₀ U ftr) {y : Fin P.n} (hy : y ∈ H₀) {m : Nat}
    {W : NodeBlock P ACP} (hW : W ∈ (ftr.store y m).tree) :
    ∀ v ∈ ((ftr.store y m).σ W.root).prog, ∃ X ∈ (ftr.store y m).tree,
      (ftr.store y m).Anc X W ∧ ∃ a ∈ X.fgPayload, a.val = v ∧
        a.T = ((ftr.store y m).σ W.root).Th := by
  have hR := Store.store_reachable hr hy m
  have hg := (Store.accepted_tree P ACP acp₀ _ hR).2.2.2 W hW
  clear hW
  induction hg with
  | refl =>
    rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, Store.σ_genesis hr hy]
    intro v hv
    exact absurd hv (Finset.notMem_empty v)
  | @tail W' W _ hpar ih =>
    obtain ⟨h1, h2, hp⟩ := hpar
    obtain ⟨c, -, -, -, hc⟩ := Store.chain_state_of_chain P ACP acp₀ _ hR W' h1
    obtain ⟨-, p, hpv, hcase⟩ := Store.step_prog (Store.step_σ hr hy h2 hp)
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

/-- **Crossing quorums**: every height `1 ≤ j` that a held block's chain left has an entry block
`E` (height `j`, its own entry) on the chain and a quorum of validators with an attestation on the
chain naming `E`. -/
private theorem crossing_quorum (hr : FGLocalRun acp₀ H₀ U ftr) {y : Fin P.n} (hy : y ∈ H₀)
    {m : Nat} {W : NodeBlock P ACP} (hW : W ∈ (ftr.store y m).tree) :
    ∀ j, 1 ≤ j → j < ((ftr.store y m).σ W.root).h →
      ∃ E ∈ (ftr.store y m).tree, (ftr.store y m).Anc E W ∧
        ((ftr.store y m).σ E.root).h = j ∧ ((ftr.store y m).σ E.root).Th = E.root ∧
        ∃ Q : Finset (Fin P.n), P.fg.q ≤ Q.card ∧ ∀ v ∈ Q, ∃ X ∈ (ftr.store y m).tree,
          (ftr.store y m).Anc X W ∧ ∃ a ∈ X.fgPayload, a.val = v ∧ a.T = E.root := by
  have hR := Store.store_reachable hr hy m
  have hg := (Store.accepted_tree P ACP acp₀ _ hR).2.2.2 W hW
  clear hW
  induction hg with
  | refl =>
    intro j h1 h2
    rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, Store.σ_genesis hr hy] at h2
    simp [FG.ChainState.init] at h2
    omega
  | @tail W' W _ hpar ih =>
    obtain ⟨h1, h2, hp⟩ := hpar
    have hst := Store.step_σ hr hy h2 hp
    obtain ⟨c, -, -, -, hc⟩ := Store.chain_state_of_chain P ACP acp₀ _ hR W' h1
    obtain ⟨hstep, -⟩ := FG.height_step P.fg _ _ _ _ hc hst
    have lift : ∀ X, (ftr.store y m).Anc X W' → (ftr.store y m).Anc X W :=
      fun X hX => hX.tail ⟨h1, h2, hp⟩
    intro j hj1 hj2
    by_cases hlt : j < ((ftr.store y m).σ W'.root).h
    · obtain ⟨E, hE, hEW, hEh, hET, Q, hQ, hv⟩ := ih j hj1 hlt
      exact ⟨E, hE, lift E hEW, hEh, hET, Q, hQ, fun v hv' =>
        let ⟨X, hX, hXW, a, ha, h⟩ := hv v hv'; ⟨X, hX, lift X hXW, a, ha, h⟩⟩
    · have hjeq : j = ((ftr.store y m).σ W'.root).h := by rcases hstep with h | h <;> omega
      have hh : ((ftr.store y m).σ W.root).h = ((ftr.store y m).σ W'.root).h + 1 := by
        rcases hstep with h | h <;> omega
      obtain ⟨-, p, hpv, hcase⟩ := Store.step_prog hst
        (FG.chain_invariants P.fg _ _ hc).2.2.2.2.2.2.2.2.2
      have hq : P.fg.q ≤ p.card := by
        rcases hcase with ⟨he, -⟩ | ⟨hq, -⟩
        · omega
        · exact hq
      obtain ⟨⟨E, hE, hEr, hEW', hEh, hET⟩, -⟩ :=
        Store.entry_state_of_source P ACP acp₀ _ hR W' h1
      refine ⟨E, hE, lift E hEW', hEh.trans hjeq.symm, hET.trans hEr.symm, p, hq, fun v hv => ?_⟩
      rcases hpv v hv with hv | ⟨a, ha, hav, haT⟩
      · obtain ⟨X, hX, hXW, a, ha, hav, haT⟩ := prog_rows hr hy h1 v hv
        exact ⟨X, hX, lift X hXW, a, ha, hav, haT.trans hEr.symm⟩
      · exact ⟨W, h2, .refl, a, ha, hav, haT.trans hEr.symm⟩

/-- **The justification of a held block is an entry block** on its chain, of the justified
height. -/
private theorem J_entry (hr : FGLocalRun acp₀ H₀ U ftr) {y : Fin P.n} (hy : y ∈ H₀) {m : Nat}
    {Z : NodeBlock P ACP} (hZ : Z ∈ (ftr.store y m).tree) :
    1 ≤ ((ftr.store y m).σ Z.root).hj → ∃ E ∈ (ftr.store y m).tree,
      E.root = ((ftr.store y m).σ Z.root).J ∧ (ftr.store y m).Anc E Z ∧
      ((ftr.store y m).σ E.root).h = ((ftr.store y m).σ Z.root).hj ∧
      ((ftr.store y m).σ E.root).Th = E.root := by
  have hR := Store.store_reachable hr hy m
  have hg := (Store.accepted_tree P ACP acp₀ _ hR).2.2.2 Z hZ
  clear hZ
  induction hg with
  | refl =>
    rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, Store.σ_genesis hr hy]
    intro h
    simp [FG.ChainState.init] at h
  | @tail W' W _ hpar ih =>
    obtain ⟨h1, h2, hp⟩ := hpar
    intro hj
    rcases step_J (Store.step_σ hr hy h2 hp) with ⟨hJ, hhj⟩ | ⟨hJ, hhj⟩
    · obtain ⟨E, hE, hEr, hEW, hEh, hET⟩ := ih (by omega)
      exact ⟨E, hE, hEr.trans hJ.symm, hEW.tail ⟨h1, h2, hp⟩, hEh.trans hhj.symm, hET⟩
    · obtain ⟨⟨E, hE, hEr, hEW', hEh, hET⟩, -⟩ :=
        Store.entry_state_of_source P ACP acp₀ _ hR W' h1
      exact ⟨E, hE, hEr.trans hJ.symm, hEW'.tail ⟨h1, h2, hp⟩, hEh.trans hhj.symm,
        hET.trans hEr.symm⟩

end Store

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- With `f < n/2`, a quorum has an honest member (`f < n/2 < q`). -/
private theorem honest_mem (hf : 2 * Hᶜ.ncard < sp.n) {Q : Finset (Fin sp.n)}
    (hQ : sp.toParams.fg.q ≤ Q.card) : ∃ v ∈ Q, v ∈ H := by
  by_contra hno
  have hsub : (↑Q : Set (Fin sp.n)) ⊆ Hᶜ := fun v hv hvH => hno ⟨v, hv, hvH⟩
  have hc := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset] at hc
  have hq : sp.toParams.fg.q = (2 * sp.n + 2) / 3 := rfl
  omega

section Geometry

variable (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr) (hf : 2 * Hᶜ.ncard < sp.n)
  {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}

include hrun hnc hf hy in
/-- A crossing quorum has an honest attestation, whose source satisfies `G`. -/
theorem frame_crossing_source_of {h₀ : Nat} (hsrc : RowsAbove tr H G y i h₀)
    {W : SA.Blk sp.n (List (FG.Att sp.n))}
    (hW : W ∈ (tr.state y i).fg.tree) {j : Nat} (hj0 : h₀ ≤ j) (hj1 : 1 ≤ j)
    (hj2 : j < ((tr.state y i).fg.σ W.root).h) :
    ∃ E ∈ (tr.state y i).fg.tree, (tr.state y i).fg.Anc E W ∧
      ((tr.state y i).fg.σ E.root).h = j ∧ ((tr.state y i).fg.σ E.root).Th = E.root ∧
      ∃ D, G D ∧ IsHonestSource tr H D E.root := by
  rw [← store_eq hrun hy i] at hW hj2
  obtain ⟨E, hE, hEW, hEh, hET, Q, hQ, hv⟩ :=
    crossing_quorum (projFG_localRun hrun hnc) hy hW j hj1 hj2
  rw [store_eq hrun hy i] at hE hEW hEh hET hv
  obtain ⟨v, hvQ, hvH⟩ := honest_mem hf hQ
  obtain ⟨X, hX, -, a, ha, rfl, haT⟩ := hv v hvQ
  obtain ⟨D, hD, hDs⟩ :=
    rowsAbove_iff.1 hsrc X hX a ha hvH ⟨E, hE, haT.symm⟩ (by rw [haT, hEh]; exact hj0)
  exact ⟨E, hE, hEW, hEh, hET, D, hD, haT ▸ hDs⟩

include hrun hnc hf hy in
/-- **The justification has an honest source**: at `h_j ≥ 1`, `Σ.J` is an entry block of height
`h_j`, and an honest attestation of its target quorum has a source satisfying `G`. -/
theorem justified_honest_source_of (hsrc : RowsAbove tr H G y i (tr.state y i).fg.hj)
    (hj : 1 ≤ (tr.state y i).fg.hj) :
    ((tr.state y i).fg.σ (tr.state y i).fg.J.root).h = (tr.state y i).fg.hj ∧
      ((tr.state y i).fg.σ (tr.state y i).fg.J.root).Th = (tr.state y i).fg.J.root ∧
      ∃ D, G D ∧ IsHonestSource tr H D (tr.state y i).fg.J.root := by
  have hR := fg_reachable hrun.toLocalRun hy i
  obtain ⟨-, hJ, -, ⟨Z, hZ, hZJ, hZj⟩, -⟩ := Store.cache_invariants _ _ _ _ hR
  have hcoh := (Store.accepted_tree _ _ _ _ hR).2.1
  have hZ' := hZ
  rw [← store_eq hrun hy i] at hZ'
  obtain ⟨E, hE, hEr, hEZ, hEh, hET⟩ := J_entry (projFG_localRun hrun hnc) hy hZ' (by
    rw [store_eq hrun hy i]; omega)
  rw [store_eq hrun hy i] at hE hEr hEZ hEh hET
  have hEJ : E = (tr.state y i).fg.J := hcoh.1 hE hJ (hEr.trans hZJ)
  obtain ⟨E', -, hE'Z, hE'h, hE'T, D, hD, hDs⟩ :=
    frame_crossing_source_of hrun hnc hf hy hsrc hZ (j := ((tr.state y i).fg.σ Z.root).hj)
      hZj.ge (by omega)
      (honest_held_chain hrun hy hZ).2.1
  have hEE' : E = E' := held_entry_unique hrun hnc hy hZ hEZ hE'Z (hEh.trans hE'h.symm) hET hE'T
  rw [← hEJ]
  exact ⟨hEh.trans hZj, hET, D, hD, hEE' ▸ hDs⟩

end Geometry

end Consensus.Goldilocks.Compose

end

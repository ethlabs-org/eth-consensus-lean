module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FrameGeometry
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Window
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Invariants

public section

/-! # Sources of honest FG rows over any AC

Source predicates read actual FG stores. Their geometry uses the node cut law and an FG
local run, independently of the AC implementation and of how the sources are supplied. -/

namespace Consensus.Goldilocks.Compose.FrameGeometry

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A}

/-- A held source names its state's entry. -/
def IsHonestSource (tr : RunTrace A) (H : Set (Fin P.n)) (D : A.Blk) (T : Nat) : Prop :=
  ∃ x ∈ H, ∃ k, D ∈ (tr.state x k).fg.tree ∧ ((tr.state x k).fg.σ D.root).Th = T

theorem isHonestSource_iff {D : A.Blk} {T : Nat} : IsHonestSource tr H D T ↔
    ∃ x ∈ H, ∃ k, D ∈ (tr.state x k).fg.tree ∧ ((tr.state x k).fg.σ D.root).Th = T := by rfl

/-- Every honest row of the held tree has a source satisfying `G`. -/
def HonestRowsSourced (tr : RunTrace A) (H : Set (Fin P.n)) (G : A.Blk → Prop)
    (y : Fin P.n) (i : Nat) : Prop :=
  ∀ X ∈ (tr.state y i).fg.tree, ∀ a ∈ X.fgPayload, a.val ∈ H → ∃ D, G D ∧ IsHonestSource tr H D a.T

theorem honestRowsSourced_iff {G : A.Blk → Prop} {y : Fin P.n} {i : Nat} :
    HonestRowsSourced tr H G y i ↔ ∀ X ∈ (tr.state y i).fg.tree, ∀ a ∈ X.fgPayload,
      a.val ∈ H → ∃ D, G D ∧ IsHonestSource tr H D a.T := by rfl

/-- Only rows naming held entries at or above the specified height need sources. -/
def RowsAbove (tr : RunTrace A) (H : Set (Fin P.n)) (G : A.Blk → Prop)
    (y : Fin P.n) (i h₀ : Nat) : Prop :=
  ∀ X ∈ (tr.state y i).fg.tree, ∀ a ∈ X.fgPayload, a.val ∈ H →
    (∃ E ∈ (tr.state y i).fg.tree, E.root = a.T) →
    h₀ ≤ ((tr.state y i).fg.σ a.T).h → ∃ D, G D ∧ IsHonestSource tr H D a.T

theorem rowsAbove_iff {G : A.Blk → Prop} {y : Fin P.n} {i h₀ : Nat} :
    RowsAbove tr H G y i h₀ ↔ ∀ X ∈ (tr.state y i).fg.tree, ∀ a ∈ X.fgPayload, a.val ∈ H →
      (∃ E ∈ (tr.state y i).fg.tree, E.root = a.T) →
      h₀ ≤ ((tr.state y i).fg.σ a.T).h → ∃ D, G D ∧ IsHonestSource tr H D a.T := by rfl

theorem HonestRowsSourced.above {G : A.Blk → Prop} {y : Fin P.n} {i : Nat}
    (h : HonestRowsSourced tr H G y i) (h₀ : Nat) : RowsAbove tr H G y i h₀ := by
  rw [honestRowsSourced_iff] at h
  exact rowsAbove_iff.2 fun X hX a ha hav _ _ => h X hX a ha hav

/-- A source's named entry lies on its held chain. -/
theorem honest_source_entry (hr : Node.LocalRun proposer dg H sg tr)
    (hf : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    {D : A.Blk} {T : Nat} (hD : IsHonestSource tr H D T)
    {E : A.Blk} (hE : E ∈ tr.HonestBlocks H) (hET : E.root = T) :
    ∃ x ∈ H, ∃ k, D ∈ (tr.state x k).fg.tree ∧ E ∈ (tr.state x k).fg.tree ∧
      (tr.state x k).fg.Anc E D ∧
      ((tr.state x k).fg.σ E.root).h = ((tr.state x k).fg.σ D.root).h ∧
      ((tr.state x k).fg.σ E.root).Th = E.root := by
  obtain ⟨x, hx, k, hDt, hDT⟩ := isHonestSource_iff.1 hD
  obtain ⟨⟨E', hE', hE'r, hE'D, hE'h, hE'T⟩, -⟩ :=
    Store.entry_state_of_source _ _ _ _ (fg_reachable hr hx k) D hDt
  obtain rfl : E' = E := hf.coherent.1 ⟨x, hx, k, hE'⟩ hE (hE'r.trans (hDT.trans hET.symm))
  exact ⟨x, hx, k, hDt, hE', hE'D, hE'h, hE'T.trans hE'r.symm⟩

section Store

variable {ACP : Type} {acp₀ : ACP} {H₀ : Set (Fin P.n)} {U : Set (NodeBlock P ACP)}
  {ftr : FGTrace P ACP}

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

/-- An accepted block retains the justification or justifies its parent's entry. -/
theorem step_J {gp : FG.FGParams} {σ σ' : FG.ChainState gp.n} {B : FG.FGBlock gp.n}
    (h : gp.stateTransition σ B = some σ') :
    (σ'.J = σ.J ∧ σ'.hj = σ.hj) ∨ (σ'.J = σ.Th ∧ σ'.hj = σ.h) := by
  obtain ⟨-, rfl⟩ := gp.stateTransition_eq_some.1 h
  obtain ⟨f, p, t, he⟩ := FG.ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [he]
  obtain ⟨F, hF, σ₁, rfl, -, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, L := B.root, fin := f, prog := p, target := t }
  rcases hcase with ⟨-, he'⟩ | ⟨-, -, he'⟩ | ⟨-, -, he'⟩ <;> rw [he'] <;>
    simp [FG.ChainState.advance]

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

private theorem honest_mem (hf : 2 * Hᶜ.ncard < P.n) {Q : Finset (Fin P.n)}
    (hQ : P.fg.q ≤ Q.card) : ∃ v ∈ Q, v ∈ H := by
  by_contra hno
  have hsub : (↑Q : Set (Fin P.n)) ⊆ Hᶜ := fun v hv hvH => hno ⟨v, hv, hvH⟩
  have hc := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset] at hc
  have hq : P.fg.q = (2 * P.n + 2) / 3 := rfl
  omega

/-- A crossing quorum supplies an honest row at the crossing's entry. -/
theorem frame_crossing_source_of (hr : Node.LocalRun proposer dg H sg tr)
    (hf : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    (hbound : 2 * Hᶜ.ncard < P.n) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {G : A.Blk → Prop} {h₀ : Nat} (hsrc : RowsAbove tr H G y i h₀)
    {W : A.Blk} (hW : W ∈ (tr.state y i).fg.tree) {j : Nat}
    (hj0 : h₀ ≤ j) (hj1 : 1 ≤ j) (hj2 : j < ((tr.state y i).fg.σ W.root).h) :
    ∃ E ∈ (tr.state y i).fg.tree, (tr.state y i).fg.Anc E W ∧
      ((tr.state y i).fg.σ E.root).h = j ∧ ((tr.state y i).fg.σ E.root).Th = E.root ∧
      ∃ D, G D ∧ IsHonestSource tr H D E.root := by
  rw [← store_eq hr hy i] at hW hj2
  obtain ⟨E, hE, hEW, hEh, hET, Q, hQ, hv⟩ := crossing_quorum hf hy hW j hj1 hj2
  rw [store_eq hr hy i] at hE hEW hEh hET hv
  obtain ⟨v, hvQ, hvH⟩ := honest_mem hbound hQ
  obtain ⟨X, hX, -, a, ha, rfl, haT⟩ := hv v hvQ
  obtain ⟨D, hD, hDs⟩ :=
    rowsAbove_iff.1 hsrc X hX a ha hvH ⟨E, hE, haT.symm⟩ (by rw [haT, hEh]; exact hj0)
  exact ⟨E, hE, hEW, hEh, hET, D, hD, haT ▸ hDs⟩

/-- The justification entry has an honest source whenever its height is positive. -/
theorem justified_honest_source_of (hr : Node.LocalRun proposer dg H sg tr)
    (hf : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    (hbound : 2 * Hᶜ.ncard < P.n) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {G : A.Blk → Prop} (hsrc : RowsAbove tr H G y i (tr.state y i).fg.hj)
    (hj : 1 ≤ (tr.state y i).fg.hj) :
    ((tr.state y i).fg.σ (tr.state y i).fg.J.root).h = (tr.state y i).fg.hj ∧
      ((tr.state y i).fg.σ (tr.state y i).fg.J.root).Th = (tr.state y i).fg.J.root ∧
      ∃ D, G D ∧ IsHonestSource tr H D (tr.state y i).fg.J.root := by
  have hR := fg_reachable hr hy i
  obtain ⟨-, hJ, -, ⟨Z, hZ, hZJ, hZj⟩, -⟩ := Store.cache_invariants _ _ _ _ hR
  have hcoh := (Store.accepted_tree _ _ _ _ hR).2.1
  have hZ' := hZ
  rw [← store_eq hr hy i] at hZ'
  obtain ⟨E, hE, hEr, hEZ, hEh, hET⟩ := J_entry hf hy hZ' (by rw [store_eq hr hy i]; omega)
  rw [store_eq hr hy i] at hE hEr hEZ hEh hET
  have hEJ : E = (tr.state y i).fg.J := hcoh.1 hE hJ (hEr.trans hZJ)
  obtain ⟨E', -, hE'Z, hE'h, hE'T, D, hD, hDs⟩ :=
    frame_crossing_source_of hr hf hbound hy hsrc hZ (j := ((tr.state y i).fg.σ Z.root).hj)
      hZj.ge (by omega) (honest_held_chain hr hy hZ).2.1
  have hEE' : E = E' := held_entry_unique hr hf hy hZ hEZ hE'Z (hEh.trans hE'h.symm) hET hE'T
  rw [← hEJ]
  exact ⟨hEh.trans hZj, hET, D, hD, hEE' ▸ hDs⟩

theorem justified_honest_source_before (hr : Node.LocalRun proposer dg H sg tr)
    (hf : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    (hbound : 2 * Hᶜ.ncard < P.n) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {G : A.Blk → Prop} (hsrc : HonestRowsSourced tr H G y i) (hj : 1 ≤ (tr.state y i).fg.hj) :
    ((tr.state y i).fg.σ (tr.state y i).fg.J.root).h = (tr.state y i).fg.hj ∧
      ((tr.state y i).fg.σ (tr.state y i).fg.J.root).Th = (tr.state y i).fg.J.root ∧
      ∃ D, G D ∧ IsHonestSource tr H D (tr.state y i).fg.J.root :=
  justified_honest_source_of hr hf hbound hy (hsrc.above _) hj

theorem frame_crossing_source_before (hr : Node.LocalRun proposer dg H sg tr)
    (hf : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    (hbound : 2 * Hᶜ.ncard < P.n) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {G : A.Blk → Prop} (hsrc : HonestRowsSourced tr H G y i)
    {W : A.Blk} (hW : W ∈ (tr.state y i).fg.tree) {j : Nat}
    (hj1 : 1 ≤ j) (hj2 : j < ((tr.state y i).fg.σ W.root).h) :
    ∃ E ∈ (tr.state y i).fg.tree, (tr.state y i).fg.Anc E W ∧
      ((tr.state y i).fg.σ E.root).h = j ∧ ((tr.state y i).fg.σ E.root).Th = E.root ∧
      ∃ D, G D ∧ IsHonestSource tr H D E.root :=
  frame_crossing_source_of hr hf hbound hy (hsrc.above 0) hW (Nat.zero_le _) hj1 hj2

/-- Compatibility with all sources implies compatibility with the justification. -/
theorem J_compatible_before (hr : Node.LocalRun proposer dg H sg tr)
    (hf : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    (hbound : 2 * Hᶜ.ncard < P.n) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {G : A.Blk → Prop} (hsrc : HonestRowsSourced tr H G y i) {B : A.Blk}
    (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B) (hB : B ∈ tr.HonestBlocks H) :
    Compatible (tr.HonestBlocks H) (tr.state y i).fg.J B := by
  by_cases h0 : (tr.state y i).fg.hj = 0
  · rw [justified_genesis hr h0 hy]
    exact Or.inl (honest_genesis_anc hr hB).2
  obtain ⟨-, -, D, hD, hDs⟩ := justified_honest_source_before hr hf hbound hy hsrc (by omega)
  have hJ := (Store.cache_invariants _ _ _ _ (fg_reachable hr hy i)).2.1
  obtain ⟨x, hx, k, -, -, hJD, -, -⟩ := honest_source_entry hr hf hDs ⟨y, hy, i, hJ⟩ rfl
  have hJDU : Anc (tr.HonestBlocks H) (tr.state y i).fg.J D :=
    hJD.mono fun _ hX => ⟨x, hx, k, hX⟩
  rcases hGB D hD with h | h
  · exact Or.inl (hJDU.trans h)
  · exact Anc.total hf.coherent hJDU h

end Consensus.Goldilocks.Compose.FrameGeometry

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Family
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.CutBase

public section

/-! # FG geometry on the actual node run

No AC observation or execution seam occurs here. The FG projection is an ordinary
`FGLocalRun`, supplied by the existing generic projection theorem and AC requirements.
The source predicates read actual FG stores, not a projected SA state.
-/

namespace Consensus.Goldilocks.FamilySafety

open SA (SAParams ReplayOrder Payload SAOperations SAFamily)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {S M : Type} {A : SAOperations sp (List (FG.Att sp.n)) S M}
  {F : SAFamily sp (List (FG.Att sp.n)) ro A} {tr : RunTrace A.toAC}
  {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {sg : M → Fin sp.n}

/-- FG projection needs the candidate's existing interface requirements, not SA execution. -/
theorem projFG_localRun (hr : FamilyRun F proposer dg H sg tr)
    (hq : A.toAC.Requirements) (hnc : Compose.NoCollRun dg tr) :
    FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG :=
  Compose.fg_projection _ _ dg H _ tr proposer hq hr.genesis_root_ok hr.toLocalRun hnc

/-- Honest stores of the FG projection are the actual stores. -/
theorem store_eq (hr : Node.LocalRun proposer dg H sg tr)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) :
    tr.projFG.store y i = (tr.state y i).fg := by
  change (tr.projFG.state y i).1 = _
  rw [Compose.projFG_state hr hy i]

/-- Store ancestry can be recovered below a held block. -/
theorem honest_held_anc (hr : Node.LocalRun proposer dg H sg tr)
    (hf : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {B W : SA.Blk sp.n (List (FG.Att sp.n))} (h : Anc (tr.HonestBlocks H) B W)
    (hW : W ∈ (tr.state y i).fg.tree) : (tr.state y i).fg.Anc B W := by
  rw [← store_eq hr hy i] at hW ⊢
  exact Store.anc_of_U hf hy h hW

/-- The chain invariants are generic in the AC payload. -/
theorem honest_held_chain (hr : Node.LocalRun proposer dg H sg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.state y i).fg.tree) :
    1 ≤ ((tr.state y i).fg.σ B.root).h ∧
      ((tr.state y i).fg.σ B.root).hj < ((tr.state y i).fg.σ B.root).h ∧
      (((tr.state y i).fg.σ B.root).hj = 0 → ((tr.state y i).fg.σ B.root).J = sp.genesisRoot) := by
  obtain ⟨c, -, -, -, hc⟩ :=
    Store.chain_state_of_chain _ _ _ _ (Compose.fg_reachable hr hy i) B hB
  obtain ⟨h1, -, h2, h3, -⟩ := FG.chain_invariants _ _ _ hc
  exact ⟨h1, h2, h3⟩

/-- Height monotonicity in a component trace; no node or AC laws are involved. -/
private theorem anc_height {P : Params} {ACP : Type} {acp₀ : ACP} {H₀ : Set (Fin P.n)}
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

/-- Height and entry constancy lifted to the real node store. -/
theorem honest_held_height (hr : Node.LocalRun proposer dg H sg tr)
    (hf : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {B W : SA.Blk sp.n (List (FG.Att sp.n))} (h : (tr.state y i).fg.Anc B W) :
    ((tr.state y i).fg.σ B.root).h ≤ ((tr.state y i).fg.σ W.root).h ∧
      (((tr.state y i).fg.σ W.root).h = ((tr.state y i).fg.σ B.root).h →
        ((tr.state y i).fg.σ W.root).Th = ((tr.state y i).fg.σ B.root).Th) := by
  rw [← store_eq hr hy i] at h ⊢
  exact anc_height hf hy h

/-- Two entry blocks of the same height below a held block coincide. -/
theorem held_entry_unique (hr : Node.LocalRun proposer dg H sg tr)
    (hf : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {E E' W : SA.Blk sp.n (List (FG.Att sp.n))} (hW : W ∈ (tr.state y i).fg.tree)
    (hE : (tr.state y i).fg.Anc E W) (hE' : (tr.state y i).fg.Anc E' W)
    (hh : ((tr.state y i).fg.σ E.root).h = ((tr.state y i).fg.σ E'.root).h)
    (hT : ((tr.state y i).fg.σ E.root).Th = E.root)
    (hT' : ((tr.state y i).fg.σ E'.root).Th = E'.root) : E = E' := by
  have hsub : (tr.state y i).fg.tree ⊆ tr.HonestBlocks H := fun _ hX => ⟨y, hy, i, hX⟩
  have coh : Coherent (tr.state y i).fg.tree := hf.coherent.mono hsub
  apply coh.1 (Compose.anc_mem hE hW) (Compose.anc_mem hE' hW)
  rcases Anc.total coh hE hE' with h | h
  · exact hT.symm.trans (((honest_held_height hr hf hy h).2 hh.symm).symm.trans hT')
  · exact hT.symm.trans (((honest_held_height hr hf hy h).2 hh).trans hT')

/-- Actual genesis lies below every held block, for any AC. -/
theorem honest_genesis_anc (hr : Node.LocalRun proposer dg H sg tr)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ tr.HonestBlocks H) :
    sp.toParams.genesisBlock A.genesisPayload ∈ tr.HonestBlocks H ∧
      Anc (tr.HonestBlocks H) (sp.toParams.genesisBlock A.genesisPayload) B := by
  obtain ⟨y, hy, i, hBt⟩ := hB
  obtain ⟨-, -, hg, hanc⟩ := Store.accepted_tree _ _ _ _ (Compose.fg_reachable hr hy i)
  exact ⟨⟨y, hy, i, hg⟩, (hanc B hBt).mono fun X hX => ⟨y, hy, i, hX⟩⟩

/-- Source entry provenance is a fact about actual FG stores. -/
def IsHonestSource (tr : RunTrace A.toAC) (H : Set (Fin sp.n))
    (D : SA.Blk sp.n (List (FG.Att sp.n))) (T : Nat) : Prop :=
  ∃ x ∈ H, ∃ k, D ∈ (tr.state x k).fg.tree ∧ ((tr.state x k).fg.σ D.root).Th = T

/-- Honest rows use one source predicate, independently of the AC family. -/
def HonestRowsSourced (tr : RunTrace A.toAC) (H : Set (Fin sp.n))
    (G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop) (y : Fin sp.n) (i : Nat) : Prop :=
  ∀ X ∈ (tr.state y i).fg.tree, ∀ a ∈ X.fgPayload, a.val ∈ H →
    ∃ D, G D ∧ IsHonestSource tr H D a.T

theorem honestRowsSourced_iff {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}
    {y : Fin sp.n} {i : Nat} : HonestRowsSourced tr H G y i ↔
      ∀ X ∈ (tr.state y i).fg.tree, ∀ a ∈ X.fgPayload, a.val ∈ H →
        ∃ D, G D ∧ IsHonestSource tr H D a.T := by rfl

theorem isHonestSource_iff {D : SA.Blk sp.n (List (FG.Att sp.n))} {T : Nat} :
    IsHonestSource tr H D T ↔
      ∃ x ∈ H, ∃ k, D ∈ (tr.state x k).fg.tree ∧ ((tr.state x k).fg.σ D.root).Th = T := by rfl

/-- An honest source's named entry is held on its chain. -/
theorem honest_source_entry (hr : Node.LocalRun proposer dg H sg tr)
    (hf : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    {D : SA.Blk sp.n (List (FG.Att sp.n))} {T : Nat} (hD : IsHonestSource tr H D T)
    {E : SA.Blk sp.n (List (FG.Att sp.n))} (hE : E ∈ tr.HonestBlocks H) (hET : E.root = T) :
    ∃ x ∈ H, ∃ k, D ∈ (tr.state x k).fg.tree ∧ E ∈ (tr.state x k).fg.tree ∧
      (tr.state x k).fg.Anc E D ∧
      ((tr.state x k).fg.σ E.root).h = ((tr.state x k).fg.σ D.root).h ∧
      ((tr.state x k).fg.σ E.root).Th = E.root := by
  obtain ⟨x, hx, k, hDt, hDT⟩ := hD
  obtain ⟨⟨E', hE', hE'r, hE'D, hE'h, hE'T⟩, -⟩ :=
    Store.entry_state_of_source _ _ _ _ (Compose.fg_reachable hr hx k) D hDt
  obtain rfl : E' = E :=
    hf.coherent.1 ⟨x, hx, k, hE'⟩ hE (hE'r.trans (hDT.trans hET.symm))
  exact ⟨x, hx, k, hDt, hE', hE'D, hE'h, hE'T.trans hE'r.symm⟩

/-- Every progress bit is witnessed on the accepted chain. -/
private theorem prog_rows {P : Params} {ACP : Type} {acp₀ : ACP} {H₀ : Set (Fin P.n)}
    {U : Set (NodeBlock P ACP)} {ftr : FGTrace P ACP}
    (hr : FGLocalRun acp₀ H₀ U ftr) {y : Fin P.n} (hy : y ∈ H₀) {m : Nat}
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

/-- Every crossed height has an entry and a quorum naming it. -/
private theorem crossing_quorum {P : Params} {ACP : Type} {acp₀ : ACP} {H₀ : Set (Fin P.n)}
    {U : Set (NodeBlock P ACP)} {ftr : FGTrace P ACP}
    (hr : FGLocalRun acp₀ H₀ U ftr) {y : Fin P.n} (hy : y ∈ H₀)
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

/-- Crossing provenance over generic node stores. -/
theorem frame_crossing_source_before (hr : Node.LocalRun proposer dg H sg tr)
    (hf : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    (hbound : 2 * Hᶜ.ncard < sp.n) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop} (hsrc : HonestRowsSourced tr H G y i)
    {W : SA.Blk sp.n (List (FG.Att sp.n))} (hW : W ∈ (tr.state y i).fg.tree)
    {j : Nat} (hj1 : 1 ≤ j) (hj2 : j < ((tr.state y i).fg.σ W.root).h) :
    ∃ E ∈ (tr.state y i).fg.tree, (tr.state y i).fg.Anc E W ∧
      ((tr.state y i).fg.σ E.root).h = j ∧ ((tr.state y i).fg.σ E.root).Th = E.root ∧
      ∃ D, G D ∧ IsHonestSource tr H D E.root := by
  rw [← store_eq hr hy i] at hW hj2
  obtain ⟨E, hE, hEW, hEh, hET, Q, hQ, hv⟩ := crossing_quorum hf hy hW j hj1 hj2
  rw [store_eq hr hy i] at hE hEW hEh hET hv
  have hex : ∃ v ∈ Q, v ∈ H := by
    by_contra hno
    have hsub : (↑Q : Set (Fin sp.n)) ⊆ Hᶜ := fun v hv hvH => hno ⟨v, hv, hvH⟩
    have hc := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_coe_finset] at hc
    have hq : sp.toParams.fg.q = (2 * sp.n + 2) / 3 := rfl
    omega
  obtain ⟨v, hvQ, hvH⟩ := hex
  obtain ⟨X, hX, -, a, ha, rfl, haT⟩ := hv v hvQ
  obtain ⟨D, hD, hDs⟩ := hsrc X hX a ha hvH
  exact ⟨E, hE, hEW, hEh, hET, D, hD, haT ▸ hDs⟩

/-- Zero justified height names the actual genesis payload. -/
theorem justified_genesis (hr : Node.LocalRun proposer dg H sg tr)
    {y : Fin sp.n} {i : Nat} (h0 : (tr.state y i).fg.hj = 0) (hy : y ∈ H) :
    (tr.state y i).fg.J = sp.toParams.genesisBlock A.genesisPayload := by
  have hR := Compose.fg_reachable hr hy i
  obtain ⟨-, hJ, -, ⟨Z, hZ, hZJ, hZj⟩, -⟩ := Store.cache_invariants _ _ _ _ hR
  obtain ⟨-, hcoh, hg, -⟩ := Store.accepted_tree _ _ _ _ hR
  exact hcoh.1 hJ hg (hZJ.symm.trans ((honest_held_chain hr hy hZ).2.2 (hZj.trans h0)))

/-- The justification entry is witnessed on every accepted chain. -/
private theorem J_entry {P : Params} {ACP : Type} {acp₀ : ACP} {H₀ : Set (Fin P.n)}
    {U : Set (NodeBlock P ACP)} {ftr : FGTrace P ACP}
    (hr : FGLocalRun acp₀ H₀ U ftr) {y : Fin P.n} (hy : y ∈ H₀) {m : Nat}
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
    rcases Compose.step_J (Store.step_σ hr hy h2 hp) with ⟨hJ, hhj⟩ | ⟨hJ, hhj⟩
    · obtain ⟨E, hE, hEr, hEW, hEh, hET⟩ := ih (by omega)
      exact ⟨E, hE, hEr.trans hJ.symm, hEW.tail ⟨h1, h2, hp⟩, hEh.trans hhj.symm, hET⟩
    · obtain ⟨⟨E, hE, hEr, hEW', hEh, hET⟩, -⟩ :=
        Store.entry_state_of_source P ACP acp₀ _ hR W' h1
      exact ⟨E, hE, hEr.trans hJ.symm, hEW'.tail ⟨h1, h2, hp⟩, hEh.trans hhj.symm,
        hET.trans hEr.symm⟩

/-- Justification provenance uses a fault bound and FG geometry only. -/
theorem justified_honest_source_before (hr : Node.LocalRun proposer dg H sg tr)
    (hf : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    (hbound : 2 * Hᶜ.ncard < sp.n) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop} (hsrc : HonestRowsSourced tr H G y i)
    (hj : 1 ≤ (tr.state y i).fg.hj) :
    ((tr.state y i).fg.σ (tr.state y i).fg.J.root).h = (tr.state y i).fg.hj ∧
      ((tr.state y i).fg.σ (tr.state y i).fg.J.root).Th = (tr.state y i).fg.J.root ∧
      ∃ D, G D ∧ IsHonestSource tr H D (tr.state y i).fg.J.root := by
  have hR := Compose.fg_reachable hr hy i
  obtain ⟨-, hJ, -, ⟨Z, hZ, hZJ, hZj⟩, -⟩ := Store.cache_invariants _ _ _ _ hR
  have hcoh := (Store.accepted_tree _ _ _ _ hR).2.1
  have hZ' := hZ
  rw [← store_eq hr hy i] at hZ'
  obtain ⟨E, hE, hEr, hEZ, hEh, hET⟩ := J_entry hf hy hZ' (by
    rw [store_eq hr hy i]; omega)
  rw [store_eq hr hy i] at hE hEr hEZ hEh hET
  have hEJ : E = (tr.state y i).fg.J := hcoh.1 hE hJ (hEr.trans hZJ)
  obtain ⟨E', -, hE'Z, hE'h, hE'T, D, hD, hDs⟩ :=
    frame_crossing_source_before hr hf hbound hy hsrc hZ
      (j := ((tr.state y i).fg.σ Z.root).hj) (by omega) (honest_held_chain hr hy hZ).2.1
  have hEE' : E = E' := held_entry_unique hr hf hy hZ hEZ hE'Z (hEh.trans hE'h.symm) hET hE'T
  rw [← hEJ]
  exact ⟨hEh.trans hZj, hET, D, hD, hEE' ▸ hDs⟩

/-- A justification is compatible with any honest block compatible with its sources. -/
theorem J_compatible_before (hr : Node.LocalRun proposer dg H sg tr)
    (hf : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    (hbound : 2 * Hᶜ.ncard < sp.n) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop} (hsrc : HonestRowsSourced tr H G y i)
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B) (hB : B ∈ tr.HonestBlocks H) :
    Compatible (tr.HonestBlocks H) (tr.state y i).fg.J B := by
  by_cases h0 : (tr.state y i).fg.hj = 0
  · rw [justified_genesis hr h0 hy]
    exact Or.inl (honest_genesis_anc hr hB).2
  obtain ⟨-, -, D, hD, hDs⟩ := justified_honest_source_before hr hf hbound hy hsrc (by omega)
  have hJ := (Store.cache_invariants _ _ _ _ (Compose.fg_reachable hr hy i)).2.1
  obtain ⟨x, hx, k, -, -, hJD, -, -⟩ := honest_source_entry hr hf hDs ⟨y, hy, i, hJ⟩ rfl
  have hJDU : Anc (tr.HonestBlocks H) (tr.state y i).fg.J D :=
    hJD.mono fun _ hX => ⟨x, hx, k, hX⟩
  rcases hGB D hD with h | h
  · exact Or.inl (hJDU.trans h)
  · exact Anc.total hf.coherent hJDU h

end Consensus.Goldilocks.FamilySafety

end

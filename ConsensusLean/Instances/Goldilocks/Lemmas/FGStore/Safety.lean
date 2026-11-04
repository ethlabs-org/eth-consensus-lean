module
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Accountable
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Client
public import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Order

public section

/-! # Goldilocks FG store: finalized safety (G1.4)

Two honest finalized tips that conflict are the finalizations of two accepted chains that
finalize conflicting blocks (G0.3, G0.1), so accountable safety (G1.3) gives `2q − n` validators
with a slashable pair on the two chains; one of them is honest. Its two attestations were
processed by the honest nodes that accepted the blocks carrying them, so (unforgeability) it
signed both, and they are outputs of one client run (`signed_run`): client safety (G0.5)
excludes the pair. -/

namespace Consensus.Goldilocks.Store

/-- Every block of a chain of `S` linked from `A ∈ S` (and `A`) is an ancestor of its last
block. -/
theorem anc_of_linked {P : Params} {ACP : Type} {S : Set (NodeBlock P ACP)} :
    ∀ (c : List (NodeBlock P ACP)) (A : NodeBlock P ACP), A ∈ S → (∀ X ∈ c, X ∈ S) →
      c.map Block.parent = ((A.root :: c.map Block.root).take c.length).map some →
      ∀ B, (A :: c).getLast? = some B → ∀ X ∈ A :: c, Goldilocks.Anc S X B
  | [], A, _, _, _, B, hB, X, hX => by
    simp only [List.getLast?_singleton, Option.some.injEq, List.mem_singleton] at hB hX
    exact hX ▸ hB ▸ .refl
  | C :: c, A, hA, hc, hl, B, hB, X, hX => by
    simp only [List.map_cons, List.length_cons, List.take_succ_cons, List.cons.injEq] at hl
    rw [List.getLast?_cons_cons] at hB
    have ih := anc_of_linked c C (hc C List.mem_cons_self)
      (fun X hX => hc X (List.mem_cons_of_mem _ hX)) hl.2 B hB
    rcases List.mem_cons.1 hX with rfl | hX
    · exact .head ⟨hA, hc C List.mem_cons_self, hl.1⟩ (ih C List.mem_cons_self)
    · exact ih X hX

/-- **What one honest store gives**: a chain whose state finalizes its finalized tip, every block
of `U` named by a root of the chain is compatible with that tip, every attestation of the chain
with an honest signer was signed before the cut, and the chain is that of a block `B` of the
store's tree (each attestation of the chain is in the payload of an ancestor of `B` there). -/
theorem finalized_chain {P : Params} {ACP : Type} {acp₀ : ACP} {H : Set (Fin P.n)}
    {U : Set (NodeBlock P ACP)} {tr : FGTrace P ACP} (hr : FGLocalRun acp₀ H U tr)
    {y : Fin P.n} (hy : y ∈ H) (i : Nat) :
    ∃ c σ, P.fg.chainState c = some σ ∧ σ.F = (tr.store y i).F.root ∧
      (tr.store y i).F ∈ U ∧ (∀ X ∈ U, X.root ∈ P.fg.roots c → Compatible U X (tr.store y i).F) ∧
      (∀ a ∈ P.fg.chainAtts c, a.val ∈ H → ∃ k < i, tr.SignAt a.val k a) ∧
      ∃ B ∈ (tr.store y i).tree, ∀ a ∈ P.fg.chainAtts c,
        ∃ Y ∈ (tr.store y i).tree, (tr.store y i).Anc Y B ∧ a ∈ Y.fgPayload := by
  have hR := store_reachable hr hy i
  have hsub := hr.tree_subset y hy i
  obtain ⟨hF, -, -, -, -, -, B, hB, hBF⟩ := cache_invariants P ACP acp₀ _ hR
  obtain ⟨c, hc, hl, hlast, hσ⟩ := chain_state_of_chain P ACP acp₀ _ hR B hB
  obtain ⟨-, hcoh, hg, -⟩ := accepted_tree P ACP acp₀ _ hR
  obtain ⟨-, ⟨X', hX', hX'r, hX'B⟩, -⟩ := entry_state_of_source P ACP acp₀ _ hR B hB
  rw [hr.coherent.1 (hsub hX') (hsub hF) (hX'r.trans hBF)] at hX'B
  have hanc := anc_of_linked c _ hg hc hl B (by
    rcases hlast with ⟨rfl, rfl⟩ | h
    · rfl
    · simp [List.getLast?_cons, h])
  refine ⟨_, _, hσ, hBF, hsub hF, fun X hXU hX => ?_, fun a ha hav => ?_, B, hB,
    fun a ha => ?_⟩
  · obtain ⟨Y, hY, hYX⟩ : ∃ Y ∈ P.genesisBlock acp₀ :: c, Y.root = X.root := by
      simpa [FG.FGParams.roots, Block.fgView, Params.fg, Params.genesisBlock, eq_comm] using hX
    have hYt : Y ∈ (tr.store y i).tree := by
      rcases List.mem_cons.1 hY with rfl | h
      exacts [hg, hc _ h]
    rw [← hr.coherent.1 (hsub hYt) hXU hYX]
    exact (Goldilocks.Anc.total hcoh (hanc Y hY) hX'B).imp (Anc.mono hsub) (Anc.mono hsub)
  · obtain ⟨_, hX, haX⟩ := List.mem_flatMap.1 ha
    obtain ⟨X, hXc, rfl⟩ := List.mem_map.1 hX
    rcases tree_accepted hr hy (hc X hXc) with rfl | ⟨k, hk, hacc⟩
    · cases haX
    · obtain ⟨k', hk', hs⟩ := hr.unforgeable y hy k a ⟨_, hacc, haX⟩ hav
      exact ⟨k', by omega, hs⟩
  · obtain ⟨_, hX, haX⟩ := List.mem_flatMap.1 ha
    obtain ⟨X, hXc, rfl⟩ := List.mem_map.1 hX
    exact ⟨X, hc X hXc, hanc X (List.mem_cons_of_mem _ hXc), haX⟩

/-- The replay-finalized target of an honest held carrier is compatible with any honest
cache. The two signature prefixes end at the given cuts; no future event is required. -/
theorem replay_finalized_safety {P : Params} {ACP : Type} {acp₀ : ACP}
    {H : Set (Fin P.n)} {U : Set (NodeBlock P ACP)} {tr : FGTrace P ACP}
    (hr : FGLocalRun acp₀ H U tr) (hH : Hᶜ.ncard < 2 * P.fg.q - P.n)
    {x y : Fin P.n} (hx : x ∈ H) (hy : y ∈ H) {i j : Nat} {B X : NodeBlock P ACP}
    (hB : B ∈ (tr.store x i).tree) (hX : X ∈ (tr.store x i).tree)
    (hXr : X.root = ((tr.store x i).σ B.root).F) :
    Compatible U X (tr.store y j).F := by
  have hR := store_reachable hr hx i
  have hsub := hr.tree_subset x hx i
  obtain ⟨c, hc, hl, hlast, hσ⟩ := chain_state_of_chain P ACP acp₀ _ hR B hB
  obtain ⟨_, hcoh, hg, _⟩ := accepted_tree P ACP acp₀ _ hR
  obtain ⟨_, ⟨X', hX', hX'r, hXB⟩, _⟩ := entry_state_of_source P ACP acp₀ _ hR B hB
  have he : X' = X := hr.coherent.1 (hsub hX') (hsub hX) (hX'r.trans hXr.symm)
  rw [he] at hXB
  have hanc := anc_of_linked c _ hg hc hl B (by
    rcases hlast with ⟨rfl, rfl⟩ | h
    · rfl
    · simp [List.getLast?_cons, h])
  have hcompat : ∀ Z ∈ U, Z.root ∈ P.fg.roots (c.map Block.fgView) → Compatible U Z X := by
    intro Z hZU hZ
    obtain ⟨W, hW, hWZ⟩ : ∃ W ∈ P.genesisBlock acp₀ :: c, W.root = Z.root := by
      simpa [FG.FGParams.roots, Block.fgView, Params.fg, Params.genesisBlock, eq_comm] using hZ
    have hWt : W ∈ (tr.store x i).tree := by
      rcases List.mem_cons.mp hW with rfl | h
      exacts [hg, hc _ h]
    rw [← hr.coherent.1 (hsub hWt) hZU hWZ]
    exact (Goldilocks.Anc.total hcoh (hanc W hW) hXB).imp (Anc.mono hsub) (Anc.mono hsub)
  have hsig : ∀ a ∈ P.fg.chainAtts (c.map Block.fgView), a.val ∈ H →
      ∃ k < i, tr.SignAt a.val k a := by
    intro a ha hav
    obtain ⟨_, hW, haW⟩ := List.mem_flatMap.mp ha
    obtain ⟨W, hWc, rfl⟩ := List.mem_map.mp hW
    rcases tree_accepted hr hx (hc W hWc) with rfl | ⟨k, hk, hacc⟩
    · cases haW
    · obtain ⟨l, hl, hs⟩ := hr.unforgeable x hx k a ⟨_, hacc, haW⟩ hav
      exact ⟨l, by omega, hs⟩
  by_contra hne
  obtain ⟨c₂, σ₂, h₂, hF₂, hU₂, hc₂, ha₂, _⟩ := finalized_chain hr hy j
  obtain ⟨S, hS, hSv⟩ := FG.accountable_safety P.fg _ _ _ _ hσ h₂
    (fun h => hne (hc₂ _ (hsub hX) (hXr ▸ h)))
    (fun h => hne (hcompat _ hU₂ (hF₂ ▸ h)).symm)
  obtain ⟨v, hvS, hv⟩ : ∃ v ∈ S, v ∈ H := by
    by_contra! hS'
    have := Set.ncard_le_ncard (s := (S : Set (Fin P.fg.n))) (t := Hᶜ) hS'
    rw [Set.ncard_coe_finset] at this
    have : (Hᶜ : Set (Fin P.fg.n)).ncard = (Hᶜ : Set (Fin P.n)).ncard := rfl
    have : P.fg.n = P.n := rfl
    omega
  obtain ⟨a, ha, b, hb, rfl, hab⟩ := hSv v hvS
  have signs : ∀ z ∈ P.fg.chainAtts (c.map Block.fgView) ++ P.fg.chainAtts c₂,
      z.val = a.val → ∃ k < max i j, tr.SignAt a.val k z := by
    intro z hz hzv
    rcases List.mem_append.mp hz with hz | hz
    · obtain ⟨k, hk, hs⟩ := hsig z hz (hzv ▸ hv)
      exact ⟨k, hk.trans_le (le_max_left _ _), hzv ▸ hs⟩
    · obtain ⟨k, hk, hs⟩ := ha₂ z hz (hzv ▸ hv)
      exact ⟨k, hk.trans_le (le_max_right _ _), hzv ▸ hs⟩
  obtain ⟨inputs, hin, hrun⟩ := signed_run hr hv (max i j)
  obtain ⟨k, hk, hka⟩ := signs a ha rfl
  obtain ⟨l, hl, hlb⟩ := signs b hb hab.1.symm
  exact FG.client_safety P.fg a.val inputs hin a (hrun k hk a hka) b (hrun l hl b hlb) hab

variable (P : Params) (ACP : Type)

/-- **G1.4.** -/
theorem finalized_safety : FinalizedSafety P ACP := by
  intro acp₀ H U tr hr hH y hy z hz i j
  by_contra hne
  obtain ⟨c₁, σ₁, h₁, hF₁, hU₁, hc₁, ha₁, -⟩ := finalized_chain hr hy i
  obtain ⟨c₂, σ₂, h₂, hF₂, hU₂, hc₂, ha₂, -⟩ := finalized_chain hr hz j
  obtain ⟨S, hS, hSv⟩ := FG.accountable_safety P.fg c₁ c₂ σ₁ σ₂ h₁ h₂
    (fun h => hne (hc₂ _ hU₁ (hF₁ ▸ h))) (fun h => hne (hc₁ _ hU₂ (hF₂ ▸ h)).symm)
  obtain ⟨v, hvS, hv⟩ : ∃ v ∈ S, v ∈ H := by
    by_contra! hS'
    have := Set.ncard_le_ncard (s := (S : Set (Fin P.fg.n))) (t := Hᶜ) hS'
    rw [Set.ncard_coe_finset] at this
    have : (Hᶜ : Set (Fin P.fg.n)).ncard = (Hᶜ : Set (Fin P.n)).ncard := rfl
    have : P.fg.n = P.n := rfl
    omega
  obtain ⟨a, ha, b, hb, rfl, hab⟩ := hSv v hvS
  have hsig : ∀ x ∈ P.fg.chainAtts c₁ ++ P.fg.chainAtts c₂, x.val = a.val →
      ∃ k < i + j, tr.SignAt a.val k x := by
    intro x hx hxv
    rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨k, hk, h⟩ := ha₁ x hx (hxv ▸ hv)
      exact ⟨k, by omega, hxv ▸ h⟩
    · obtain ⟨k, hk, h⟩ := ha₂ x hx (hxv ▸ hv)
      exact ⟨k, by omega, hxv ▸ h⟩
  obtain ⟨inputs, hin, hrun⟩ := signed_run hr hv (i + j)
  obtain ⟨k, hk, hka⟩ := hsig a ha rfl
  obtain ⟨k', hk', hkb⟩ := hsig b hb hab.1.symm
  exact FG.client_safety P.fg a.val inputs hin a (hrun k hk a hka) b (hrun k' hk' b hkb) hab

end Consensus.Goldilocks.Store

end

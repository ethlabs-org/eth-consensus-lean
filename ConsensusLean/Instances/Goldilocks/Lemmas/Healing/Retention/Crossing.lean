module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Quorum
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Client
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Accountable

public section

/-! # Goldilocks Healing, HR.4: G1.2 over FG traces

G1.2 (claims G1.2, G1.3) at chain level is `FG.FGParams.finalization_meets_crossing`
(`Lemmas/FGChain/Accountable`). Over an FG trace with `f < 2q − n` it gives, with
`Store.finalized_safety`'s signing argument
(unforgeability, `Store.signed_run`, client safety G0.5), that a block finalized at height `h_F`
in an honest store is an ancestor of every honest block of state height `> h_F`
(`finalized_anc_of_lt_fg`). -/

namespace Consensus.Goldilocks.Healing

variable {P : Params} {ACP : Type} {acp₀ : ACP} {H : Set (Fin P.n)} {U : Set (NodeBlock P ACP)}
  {tr : FGTrace P ACP}

private theorem anc_of_linked' {S : Set (NodeBlock P ACP)} :
    ∀ (c : List (NodeBlock P ACP)) (A : NodeBlock P ACP), A ∈ S → (∀ X ∈ c, X ∈ S) →
      c.map Block.parent = ((A.root :: c.map Block.root).take c.length).map some →
      ∀ B, (A :: c).getLast? = some B → ∀ X ∈ A :: c, Goldilocks.Anc S X B
  | [], A, _, _, _, B, hB, X, hX => by
    simp only [List.getLast?_singleton, Option.some.injEq, List.mem_singleton] at hB hX
    exact hX ▸ hB ▸ .refl
  | C :: c, A, hA, hc, hl, B, hB, X, hX => by
    simp only [List.map_cons, List.length_cons, List.take_succ_cons, List.cons.injEq] at hl
    rw [List.getLast?_cons_cons] at hB
    have ih := anc_of_linked' c C (hc C List.mem_cons_self)
      (fun X hX => hc X (List.mem_cons_of_mem _ hX)) hl.2 B hB
    rcases List.mem_cons.1 hX with rfl | hX
    · exact .head ⟨hA, hc C List.mem_cons_self, hl.1⟩ (ih C List.mem_cons_self)
    · exact ih X hX

/-- The attestations of honest signers on the chain of blocks of an honest store were signed
before the cut. -/
private theorem chain_signed (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {c : List (NodeBlock P ACP)} (hc : ∀ X ∈ c, X ∈ (tr.store y i).tree) :
    ∀ a ∈ P.fg.chainAtts (c.map Block.fgView), a.val ∈ H → ∃ k < i, tr.SignAt a.val k a := by
  intro a ha hav
  obtain ⟨_, hX, haX⟩ := List.mem_flatMap.1 ha
  obtain ⟨X, hXc, rfl⟩ := List.mem_map.1 hX
  rcases Goldilocks.Store.tree_accepted hr hy (hc X hXc) with rfl | ⟨k, hk, hacc⟩
  · cases haX
  · obtain ⟨k', hk', hs⟩ := hr.unforgeable y hy k a ⟨_, hacc, haX⟩ hav
    exact ⟨k', by omega, hs⟩

/-- **G1.2 over an FG trace** (claims G1.2, G1.4). With `f < 2q − n`, a block `F` finalized by
the state of a held `X` in an honest store is an ancestor of every block `W` of an honest store
whose state height exceeds the finalized height: otherwise `F` is not a root of `W`'s chain, and
the finality quorum on `X`'s chain meets the crossing quorum on `W`'s chain in an honest
validator with an E1 pair, against client safety. -/
theorem finalized_anc_of_lt_fg (hr : FGLocalRun acp₀ H U tr) (hH : Hᶜ.ncard < 2 * P.fg.q - P.n)
    {y z : Fin P.n} (hy : y ∈ H) (hz : z ∈ H) {k m : Nat} {X F W : NodeBlock P ACP}
    (hX : X ∈ (tr.store y k).tree) (hF : F ∈ (tr.store y k).tree)
    (hFr : F.root = ((tr.store y k).σ X.root).F) (hW : W ∈ (tr.store z m).tree)
    (hlt : ((tr.store y k).σ X.root).hF < ((tr.store z m).σ W.root).h) :
    Goldilocks.Anc U F W := by
  have hR₁ := Goldilocks.Store.store_reachable hr hy k
  have hR₂ := Goldilocks.Store.store_reachable hr hz m
  have hsub₁ := hr.tree_subset y hy k
  have hsub₂ := hr.tree_subset z hz m
  obtain ⟨c₁, hc₁, -, -, hσ₁⟩ := Goldilocks.Store.chain_state_of_chain P ACP acp₀ _ hR₁ X hX
  obtain ⟨c₂, hc₂, hl₂, hlast₂, hσ₂⟩ :=
    Goldilocks.Store.chain_state_of_chain P ACP acp₀ _ hR₂ W hW
  obtain ⟨-, -, hg₂, -⟩ := Goldilocks.Store.accepted_tree P ACP acp₀ _ hR₂
  have hanc := anc_of_linked' c₂ _ hg₂ hc₂ hl₂ W (by
    rcases hlast₂ with ⟨rfl, rfl⟩ | h
    · rfl
    · simp [List.getLast?_cons, h])
  by_contra hn
  have hnot : ((tr.store y k).σ X.root).F ∉ P.fg.roots (c₂.map Block.fgView) := by
    intro hmem
    rw [← hFr] at hmem
    obtain ⟨Y, hY, hYF⟩ : ∃ Y ∈ P.genesisBlock acp₀ :: c₂, Y.root = F.root := by
      simpa [FG.FGParams.roots, Block.fgView, Params.fg, Params.genesisBlock, eq_comm] using hmem
    have hYt : Y ∈ (tr.store z m).tree := by
      rcases List.mem_cons.1 hY with rfl | h
      exacts [hg₂, hc₂ _ h]
    obtain rfl : Y = F := hr.coherent.1 (hsub₂ hYt) (hsub₁ hF) hYF
    exact hn ((hanc Y hY).mono hsub₂)
  have hF1 : 1 ≤ ((tr.store y k).σ X.root).hF := by
    by_contra h0
    apply hnot
    rw [(FG.chain_invariants P.fg _ _ hσ₁).2.2.2.2.1 (by omega)]
    exact List.mem_cons_self
  obtain ⟨S, hS, hSv⟩ :=
    P.fg.finalization_meets_crossing hσ₁ hσ₂ hF1 hlt hnot
  obtain ⟨v, hvS, hv⟩ : ∃ v ∈ S, v ∈ H := by
    by_contra! hS'
    have := Set.ncard_le_ncard (s := (S : Set (Fin P.fg.n))) (t := Hᶜ) hS'
    rw [Set.ncard_coe_finset] at this
    have : (Hᶜ : Set (Fin P.fg.n)).ncard = (Hᶜ : Set (Fin P.n)).ncard := rfl
    have : P.fg.n = P.n := rfl
    omega
  obtain ⟨a, ha, b, hb, rfl, hab⟩ := hSv v hvS
  obtain ⟨inputs, hin, hrun⟩ := Goldilocks.Store.signed_run hr hv (k + m)
  obtain ⟨k₁, hk₁, hka⟩ := chain_signed hr hy hc₁ a ha hv
  obtain ⟨k₂, hk₂, hkb⟩ := chain_signed hr hz hc₂ b hb (hab.1 ▸ hv)
  rw [← hab.1] at hkb
  exact FG.client_safety P.fg a.val inputs hin a (hrun k₁ (by omega) a hka) b
    (hrun k₂ (by omega) b hkb) hab

end Consensus.Goldilocks.Healing

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.HeldChains
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Client

public section

/-! # Crossing sets with a fault bound

The crossing sets of `FGStore/HeldChains` have at least `2q − n` validators; a signer set `V`
with `|Vᶜ| < 2q − n` meets them. A premise that two attestations on held blocks with a signer in
`V` are never slashable then completes G1.1 and G1.2 at the stores. The premise is all that is
read from the run, so readers honest at different cuts, under constant or growing faults, supply
it from their own signatures.

* `Store.J_eq_of_hj_eq_of_safe`: two held blocks of two reachable stores with the same `h_j`
  have the same `J`.
* `Store.finalized_anc_of_safe` (G1.2): a block finalized at height `h_F` by a held block of
  one store is a store ancestor of every block of the other store of state height `> h_F`;
  `Store.F_anc_of_hmax_le_of_safe`: so `Σ.F` of the first store is below every block of the
  other of state height `≥ h_max` (`h_F ≤ h_j < h ≤ h_max`).
* `held_atts_safe`: over an FG trace, attestations on blocks held by honest nodes with an honest
  signer are not slashable (unforgeability, `Store.signed_run`, client safety G0.5). -/

namespace Consensus.Goldilocks

/-- A set of at least `k` validators meets every set whose complement has fewer than `k`
members. -/
theorem exists_mem_of_ncard_compl_lt {n k : Nat} {S : Finset (Fin n)} {V : Set (Fin n)}
    (hS : k ≤ S.card) (hV : Vᶜ.ncard < k) : ∃ v ∈ S, v ∈ V := by
  by_contra! h
  have := Set.ncard_le_ncard (s := (S : Set (Fin n))) (t := Vᶜ) h
  rw [Set.ncard_coe_finset] at this
  omega

namespace Store

variable {P : Params} {ACP : Type} {acp₀ : ACP}

/-- **Equal justified heights agree** (G1.1, G0.5 at the stores). Two justification quorums at
one height with different `J` meet in `2q − n` validators with E2 pairs, one of them in `V`. -/
theorem J_eq_of_hj_eq_of_safe {st₁ st₂ : Store P ACP} (hR₁ : st₁.Reachable acp₀)
    (hR₂ : st₂.Reachable acp₀) {V : Set (Fin P.n)} (hV : Vᶜ.ncard < 2 * P.fg.q - P.n)
    -- Safety: attestations on held blocks of `st₁` and `st₂` with a signer in `V` are not
    -- slashable.
    (hsafe : ∀ a b, (∃ Y ∈ st₁.tree, a ∈ Y.fgPayload) → (∃ Y ∈ st₂.tree, b ∈ Y.fgPayload) →
      a.val ∈ V → ¬ FG.slashable a b)
    {B B' : NodeBlock P ACP} (hB : B ∈ st₁.tree) (hB' : B' ∈ st₂.tree)
    (he : (st₁.σ B.root).hj = (st₂.σ B'.root).hj) :
    (st₁.σ B.root).J = (st₂.σ B'.root).J := by
  by_contra hne
  obtain ⟨W, hW, hw⟩ := justified_crossing hR₁ hR₂ hB hB' he hne
  obtain ⟨v, hvW, hv⟩ := exists_mem_of_ncard_compl_lt hW hV
  obtain ⟨a, ⟨Y, hY, -, ha⟩, b, ⟨Y', hY', -, hb⟩, rfl, hab⟩ := hw v hvW
  exact hsafe a b ⟨Y, hY, ha⟩ ⟨Y', hY', hb⟩ hv hab

/-- **G1.2 at the stores.** A block `F` finalized by the state of a held `X` of `st₁` is a store
ancestor of every held `W` of `st₂` whose state height exceeds the finalized height: otherwise
`F` is not on `W`'s chain (roots are injective on the coherent `U`), and the finality and
crossing quorums meet in `2q − n` validators with slashable pairs, one of them in `V`. -/
theorem finalized_anc_of_safe {st₁ st₂ : Store P ACP} (hR₁ : st₁.Reachable acp₀)
    (hR₂ : st₂.Reachable acp₀) {U : Set (NodeBlock P ACP)} (hU : Coherent U)
    (hsub₁ : st₁.tree ⊆ U) (hsub₂ : st₂.tree ⊆ U) {V : Set (Fin P.n)}
    (hV : Vᶜ.ncard < 2 * P.fg.q - P.n)
    -- Safety: attestations on held blocks of `st₁` and `st₂` with a signer in `V` are not
    -- slashable.
    (hsafe : ∀ a b, (∃ Y ∈ st₁.tree, a ∈ Y.fgPayload) → (∃ Y ∈ st₂.tree, b ∈ Y.fgPayload) →
      a.val ∈ V → ¬ FG.slashable a b)
    {X F W : NodeBlock P ACP} (hX : X ∈ st₁.tree) (hF : F ∈ st₁.tree)
    (hFr : F.root = (st₁.σ X.root).F) (hW : W ∈ st₂.tree)
    (hlt : (st₁.σ X.root).hF < (st₂.σ W.root).h) : st₂.Anc F W := by
  by_contra hn
  obtain ⟨S, hS, hw⟩ := finalized_crossing hR₁ hR₂ hX hFr hW hlt fun Y hY hYW hYr =>
    hn (hU.1 (hsub₂ hY) (hsub₁ hF) hYr ▸ hYW)
  obtain ⟨v, hvS, hv⟩ := exists_mem_of_ncard_compl_lt hS hV
  obtain ⟨a, ⟨Y, hY, -, ha⟩, b, ⟨Y', hY', -, hb⟩, rfl, hab⟩ := hw v hvS
  exact hsafe a b ⟨Y, hY, ha⟩ ⟨Y', hY', hb⟩ hv hab

/-- **`Σ.F` below every block of state height `≥ h_max`** (G1.2 with `h_F ≤ h_j < h ≤ h_max`
on the chain of the block whose state finalizes `Σ.F`). -/
theorem F_anc_of_hmax_le_of_safe {st₁ st₂ : Store P ACP} (hR₁ : st₁.Reachable acp₀)
    (hR₂ : st₂.Reachable acp₀) {U : Set (NodeBlock P ACP)} (hU : Coherent U)
    (hsub₁ : st₁.tree ⊆ U) (hsub₂ : st₂.tree ⊆ U) {V : Set (Fin P.n)}
    (hV : Vᶜ.ncard < 2 * P.fg.q - P.n)
    -- Safety: attestations on held blocks of `st₁` and `st₂` with a signer in `V` are not
    -- slashable.
    (hsafe : ∀ a b, (∃ Y ∈ st₁.tree, a ∈ Y.fgPayload) → (∃ Y ∈ st₂.tree, b ∈ Y.fgPayload) →
      a.val ∈ V → ¬ FG.slashable a b)
    {B : NodeBlock P ACP} (hB : B ∈ st₂.tree) (hle : st₁.hmax ≤ (st₂.σ B.root).h) :
    st₂.Anc st₁.F B := by
  obtain ⟨hF, -, -, -, hge, -, X, hX, hXF⟩ := cache_invariants _ _ _ _ hR₁
  obtain ⟨c, -, -, -, hc⟩ := chain_state_of_chain _ _ _ _ hR₁ X hX
  have hinv := FG.chain_invariants _ _ _ hc
  have hXh := hge X hX
  have h1 := hinv.2.1
  have h2 := hinv.2.2.1
  exact finalized_anc_of_safe hR₁ hR₂ hU hsub₁ hsub₂ hV hsafe hX hF hXF.symm hB (by omega)

end Store

namespace Healing

variable {P : Params} {ACP : Type} {acp₀ : ACP} {H : Set (Fin P.n)} {U : Set (NodeBlock P ACP)}
  {tr : FGTrace P ACP}

/-- An attestation on a block held by an honest store, with an honest signer, was signed before
the cut. -/
private theorem held_att_signed (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H)
    {i : Nat} {a : FG.Att P.n} (ha : ∃ Y ∈ (tr.store y i).tree, a ∈ Y.fgPayload)
    (hav : a.val ∈ H) : ∃ k < i, tr.SignAt a.val k a := by
  obtain ⟨X, hX, haX⟩ := ha
  rcases Store.tree_accepted hr hy hX with rfl | ⟨k, hk, hacc⟩
  · cases haX
  · obtain ⟨k', hk', hs⟩ := hr.unforgeable y hy k a ⟨_, hacc, haX⟩ hav
    exact ⟨k', by omega, hs⟩

/-- **Honest held attestations are not slashable.** Two attestations on blocks held by honest
stores, with an honest signer, were signed by that signer's client run, which client safety
(G0.5) keeps free of slashable pairs. -/
theorem held_atts_safe (hr : FGLocalRun acp₀ H U tr) {y z : Fin P.n} (hy : y ∈ H) (hz : z ∈ H)
    (i j : Nat) (a b : FG.Att P.n) (ha : ∃ Y ∈ (tr.store y i).tree, a ∈ Y.fgPayload)
    (hb : ∃ Y ∈ (tr.store z j).tree, b ∈ Y.fgPayload) (hav : a.val ∈ H) :
    ¬ FG.slashable a b := fun hab => by
  obtain ⟨inputs, hin, hrun⟩ := Store.signed_run hr hav (i + j)
  obtain ⟨k, hk, hka⟩ := held_att_signed hr hy ha hav
  obtain ⟨l, hl, hlb⟩ := held_att_signed hr hz hb (hab.1 ▸ hav)
  rw [← hab.1] at hlb
  exact FG.client_safety P.fg a.val inputs hin a (hrun k (by omega) a hka) b
    (hrun l (by omega) b hlb) hab

end Healing

end Consensus.Goldilocks

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.HeldSafety
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Finality
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Quorum

public section

/-! # The cache of a reachable store under the held-attestation safety premise

Facts about the cached `h_j`, `Σ.J` and `Σ.F` of reachable FG stores, from the premise of
`Healing/HeldSafety` (attestations on held blocks with a signer in a set `V` with
`|Vᶜ| < 2q − n` are not slashable), so that readers honest at different cuts, under constant or
growing faults, share them.

* `Store.hj_lt_hmax_of_reachable`: `h_j < h_max`.
* `Store.J_eq_of_cache_hj_eq_of_safe`: two stores with equal cached `h_j` have equal `Σ.J`
  (G1.1 on the blocks that cache them; roots are injective on a coherent `U`).
* `Store.F_anc_of_hj_lt_of_safe` (store-level G1.2): `Σ.F` of one store is a store ancestor of
  every block of the other of state height above its `h_j`; `Σ.F` is genesis, below a genesis
  `Σ.J`, or the finalized entry of height `h_F ≤ h(Σ.J) ≤ h_j`. -/

namespace Consensus.Goldilocks.Healing

namespace Store

variable {P : Params} {ACP : Type} {acp₀ : ACP}

/-- `h_j < h_max` in a reachable store. -/
theorem hj_lt_hmax_of_reachable {st : Store P ACP} (hR : st.Reachable acp₀) :
    st.hj < st.hmax := by
  obtain ⟨-, -, -, ⟨Bj, hBj, -, hBjhj⟩, hge, -, -⟩ := Goldilocks.Store.cache_invariants _ _ _ _ hR
  exact hBjhj ▸ (hj_lt_h hR hBj).trans_le (hge Bj hBj)

/-- **Equal cached `h_j` give equal `Σ.J`.** -/
theorem J_eq_of_cache_hj_eq_of_safe {st₁ st₂ : Store P ACP} (hR₁ : st₁.Reachable acp₀)
    (hR₂ : st₂.Reachable acp₀) {U : Set (NodeBlock P ACP)} (hU : Coherent U)
    (hsub₁ : st₁.tree ⊆ U) (hsub₂ : st₂.tree ⊆ U) {V : Set (Fin P.n)}
    (hV : Vᶜ.ncard < 2 * P.fg.q - P.n)
    -- Safety: attestations on held blocks of `st₁` and `st₂` with a signer in `V` are not
    -- slashable.
    (hsafe : ∀ a b, (∃ Y ∈ st₁.tree, a ∈ Y.fgPayload) → (∃ Y ∈ st₂.tree, b ∈ Y.fgPayload) →
      a.val ∈ V → ¬ FG.slashable a b)
    (he : st₁.hj = st₂.hj) : st₁.J = st₂.J := by
  obtain ⟨-, hJ₁, -, ⟨B₁, hB₁, hB₁J, hB₁hj⟩, -⟩ := Goldilocks.Store.cache_invariants _ _ _ _ hR₁
  obtain ⟨-, hJ₂, -, ⟨B₂, hB₂, hB₂J, hB₂hj⟩, -⟩ := Goldilocks.Store.cache_invariants _ _ _ _ hR₂
  have h := Goldilocks.Store.J_eq_of_hj_eq_of_safe hR₁ hR₂ hV hsafe hB₁ hB₂ (by omega)
  exact hU.1 (hsub₁ hJ₁) (hsub₂ hJ₂) (hB₁J.symm.trans (h.trans hB₂J))

/-- **`Σ.F` below every block of state height `> h_j`** (store-level G1.2). -/
theorem F_anc_of_hj_lt_of_safe {st₁ st₂ : Store P ACP} (hR₁ : st₁.Reachable acp₀)
    (hR₂ : st₂.Reachable acp₀) {U : Set (NodeBlock P ACP)} (hU : Coherent U)
    (hsub₁ : st₁.tree ⊆ U) (hsub₂ : st₂.tree ⊆ U) {V : Set (Fin P.n)}
    (hV : Vᶜ.ncard < 2 * P.fg.q - P.n)
    -- Safety: attestations on held blocks of `st₁` and `st₂` with a signer in `V` are not
    -- slashable.
    (hsafe : ∀ a b, (∃ Y ∈ st₁.tree, a ∈ Y.fgPayload) → (∃ Y ∈ st₂.tree, b ∈ Y.fgPayload) →
      a.val ∈ V → ¬ FG.slashable a b)
    {B : NodeBlock P ACP} (hB : B ∈ st₂.tree) (hlt : st₁.hj < (st₂.σ B.root).h) :
    st₂.Anc st₁.F B := by
  have hcoh : Coherent st₁.tree := hU.mono hsub₁
  have hg := genesis_mem hR₁
  obtain ⟨hFm, hJm, hFJ, ⟨Bj, hBj, hBjJ, hBjhj⟩, -, -, ⟨Bf, hBf, hBfF⟩⟩ :=
    Goldilocks.Store.cache_invariants _ _ _ _ hR₁
  have hgF : st₁.Anc (P.genesisBlock acp₀) st₁.F :=
    (Goldilocks.Store.accepted_tree _ _ _ _ hR₁).2.2.2 _ hFm
  have hgen : st₁.F.root = P.genesisRoot → st₂.Anc st₁.F B := fun he => by
    rw [hcoh.1 hFm hg he]
    exact (Goldilocks.Store.accepted_tree _ _ _ _ hR₂).2.2.2 B hB
  rcases fin_pair_entry hR₁ hBf with he | ⟨W, hW, hWr, hWh⟩
  · exact hgen (hBfF.symm.trans he)
  obtain rfl : W = st₁.F := hcoh.1 hW hFm (hWr.trans hBfF)
  obtain ⟨E, hE, hEr, -, hcase⟩ := J_entry_of_reachable hR₁ hBj
  obtain rfl : E = st₁.J := hcoh.1 hE hJm (hEr.trans hBjJ)
  rcases hcase with hEg | ⟨hEh, -⟩
  · rw [hEg] at hFJ
    exact hgen (congrArg Block.root (Anc.antisymm hcoh hFJ hgF))
  have h₁ := h_le_of_store_anc hR₁ hFJ
  exact Goldilocks.Store.finalized_anc_of_safe hR₁ hR₂ hU hsub₁ hsub₂ hV hsafe hBf hFm
    hBfF.symm hB (by omega)

end Store

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

end Consensus.Goldilocks.Healing

end

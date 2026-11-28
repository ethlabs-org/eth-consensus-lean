module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Store
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.CutSteps
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.CoreStock

public section

/-! # Goldilocks Healing, HR.4: the prefix-local quorum-free core

The core of `Store.quorum_free_entries` (G1.10) at one reachable FG store, with the time bounds
replaced by a premise on the store itself: if no attestation of an
honest signer on a block of the store names the entry `E`, then the progress set of every state
with entry `E` holds faulty validators only (fewer than `q`), so no block above an ancestor with
entry `E` leaves its height or entry (`entry_kept`). The justification of a state names its
entry at the justified height (`J_entry_of_reachable`), so a store's `Σ.J` whose entry is kept
would have a state of height `h_j`, against `h_j < h` (`J_compatible_of_rows`). -/

namespace Consensus.Goldilocks.Healing

namespace Store

variable {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}

/-- The state of a held block is above its justification: `h_j < h`. -/
theorem hj_lt_h (hr : st.Reachable acp₀) {B : NodeBlock P ACP} (hB : B ∈ st.tree) :
    (st.σ B.root).hj < (st.σ B.root).h := by
  obtain ⟨c, -, -, -, hc⟩ := Goldilocks.Store.chain_state_of_chain P ACP acp₀ _ hr B hB
  exact (FG.chain_invariants P.fg _ _ hc).2.2.1

/-- The justification of a held block's state names a held ancestor: genesis, or the entry of
the justified height. -/
theorem J_entry_of_reachable (hr : st.Reachable acp₀) {W : NodeBlock P ACP} (hW : W ∈ st.tree) :
    ∃ E ∈ st.tree, E.root = (st.σ W.root).J ∧ st.Anc E W ∧ (E = P.genesisBlock acp₀ ∨
      ((st.σ E.root).h = (st.σ W.root).hj ∧ (st.σ E.root).Th = E.root)) := by
  have hg := genesis_mem hr
  have hA := (Goldilocks.Store.accepted_tree P ACP acp₀ _ hr).2.2.2 W hW
  clear hW
  induction hA with
  | refl =>
    rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, σ_genesis hr]
    exact ⟨_, hg, rfl, .refl, Or.inl rfl⟩
  | tail _ hYW ih =>
    obtain ⟨X, -, hXr, ht⟩ := step_σ hr hYW.2.1 hYW.2.2
    rcases (Goldilocks.Store.step_fields ht).2 with ⟨hJ, hj⟩ | ⟨hJ, hj⟩
    · obtain ⟨E, hE, h1, hEY, h2⟩ := ih
      refine ⟨E, hE, h1.trans hJ.symm, hEY.tail hYW, ?_⟩
      rw [hj]
      exact h2
    · obtain ⟨⟨E, hE, h1, hEY, h2, h3⟩, -⟩ :=
        Goldilocks.Store.entry_state_of_source P ACP acp₀ _ hr _ hYW.1
      exact ⟨E, hE, h1.trans hJ.symm, hEY.tail hYW, Or.inr ⟨h2.trans hj.symm, h3.trans h1.symm⟩⟩

/-- The block named by a justification has at least its recorded height, including genesis. -/
theorem J_height_le (hr : st.Reachable acp₀) {W J : NodeBlock P ACP}
    (hW : W ∈ st.tree) (hJ : J ∈ st.tree) (hJr : J.root = (st.σ W.root).J) :
    (st.σ W.root).hj ≤ (st.σ J.root).h := by
  have hA := (Goldilocks.Store.accepted_tree P ACP acp₀ _ hr).2.2.2 W hW
  clear hW
  induction hA generalizing J with
  | refl =>
    rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, σ_genesis hr]
    exact Nat.zero_le _
  | tail _ hYW ih =>
    obtain ⟨_, _, _, ht⟩ := step_σ hr hYW.2.1 hYW.2.2
    rcases (Goldilocks.Store.step_fields ht).2 with ⟨hroot, hh⟩ | ⟨hroot, hh⟩
    · rw [hh]
      exact ih hJ (hJr.trans hroot)
    · obtain ⟨⟨E, hE, hEr, _, hEh, _⟩, _⟩ :=
        Goldilocks.Store.entry_state_of_source P ACP acp₀ _ hr _ hYW.1
      have he : J = E := (Goldilocks.Store.accepted_tree P ACP acp₀ _ hr).2.1.1
        hJ hE ((hJr.trans hroot).trans hEr.symm)
      rw [he, hEh, hh]

/-- **The prefix-local quorum-free core** (the counting of
`Store.quorum_free_entries` at one store). If no honest signer has an attestation naming `E` on a
block of the store and the faulty validators are fewer than `q`, then every block above an
ancestor with entry `E` keeps that ancestor's height and the entry `E`. -/
theorem entry_kept (hr : st.Reachable acp₀) {H : Set (Fin P.n)} (hq : Hᶜ.ncard < P.fg.q)
    {E : NodeBlock P ACP}
    (hE : ∀ W ∈ st.tree, ∀ a ∈ W.fgPayload, a.T = E.root → a.val ∉ H)
    {A X : NodeBlock P ACP} (hAX : st.Anc A X) (hATh : (st.σ A.root).Th = E.root) :
    (st.σ X.root).h = (st.σ A.root).h ∧ (st.σ X.root).Th = E.root :=
  Goldilocks.Store.entry_kept_with Goldilocks.Store.finalitySpec_updateFinality
    hr.reachableWith hq hE hAX hATh

/-- **A high `Σ.J` is compatible with `B`** when, for every high entry of
the store that conflicts with `B`, no honest signer has an attestation naming it on a block of
the store: otherwise its entry is kept above it (`entry_kept`), against `h_j < h` at the block
whose state justifies it. A genesis `Σ.J` is below `B`. -/
theorem J_compatible_of_rows (hr : st.Reachable acp₀) {H : Set (Fin P.n)}
    (hq : Hᶜ.ncard < P.fg.q) {U : Set (NodeBlock P ACP)} (hU : Coherent U) (hsub : st.tree ⊆ U)
    {B : NodeBlock P ACP} (hgB : Goldilocks.Anc U (P.genesisBlock acp₀) B) {Hz : Nat}
    (hrow : ∀ E ∈ st.tree, Hz + 1 ≤ (st.σ E.root).h → (st.σ E.root).Th = E.root →
      ¬ Compatible U E B → ∀ W ∈ st.tree, ∀ a ∈ W.fgPayload, a.T = E.root → a.val ∉ H)
    (hj : Hz + 1 ≤ st.hj) : Compatible U st.J B := by
  obtain ⟨-, hJ, -, ⟨Bj, hBj, hBjJ, hBjhj⟩, -⟩ :=
    Goldilocks.Store.cache_invariants P ACP acp₀ st hr
  obtain ⟨E, hE, hEr, hEBj, hcase⟩ := J_entry_of_reachable hr hBj
  obtain rfl : E = st.J := hU.1 (hsub hE) (hsub hJ) (hEr.trans hBjJ)
  rcases hcase with he | ⟨hEh, hETh⟩
  · rw [he]
    exact Or.inl hgB
  · by_contra hc
    have h₁ := (entry_kept hr hq (hrow _ hE (by omega) hETh hc) hEBj hETh).1
    have h₂ := hj_lt_h hr hBj
    omega

end Store

end Consensus.Goldilocks.Healing

end

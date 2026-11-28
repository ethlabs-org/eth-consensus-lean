module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Prefix

public section

/-! # Goldilocks Healing: viable entries and bounded finality -/

namespace Consensus.Goldilocks.Healing

variable {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}

/-- **A high block above every high left entry is viable.** A held block `B` above the snapshot
height that is a store descendant of every high left entry is viable:
it reaches `h_max − 1` (the entry at `h_max − 1` of a maximal block is such a left entry); at
`h_max − 1` in a top frame, `Σ.J` is genesis or a high left entry (`h_j = h_max − 1 ≥ hz + 1`),
so `Σ.J ⪯ B`. -/
theorem isViable_of_entries_below (hr : st.Reachable acp₀) {hz : Nat}
    {B : NodeBlock P ACP} (hB : B ∈ st.tree)
    -- Highness: `B` is above the snapshot height.
    (hBh : hz + 1 ≤ (st.σ B.root).h)
    -- Crossings: a high left entry (an entry below a higher block) is a store ancestor of `B`.
    (hcross : ∀ E ∈ st.tree, ∀ C, (st.σ E.root).Th = E.root → hz + 1 ≤ (st.σ E.root).h →
      st.Anc E C → (st.σ E.root).h < (st.σ C.root).h → st.Anc E B) :
    st.IsViable B := by
  obtain ⟨-, hJm, -, ⟨W, hW, hWJ, hWj⟩, hmax, ⟨C, hC, hCh⟩, -⟩ :=
    Store.cache_invariants _ _ _ _ hr
  have hpred : st.hmax - 1 ≤ (st.σ B.root).h := by
    by_contra hn
    obtain ⟨E, hE, hEC, hEh, hET⟩ := entry_at_height hr hC (h := st.hmax - 1)
      (by clear * - hn hBh; omega) (by clear * - hCh; omega)
    have := h_le_of_store_anc hr (hcross E hE C hET (by clear * - hBh hn hEh; omega) hEC
      (by clear * - hn hCh hEh; omega))
    clear * - hn hEh this; omega
  by_cases hm : st.hmax ≤ (st.σ B.root).h
  · exact Or.inl hm
  refine Or.inr ⟨by clear * - hpred hm; omega, ?_⟩
  by_cases hgap : st.hj + 1 < st.hmax
  · exact Or.inl hgap
  right
  have hjW := Store.hj_lt_h hr hW
  obtain ⟨E, hE, hEr, hEW, hcase⟩ := Store.J_entry_of_reachable hr hW
  have hEJ : E = st.J := (Store.accepted_tree _ _ _ _ hr).2.1.1 hE hJm (hEr.trans hWJ)
  subst hEJ
  rcases hcase with hg | ⟨hJh, hJT⟩
  · rw [hg]
    exact (Store.accepted_tree _ _ _ _ hr).2.2.2 B hB
  · have hjm := hmax W hW
    exact hcross _ hE W hJT (by clear * - hJh hWj hjW hBh hpred hm hgap hjm; omega) hEW
      (by clear * - hJh hWj hjW; omega)

/-- **Finality is genesis or below a source.** A high `J` is a left entry above `F`;
at a low justified height the seed bounds `F` directly. -/
theorem finalized_genesis_or_below_source (hr : st.Reachable acp₀)
    {U : Set (NodeBlock P ACP)} (hU : Coherent U) (hsub : st.tree ⊆ U) {hz : Nat}
    (Src : NodeBlock P ACP → Prop)
    -- Crossings: a high left entry (an entry below a higher block) is below a source.
    (hcross : ∀ E ∈ st.tree, ∀ C, (st.σ E.root).Th = E.root → hz + 1 ≤ (st.σ E.root).h →
      st.Anc E C → (st.σ E.root).h < (st.σ C.root).h → ∃ O, Src O ∧ Anc U E O)
    (hseed : st.hj ≤ hz → ∃ O, Src O ∧ Anc U st.F O) :
    st.F = P.genesisBlock acp₀ ∨ ∃ O, Src O ∧ Anc U st.F O := by
  obtain ⟨hFm, hJm, hFJ, ⟨B, hBm, hBJ, hBhj⟩, -⟩ := Store.cache_invariants _ _ _ _ hr
  obtain ⟨E, hEm, hEr, hEB, hcase⟩ := Store.J_entry_of_reachable hr hBm
  obtain rfl : E = st.J := hU.1 (hsub hEm) (hsub hJm) (hEr.trans hBJ)
  rcases hcase with hg | ⟨hJh, hJT⟩
  · left
    have hJF := (Store.accepted_tree _ _ _ _ hr).2.2.2 _ hFm
    rw [← hg] at hJF
    exact (Anc.antisymm hU (hFJ.mono hsub) (hJF.mono hsub)).trans hg
  right
  by_cases hh : hz + 1 ≤ st.hj
  · obtain ⟨O, hO, hJO⟩ := hcross _ hJm _ hJT (by clear * - hBhj hJh hh; omega) hEB
      (by have := Store.hj_lt_h hr hBm; clear * - hJh this; omega)
    exact ⟨O, hO, (hFJ.mono hsub).trans hJO⟩
  exact hseed (by clear * - hh; omega)

end Consensus.Goldilocks.Healing

end

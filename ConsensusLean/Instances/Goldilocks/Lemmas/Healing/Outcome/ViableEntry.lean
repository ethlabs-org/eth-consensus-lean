module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Prefix

public section

/-! # Goldilocks Healing: viable entries and the analysis root

Two cache arguments about one reachable FG store, stated for a height bound `hz` (the snapshot
height `H_z`), a set `U` of blocks around the store and a predicate `Src` of sources (the old
high origins). Run facts enter only as premises, so readers honest under constant or growing
faults, proposers or voters, instantiate the same proofs.

* `isViable_of_entries_below`: such a block is viable.
* `fcRoot_genesis_or_below_source`: the fork-choice root is genesis or below a source. A high
  `J` is a left entry; a low `J` has a source above `F`, and when the root is `J` that source is
  held and high, so `J` is below it by the root's no-contest condition. -/

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

/-- **The fork-choice root is genesis or below a source.** -/
theorem fcRoot_genesis_or_below_source (hr : st.Reachable acp₀)
    {U : Set (NodeBlock P ACP)} (hU : Coherent U) (hsub : st.tree ⊆ U) {hz : Nat}
    (Src : NodeBlock P ACP → Prop)
    -- Crossings: a high left entry (an entry below a higher block) is below a source.
    (hcross : ∀ E ∈ st.tree, ∀ C, (st.σ E.root).Th = E.root → hz + 1 ≤ (st.σ E.root).h →
      st.Anc E C → (st.σ E.root).h < (st.σ C.root).h → ∃ O, Src O ∧ Anc U E O)
    -- Highness: a held block above a source is above the snapshot height.
    (hhigh : ∀ O, Src O → ∀ W ∈ st.tree, Anc U O W → hz + 1 ≤ (st.σ W.root).h)
    -- Seed: at a low justified height, a source is above `F`, and is held above `F` or below it.
    (hseed : st.hj ≤ hz → ∃ O, Src O ∧ Anc U st.F O ∧
      ((O ∈ st.tree ∧ st.Anc st.F O) ∨ Anc U O st.F)) :
    st.fcRoot = P.genesisBlock acp₀ ∨ ∃ O, Src O ∧ Anc U st.fcRoot O := by
  obtain ⟨hFm, hJm, hFJ, ⟨B, hBm, hBJ, hBhj⟩, hmax, _⟩ := Store.cache_invariants _ _ _ _ hr
  obtain ⟨E, hEm, hEr, hEB, hcase⟩ := Store.J_entry_of_reachable hr hBm
  obtain rfl : E = st.J := hU.1 (hsub hEm) (hsub hJm) (hEr.trans hBJ)
  have hroot : st.fcRoot = st.J ∨ st.fcRoot = st.F := by
    unfold Store.fcRoot
    split_ifs <;> simp
  rcases hcase with hg | ⟨hJh, hJT⟩
  · left
    rcases hroot with h | h
    · exact h.trans hg
    · have hJF := (Store.accepted_tree _ _ _ _ hr).2.2.2 _ hFm
      rw [← hg] at hJF
      exact h.trans ((Anc.antisymm hU (hFJ.mono hsub) (hJF.mono hsub)).trans hg)
  right
  by_cases hh : hz + 1 ≤ st.hj
  · obtain ⟨O, hO, hJO⟩ := hcross _ hJm _ hJT (by clear * - hBhj hJh hh; omega) hEB
      (by have := Store.hj_lt_h hr hBm; clear * - hJh this; omega)
    refine ⟨O, hO, ?_⟩
    rcases hroot with h | h
    · rw [h]; exact hJO
    · rw [h]; exact (hFJ.mono hsub).trans hJO
  obtain ⟨O, hO, hFO, hheld⟩ := hseed (by clear * - hh; omega)
  refine ⟨O, hO, ?_⟩
  unfold Store.fcRoot
  split_ifs with hchoose
  · rcases hheld with ⟨hOt, hFOs⟩ | hOF
    · have hOh := hhigh O hO O hOt .refl
      have hOm := hmax O hOt
      have hJO : st.Anc st.J O := by
        by_contra hn
        exact hchoose.2 ⟨hchoose.1, O, hOt, hFOs, by clear * - hh hchoose hOh hOm; omega, hn⟩
      exact hJO.mono hsub
    · have := hhigh O hO st.J hJm (hOF.trans (hFJ.mono hsub))
      rw [hJh, hBhj] at this
      clear * - hh this; omega
  · exact hFO

end Consensus.Goldilocks.Healing

end

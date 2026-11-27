module
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Parametric
import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Order

public section

/-! # A comparable seed supplies candidacy in the frame of a reachable store

`guarded_seed_ancestor_candidate`: in the frame `fg_to_ac(Σ)` of a reachable store (root `Σ.F`), a
held target `P` is an ancestor candidate when it is comparable with a seed `S` of height above `z`,
held once it is above `Σ.F` (and above it when `h_j ≤ z`), with every block of a set of origins,
one of which lies above a held entry at or past `h_max − 1` whenever the seed is below it, and,
in a top frame with `h_j > z`, with `Σ.J`.

The store geometry is all that is used: honesty, the run and the sources are the callers'
premises (`Healing.Growing.ResetPremisesUpTo.guarded_seed_ancestor_candidate_at_state_covered_at`).
`anc_of_anc_universe` transports ancestry from a coherent universe into the tree. -/

namespace Consensus.Goldilocks.Store

variable {p : Params} {ACP : Type} {acp₀ : ACP} {st : Store p ACP}

/-- Ancestry in a coherent universe containing the tree of a reachable store, down to a held
block, is ancestry in the tree (the tree extends genesis). -/
theorem anc_of_anc_universe (hreach : st.Reachable acp₀) {U : Set (NodeBlock p ACP)}
    (hU : Coherent U) (hsub : st.tree ⊆ U) {A C : NodeBlock p ACP} (h : Goldilocks.Anc U A C)
    (hC : C ∈ st.tree) : st.Anc A C := by
  induction h with
  | refl => exact .refl
  | tail _ hYC ih =>
    rcases ((accepted_tree _ _ _ _ hreach).2.2.2 _ hC).cases_tail with hg | ⟨Z, -, hZ⟩
    · exact absurd hYC.2.2 (by rw [hg]; simp [Params.genesisBlock])
    obtain rfl : Z = _ := hU.1 (hsub hZ.1) hYC.1 (Option.some.inj (hZ.2.2.symm.trans hYC.2.2))
    exact (ih hZ.1).tail hZ

/-- A reachable store is reached with the stock finality update (the store layer's copy of
`Store.Reachable.reachableWith`). -/
private theorem reachableWith_of_reachable (h : st.Reachable acp₀) :
    ReachableWith updateFinality acp₀ st := by
  rw [reachableWith_eq]
  induction h with
  | refl => exact .refl
  | tail _ hs ih =>
    refine ih.tail ((stepWith_iff _ _ _).2 ?_)
    rcases hs with ⟨B, hB⟩ | ⟨a, ha⟩
    · exact Or.inl ⟨B, by rw [onBlockWith_eq]; exact hB⟩
    · exact Or.inr ⟨a, ha⟩

/-- **A comparable seed, held whenever it is above finalization, supplies candidacy**, in the
frame of a reachable store. Gap frames (`h_j + 1 < h_max`): the target, the seed or an origin's
entry is a descendant at height at least `h_max − 1`, viable by the gap. Top frames with a low
`h_j ≤ z` below the seed's height: the seed, held above `Σ.F`, has height `h_max`, so it or the
target above it is viable. Top frames with a high `h_j`: the target compares with `Σ.J`, and is
viable on the `J` side or below the viable head `Σ.J`. -/
theorem guarded_seed_ancestor_candidate (hreach : st.Reachable acp₀)
    {P S : NodeBlock p ACP} (hPt : P ∈ st.toFrame.tree) {s z : Nat}
    (hSh : S ∈ st.tree → (st.σ S.root).h = s)
    (hhigh : z + 1 ≤ s)
    (hhold : st.Anc st.F S → S ∈ st.tree)
    (hlowF : st.hj ≤ z → st.Anc st.F S)
    (hPS : Compatible st.tree P S)
    (hhighroot : st.hj + 1 ≥ st.hmax → ¬ st.hj ≤ z → Compatible st.tree st.J P)
    {Origin : NodeBlock p ACP → Prop}
    (hcompare : ∀ O, Origin O → Compatible st.tree P O)
    (hsource : s < st.hmax - 1 →
      ∃ O, Origin O ∧ ∃ E ∈ st.tree, st.Anc E O ∧ st.hmax - 1 ≤ (st.σ E.root).h) :
    st.toFrame.AncestorCandidate P := by
  have hu := finalitySpec_updateFinality (P := p) (ACP := ACP)
  have hr := reachableWith_of_reachable hreach
  have hmono : ∀ {A B : NodeBlock p ACP}, st.Anc A B → (st.σ A.root).h ≤ (st.σ B.root).h :=
    fun h => h_le_of_store_anc_with hu hr h
  obtain ⟨hfin, hcoh, -, -⟩ := accepted_tree_with hu hr
  obtain ⟨-, hJm, hFJ, ⟨BJ, hBJ, -, hBJhj⟩, hbound, -⟩ := cache_invariants_with hu hr
  have hjm : st.hj < st.hmax := by
    have := hj_lt_h_with hu hr hBJ
    have := hbound BJ hBJ
    omega
  obtain ⟨hPy, hFP⟩ : P ∈ st.tree ∧ st.Anc st.F P := hPt
  have finish : ∀ W ∈ st.tree, st.Anc P W → st.IsViable W → st.toFrame.AncestorCandidate P := by
    intro W hW hPW hv
    exact Or.inr ⟨⟨hPy, hFP⟩, Anc.restrict .refl hFP, W, ⟨hW, hFP.trans hPW⟩,
      ⟨hW, hFP.trans hPW, hv⟩, Anc.restrict hFP hPW⟩
  by_cases hgap : st.hj + 1 < st.hmax
  · have witness : ∃ E ∈ st.tree, st.Anc P E ∧ st.hmax - 1 ≤ (st.σ E.root).h := by
      by_cases hfloor : st.hmax - 1 ≤ (st.σ P.root).h
      · exact ⟨P, hPy, .refl, hfloor⟩
      by_cases hSf : st.hmax - 1 ≤ s
      · have hPS' : st.Anc P S := by
          rcases hPS with hPS | hSP
          · exact hPS
          · have hSy : S ∈ st.tree := by
              by_cases he : S = P
              · exact he ▸ hPy
              · exact (Anc.mem hSP he).1
            have := hmono hSP
            rw [hSh hSy] at this
            omega
        have hSy := hhold (hFP.trans hPS')
        exact ⟨S, hSy, hPS', (hSh hSy).symm ▸ hSf⟩
      obtain ⟨O, hO, E, hE, hEO, hEf⟩ := hsource (by omega)
      have hPE : Compatible st.tree P E := by
        rcases hcompare O hO with hPO | hOP
        · exact Anc.total hcoh hPO hEO
        · exact Or.inr (hEO.trans hOP)
      rcases hPE with hPE | hEP
      · exact ⟨E, hE, hPE, hEf⟩
      · have := hmono hEP
        omega
    obtain ⟨E, hE, hPE, hEf⟩ := witness
    apply finish E hE hPE
    by_cases hh : st.hmax ≤ (st.σ E.root).h
    · exact Or.inl hh
    · exact Or.inr ⟨by omega, Or.inl hgap⟩
  by_cases hlow : st.hj ≤ z
  · have hSy := hhold (hlowF hlow)
    have hSm : (st.σ S.root).h = st.hmax := by
      have := hbound S hSy
      rw [hSh hSy] at this ⊢
      omega
    rcases hPS with hPS | hSP
    · exact finish S hSy hPS (Or.inl hSm.ge)
    · exact finish P hPy .refl (Or.inl (hSm.symm.trans_le (hmono hSP)))
  have hJh : (st.σ st.J.root).h = st.hj := by
    rcases (store_J_entry_with hu hr).1 with ⟨-, h0⟩ | ⟨h, -⟩
    · omega
    · exact h
  rcases hhighroot (by omega) hlow with hJP | hPJ
  · apply finish P hPy .refl
    have hm := hmono hJP
    by_cases hh : st.hmax ≤ (st.σ P.root).h
    · exact Or.inl hh
    · exact Or.inr ⟨by omega, Or.inr hJP⟩
  · exact finish st.J hJm hPJ (Or.inr ⟨by omega, Or.inr .refl⟩)

end Consensus.Goldilocks.Store

end

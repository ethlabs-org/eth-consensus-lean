module
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Order

public section

/-! # A comparable seed supplies candidacy in the frame of a reachable store

`guarded_seed_ancestor_candidate`: in the frame `fg_to_ac(Σ)` of a reachable store whose tree
lies in a coherent universe `U`, a held target `P` comparable with `get_fc_root(Σ)` is an ancestor
candidate when it is comparable with a seed `S`, held once it is above `Σ.F`, and with every block
of a set of origins, one of which lies above a held entry at or past the head-height floor
whenever the seed's height is below it. The witness is `P` itself if it meets the floor, else `S`
if the seed does, else the origin's entry, oriented above `P` by height monotonicity.

The store geometry is all that is used: honesty, the run and the source of the high entry are the
callers' premises (`Obligations.UpTo.guarded_seed_ancestor_candidate_at_state`,
`Obligations.UpTo.held_target_ancestor_candidate_at_state`,
`Healing.Growing.ResetPremisesUpTo.guarded_seed_ancestor_candidate_at_state_at`). -/

namespace Consensus.Goldilocks.Store

variable {p : Params} {ACP : Type} {acp₀ : ACP} {st : Store p ACP}

/-- Ancestry in a coherent universe containing the tree of a reachable store, down to a held
block, is ancestry in the tree (the tree extends genesis). -/
private theorem anc_of_anc_universe (hreach : st.Reachable acp₀) {U : Set (NodeBlock p ACP)}
    (hU : Coherent U) (hsub : st.tree ⊆ U) {A C : NodeBlock p ACP} (h : Goldilocks.Anc U A C)
    (hC : C ∈ st.tree) : st.Anc A C := by
  induction h with
  | refl => exact .refl
  | tail _ hYC ih =>
    rcases ((accepted_tree _ _ _ _ hreach).2.2.2 _ hC).cases_tail with hg | ⟨Z, -, hZ⟩
    · exact absurd hYC.2.2 (by rw [hg]; simp [Params.genesisBlock])
    obtain rfl : Z = _ := hU.1 (hsub hZ.1) hYC.1 (Option.some.inj (hZ.2.2.symm.trans hYC.2.2))
    exact (ih hZ.1).tail hZ

/-- **A comparable seed, held whenever it is above finalization, supplies candidacy**, in the
frame of a reachable store, given the target's comparison with the fork-choice root and a held
entry at or past the head-height floor below an origin whenever the seed is below the floor. -/
theorem guarded_seed_ancestor_candidate (hreach : st.Reachable acp₀)
    {U : Set (NodeBlock p ACP)} (hU : Coherent U) (hsub : st.tree ⊆ U)
    -- heights do not decrease along the store's ancestry (`Healing.σ_h_le_of_anc`)
    (hmono : ∀ {A B : NodeBlock p ACP}, st.Anc A B → (st.σ A.root).h ≤ (st.σ B.root).h)
    {P S : NodeBlock p ACP} (hPt : P ∈ st.toFrame.tree) {s : Nat}
    -- the seed's height `s`, as read where the seed was written, is its height in this store
    (hSh : S ∈ st.tree → (st.σ S.root).h = s)
    -- the seed is held once it is above finalization
    (hhold : Goldilocks.Anc U st.F S → S ∈ st.tree)
    (hPS : Compatible U P S)
    -- the target compares with the fork-choice root (the root lemmas of the caller's run)
    (hroot : Compatible U st.fcRoot P)
    {Origin : NodeBlock p ACP → Prop}
    (hcompare : ∀ O, Origin O → Compatible U P O)
    -- a seed below the floor leaves a held entry at or past the floor below an origin
    (hsource : s < st.headHeightFloor →
      ∃ O, Origin O ∧ ∃ E ∈ st.tree, Goldilocks.Anc U E O ∧
        st.headHeightFloor ≤ (st.σ E.root).h) :
    st.toFrame.AncestorCandidate P := by
  have hanc : ∀ {A C : NodeBlock p ACP}, Goldilocks.Anc U A C → C ∈ st.tree → st.Anc A C :=
    anc_of_anc_universe hreach hU hsub
  have hfc : st.fcRoot ∈ st.toFrame.tree := (frame_realization _ _ _ _ hreach).1.fcRoot_mem
  have hPy := hPt.1
  rcases hroot with hroot | hroot
  swap
  · exact Or.inl (Anc.restrict hPt.2 (hanc hroot hfc.1))
  have hrootP := hanc hroot hPy
  have witness : ∃ E ∈ st.tree, st.Anc P E ∧ st.headHeightFloor ≤ (st.σ E.root).h := by
    by_cases hfloor : st.headHeightFloor ≤ (st.σ P.root).h
    · exact ⟨P, hPy, .refl, hfloor⟩
    by_cases hSf : st.headHeightFloor ≤ s
    · have hPS' : Goldilocks.Anc U P S := by
        rcases hPS with hPS | hSP
        · exact hPS
        · have hSP' := hanc hSP hPy
          have hSy : S ∈ st.tree := by
            by_cases he : S = P
            · exact he ▸ hPy
            · exact (Anc.mem hSP' he).1
          have := hmono hSP'
          rw [hSh hSy] at this
          omega
      have hSy := hhold ((hPt.2.mono hsub).trans hPS')
      exact ⟨S, hSy, hanc hPS' hSy, (hSh hSy).symm ▸ hSf⟩
    obtain ⟨O, hO, E, hE, hEO, hEf⟩ := hsource (by omega)
    have hPE : Compatible U P E := by
      rcases hcompare O hO with hPO | hOP
      · exact Anc.total hU hPO hEO
      · exact Or.inr (hEO.trans hOP)
    rcases hPE with hPE | hEP
    · exact ⟨E, hE, hanc hPE hE, hEf⟩
    · have := hmono (hanc hEP hPy)
      omega
  obtain ⟨E, hE, hPE, hEf⟩ := witness
  refine Or.inr ⟨hPt, Anc.restrict hfc.2 hrootP, E, ⟨hE, hPt.2.trans hPE⟩,
    ⟨hE, hPt.2.trans hPE, hrootP.trans hPE, hEf⟩, Anc.restrict hPt.2 hPE⟩

end Consensus.Goldilocks.Store

end

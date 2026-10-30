module
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Store.Handlers

public section

/-! # Goldilocks FG store: what the handlers write

`fg_on_attestation` (and so `addAtts`) writes only the pool; `update_finality` writes `h_max`,
the justification cache and the finalized tip, each under its test; `fg_on_block` accepts a
block only after its tests and its state transition, and then adds the block and its state. -/

namespace Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type}

theorem onAttestation_eq (st : Store P ACP) (a : FG.Att P.n) :
    ∃ atts, st.onAttestation a = { st with atts := atts } := by
  unfold onAttestation
  split_ifs
  · exact ⟨st.atts, rfl⟩
  · exact ⟨_, rfl⟩

theorem addAtts_eq (st : Store P ACP) (l : List (FG.Att P.n)) :
    ∃ atts, st.addAtts l = { st with atts := atts } := by
  induction l generalizing st with
  | nil => exact ⟨st.atts, rfl⟩
  | cons a l ih =>
    obtain ⟨atts, he⟩ := st.onAttestation_eq a
    obtain ⟨atts', he'⟩ := ih (st.onAttestation a)
    refine ⟨atts', ?_⟩
    rw [addAtts, List.foldl_cons, ← addAtts, he', he]

open Classical in
theorem updateFinality_spec (st : Store P ACP) (σ : FG.ChainState P.n) :
    (st.updateFinality σ).blocks = st.blocks ∧ (st.updateFinality σ).σ = st.σ ∧
      (st.updateFinality σ).atts = st.atts ∧ (st.updateFinality σ).hmax = max st.hmax σ.h ∧
      (((st.updateFinality σ).J = st.J ∧ (st.updateFinality σ).hj = st.hj) ∨
        (st.blocks σ.J = some (st.updateFinality σ).J ∧ (st.updateFinality σ).hj = σ.hj ∧
          st.Anc st.F (st.updateFinality σ).J ∧
          LexLt (st.hj, st.J.root) (σ.hj, σ.J))) ∧
      ((st.updateFinality σ).F = st.F ∨
        (st.blocks σ.F = some (st.updateFinality σ).F ∧ st.Anc st.F (st.updateFinality σ).F ∧
          st.F ≠ (st.updateFinality σ).F ∧
          st.Anc (st.updateFinality σ).F (st.updateFinality σ).J)) := by
  unfold updateFinality
  dsimp only
  rcases hJ : st.blocks σ.J with _ | X
  · dsimp only
    rcases hF : st.blocks σ.F with _ | Y
    · exact ⟨rfl, rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩, Or.inl rfl⟩
    · dsimp only
      split_ifs with hFc
      · exact ⟨rfl, rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, hFc.1, hFc.2.1, hFc.2.2.1⟩⟩
      · exact ⟨rfl, rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩, Or.inl rfl⟩
  · dsimp only
    by_cases hJc : ({ st with hmax := max st.hmax σ.h } : Store P ACP).Anc st.F X ∧
        LexLt (st.hj, st.J.root) (σ.hj, σ.J)
    · simp only [eq_true hJc, ite_true]
      rcases hF : st.blocks σ.F with _ | Y
      · exact ⟨rfl, rfl, rfl, rfl, Or.inr ⟨rfl, rfl, hJc.1, hJc.2⟩, Or.inl rfl⟩
      · dsimp only
        split_ifs with hFc
        · exact ⟨rfl, rfl, rfl, rfl, Or.inr ⟨rfl, rfl, hJc.1, hJc.2⟩,
            Or.inr ⟨rfl, hFc.1, hFc.2.1, hFc.2.2.1⟩⟩
        · exact ⟨rfl, rfl, rfl, rfl, Or.inr ⟨rfl, rfl, hJc.1, hJc.2⟩, Or.inl rfl⟩
    · simp only [eq_false hJc, ite_false]
      rcases hF : st.blocks σ.F with _ | Y
      · exact ⟨rfl, rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩, Or.inl rfl⟩
      · dsimp only
        split_ifs with hFc
        · exact ⟨rfl, rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, hFc.1, hFc.2.1, hFc.2.2.1⟩⟩
        · exact ⟨rfl, rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩, Or.inl rfl⟩

theorem onBlock_eq_some {st st' : Store P ACP} {B : NodeBlock P ACP}
    (h : st.onBlock B = some st') :
    ∃ pr σ', B.parent = some pr ∧ st.blocks B.root = none ∧ (st.blocks pr).isSome ∧
      Goldilocks.Anc (insert B st.tree) st.F B ∧
      P.fg.stateTransition (st.σ pr) B.fgView = some σ' ∧
      st' = (updateFinality { st with blocks := Function.update st.blocks B.root (some B),
                                      σ := Function.update st.σ B.root σ' } σ').addAtts
                B.fgPayload := by
  unfold onBlock at h
  split at h
  · cases h
  rename_i pr hpr
  split_ifs at h with hc
  split at h
  · cases h
  rename_i σ' hσ'
  simp only [not_or, not_not, Bool.not_eq_true, Option.isSome_eq_false_iff,
    Option.isNone_iff_eq_none] at hc
  exact ⟨pr, σ', hpr, hc.1, Option.isSome_iff_ne_none.2 hc.2.1, hc.2.2, hσ',
    (Option.some.inj h).symm⟩

end Consensus.Goldilocks.Store

end

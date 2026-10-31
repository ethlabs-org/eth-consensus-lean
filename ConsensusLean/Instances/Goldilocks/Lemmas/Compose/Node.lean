module
public import ConsensusLean.Instances.Goldilocks.Statements.Compose.Node
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Interface
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Reach

public section

/-! # Goldilocks Compose/AnyAC: one node composed with any AC (C0.1–C0.5)

The node statements over the configurations one honest node reaches. -/

namespace Consensus.Goldilocks.Compose

open Node

variable {P : Params} {A : NodeAC P} (proposer : Nat → Fin P.n)
  (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n)

/-- The facts of `fg_on_block`'s acceptance. -/
private theorem accepted_facts {fg fg' : Store P A.Payload} {B : A.Blk}
    (h : fg.onBlock B = some fg') :
    (fg.onBlock B).isSome ∧ fg.blocks B.root = none ∧
      ∃ pr, B.parent = some pr ∧ (fg.blocks pr).isSome ∧ Anc (insert B fg.tree) fg.F B ∧
        (P.fg.stateTransition (fg.σ pr) B.fgView).isSome := by
  obtain ⟨pr, σ', hpr, hnew, hpar, hanc, hσ, -⟩ := Store.onBlock_eq_some h
  exact ⟨by rw [h]; rfl, hnew, pr, hpr, hpar, hanc, by rw [hσ]; rfl⟩

/-- The AC cut of `on_block` with a block call follows the accepting FG cut. -/
private theorem onBlock_ac {st : NodeState A} {t : Time} {B' B : A.Blk} {ℓ : ACLabel A}
    (h : Cut.ac ℓ ∈ (onBlock self st t B').2) (hc : ℓ.call = .block B) :
    B' = B ∧ (onBlock self st t B').2 = [.fg (.block B true), .ac ℓ] ∧ B.slot ≤ P.slotOf t ∧
      ∃ fg', st.fg.onBlock B = some fg' := by
  unfold Node.onBlock at h ⊢
  split_ifs at h ⊢ with hf
  · simp at h
  split at h
  · simp at h
  rename_i fg' hb
  simp only [List.mem_cons, reduceCtorEq, false_or, acCall, Cut.ac.injEq] at h
  rcases h with rfl | h
  · obtain rfl : B' = B := ACInterface.Call.block.inj hc
    exact ⟨rfl, rfl, Nat.le_of_not_lt hf, fg', hb⟩
  · simp at h

/-- The AC cut of the proposal step with a block call is the own block's, after its acceptance. -/
private theorem proposal_ac {st : NodeState A} {t : Time} {x : Nat} {B : A.Blk} {ℓ : ACLabel A}
    (h : Cut.ac ℓ ∈ (tickStep proposer dg self st t x .proposal).2) (hc : ℓ.call = .block B) :
    (tickStep proposer dg self st t x .proposal).2 =
        [(Node.acProposal st t).2.1, .fg (.block B true), .ac ℓ] ∧
      B.slot ≤ P.slotOf t ∧ ∃ fg', (Node.acProposal st t).1.fg.onBlock B = some fg' := by
  simp only [Node.tickStep, Node.acProposal] at h ⊢
  by_cases hp : Proposes proposer self t
  · simp only [hp, ↓reduceIte] at h ⊢
    cases hr : (A.proposal st.ac (frame st) t).2 with
    | none =>
      simp only [hr, List.mem_singleton, Cut.ac.injEq] at h
      subst h; cases hc
    | some q =>
      obtain ⟨d, p⟩ := q
      simp only [hr] at h ⊢
      rcases List.mem_cons.1 h with h | h
      · simp only [Cut.ac.injEq] at h
        subst h; cases hc
      · obtain ⟨-, heq, hs, hfg⟩ := onBlock_ac self h hc
        refine ⟨?_, hs, hfg⟩
        simp only [proposeBlock] at heq ⊢
        rw [heq]
  · simp only [hp, ↓reduceIte] at h
    simp at h

/-- The FG update makes no block call. -/
private theorem update_no_block {st : NodeState A} {t : Time} {x : Nat} {ℓ : ACLabel A}
    (h : Cut.ac ℓ ∈ (tickStep proposer dg self st t x .fgUpdate).2) : ℓ.call = .toFG := by
  simp only [Node.tickStep] at h
  split at h
  · simp only [List.mem_singleton, Node.acToFG, Cut.ac.injEq] at h
    rw [h]
  · rcases List.mem_cons.1 h with h | h
    · simp only [Node.acToFG, Cut.ac.injEq] at h
      rw [h]
    · simp only [Node.attest] at h
      split at h <;> simp [Node.onAttestation] at h

/-- **C0.5 (b), the AC sees only accepted blocks.** -/
theorem ac_sees_accepted_blocks : ACSeesAcceptedBlocks proposer dg self := by
  intro st t e ℓ B h hc
  cases e with
  | block B' =>
    obtain ⟨rfl, heq, hs, fg', hb⟩ := onBlock_ac self h hc
    exact ⟨[], [], st, heq, .nil _, hs, accepted_facts hb⟩
  | message m =>
    simp only [Node.exec, onMessage, acCall, List.mem_singleton, Cut.ac.injEq] at h
    subst h; cases hc
  | attestation a => simp [Node.exec, Node.onAttestation] at h
  | restart =>
    simp only [Node.exec, Node.restart, acCall, List.mem_singleton, Cut.ac.injEq] at h
    subst h; cases hc
  | tick x =>
    have hcuts : exec proposer dg self st t (.tick x) =
        ((tickStep proposer dg self
          (tickStep proposer dg self (tickStep proposer dg self st t x .acTick).1 t x .proposal).1
            t x .fgUpdate).1,
          (tickStep proposer dg self st t x .acTick).2 ++
            (tickStep proposer dg self (tickStep proposer dg self st t x .acTick).1
              t x .proposal).2 ++
            (tickStep proposer dg self
              (tickStep proposer dg self (tickStep proposer dg self st t x .acTick).1
                t x .proposal).1
              t x .fgUpdate).2) := by
      simp [Node.exec, onTick, runSteps, tickSteps]
    rw [hcuts] at h ⊢
    simp only [List.mem_append] at h
    rcases h with (h | h) | h
    · simp only [Node.tickStep, acCall, List.mem_singleton, Cut.ac.injEq] at h
      subst h; cases hc
    · obtain ⟨heq, hs, fg', hb⟩ := proposal_ac proposer dg self h hc
      refine ⟨(tickStep proposer dg self st t x .acTick).2 ++
          [(Node.acProposal (tickStep proposer dg self st t x .acTick).1 t).2.1],
        (tickStep proposer dg self
          (tickStep proposer dg self (tickStep proposer dg self st t x .acTick).1 t x .proposal).1
          t x .fgUpdate).2,
        (Node.acProposal (tickStep proposer dg self st t x .acTick).1 t).1, ?_,
        .cons (st₁ := (tickStep proposer dg self st t x .acTick).1) ⟨rfl, rfl, rfl, rfl⟩
          (.cons (st₁ := (Node.acProposal (tickStep proposer dg self st t x .acTick).1 t).1)
            ⟨rfl, rfl, rfl, rfl⟩ (.nil _)), hs, accepted_facts hb⟩
      rw [heq]
      simp
    · have := update_no_block proposer dg self h
      rw [hc] at this
      cases this

end Consensus.Goldilocks.Compose

end

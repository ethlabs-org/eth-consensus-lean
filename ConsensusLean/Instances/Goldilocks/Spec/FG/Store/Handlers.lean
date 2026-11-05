module
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Store.View

@[expose] public section

/-! # Goldilocks FG store: the handlers

fg.tex Figure "FG: handlers, finality caches and frame": `fg_on_attestation`,
`update_finality` and `fg_on_block`. `fg_on_block` returns the new FG state, or `none` when it
refuses the block: a held root, a parent that is not held, a block that does not extend `Σ.F`,
or a failed assertion of `state_transition` (no write). An accepted block's attestations enter
the pool after the block's finality update.

This module holds only what the Challenge statements reach; `Store.Step` and `Reachable` are in
`Milestones/Spec/FG/Store/Handlers` (`docs/decisions.md`
§"Trusted surface and Challenge scope"). -/

namespace Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type}

/-- `fg_on_attestation(Σ, a)`: add `a` to the pool, one copy of each, in the order of first
acceptance. -/
def onAttestation (st : Store P ACP) (a : FG.Att P.n) : Store P ACP :=
  if a ∈ st.atts then st else { st with atts := st.atts ++ [a] }

/-- The attestations of a list, in order, through `fg_on_attestation`. -/
def addAtts (st : Store P ACP) (l : List (FG.Att P.n)) : Store P ACP := l.foldl onAttestation st

/-- The lexicographic order on `(height, root)` pairs. -/
def LexLt (a b : Nat × Nat) : Prop := a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)

open Classical in
/-- `update_finality(Σ, σ)`: raise `h_max` to `σ.h`; take `(σ.J, σ.h_j)` as `(Σ.J, Σ.h_j)` when
`Σ.F ⪯ σ.J` and it is lex-greater than `(Σ.h_j, Σ.J.root)`; then move `Σ.F` to `σ.F` when
`Σ.F ≺ σ.F ⪯ Σ.J` and `σ.F` has a viable descendant (each test reads the state after the
earlier writes). A root of `σ` that is not held names no block, so its test fails. -/
noncomputable def updateFinality (st : Store P ACP) (σ : FG.ChainState P.n) : Store P ACP :=
  let st₁ : Store P ACP := { st with hmax := max st.hmax σ.h }
  let st₂ : Store P ACP :=
    match st₁.blocks σ.J with
    | some X =>
        if st₁.Anc st₁.F X ∧ LexLt (st₁.hj, st₁.J.root) (σ.hj, σ.J) then
          { st₁ with J := X, hj := σ.hj }
        else st₁
    | none => st₁
  match st₂.blocks σ.F with
  | some X =>
      if st₂.Anc st₂.F X ∧ st₂.F ≠ X ∧ st₂.Anc X st₂.J ∧ st₂.HasViableDescendant X then
        { st₂ with F := X }
      else st₂
  | none => st₂

open Classical in
/-- `fg_on_block(Σ, B)`: refuse (`none`) a block whose root is held, whose parent is not held,
that does not extend `Σ.F`, or whose state transition from the parent's state fails; otherwise
add `B` and `σ[B]`, run `update_finality`, then `fg_on_attestation` for each attestation of
`B` in order. -/
noncomputable def onBlock (st : Store P ACP) (B : NodeBlock P ACP) : Option (Store P ACP) :=
  match B.parent with
  | none => none
  | some pr =>
      if (st.blocks B.root).isSome ∨ (st.blocks pr).isNone ∨
          ¬ Goldilocks.Anc (insert B st.tree) st.F B then
        none
      else
        match P.fg.stateTransition (st.σ pr) B.fgView with
        | none => none
        | some σ' =>
            let st₁ : Store P ACP :=
              { st with blocks := Function.update st.blocks B.root (some B),
                        σ := Function.update st.σ B.root σ' }
            some ((updateFinality st₁ σ').addAtts B.fgPayload)

end Consensus.Goldilocks.Store

end

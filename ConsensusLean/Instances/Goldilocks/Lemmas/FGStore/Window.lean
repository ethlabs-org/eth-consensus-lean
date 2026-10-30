module
public import ConsensusLean.Instances.Goldilocks.Statements.FGStore.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Entries

public section

/-! # Goldilocks FG store: a good window justifies its entry (theorem A's core)

Under `GW(E, a, k_F)` (`GoodWindow`), the chain of the serving block `B*` justifies the entry `E`
at `B*` or earlier, at a block `X` before which the height is not left; `X` enters the next height
as its own entry, with `(h, T_h)` pending; and at a bound entry `X` has finalized `P_E`
(`window_justifies`, theorem.md §3). The rows of `GW` are on `B*`'s chain (on the parent's, or
pooled and so included by the honest proposal); while `h` is current they stay valid and their
target and finality bits persist; no block before `B*` is old enough to time out
(`v* ≤ u + D ≤ u + δ_t`), and `B*` tests justification before the timeout. The state of a block
is the same at every honest node that holds it (`σ_eq_of_held`): it is the fold over the block's
chain, which the coherent `U` fixes. -/

namespace Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type} {acp₀ : ACP} {H : Set (Fin P.n)} {U : Set (NodeBlock P ACP)}
  {tr : FGTrace P ACP}

/-- Two honest nodes that hold a block give it the same state. -/
theorem σ_eq_of_held (hr : FGLocalRun acp₀ H U tr) {y z : Fin P.n} (hy : y ∈ H) (hz : z ∈ H)
    {i j : Nat} {B : NodeBlock P ACP} (hBy : B ∈ (tr.store y i).tree)
    (hBz : B ∈ (tr.store z j).tree) : (tr.store y i).σ B.root = (tr.store z j).σ B.root := by
  sorry

/-- **Theorem A's core.** A good window's serving block justifies the entry on its chain, at a
block `X ⪯ B*` before which the height is not left; `X` enters the next height as its own entry
with `(h, T_h)` pending; at a bound entry, `X` has finalized `P_E`. -/
theorem window_justifies (hr : FGLocalRun acp₀ H U tr) {cF : Nat} {T : NodeBlock P ACP}
    {a kF : Nat} {p : Fin P.n} {i : Nat} {Bs Pr : NodeBlock P ACP} {R : Finset (FG.Att P.n)}
    (hw : GoodWindow P ACP H tr cF T a kF p i Bs Pr R) :
    ∃ X, JustifiesEntry P ACP (tr.store p (i + 1)) T ((tr.store p i).σ T.root).h X ∧
      (tr.store p (i + 1)).Anc X Bs ∧
      ((tr.store p (i + 1)).σ X.root).h = ((tr.store p i).σ T.root).h + 1 ∧
      ((tr.store p (i + 1)).σ X.root).Th = X.root ∧
      (((tr.store p i).σ T.root).h, T.root) ∈ ((tr.store p (i + 1)).σ X.root).pending ∧
      (((tr.store p i).σ T.root).bound →
        ((tr.store p (i + 1)).σ X.root).F = ((tr.store p i).σ T.root).J ∧
        ((tr.store p (i + 1)).σ X.root).hF = ((tr.store p i).σ T.root).hj) := by
  sorry

end Consensus.Goldilocks.Store

end

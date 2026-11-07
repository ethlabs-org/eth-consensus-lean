module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.LiftFrame

public section

/-! # Goldilocks under `Sleepy` with growing faults: honest rows and their sources

`HonestRowsSourcedAt tr H G y i`: every attestation of a block in the tree of `y` before cut `i`
whose signer is honest at `tr.time i` has a source satisfying `G`, held by a node honest at
`tr.time i` at a cut `k ≤ i` (the signers and the source holder are classified at the reading cut,
Lemma G). -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- The honest rows of `y`'s tree before cut `i` are sourced in `G`, classified at `tr.time i`. -/
def HonestRowsSourcedAt (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop) (y : Fin sp.n) (i : Nat) : Prop :=
  ∀ X ∈ (tr.state y i).fg.tree, ∀ a ∈ X.fgPayload, a.val ∈ H (tr.time i) →
    ∃ D, G D ∧ ∃ x k, x ∈ H (tr.time i) ∧ k ≤ i ∧ D ∈ (tr.state x k).fg.tree ∧
      ((tr.state x k).fg.σ D.root).Th = a.T

theorem honestRowsSourcedAt_iff {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)}
    {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop} {y : Fin sp.n} {i : Nat} :
    HonestRowsSourcedAt tr H G y i ↔
      ∀ X ∈ (tr.state y i).fg.tree, ∀ a ∈ X.fgPayload, a.val ∈ H (tr.time i) →
        ∃ D, G D ∧ ∃ x k, x ∈ H (tr.time i) ∧ k ≤ i ∧ D ∈ (tr.state x k).fg.tree ∧
          ((tr.state x k).fg.σ D.root).Th = a.T :=
  Iff.rfl

end Consensus.Goldilocks.Compose.Growing

end

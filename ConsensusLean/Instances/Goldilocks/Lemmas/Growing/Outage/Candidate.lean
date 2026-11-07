module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Candidate

public section

/-! # Outage under growing faults: a held block stays a viable-ancestor candidate

`held_candidate_of_rows_at` is the static `held_candidate_of_rows` at a cut `i` of a node honest
then, lifted to the prefix through `t_i`: the attestations of the node's tree by validators honest
at `t_i` are sourced (`HonestRowsSourcedAt`: by a block of the tree of a validator honest at `t_i`,
at a cut no later than `i`), and the count is `2 f_{t_i} < n` at the reading cut. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- The attestations of `y`'s tree at cut `i` by validators honest at `t_i` are sourced by blocks
satisfying `G`: each names the entry of a block satisfying `G` held, at a cut no later than `i`,
by a validator honest at `t_i`. -/
def HonestRowsSourcedAt (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop) (y : Fin sp.n) (i : Nat) : Prop :=
  ∀ X ∈ (tr.state y i).fg.tree, ∀ a ∈ X.fgPayload, a.val ∈ H (tr.time i) →
    ∃ D, G D ∧ ∃ x k, x ∈ H (tr.time i) ∧ k ≤ i ∧ D ∈ (tr.state x k).fg.tree ∧
      ((tr.state x k).fg.σ D.root).Th = a.T

theorem honestRowsSourcedAt_iff {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop} {y : Fin sp.n}
    {i : Nat} : HonestRowsSourcedAt tr H G y i ↔
      ∀ X ∈ (tr.state y i).fg.tree, ∀ a ∈ X.fgPayload, a.val ∈ H (tr.time i) →
        ∃ D, G D ∧ ∃ x k, x ∈ H (tr.time i) ∧ k ≤ i ∧ D ∈ (tr.state x k).fg.tree ∧
          ((tr.state x k).fg.σ D.root).Th = a.T :=
  Iff.rfl

/-- **The sourced rows in the prefix**: at a cut `i` of a node honest then, the rows sourced by
`G` are, in the prefix through `t_i`, rows sourced by the `G`-blocks held in the prefix. -/
theorem HonestRowsSourcedAt.upTo
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) {y : Fin sp.n} {i : Nat}
    {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop} (hsrc : HonestRowsSourcedAt tr H G y i) :
    HonestRowsSourced (tr.upTo (tr.time i)) (H (tr.time i))
      (fun D => G D ∧ D ∈ (tr.upTo (tr.time i)).HonestBlocks (H (tr.time i))) y i := by
  have hst : ∀ x k, k ≤ i → (tr.upTo (tr.time i)).state x k = tr.state x k :=
    fun x k hk => RunTrace.upTo_state_of_le hrun.time_mono (hrun.time_mono hk)
  refine Compose.honestRowsSourced_iff.2 fun X hX a ha hav => ?_
  rw [hst y i le_rfl] at hX
  obtain ⟨D, hD, x, k, hx, hki, hDt, hDT⟩ := hsrc X hX a ha hav
  have hDU : D ∈ (tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)) :=
    ⟨x, hx, k, by rw [hst x k hki]; exact hDt⟩
  exact ⟨D, ⟨hD, hDU⟩, Compose.isHonestSource_iff.2 ⟨x, hx, k,
    by rw [hst x k hki]; exact hDt, by rw [hst x k hki]; exact hDT⟩⟩

/-- **A held block compatible with every source stays a candidate**, at a cut `i` of a node
honest then, with `2 f_{t_i} < n`: a block `B` of the frame's tree compatible with every
`G`-source is at or below `fc_root` or in the full viable tree. -/
theorem held_candidate_of_rows_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) (hf : 2 * (H (tr.time i))ᶜ.ncard < sp.n)
    {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop} (hsrc : HonestRowsSourcedAt tr H G y i)
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hGB : ∀ D, G D → Compatible (tr.HonestBlocksAt H) D B)
    (hBt : B ∈ (Node.frame (tr.state y i)).tree) :
    (Node.frame (tr.state y i)).Anc B (Node.frame (tr.state y i)).fcRoot ∨
      B ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree := by
  have hd := hrun.time_nonneg i
  have hm := hrun.time_mono
  have hst : ∀ x k, k ≤ i → (tr.upTo (tr.time i)).state x k = tr.state x k :=
    fun x k hk => RunTrace.upTo_state_of_le hm (hm hk)
  have hBU : B ∈ (tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)) :=
    ⟨y, hy, i, by rw [hst y i le_rfl]; exact hBt.1⟩
  have h := held_candidate_of_rows (hrun.upTo hd) (hnc.upTo _) hf hy i (hsrc.upTo hrun)
    (fun D ⟨hD, hDU⟩ => compatible_upTo hrun hnc hd hDU hBU (hGB D hD))
    (by rw [hst y i le_rfl]; exact hBt)
  rwa [hst y i le_rfl] at h

end Consensus.Goldilocks.Compose.Growing

end

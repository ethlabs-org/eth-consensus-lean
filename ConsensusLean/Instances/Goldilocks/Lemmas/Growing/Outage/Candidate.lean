module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Frame
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FrameCandidate

public section

/-! # Outage under growing faults: a held block stays a viable-ancestor candidate

`held_candidate_of_rows` (one honest set, no pairwise source premise) and
`held_candidate_of_rows_by`, that lemma at a cut `i` of a node honest
at a time `t` after every cut before `i`, lifted to the prefix through `t`: the attestations of the
node's tree by validators honest at `t` are sourced (`HonestRowsSourcedBy`: by a block held while
honest at `t`, `IsHonestSourceAt`), and the count is `2 f_t < n`. `held_candidate_of_rows_at` is the
case `t = t_i`, from the rows sourced at the reading cut (`HonestRowsSourcedAt`,
`Sleepy/Node/Frame`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **A held block compatible with every honest source stays a candidate**: with
`f < n/2` and the honest attestations of `y`'s tree sourced by `G`, a block `B` of the frame's tree
compatible with every `G`-source is at or below `fc_root` or in the full viable tree. No pairwise
premise on the sources. -/
theorem held_candidate_of_rows {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) (hf : 2 * Hᶜ.ncard < sp.n) {y : Fin sp.n} (hy : y ∈ H) (i : Nat)
    {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop} (hsrc : HonestRowsSourced tr H G y i)
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B)
    (hBt : B ∈ (Node.frame (tr.state y i)).tree) :
    (Node.frame (tr.state y i)).Anc B (Node.frame (tr.state y i)).fcRoot ∨
      B ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree := by
  apply FrameGeometry.held_candidate_of_rows hrun.toLocalRun (projFG_localRun hrun hnc)
    hf hy i _ hGB hBt
  exact FrameGeometry.honestRowsSourced_iff.2 fun X hX a ha hav => by
    obtain ⟨D, hD, hDs⟩ := honestRowsSourced_iff.1 hsrc X hX a ha hav
    exact ⟨D, hD, FrameGeometry.isHonestSource_iff.2 (isHonestSource_iff.1 hDs)⟩

end Consensus.Goldilocks.Compose

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- The attestations of `y`'s tree at cut `i` by validators honest at a time `t` are sourced by
blocks satisfying `G`, held while honest at `t` (`IsHonestSourceAt`). -/
def HonestRowsSourcedBy (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop) (y : Fin sp.n) (i : Nat) (t : Time) : Prop :=
  ∀ X ∈ (tr.state y i).fg.tree, ∀ a ∈ X.fgPayload, a.val ∈ H t →
    ∃ D, G D ∧ IsHonestSourceAt tr H D a.T t

theorem honestRowsSourcedBy_iff {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop} {y : Fin sp.n}
    {i : Nat} {t : Time} : HonestRowsSourcedBy tr H G y i t ↔
      ∀ X ∈ (tr.state y i).fg.tree, ∀ a ∈ X.fgPayload, a.val ∈ H t →
        ∃ D, G D ∧ IsHonestSourceAt tr H D a.T t :=
  Iff.rfl

/-- The rows sourced at the reading cut are sourced by blocks held while honest at its time. -/
theorem HonestRowsSourcedAt.by_
    {ini} (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini) {y : Fin sp.n}
    {i : Nat}
    {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop} (hsrc : HonestRowsSourcedAt tr H G y i) :
    HonestRowsSourcedBy tr H G y i (tr.time i) := fun X hX a ha hav => by
  obtain ⟨D, hD, x, k, hx, hki, hDt, hDT⟩ := honestRowsSourcedAt_iff.1 hsrc X hX a ha hav
  exact ⟨D, hD, isHonestSourceAt_iff.2
    ⟨x, k, hx, fun k' hk' => hrun.time_mono (hk'.le.trans hki), hDt, hDT⟩⟩

/-- **The sourced rows in the prefix**: when every cut before `i` is at a time `≤ t`, the rows of
`y`'s tree at `i` sourced at `t` are, in the prefix through `t`, rows sourced by the `G`-blocks held
in the prefix. -/
theorem HonestRowsSourcedBy.upTo_held {y : Fin sp.n} {i : Nat} {t : Time}
    (ht : ∀ k < i, tr.time k ≤ t) {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}
    (hsrc : HonestRowsSourcedBy tr H G y i t) :
    HonestRowsSourced (tr.upTo t) (H t)
      (fun D => G D ∧ D ∈ (tr.upTo t).HonestBlocks (H t)) y i := by
  refine Compose.honestRowsSourced_iff.2 fun X hX a ha hav => ?_
  rw [Trace.upTo_state tr y ht] at hX
  obtain ⟨D, hD, hDs⟩ := hsrc X hX a ha hav
  obtain ⟨x, k, hx, hk, hDt, hDT⟩ := isHonestSourceAt_iff.1 hDs
  have hstk := Trace.upTo_state tr x hk
  exact ⟨D, ⟨hD, x, hx, k, by rw [hstk]; exact hDt⟩, Compose.isHonestSource_iff.2 ⟨x, hx, k,
    by rw [hstk]; exact hDt, by rw [hstk]; exact hDT⟩⟩

/-- **A held block compatible with every source stays a candidate**, at a cut `i` of a node
honest at a time `t ≥ 0` after every cut before `i`, with `2 f_t < n`: a block `B` of the frame's
tree compatible with every `G`-source is at or below `fc_root` or in the full viable tree. -/
theorem held_candidate_of_rows_by
    {ini} (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {y : Fin sp.n} {i : Nat} {t : Time} (ht0 : 0 ≤ t) (ht : ∀ k < i, tr.time k ≤ t)
    (hy : y ∈ H t) (hf : 2 * (H t)ᶜ.ncard < sp.n)
    {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop} (hsrc : HonestRowsSourcedBy tr H G y i t)
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hGB : ∀ D, G D → Compatible (tr.HonestBlocksAt H) D B)
    (hBt : B ∈ (Node.frame (tr.state y i)).tree) :
    (Node.frame (tr.state y i)).Anc B (Node.frame (tr.state y i)).fcRoot ∨
      B ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree := by
  have hst := Trace.upTo_state tr y ht
  have hBU : B ∈ (tr.upTo t).HonestBlocks (H t) := ⟨y, hy, i, by rw [hst]; exact hBt.1⟩
  have h := held_candidate_of_rows (hrun.upTo ht0) (hnc.upTo _) hf hy i (hsrc.upTo_held ht)
    (fun D ⟨hD, hDU⟩ => compatible_upTo hrun hnc ht0 hDU hBU (hGB D hD))
    (by rw [hst]; exact hBt)
  rwa [hst] at h

/-- **A held block compatible with every source stays a candidate**, at a cut `i` of a node
honest then, with `2 f_{t_i} < n`. -/
theorem held_candidate_of_rows_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) (hf : 2 * (H (tr.time i))ᶜ.ncard < sp.n)
    {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop} (hsrc : HonestRowsSourcedAt tr H G y i)
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hGB : ∀ D, G D → Compatible (tr.HonestBlocksAt H) D B)
    (hBt : B ∈ (Node.frame (tr.state y i)).tree) :
    (Node.frame (tr.state y i)).Anc B (Node.frame (tr.state y i)).fcRoot ∨
      B ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree :=
  held_candidate_of_rows_by hrun hnc (hrun.time_nonneg i) (fun _ hk => hrun.time_mono hk.le) hy
    hf (hsrc.by_ hrun) hGB hBt

end Consensus.Goldilocks.Compose.Growing

end

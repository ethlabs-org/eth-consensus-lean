module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Served

public section

/-! # Goldilocks under `Sleepy` with growing faults: the head certificate from target votes

The growing-fault forms of `read_majority_of_target_votes` and
`read_head_support_of_target_votes` (`Compose/Sleepy/Served`), lifted to the prefix through the
read time `t` with the honest set `H t`. The reader is honest at `t` (`y ∈ H t`, `0 ≤ t`, every
cut before `i` at a time `≤ t ≤ tr.time i`), awake and joined at `t`. The window service is the
static one of that prefix (a service whose senders are honest at the send and recipients at the
call gives it, since `H` is antitone); the target votes are votes of nodes honest at them, at
times `≤ t`; the latest view's count is charged at `t` (`FaultBoundAt H (t_L + Δ) t`). -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **The target's supporter majority at a read** under growing faults: at a read at `t` by a node
honest then, with the prefix's window service from `a ≤ t_L` (`L` the latest view's slot), every
vote of slot `L` of a node honest at it, at a time `≤ t`, extending `R`, and the latest view's
count at `t`, the supporters of `R` are a strict majority of the latest view's voters. -/
theorem read_majority_of_target_votes_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {i : Nat} {t : Time} (ht0 : 0 ≤ t) (hy : y ∈ H t)
    (hle : ∀ q < i, tr.time q ≤ t) (hti : t ≤ tr.time i)
    (hw : tr.awake y t) (hj : tr.JoinedAt y t) {a : Time}
    (hsync : SyncACWindowBefore (H t) ((tr.upTo t).HonestBlocks (H t)) a t (tr.projAC.upTo t))
    (hcatch : CatchACWindowBefore (tr.projAC.upTo t) (H t) ((tr.upTo t).HonestBlocks (H t)) a
      (2 * sp.Δ) t)
    {L : Nat} (hL : (L : Int) =
      (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2)
    (ha : a ≤ sp.ts L) {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hR : R ∈ (Node.frame (tr.state y i)).tree)
    (hvotes : ∀ z q e, HVoteAt tr H z q e → tr.time q ≤ t → e.msg.slot = L →
      SA.VoteExtends (tr.HonestBlocksAt H) e.msg R)
    (hLt : sp.ts L + sp.Δ ≤ t) (hfault : tr.FaultBoundAt H (sp.ts L + sp.Δ) t) :
    (SA.voters (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).1.votes).ncard <
      2 * (SA.supporters (Node.frame (tr.state y i))
        (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).1
        (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2 R).ncard := by
  have hst := Trace.upTo_state tr y hle
  have h := read_majority_of_target_votes (hrun.upTo ht0) (hnc.upTo t) hy ht0 hle hti
    ⟨hw, le_rfl⟩ (joinedAt_upTo hj) (by rw [RunTrace.upTo_projAC]; exact hsync)
    (by rw [RunTrace.upTo_projAC]; exact hcatch) (by rw [hst]; exact hL) ha
    (by rw [hst]; exact hR) (fun z hz q hq e hv hes => by
      have hv' := hv
      rw [RunTrace.upTo_projAC] at hv'
      exact voteExtends_upTo hrun hnc ht0 hz hv
        (hvotes z q e (hVoteAt_iff.2 ⟨hrun.antitone hq hz, (sa_voteAt_upTo.mp hv').2⟩) hq hes))
    (faultBound_upTo hLt hfault)
  rwa [hst] at h

/-- **The head certificate from target votes** under growing faults: with the record's anchor
compatible with `R`, and `R` below the anchor or viable and extended by every vote of slot `L` of
a node honest at it at a time `≤ t`, the certificate holds, the majority as in
`read_majority_of_target_votes_at`. -/
theorem read_head_support_of_target_votes_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {i : Nat} {t : Time} (ht0 : 0 ≤ t) (hy : y ∈ H t)
    (hle : ∀ q < i, tr.time q ≤ t) (hti : t ≤ tr.time i)
    (hw : tr.awake y t) (hj : tr.JoinedAt y t) {a : Time}
    (hsync : SyncACWindowBefore (H t) ((tr.upTo t).HonestBlocks (H t)) a t (tr.projAC.upTo t))
    (hcatch : CatchACWindowBefore (tr.projAC.upTo t) (H t) ((tr.upTo t).HonestBlocks (H t)) a
      (2 * sp.Δ) t)
    {L : Nat} (hL : (L : Int) =
      (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2)
    (ha : a ≤ sp.ts L) {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hR : R ∈ (Node.frame (tr.state y i)).tree)
    (hanchor : Compatible (Node.frame (tr.state y i)).tree
      (SA.getAnchor sp (tr.state y i).ac (Node.frame (tr.state y i)) t) R)
    (hsource : (Node.frame (tr.state y i)).Anc R
        (SA.getAnchor sp (tr.state y i).ac (Node.frame (tr.state y i)) t) ∨
      (R ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree ∧
        ∀ z q e, HVoteAt tr H z q e → tr.time q ≤ t → e.msg.slot = L →
          SA.VoteExtends (tr.HonestBlocksAt H) e.msg R))
    (hLt : sp.ts L + sp.Δ ≤ t) (hfault : tr.FaultBoundAt H (sp.ts L + sp.Δ) t) :
    Compatible (Node.frame (tr.state y i)).tree
      (SA.getAnchor sp (tr.state y i).ac (Node.frame (tr.state y i)) t) R ∧
      ((Node.frame (tr.state y i)).Anc R
        (SA.getAnchor sp (tr.state y i).ac (Node.frame (tr.state y i)) t) ∨
      (R ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree ∧
        (SA.voters (SA.latestView sp (tr.state y i).ac
          (Node.frame (tr.state y i)) t).1.votes).ncard <
          2 * (SA.supporters (Node.frame (tr.state y i))
            (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).1
            (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2 R).ncard)) := by
  refine ⟨hanchor, ?_⟩
  rcases hsource with h | ⟨hv, hvotes⟩
  · exact Or.inl h
  · exact Or.inr ⟨hv, read_majority_of_target_votes_at hrun hnc ht0 hy hle hti hw hj
      hsync hcatch hL ha hR hvotes hLt hfault⟩

end Consensus.Goldilocks.Compose.Growing

end

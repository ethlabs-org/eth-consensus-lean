module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift

public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.ServedSteps
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Gate
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Local
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Regimes
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Components

public section

/-! # Goldilocks under `Sleepy` with growing faults: the head certificate from target votes

The served head support from target votes, at a read on the prefix through the read time `t`
with the honest set `H t`, counted on the slot committees. The reader is honest at `t`
(`y ∈ H t`, `0 ≤ t`, every cut before `i` at a time `≤ t ≤ tr.time i`), awake and joined at `t`.
The window service is the static one of that prefix (a service whose senders are honest at the
send and recipients at the call gives it, since `H` is antitone); the target votes are votes of
nodes honest at them, at times `≤ t`; the latest view's committee count is charged at `t`
(`FaultBoundK K L (H t) (t_L + Δ)`), and its majority is `read_majority_of_extending_at`. -/

namespace Consensus.Goldilocks.Compose.Growing

open AC (ACParams Vote Payload)

variable {sp : ACParams}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {proposer : Nat → Fin sp.n}

/-- The committee majority at a read cut `m` of the prefix through `t`: with every vote of the
latest view's slot `L` of a node honest at it extending `R`, the slot-`L` committee's fault bound
charged at `t`, and the prefix's window service from `a ≤ t_L`, the supporters of `R` are a strict
majority of the latest view's voters (`read_majority_of_extending_at`). -/
private theorem read_majority_at_read_cut {ini}
    (hrun : Growing.GoldilocksRun proposer dg H tr ini) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} {m : Nat} {t : Time} (ht0 : 0 ≤ t) (hy : y ∈ H t)
    (hrd : ReadAtCut proposer dg (tr.upTo t) y m t) {a : Time}
    (hsync : SyncACWindowBefore (H t) ((tr.upTo t).HonestBlocks (H t)) a t (tr.projAC.upTo t))
    (hcatch : CatchACWindowBefore (tr.projAC.upTo t) (H t) ((tr.upTo t).HonestBlocks (H t)) a
      (2 * sp.Δ) t)
    {L : Nat} (hL : (L : Int) =
      (AC.latestView sp (tr.state y m).ac (Node.frame (tr.state y m)) t).2)
    (ha : a ≤ sp.ts L) {R : AC.Blk sp.n (List (FG.Att sp.n))}
    (hR : R ∈ (Node.frame (tr.state y m)).tree) {K : AC.CommitteeDict sp.n}
    (hKB : CommitteeFacts tr H K)
    (hall : ∀ x k e, HVoteAt tr H x k e → e.msg.slot = L →
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg R)
    (hLt : sp.ts L + sp.Δ ≤ t) (hfb : AC.FaultBoundK K L tr.projAC (H t) (sp.ts L + sp.Δ)) :
    (AC.voters (AC.latestView sp (tr.state y m).ac (Node.frame (tr.state y m)) t).1.votes).ncard <
      2 * (AC.supporters (Node.frame (tr.state y m))
        (AC.latestView sp (tr.state y m).ac (Node.frame (tr.state y m)) t).1
        (AC.latestView sp (tr.state y m).ac (Node.frame (tr.state y m)) t).2 R).ncard := by
  have hle : ∀ k < m, tr.time k ≤ t := hrd.before
  have hst : (tr.upTo t).state y m = tr.state y m := Trace.upTo_state tr y hle
  have hLp : (L : Int) = (AC.latestView sp ((tr.upTo t).state y m).ac
      (Node.frame ((tr.upTo t).state y m)) t).2 := by rw [hst]; exact hL
  have hsync' : SyncACWindowBefore (H t) ((tr.upTo t).HonestBlocks (H t)) a t
      (tr.upTo t).projAC := by rw [RunTrace.upTo_projAC]; exact hsync
  have hcatch' : CatchACWindowBefore (tr.upTo t).projAC (H t) ((tr.upTo t).HonestBlocks (H t)) a
      (2 * sp.Δ) t := by rw [RunTrace.upTo_projAC]; exact hcatch
  have ha' : a ≤ sp.ts (AC.latestView sp ((tr.upTo t).state y m).ac
      (Node.frame ((tr.upTo t).state y m)) t).2 := by rw [← hLp]; exact ha
  exact read_majority_of_extending_at hrun hnc hKB.hP ht0 hy hle hL.symm
    (extendingMajority_of_all_at hrun hnc hKB.hGate hall hLt hfb) hR (by
      intro x k e hv hx hs hext
      obtain ⟨hxk, ℓ, hc⟩ := hVoteAt_iff.1 hv
      have hkt := (cast_time_at hrun hnc hxk hc).2
      rw [hs] at hkt
      have hvp : AC.VoteAt (tr.upTo t).projAC x k e := by
        rw [RunTrace.upTo_projAC]
        exact AC.upTo_voteAt.mpr ⟨hkt.trans hLt, ℓ, hc⟩
      have hpool := latest_vote_delivered (hrun.upTo ht0) (hnc.upTo t)
        (Or.inr ⟨a, hsync', ha'⟩) hy hrd hLp hx hvp hs
      obtain ⟨Hd, hHd, hHdr, hRHd⟩ := voteExtends_upTo hrun hnc ht0 hx hvp hext
      have hΦ := frameOK_at hrun ht0 hy hle
      have hΦU : (Node.frame (tr.state y m)).tree ⊆ (tr.upTo t).HonestBlocks (H t) :=
        fun X hX => ⟨y, hy, m, by rw [hst]; exact hX.1⟩
      have hF : Anc ((tr.upTo t).HonestBlocks (H t)) ((tr.upTo t).state y m).fg.F Hd := by
        rw [hst]
        exact ((hΦ.rooted.2 R hR).mono hΦU).trans hRHd
      obtain ⟨hHdt, hstamp⟩ := honest_head_in_frame_at_read (hrun.upTo ht0) (hnc.upTo t)
        (Or.inr ⟨a, hsync', hcatch', ha'⟩) hy hrd hLp hx hvp hs hHd hHdr hF
      rw [hst] at hpool hHdt
      rw [projAC_state (hrun.upTo ht0).toLocalRun hy m, hst] at hstamp
      exact ⟨hpool, Hd, hHdt, hHdr, hstamp⟩)

/-- **The target's supporter majority at a read** under growing faults: at a read at `t` by a node
honest then, with the prefix's window service from `a ≤ t_L` (`L` the latest view's slot), every
vote of slot `L` of a node honest at it, at a time `≤ t`, extending `R`, and the slot-`L`
committee's fault bound charged at `t`, the supporters of `R` are a strict majority of the latest
view's voters. When the node's tick at `t` is at a cut `≥ i`, the read is the one before the
tick's cut, with the same state. -/
theorem read_majority_of_target_votes_at {ini}
    (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {i : Nat} {t : Time} (ht0 : 0 ≤ t) (hy : y ∈ H t)
    (hle : ∀ q < i, tr.time q ≤ t) (hti : t ≤ tr.time i)
    (hw : tr.awake y t) (hj : tr.JoinedAt y t) {a : Time}
    (hsync : SyncACWindowBefore (H t) ((tr.upTo t).HonestBlocks (H t)) a t (tr.projAC.upTo t))
    (hcatch : CatchACWindowBefore (tr.projAC.upTo t) (H t) ((tr.upTo t).HonestBlocks (H t)) a
      (2 * sp.Δ) t)
    {L : Nat} (hL : (L : Int) =
      (AC.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2)
    (ha : a ≤ sp.ts L) {R : AC.Blk sp.n (List (FG.Att sp.n))}
    (hR : R ∈ (Node.frame (tr.state y i)).tree)
    (hvotes : ∀ z q e, HVoteAt tr H z q e → tr.time q ≤ t → e.msg.slot = L →
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg R)
    {K : AC.CommitteeDict sp.n} (hKB : CommitteeFacts tr H K)
    (hLt : sp.ts L + sp.Δ ≤ t) (hfb : AC.FaultBoundK K L tr.projAC (H t) (sp.ts L + sp.Δ)) :
    (AC.voters (AC.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).1.votes).ncard <
      2 * (AC.supporters (Node.frame (tr.state y i))
        (AC.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).1
        (AC.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2 R).ncard := by
  have hall : ∀ x k e, HVoteAt tr H x k e → e.msg.slot = L →
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg R := by
    intro x k e hv hs
    obtain ⟨hx, ℓ, hc⟩ := hVoteAt_iff.1 hv
    have hkt := (cast_time_at hrun hnc hx hc).2
    rw [hs] at hkt
    exact hvotes x k e hv (hkt.trans hLt) hs
  have hr := hrun.upTo ht0
  have hj' : (tr.upTo t).JoinedAt y t := joinedAt_upTo hj
  have hw' : (tr.upTo t).awake y t := ⟨hw, le_rfl⟩
  by_cases hT : ∃ j₁, i ≤ j₁ ∧ (tr.upTo t).TickAt proposer dg y j₁ t
  · obtain ⟨j₁, hij, hT⟩ := hT
    obtain ⟨-, -, -, ht₁⟩ := tickAt_acCall hT
    -- no call of `y` in `[i, j₁)`: it would be at `t`, before the tick
    have hst : ∀ m, i ≤ m → m ≤ j₁ → (tr.upTo t).state y m = (tr.upTo t).state y i := by
      intro m him
      induction m, him using Nat.le_induction with
      | base => exact fun _ => rfl
      | succ m him ih =>
        intro hm
        have htm : (tr.upTo t).time m = t := le_antisymm
          (by rw [← ht₁]; exact hr.time_mono (by omega)) (hti.trans (hr.time_mono him))
        rw [(tr.upTo t).state_succ_of_not fun c hc => not_before_tick hr hy ⟨c, hc⟩
          (by rw [htm]; exact hj') (by rw [htm]; exact hT) (by omega), ih (by omega)]
    have hle₁ : ∀ k < j₁, tr.time k ≤ t := fun k hk => ht₁ ▸ hr.time_mono hk.le
    have hs : tr.state y j₁ = tr.state y i := by
      rw [← Trace.upTo_state tr y hle₁, ← Trace.upTo_state tr y hle]
      exact hst j₁ hij le_rfl
    have hrd₁ : ReadAtCut proposer dg (tr.upTo t) y j₁ t :=
      ⟨ht0, hle₁, ht₁.ge, fun k hk => (hr.tick_unique y hy k j₁ t hk hT).le, hw', hj'⟩
    have h := read_majority_at_read_cut hrun hnc ht0 hy hrd₁ hsync hcatch (by rw [hs]; exact hL)
      ha (by rw [hs]; exact hR) hKB hall hLt hfb
    rwa [hs] at h
  · exact read_majority_at_read_cut hrun hnc ht0 hy
      ⟨ht0, hle, hti, fun k hk => not_lt.1 fun hik => hT ⟨k, hik.le, hk⟩, hw', hj'⟩
      hsync hcatch hL ha hR hKB hall hLt hfb

/-- **The head certificate from target votes** under growing faults: with the record's anchor
compatible with `R`, and `R` below the anchor or viable and extended by every vote of slot `L` of
a node honest at it at a time `≤ t`, the certificate holds, the majority as in
`read_majority_of_target_votes_at`. -/
theorem read_head_support_of_target_votes_at {ini}
    (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {i : Nat} {t : Time} (ht0 : 0 ≤ t) (hy : y ∈ H t)
    (hle : ∀ q < i, tr.time q ≤ t) (hti : t ≤ tr.time i)
    (hw : tr.awake y t) (hj : tr.JoinedAt y t) {a : Time}
    (hsync : SyncACWindowBefore (H t) ((tr.upTo t).HonestBlocks (H t)) a t (tr.projAC.upTo t))
    (hcatch : CatchACWindowBefore (tr.projAC.upTo t) (H t) ((tr.upTo t).HonestBlocks (H t)) a
      (2 * sp.Δ) t)
    {L : Nat} (hL : (L : Int) =
      (AC.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2)
    (ha : a ≤ sp.ts L) {R : AC.Blk sp.n (List (FG.Att sp.n))}
    (hR : R ∈ (Node.frame (tr.state y i)).tree)
    (hanchor : Compatible (Node.frame (tr.state y i)).tree
      (AC.getAnchor sp (tr.state y i).ac (Node.frame (tr.state y i)) t) R)
    (hsource : (Node.frame (tr.state y i)).Anc R
        (AC.getAnchor sp (tr.state y i).ac (Node.frame (tr.state y i)) t) ∨
      (R ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree ∧
        ∀ z q e, HVoteAt tr H z q e → tr.time q ≤ t → e.msg.slot = L →
          AC.VoteExtends (tr.HonestBlocksAt H) e.msg R))
    {K : AC.CommitteeDict sp.n} (hKB : CommitteeFacts tr H K)
    (hLt : sp.ts L + sp.Δ ≤ t) (hfb : AC.FaultBoundK K L tr.projAC (H t) (sp.ts L + sp.Δ)) :
    Compatible (Node.frame (tr.state y i)).tree
      (AC.getAnchor sp (tr.state y i).ac (Node.frame (tr.state y i)) t) R ∧
      ((Node.frame (tr.state y i)).Anc R
        (AC.getAnchor sp (tr.state y i).ac (Node.frame (tr.state y i)) t) ∨
      (R ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree ∧
        (AC.voters (AC.latestView sp (tr.state y i).ac
          (Node.frame (tr.state y i)) t).1.votes).ncard <
          2 * (AC.supporters (Node.frame (tr.state y i))
            (AC.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).1
            (AC.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2 R).ncard)) := by
  refine ⟨hanchor, ?_⟩
  rcases hsource with h | ⟨hv, hvotes⟩
  · exact Or.inl h
  · exact Or.inr ⟨hv, read_majority_of_target_votes_at hrun hnc ht0 hy hle hti hw hj
      hsync hcatch hL ha hR hvotes hKB hLt hfb⟩

end Consensus.Goldilocks.Compose.Growing

end

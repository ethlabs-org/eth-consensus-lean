module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshSupport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.FreshViable
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RunCore
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Honest support at the next-slot vote branch over the stock shadow window -/

namespace Consensus.Goldilocks.Healing.Growing.Shadow

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace' sp} {hold : Time}

/-- Every member of the slot committee `K u` still honest at the next-slot read supports the
unanimous proposal in the merged view of the receiver's next-slot vote branch, for a run from
`K`'s committee start. -/
theorem unanimous_next_cast_supporters_at' {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {u : Nat} (hmargin : gbar g + 2 * sp.Δ ≤ sp.ts u)
    {P : AC.Blk sp.n (List (FG.Att sp.n))} (hPs : P.slot = u)
    (hun : ∀ x i e, x ∈ H (tr.time i) → AC.VoteAt tr.projAC x i e →
      e.msg.slot = u → e.msg.head = P.root)
    {z : Fin sp.n} {a : Nat} (hz : z ∈ H (tr.time a))
    (ha : tr.projAC.AcceptAt z a P) (hta : tr.time a = sp.ts u)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {ell : ACLabel (goldilocksNode' sp)} {R : AC.ACState sp.n}
    (hb : AC.VoteBranchAt tr.projAC y j ell R) (hjs : sp.slot (tr.time j) = u + 1)
    (ht : sp.ts u + 2 * sp.Δ ≤ tr.time j) (hjb : tr.time j ≤ b)
    (hPt : P ∈ ell.frame.tree)
    (hvotes : ∀ x, x ∈ H (tr.time j) → x ∈ K.committee u → ∃ i ev,
      AC.VoteAt tr.projAC x i ev ∧ ev.msg.slot = u ∧ tr.time i ≤ tr.time j)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ x, x ∈ H (tr.time j) → x ∈ K.committee u →
      x ∈ AC.supporters ell.frame (AC.mergedVoteView sp R ell.frame (u + 1)) u P :=
  Core.unanimous_next_cast_supporters_at hrun.toCore hnc hsvc hawake hf hcatch hnr hmargin hPs hun
    hz ha hta hy hb hjs ht hjb hPt hvotes hK

/-- The receiver's next-slot vote branch clears every older incompatible lock before the update,
including labels surviving an intervening update, at the slot committees `K` of a run from `K`'s
committee start. The honest members of `K u` support the proposal at the branch's unlock and are
more than half of `K u`. The receiver need not vote in either slot. -/
theorem FrameWindow.older_locks_compatible_at_update_at' {K : AC.CommitteeDict sp.n}
    {g ΔF b : Time} {u floor : Nat} {kindJ : Prop}
    {J P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts u) (sp.ts (u + 1 : Nat) + 2 * sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hmargin : gbar g + 2 * sp.Δ ≤ sp.ts u)
    (hjoin : ∀ x, x ∈ H (sp.ts u + sp.Δ) → AC.JoinedAt tr.projAC x (sp.ts u + sp.Δ))
    (hTb : sp.ts (u + 1 : Nat) + 2 * sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hun : ∀ x i e, x ∈ H (tr.time i) → AC.VoteAt tr.projAC x i e →
      e.msg.slot = u → e.msg.head = P.root)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode' sp)} (hu : AC.UpdateAt tr.projAC y k u ell)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ l ∈ (tr.projAC.state y k).locks, l.slot < u →
      ∀ L ∈ tr.HonestBlocksAt H, L.root = l.block →
        Compatible (tr.HonestBlocksAt H) L P :=
  Core.older_locks_compatible_at_update_at
    (fun hy' hc' hlo hhi => (proposal_viable_after_votes_at' hframe hrun hnc hsvc hf hnr
      (by linarith [sp.toParams.hΔ]) hTb hz hdes hP hPs hy' hc' hlo hhi).1)
    hrun.toCore hnc hsvc hawake hf hcatch hnr hmargin hjoin hTb hz hdes hP hPs hun hy hu hK

end Consensus.Goldilocks.Healing.Growing.Shadow

end

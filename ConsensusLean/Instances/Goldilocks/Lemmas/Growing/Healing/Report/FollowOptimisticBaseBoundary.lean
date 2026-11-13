module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.OptimisticBaseProposal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.OptimisticBaseVotes

public section

/-! # First-slot optimistic propagation bases

Forwarded to their proofs in `Report/OptimisticBaseVotes` and `Report/OptimisticBaseProposal`. -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- An optimistic write propagates an arbitrary viable prefix to next-slot votes. -/
theorem optimistic_next_votes_of_early_witness_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ))
    {s floor : Nat} (hm : gbar g ≤ sp.ts s)
    (hmb : sp.ts (s + 1 : Nat) + sp.Δ ≤ b)
    {kindJ : Prop} {J X Q D : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s) (sp.ts (s + 1 : Nat) + sp.Δ) floor kindJ J)
    {x : Fin sp.n} {c : Nat} (hx : x ∈ H (tr.time c)) {CV : Set (SA.Vote sp.n)}
    (hopt : SA.OptimisticLockAt tr.projAC x c s D CV)
    (hXD : Anc (tr.HonestBlocksAt H) X D)
    {w : Fin sp.n} {a : Nat} (hw : w ∈ H (tr.time a))
    (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode sp ro)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree) (hh : floor ≤ ((tr.state w a).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocksAt H) J X)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q) (hstock : sp.committeeSize = sp.n) :
    ∀ y i e, y ∈ H (tr.time i) → SA.VoteAt tr.projAC y i e →
      e.msg.slot = s + 1 → SA.VoteExtends (tr.HonestBlocksAt H) e.msg X := by
  exact KernelProof.optimistic_next_votes_of_early_witness_at hrun hnc hsvc hawake hf hcatch
    hm hmb hframe hx hopt hXD hw hat hcw hQw hh hJ hXQ hstock

/-- The first next-slot proposal follows the same prefix, before unanimity induction starts. -/
theorem optimistic_next_proposal_of_early_witness_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ))
    {s floor : Nat} (hm : gbar g ≤ sp.ts s) (hmb : sp.ts (s + 1 : Nat) ≤ b)
    {kindJ : Prop} {J X Q D : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s) (sp.ts (s + 1 : Nat)) floor kindJ J)
    {x : Fin sp.n} {c : Nat} (hx : x ∈ H (tr.time c)) {CV : Set (SA.Vote sp.n)}
    (hopt : SA.OptimisticLockAt tr.projAC x c s D CV)
    (hXD : Anc (tr.HonestBlocksAt H) X D)
    {w : Fin sp.n} {a : Nat} (hw : w ∈ H (tr.time a))
    (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode sp ro)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree) (hh : floor ≤ ((tr.state w a).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocksAt H) J X)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y i ell)
    (hcall : ell.call = .proposal) (hti : tr.time i = sp.ts (s + 1 : Nat))
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hd : (SA.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay))
    (hstock : sp.committeeSize = sp.n) :
    Anc (tr.HonestBlocksAt H) X d.head := by
  exact KernelProof.optimistic_next_proposal_of_early_witness_at hrun hnc hsvc hawake hf hcatch
    hm hmb hframe hx hopt hXD hw hat hcw hQw hh hJ hXQ hy hc hcall hti hd hstock

end Consensus.Goldilocks.Healing.Growing

end

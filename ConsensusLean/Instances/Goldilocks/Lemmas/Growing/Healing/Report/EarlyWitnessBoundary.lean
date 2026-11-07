module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.NextWitness

public section

/-! # The common early-witness induction, independent of supporter propagation

Forwarded to its proof, `KernelProof.next_votes_of_early_witness_at` in `Report/NextWitness`. -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- Common early-witness induction with the lock-specific transfer supplied by the caller. -/
theorem next_votes_of_early_witness_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ))
    {s floor : Nat} {hi : Time} (hm : gbar g ≤ sp.ts s)
    (hnext : sp.ts (s + 1 : Nat) + sp.Δ ≤ hi) (hmb : hi ≤ b)
    {kindJ : Prop} {J X Q : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s) hi floor kindJ J)
    {w : Fin sp.n} {a : Nat} (hw : w ∈ H (tr.time a))
    (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode sp ro)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree) (hh : floor ≤ ((tr.state w a).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocksAt H) J X)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q)
    (htransfer : ∀ y i ell e, y ∈ H (tr.time i) → SA.CastAt tr.projAC y i ell e →
      e.msg.slot = s + 1 → tr.time i ≤ hi →
      Anc (tr.HonestBlocksAt H) (Node.frame (tr.state y i)).F X →
      SA.ViableAtVote ell e (s + 1) X →
      (∀ z k ev, k < i → z ∈ H (tr.time k) → SA.VoteAt tr.projAC z k ev →
        ev.msg.slot = s + 1 → SA.VoteExtends (tr.HonestBlocksAt H) ev.msg X) →
      SA.VoteExtends (tr.HonestBlocksAt H) e.msg X) :
    ∀ y i e, y ∈ H (tr.time i) → SA.VoteAt tr.projAC y i e → e.msg.slot = s + 1 →
      SA.VoteExtends (tr.HonestBlocksAt H) e.msg X := by
  exact KernelProof.next_votes_of_early_witness_at hrun hnc hsvc hawake hf hcatch hm hnext hmb
    hframe hw hat hcw hQw hh hJ hXQ htransfer

end Consensus.Goldilocks.Healing.Growing

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.RegularCommonBoundary
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.RegularTransfer
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The early viable supporter of a historical regular fast selection -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload gbar)
open Compose.Growing

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- Fast transfer discharges the common next-vote induction without retaining the writer. -/
theorem regular_fast_next_votes_of_early_witness_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {s floor : Nat} (hm : gbar g ≤ sp.ts s) (hmb : sp.ts s + 6 * sp.Δ ≤ b)
    {kindJ : Prop} {J X Q D C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s) (sp.ts s + 6 * sp.Δ) floor kindJ J)
    {x : Fin sp.n} {c : Nat} (hx : x ∈ H (tr.time c)) {CV : Set (SA.Vote sp.n)}
    (hfast : SA.FastUpdateAt tr.projAC x c s D CV)
    {RV : Set (SA.Vote sp.n)} (hres : SA.ResultAt tr.projAC x c s C RV)
    (hXD : Anc (tr.HonestBlocksAt H) X D) (hCQ : Anc (tr.HonestBlocksAt H) C Q)
    {w : Fin sp.n} {a : Nat} (hw : w ∈ H (tr.time a))
    (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode sp ro)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree) (hh : floor ≤ ((tr.state w a).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocksAt H) J X) :
    ∀ y i e, y ∈ H (tr.time i) → SA.VoteAt tr.projAC y i e → e.msg.slot = s + 1 →
      SA.VoteExtends (tr.HonestBlocksAt H) e.msg X := by
  obtain ⟨ellx, C', hu, hconf, hsel, hCV⟩ := hfast
  have he : C' = C := by
    obtain ⟨ell', hu', hconf', -⟩ := hres
    have he : ellx = ell' := Option.some.inj (hu.1.2.symm.trans hu'.1.2)
    subst ell'
    exact Option.some.inj (hconf.symm.trans hconf')
  subst C'
  have hDC := ((SA.deepest_mem hsel).1.1.2.2).mono (frameIn_at hrun hnc hx hu.1).2
  have hfl : SA.FastLockAt tr.projAC x c s D CV :=
    Or.inl ⟨ellx, C, hu, hconf, hsel, hCV⟩
  apply Growing.next_votes_of_early_witness_at hrun hnc hsvc hawake hf hcatch hm (by
    have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := SA.ts_succ s
    linarith only [sp.toParams.hΔ, hts]) hmb hframe hw hat hcw hQw hh hJ
      (hXD.trans (hDC.trans hCQ))
  intro y i ell e hy hc hs hhigh hFX hviab ih
  refine first_transfer_service_at hrun hnc hsvc hawake hf hcatch hnr hm hx hy hfl hXD hc hs
    (hhigh.trans hmb) (by rwa [frame_of_projAC_at hrun hy hc.1]) hviab ?_ hrun.stock
  intro z k hki hz ev hv hes
  exact ih z k ev hki hz hv hes

end Consensus.Goldilocks.Healing.Growing.KernelProof

end

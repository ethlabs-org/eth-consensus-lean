module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.RegularCommonBoundary
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.RegularTransfer
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.SlowReadLocks
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.SlowCounted
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Transfer
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The early viable supporter of a historical slow selection -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload gbar)
open Compose.Growing

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- The slow-specific transfer discharges the common causal next-vote induction. -/
theorem regular_slow_next_votes_of_early_witness_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ))
    {s floor : Nat} (hm : gbar g ≤ sp.ts s)
    (hslow : gbar g ≤ sp.ts ((s : Int) - sp.k + 1))
    (hmb : sp.ts s + 6 * sp.Δ ≤ b) {kindJ : Prop}
    {J Q D C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s) (sp.ts s + 6 * sp.Δ) floor kindJ J)
    {x : Fin sp.n} {c : Nat} (hx : x ∈ H (tr.time c))
    (hsl : SA.SlowLockAt tr.projAC x c s D)
    {CV : Set (SA.Vote sp.n)} (hres : SA.ResultAt tr.projAC x c s C CV)
    (hCQ : Anc (tr.HonestBlocksAt H) C Q)
    {w : Fin sp.n} {a : Nat} (hw : w ∈ H (tr.time a))
    (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode sp ro)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree) (hh : floor ≤ ((tr.state w a).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocksAt H) J D) :
    ∀ y i e, y ∈ H (tr.time i) → SA.VoteAt tr.projAC y i e → e.msg.slot = s + 1 →
      SA.VoteExtends (tr.HonestBlocksAt H) e.msg D := by
  obtain ⟨ellx, C', hu, hconf, hsel⟩ := hsl
  have he : C' = C := by
    obtain ⟨ell', hu', hconf', -⟩ := hres
    have he : ellx = ell' := Option.some.inj (hu.1.2.symm.trans hu'.1.2)
    subst ell'
    exact Option.some.inj (hconf.symm.trans hconf')
  subst C'
  have hsl : SA.SlowLockAt tr.projAC x c s D := ⟨ellx, C, hu, hconf, hsel⟩
  have hDC := ((SA.deepest_mem hsel).1.1.2.2).mono (frameIn_at hrun hnc hx hu.1).2
  apply Growing.next_votes_of_early_witness_at hrun hnc hsvc hawake hf hcatch hm (by
    have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := SA.ts_succ s
    linarith only [sp.toParams.hΔ, hts]) hmb hframe hw hat hcw hQw hh hJ (hDC.trans hCQ)
  intro y i ell e hy hc hs hhigh hFD hviab ih
  have htwo : 2 * (H (tr.time i))ᶜ.ncard < sp.n := by
    have hb := hf _ (hrun.time_nonneg i) (hhigh.trans hmb)
    have hn : 0 < sp.n := sp.toParams.hn
    omega
  have hFC : Anc (tr.HonestBlocksAt H) ell.frame.F C := by
    rw [frame_of_projAC_at hrun hy hc.1]
    exact hFD.trans hDC
  exact SA.Growing.result_transfer_anc
    (Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc)
    hx hres hDC hy hc hs
    (result_carry_service_at hrun hnc hsvc hcatch hm hx hy hres hc hs hFC) hviab
    (slow_live_locks_service_at hrun hnc hsvc hx hsl hslow hy hc hs htwo ih)
    (writer_merged_service_at hrun hnc hsvc hm hx hy hu hc hs)

end Consensus.Goldilocks.Healing.Growing.KernelProof

end

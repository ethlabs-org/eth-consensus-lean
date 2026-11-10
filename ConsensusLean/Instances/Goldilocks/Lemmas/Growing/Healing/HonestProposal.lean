module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.Components
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Honest proposal extraction before compromise -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)
open Regimes.Growing (hold)

/-- The proposal supplier is node-local: retain the execution through the proposal time,
then transport the proposal and immediate acceptance witnesses back to the full trace. -/
theorem honestProposalRun_of_proposesAt_at
    {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr)
    {p : Fin sp.n} {kP s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hp : p ∈ H (sp.ts s + hold sp)) (hpp : p = proposer s)
    (hP : tr.ProposesAt p kP P) (hPs : P.slot = s) :
    HonestProposalRun tr H proposer s P := by
  have htime : tr.time kP = sp.ts s := by
    simpa only [sp.slotTime_eq, hPs, SAParams.ts] using hP.2.2
  have hlocal := hrun.toLocalRun
  have hret := hrun.upTo (hlocal.time_nonneg kP)
  rw [htime] at hret
  have hp' : p ∈ H (sp.ts s) := hlocal.antitone (by
    have := sp.toParams.hΔ
    simp only [hold]
    linarith) hp
  have hP' : (tr.upTo (sp.ts s)).ProposesAt p kP P := by
    rcases hP with ⟨⟨⟨acc, hc⟩, hpos⟩, hprop, htime'⟩
    exact ⟨⟨⟨acc, (Trace.upTo_callAt tr).mpr ⟨htime.le, hc⟩⟩, hpos⟩, hprop, htime'⟩
  obtain ⟨_, k, ell, d, pay, hc, hcall, hd, ht, hpar, hs, hpro, hpay,
    j, hkj, hj, hjt⟩ := Healing.honestProposalRun_of_proposesAt hret
      (hnc.upTo (sp.ts s)) hp' hpp hP' hPs
  rw [RunTrace.upTo_projAC] at hc hd ht hj hjt
  have hstate := Trace.upTo_state tr.projAC (proposer s) (i := k)
    (fun q hq => (hlocal.time_mono hq.le).trans ht.le)
  refine ⟨hpp ▸ hp, k, ell, d, pay, ((Trace.upTo_callAt tr.projAC).mp hc).2,
    hcall, ?_, ht, hpar, hs, hpro, hpay, j, hkj, ?_, hjt⟩
  · simpa only [hstate, Trace.upTo_time] using hd
  · obtain ⟨ell', hc', he⟩ := hj
    exact ⟨ell', ((Trace.upTo_callAt tr.projAC).mp hc').2, he⟩

end Consensus.Goldilocks.Healing.Growing

end

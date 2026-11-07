module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowLocal
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.RegularBase

public section

/-! # Proposal parent viability at its own honest call -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

/-- Full-frame parent viability is local to the proposer's honest observation. -/
theorem proposal_parent_viable_full_frame_at
    {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} {i s : Nat} (hy : y ∈ H (tr.time i))
    (hf : (H (tr.time i))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y i ell)
    (hcall : ell.call = .proposal) (hti : tr.time i = sp.toParams.slotTime s)
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hp : (SA.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 =
      some (d, pay)) : d.head ∈ ell.frame.viableHeads := by
  have ht := hrun.time_nonneg i
  have hc' : (tr.upTo (tr.time i)).projAC.CallAt y i ell := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt _).mpr ⟨le_rfl, hc⟩
  have hs := Trace.upTo_state tr.projAC y (d := tr.time i) (i := i)
    (fun k hk => hrun.time_mono hk.le)
  apply Healing.proposal_parent_viable_full_frame (hrun.upTo ht) (hnc.upTo _) hf hy hc'
    hcall hti
  simpa only [RunTrace.upTo_projAC, hs, Trace.upTo_time] using hp

end Consensus.Goldilocks.Healing.Growing

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowLocal
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.RegularBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Lemmas.Tactic.Linarith

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

/-- A proposal remains unique through the proposer's honesty deadline, not after compromise. -/
theorem proposal_frame_unique_at
    {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr)
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H (sp.ts u + sp.Δ)) (hdes : p = proposer u)
    (hactual : tr.ProposesAt p k P) (hPs : P.slot = u) (hu : 0 < u)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y j ell)
    (hjt : tr.time j ≤ sp.ts u + sp.Δ)
    {Q : SA.Blk sp.n (List (FG.Att sp.n))} (hQ : Q ∈ ell.frame.tree)
    (hQu : Q.slot = u) : Q = P := by
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have htime : tr.time k = sp.ts u := by
    simpa only [sp.slotTime_eq, hPs, SAParams.ts] using hactual.2.2
  have hp : p ∈ H (tr.time k) := hrun.antitone (by rw [htime]; linarith [sp.toParams.hΔ]) hpH
  have hP' : (tr.upTo (tr.time k)).ProposesAt p k P :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hactual.1⟩, hactual.2⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hprop, _, a, _, hacc, hat⟩ :=
    Healing.honestProposalRun_of_proposesAt (hrun.upTo (hrun.time_nonneg k))
      (hnc.upTo _) hp hdes hP' hPs
  rw [← hdes] at hprop hacc
  obtain ⟨ella, hca, hblock⟩ := hacc
  have hat' : tr.time a = sp.ts u := hat
  have ha : tr.time a ≤ tr.time k := by rw [hat', htime]
  have hpa := hrun.antitone ha hp
  have hr := hac.upTo (hrun.time_nonneg k)
  rw [RunTrace.upTo_projAC] at hca
  have hPm := (SA.accept_new sp hr.localRun hp ⟨ella, hca, hblock⟩).1 ella hca
  have hca' : tr.projAC.CallAt p a ella :=
    ((Trace.upTo_callAt _).mp hca).2
  have hQr : Q.root ≠ sp.genesisRoot := by
    intro hg
    have hry := hac.upTo (hrun.time_nonneg j)
    have hc' := (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hc⟩
    have hU := hac.localRun.coherent
    have hG := Store.genesis_mem (fg_reachable_at hrun (hrun.time_nonneg j)
      (fun q hq => hrun.time_mono hq.le) hy)
    have hΦ := SA.frameIn_of_callAt hry.localRun hy hc'
    obtain rfl := hU.1 (hΦ.2 hQ)
      ⟨y, j, tr.time j, hrun.time_nonneg j,
        (fun q hq => hrun.time_mono hq.le), hy, hG⟩ hg
    simp [Params.genesisBlock] at hQu
    omega
  exact (hac.honest.one_block_before hrun.antitone hpa hca' hPm
    (by change tr.time a ≤ _; rw [hat']; linarith [sp.toParams.hΔ]) hy hc hQ hjt (hprop ▸ hpH)
    (by rw [hprop, hac.honest.proposer Q ⟨y, j, ell, hy, hc, hQ⟩ hQr, hQu, hdes])
    (hPs.trans hQu.symm)).symm

end Consensus.Goldilocks.Healing.Growing

end

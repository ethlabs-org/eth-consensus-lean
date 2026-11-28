module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowLocal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.LocalFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.RegularBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Proposal parent viability at its own honest call -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload)

/-- Full-frame parent viability is local to the proposer's honest observation. -/
theorem proposal_parent_viable_full_frame_at
    {sp : ACParams}
    {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} {i s : Nat} (hy : y ∈ H (tr.time i))
    (hf : (H (tr.time i))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {ell : ACLabel (goldilocksNode sp)} (hc : tr.projAC.CallAt y i ell)
    (hcall : ell.call = .proposal) (hti : tr.time i = sp.toParams.slotTime s)
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hp : (AC.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 =
      some (d, pay)) : d.head ∈ ell.frame.viableHeads := by
  have hprefix := hrun.upTo (hrun.time_nonneg i)
  have hr := Compose.goldilocks_ac_projection_from hprefix (hnc.upTo _)
  have hc' : (tr.upTo (tr.time i)).projAC.CallAt y i ell := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hc⟩
  obtain ⟨Q, hQ, hv, hroot⟩ :=
    Healing.full_frame_viable_witness hprefix (hnc.upTo _) hf hy i
  rw [← Compose.frame_of_projAC hprefix hy hc'] at hQ hv hroot
  apply Healing.proposal_head_viable hr.localRun hrun.vstart hy hc' hcall hti
    (by rw [RunTrace.upTo_projAC,
      Trace.upTo_state tr.projAC y (fun k hk => hrun.time_mono hk.le)]; exact hp)
  exact ⟨(AC.frameIn_of_callAt hr.localRun hy hc').1.rooted.1,
    Relation.ReflTransGen.refl, Q, hQ, hv, hroot⟩

/-- A proposal remains unique through the proposer's honesty deadline, not after compromise. -/
theorem proposal_frame_unique_at
    {sp : ACParams}
    {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {p : Fin sp.n} {k u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H (sp.ts u + sp.Δ)) (hdes : p = proposer u)
    (hactual : tr.ProposesAt p k P) (hPs : P.slot = u) (hu : 0 < u)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {ell : ACLabel (goldilocksNode sp)} (hc : tr.projAC.CallAt y j ell)
    (hjt : tr.time j ≤ sp.ts u + sp.Δ)
    {Q : AC.Blk sp.n (List (FG.Att sp.n))} (hQ : Q ∈ ell.frame.tree)
    (hQu : Q.slot = u) : Q = P := by
  have hac := Compose.Growing.goldilocks_ac_projection_from hrun hnc
  have htime : tr.time k = sp.ts u := by
    simpa only [sp.slotTime_eq, hPs, ACParams.ts] using hactual.2.2
  have hp : p ∈ H (tr.time k) := hrun.antitone (by rw [htime]; linarith [sp.toParams.hΔ]) hpH
  have hP' : (tr.upTo (tr.time k)).ProposesAt p k P :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hactual.1⟩, hactual.2⟩
  have hpref := hrun.upTo (hrun.time_nonneg k)
  have haccept := (Healing.accept_of_proposesAt hpref (hnc.upTo _) hp hP').1
  obtain ⟨hacc, hat, -⟩ := Healing.ac_block_after hpref.toLocalRun hp haccept
  obtain ⟨ella, hca, hblock⟩ := hacc
  have hat' : tr.time (k + 1) = sp.ts u := hat.trans htime
  have ha : tr.time (k + 1) ≤ tr.time k := by rw [hat', htime]
  have hpa := hrun.antitone ha hp
  have hr := hac.upTo (hrun.time_nonneg k)
  rw [RunTrace.upTo_projAC] at hca
  have hPm := (AC.accept_new sp hr.localRun hp ⟨ella, hca, hblock⟩).1 ella hca
  have hca' : tr.projAC.CallAt p (k + 1) ella :=
    ((Trace.upTo_callAt _).mp hca).2
  have hQr : Q.root ≠ sp.genesisRoot := by
    intro hg
    have hry := hac.upTo (hrun.time_nonneg j)
    have hc' := (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hc⟩
    have hU := hac.localRun.coherent
    have hG := Healing.Store.genesis_mem
      (hrun.toLocalRun.reachable_at (hrun.time_nonneg j)
        (fun q hq => hrun.time_mono hq.le) hy)
    have hΦ := AC.frameIn_of_callAt hry.localRun hy hc'
    obtain rfl := hU.1 (hΦ.2 hQ)
      ⟨y, j, tr.time j, hrun.time_nonneg j,
        (fun q hq => hrun.time_mono hq.le), hy, hG⟩ hg
    simp [Params.genesisBlock] at hQu
    omega
  exact (hac.honest.one_block_before hrun.antitone hpa hca' hPm
    (by change tr.time (k + 1) ≤ _; rw [hat']; linarith [sp.toParams.hΔ]) hy hc hQ hjt
    (hactual.2.1 ▸ hpH)
    (by rw [hactual.2.1, hac.honest.proposer Q ⟨y, j, ell, hy, hc, hQ⟩ hQr, hQu, hdes])
    (hPs.trans hQu.symm)).symm

end Consensus.Goldilocks.Healing.Growing

end

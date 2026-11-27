module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowLocal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.RegularBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreStock
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Proposal parent viability at its own honest call -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload)

namespace Core

/-- The frame-specific supplier is explicit; the proposal argument is shared. -/
theorem proposal_parent_viable_full_frame_at
    {sp : ACParams}
    {u : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n → Store sp.toParams (Payload sp.n)}
    {frameOf : NodeState (goldilocksNode sp) → AC.Frm sp.n (List (FG.Att sp.n))}
    {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : GoldilocksRunCore u frameOf proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} {i s : Nat} (hy : y ∈ H (tr.time i))
    (hf : (H (tr.time i))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hwitness : ∀ (y : Fin sp.n) (i : Nat), y ∈ H (tr.time i) →
      (H (tr.time i))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n →
      ∃ Q ∈ (frameOf (tr.state y i)).tree,
        Q ∈ (frameOf (tr.state y i)).viableHeads ∧
        (frameOf (tr.state y i)).Anc (frameOf (tr.state y i)).fcRoot Q)
    {ell : ACLabel (goldilocksNode sp)} (hc : tr.projAC.CallAt y i ell)
    (hcall : ell.call = .proposal) (hti : tr.time i = sp.toParams.slotTime s)
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hp : (AC.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 =
      some (d, pay)) : d.head ∈ ell.frame.viableHeads := by
  have hr := hrun.acRun_upTo hnc (hrun.time_nonneg i)
  have hc' := (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hc⟩
  have hs := Trace.upTo_state tr.projAC y (d := tr.time i) (i := i)
    (fun k hk => hrun.time_mono hk.le)
  obtain ⟨Q, hQ, hv, hroot⟩ := hwitness y i hy hf
  rw [← hrun.frame_of_projAC_at hy hc] at hQ hv hroot
  apply Healing.proposal_head_viable hr.localRun hrun.vstart hy hc' hcall hti
    (by rw [hs]; exact hp)
  exact ⟨(AC.frameIn_of_callAt hr.localRun hy hc').1.fcRoot_mem,
    Relation.ReflTransGen.refl, Q, hQ, hv, hroot⟩

end Core

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
  apply Core.proposal_parent_viable_full_frame_at hrun.toCore hnc hy hf
    (fun y i hy hf => ?_) hc hcall hti hp
  have h := Healing.full_frame_viable_witness (hrun.upTo (hrun.time_nonneg i))
    (hnc.upTo _) hf hy i
  rwa [RunTrace.upTo_state_of_le hrun.time_mono le_rfl] at h

/-- A proposal remains unique through the proposer's honesty deadline, not after compromise. -/
theorem Core.proposal_frame_unique_at
    {sp : ACParams}
    {update : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n →
      Store sp.toParams (Payload sp.n)}
    {frameOf : NodeState (goldilocksNode sp) → AC.Frm sp.n (List (FG.Att sp.n))}
    {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : GoldilocksRunCore update frameOf proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {p : Fin sp.n} {k u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H (sp.ts u + sp.Δ)) (hdes : p = proposer u)
    (hactual : tr.ProposesAt p k P) (hPs : P.slot = u) (hu : 0 < u)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {ell : ACLabel (goldilocksNode sp)} (hc : tr.projAC.CallAt y j ell)
    (hjt : tr.time j ≤ sp.ts u + sp.Δ)
    {Q : AC.Blk sp.n (List (FG.Att sp.n))} (hQ : Q ∈ ell.frame.tree)
    (hQu : Q.slot = u) : Q = P := by
  have hac := hrun.acRun hnc
  have htime : tr.time k = sp.ts u := by
    simpa only [sp.slotTime_eq, hPs, ACParams.ts] using hactual.2.2
  have hp : p ∈ H (tr.time k) := hrun.antitone (by rw [htime]; linarith [sp.toParams.hΔ]) hpH
  have hP' : (tr.upTo (tr.time k)).ProposesAt p k P :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hactual.1⟩, hactual.2⟩
  have hpref := hrun.upTo (hrun.time_nonneg k)
  have haccept := (hpref.accept_of_proposesAt (hnc.upTo _) hp hP').1
  obtain ⟨hacc, hat, -⟩ := hpref.ac_block_after p hp haccept
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
    have hG := Store.genesis_mem_with hrun.finalitySpec
      (hrun.reachable_at (hrun.time_nonneg j) hy (fun q hq => hrun.time_mono hq.le))
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

/-- Stock specialization of proposal uniqueness. -/
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
    (hQu : Q.slot = u) : Q = P :=
  Core.proposal_frame_unique_at hrun.toCore hnc hpH hdes hactual hPs hu hy hc hjt hQ hQu

end Consensus.Goldilocks.Healing.Growing

end

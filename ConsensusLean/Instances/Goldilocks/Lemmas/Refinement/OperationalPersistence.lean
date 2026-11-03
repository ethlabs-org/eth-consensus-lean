module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealthyEffective
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Store
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Suffix
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting

public section

namespace Consensus.Goldilocks.Refinement.UpTo

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a : Time}

/-- A post-drain operational proposal is below every bounded honest proposal parent
at least two slots later. The report's enclosing origin may have an old label. -/
theorem operational_proposal_below_later_parent {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H) (hdesignated : p = proposer u) (hactual : tr.ProposesAt p k P)
    (hPs : P.slot = u) (hR : Healing.drainTime sp a ≤ sp.ts u)
    (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    {y : Fin sp.n} (hy : y ∈ H) {i v : Nat} (huv : u + 2 ≤ v)
    {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt y i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts v) (hib : tr.time i ≤ b) :
    Anc (tr.HonestBlocks H) P d.head := by
  have hDelta := sp.toParams.hΔ
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hacc := Compose.proposal_accepted hp.run hp.noColl hpH hactual
  have hPU : P ∈ tr.HonestBlocks H := by
    refine ⟨p, hpH, k + 1, ?_⟩
    rw [tr.state_succ_of_call hacc,
      (Store.tree_grows _ _ _ _ (Compose.fg_reachable hp.run.toLocalRun hpH _)).1 P _
        (hp.run.toLocalRun.cutLaw p hpH _ _ hacc).2.1]
    exact Set.mem_insert _ _
  have hca := Healing.cutZ_lt_reset_of_snapshot hp.run
    (by obtain ⟨q, hq, _⟩ := hp.snapshot; exact ⟨q, hq⟩) hp.reset
  have ha0 : 0 ≤ a := by
    have := Healing.lt_cutZ sp g
    have := SA.gbar_nonneg g
    linarith
  have hau : sp.slot a + 2 * sp.k + 5 ≤ u := by
    rw [Healing.drainTime_eq] at hR
    exact_mod_cast (SA.ts_le_iff sp).1 hR
  have hu : 0 < u := by omega
  have hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u := by
    have ha' : a < sp.ts ((sp.slot a : Int) + 1) := not_le.1 fun h => by
      have := (SA.ts_le_iff_le_slot sp ha0 _).1 h
      omega
    have hle : sp.ts ((sp.slot a : Int) + 2) ≤ sp.ts u :=
      (SA.ts_le_iff sp).2 (by omega)
    have hgap : sp.ts ((sp.slot a : Int) + 2) =
        sp.ts ((sp.slot a : Int) + 1) + 4 * sp.Δ := by
      simp only [SAParams.ts]; ring
    have := Healing.lt_cutZ sp g
    rw [hgap] at hle
    linarith
  have hPg : P.root ≠ sp.genesisRoot := by
    intro he
    have hG := Healing.Store.genesis_mem (Compose.fg_reachable hp.run.toLocalRun hpH k)
    have heq := hr.coherent.1 hPU ⟨p, hpH, k, hG⟩ he
    have hz : P.slot = 0 := by rw [heq]; rfl
    omega
  have hun : ∀ z ∈ H, ∀ q e, SA.VoteAt tr.projAC z q e → tr.time q ≤ b →
      e.msg.slot = u → e.msg.head = P.root := fun z hz q e hv hqb hs =>
    hp.operational_unanimous hc hpH hdesignated hactual hPs hR (by linarith)
      z hz q e hv hs hqb
  have hRnext := hR.trans ((SA.ts_le_iff sp).2 (show (u : Int) ≤ (u + 1 : Nat) by omega))
  obtain ⟨x, q, m, S, ho, _, _, hqt⟩ := hp.reset_seed_before_slot hR
  have hSP := old_origin_below_unanimous hp hc hPU hun hgu hRnext
    (show sp.ts u + sp.Δ ≤ b by linarith) ho hqt
  obtain ⟨z, hz, r, ellr, C, hrep, hrt, hPC⟩ :
      ∃ z ∈ H, ∃ r ellr C, SA.ToFGAt tr.projAC z r ellr C ∧
        tr.time r ≤ sp.ts u + 6 * sp.Δ ∧ Anc (tr.HonestBlocks H) P C := by
    rcases report_cover_of_unanimous hp hc hPU hPs hu hPg hun hgu hRnext hTb with hall | hsome
    · obtain ⟨r, ellr, C, hrep, ht, hPC⟩ := hall p hpH
      exact ⟨p, hpH, r, ellr, C, hrep, ht, hPC⟩
    · obtain ⟨z, hz, r, ellr, C, hrep, ht, hPC, _⟩ := hsome
      exact ⟨z, hz, r, ellr, C, hrep, ht, hPC⟩
  have hCt : C ∈ (tr.state z r).fg.tree := by
    have hcand : C ∈ SA.toFGCandidates sp (tr.projAC.state z r) ellr.frame (tr.time r) := by
      have hout := hrep.2.2
      unfold SA.acToFG at hout
      split_ifs at hout
      split at hout
      · cases hout
      · rename_i C' hC'
        split_ifs at hout
        cases hout
        exact (SA.deepest_mem hC').1
    have hCv := hcand.1
    rw [Compose.frame_of_projAC hp.run hz hrep.1] at hCv
    exact hCv.1.1
  have hhigh := hp.high_of_anc ho hz hCt (hSP.trans hPC)
  obtain ⟨io, hior, jo, O, D, CV, hO, _, _, hCO, _⟩ :=
    hp.high_report_origin hz hrep (hrt.trans hTb) hhigh
  have hTv : sp.ts u + 6 * sp.Δ < sp.ts v := by
    have hle : sp.ts (u + 2 : Nat) ≤ sp.ts v := (SA.ts_le_iff sp).2 (by omega)
    simp only [SAParams.ts] at hle ⊢
    push_cast at hle
    linarith
  have hRv := hR.trans ((SA.ts_le_iff sp).2 (show (u : Int) ≤ v by omega))
  exact hPC.trans (hCO.trans (hp.reset_proposal_passes hc hy hRv hci hcall hd hti hib O
    ⟨z, io, jo, hO, ((hp.run.time_mono hior.le).trans hrt).trans_lt hTv⟩))

end Consensus.Goldilocks.Refinement.UpTo

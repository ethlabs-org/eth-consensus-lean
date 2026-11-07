module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HealedC4
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.OperationalPending
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Store
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeBase
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Persistence of a bounded operational proposal, under growing faults

The growing form of `Obligations/OperationalPersistence` and of the C4 wrappers of
`Obligations/HealedUpTo`:

* `UpTo.operational_proposal_below_later_parent_at`: a post-drain operational proposal of slot
  `u`, by its proposer honest through `t_u + hold`, is an honest ancestor of the duty head of every
  bounded proposal call at least two slots later by a node honest at that call;
* `honest_proposal_below_next_upTo_at`, `honest_proposal_below_later_upTo_at`: no reorg of honest
  proposals one slot on (with the service reserve `t_s + 6Δ ≤ b`) and two or more slots on (with
  `t_{s'} ≤ b`). -/

namespace Consensus.Goldilocks.Obligations.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- A report's block is held in the reporter's tree, for a reporter honest at the report. -/
private theorem toFG_mem_tree_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) {y : Fin sp.n} {k : Nat}
    (hy : y ∈ H (tr.time k)) {ℓ : ACLabel (goldilocksNode sp ro)}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} (hto : SA.ToFGAt tr.projAC y k ℓ C) :
    C ∈ (tr.state y k).fg.tree := by
  have hd := hrun.time_nonneg k
  have hle : ∀ q < k, tr.time q ≤ tr.time k := fun _ hq => hrun.time_mono hq.le
  have hto' : SA.ToFGAt (tr.upTo (tr.time k)).projAC y k ℓ C := by
    obtain ⟨hc, hcall, hout⟩ := hto
    rw [RunTrace.upTo_projAC]
    refine ⟨(Trace.upTo_callAt_of_le _ le_rfl).mpr hc, hcall, ?_⟩
    rw [Trace.upTo_state tr.projAC y hle]
    exact hout
  have h := Healing.toFG_mem_tree (hrun.upTo hd) hy hto'
  rwa [RunTrace.upTo_state_of_le hrun.time_mono le_rfl] at h

/-- **A post-drain operational proposal is below every bounded honest proposal parent at least
two slots later**, under growing faults. -/
theorem UpTo.operational_proposal_below_later_parent_at
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.Growing.CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H (sp.ts u + Regimes.Growing.hold sp)) (hdesignated : p = proposer u)
    (hactual : tr.ProposesAt p k P) (hPs : P.slot = u) (hR : Healing.drainTime sp a ≤ sp.ts u)
    (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    {y : Fin sp.n} {i v : Nat} (hy : y ∈ H (tr.time i)) (huv : u + 2 ≤ v)
    {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt y i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts v) (hib : tr.time i ≤ b) :
    Anc (tr.HonestBlocksAt H) P d.head := by
  have hDelta := sp.toParams.hΔ
  have hrun := hp.run
  have hnc := hp.noColl
  have htk : tr.time k = sp.ts u := by
    rw [hactual.2.2, ← hPs, sp.slotTime_eq]; rfl
  have hpk : p ∈ H (tr.time k) := hrun.antitone (by
    rw [htk]; exact le_add_of_nonneg_right hDelta.le) hpH
  have hle1 : ∀ q < k + 1, tr.time q ≤ tr.time k := fun _ hq => hrun.time_mono (by omega)
  have hPx := (accept_of_proposesAt_at hrun hnc hpk hactual).2.1
  have hPU : P ∈ tr.HonestBlocksAt H :=
    ⟨p, k + 1, tr.time k, hrun.time_nonneg k, hle1, hpk, hPx⟩
  have hca := Healing.Growing.cutZ_lt_reset_of_snapshot_at hrun
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
    have hG := Healing.Store.genesis_mem
      (Healing.Growing.fg_reachable_at hrun (hrun.time_nonneg k) hle1 hpk)
    have heq := (Compose.Growing.honest_blocks_coherent hrun hnc).1 hPU
      ⟨p, k + 1, tr.time k, hrun.time_nonneg k, hle1, hpk, hG⟩ he
    have hz : P.slot = 0 := by rw [heq]; rfl
    omega
  have hun : ∀ z j e, z ∈ H (tr.time j) → SA.VoteAt tr.projAC z j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root := fun z j e hz hv hjb hs =>
    hp.operational_unanimous_at hc hpH hdesignated hactual hPs hR (by linarith)
      z j e hz hv hs hjb
  have hRnext := hR.trans ((SA.ts_le_iff sp).2 (show (u : Int) ≤ (u + 1 : Nat) by omega))
  obtain ⟨x, q, m, S, ho, _, _, hqt⟩ := hp.reset_seed_before_slot_at hR
  have hSP := Healing.Growing.old_origin_below_unanimous_at hp hc hPU hun hgu hRnext
    (show sp.ts u + sp.Δ ≤ b by linarith) ho hqt
  have hT0 : 0 ≤ sp.ts u + 6 * sp.Δ := by
    have := hrun.time_nonneg k; rw [htk] at this; linarith
  obtain ⟨z, r, ellr, C, hz, hrep, hrt, hPC⟩ :
      ∃ z r ellr C, z ∈ H (tr.time r) ∧ SA.ToFGAt tr.projAC z r ellr C ∧
        tr.time r ≤ sp.ts u + 6 * sp.Δ ∧ Anc (tr.HonestBlocksAt H) P C := by
    rcases Healing.Growing.report_cover_of_unanimous_at hp hc hPU hPs hu hPg hun hgu hRnext hTb
      with hall | hsome
    · obtain ⟨w, hw⟩ : (H (sp.ts u + 6 * sp.Δ)).Nonempty := by
        by_contra hne
        rw [Set.not_nonempty_iff_eq_empty] at hne
        have hf := hp.faults _ hT0 hTb
        rw [hne, Set.compl_empty, Set.ncard_univ, Nat.card_eq_fintype_card,
          Fintype.card_fin] at hf
        have := Fin.pos p
        omega
      obtain ⟨r, ellr, C, hrep, ht, hPC⟩ := hall w hw
      exact ⟨w, r, ellr, C, hrun.antitone ht hw, hrep, ht, hPC⟩
    · obtain ⟨z, r, ellr, C, hz, hrep, ht, hPC, _⟩ := hsome
      exact ⟨z, r, ellr, C, hz, hrep, ht, hPC⟩
  have hCt : C ∈ (tr.state z r).fg.tree := toFG_mem_tree_at hrun hz hrep
  have hhigh := hp.high_of_anc_at ho (hrun.time_nonneg r) (fun _ hq => hrun.time_mono hq.le) hz
    hCt (hSP.trans hPC)
  obtain ⟨io, hior, jo, O, D, CV, hO, _, _, hCO, _⟩ :=
    hp.high_report_origin_at hz hrep (hrt.trans hTb) hhigh
  have hTv : sp.ts u + 6 * sp.Δ < sp.ts v := by
    have hle : sp.ts (u + 2 : Nat) ≤ sp.ts v := (SA.ts_le_iff sp).2 (by omega)
    simp only [SAParams.ts] at hle ⊢
    push_cast at hle
    linarith
  have hRv := hR.trans ((SA.ts_le_iff sp).2 (show (u : Int) ≤ v by omega))
  exact hPC.trans (hCO.trans (hp.reset_proposal_passes_at hc hy hRv hci hcall hd hti hib O
    ⟨z, io, jo, hO, ((hrun.time_mono hior.le).trans hrt).trans_lt hTv⟩))

/-- **No reorg two slots on, through the horizon**, under growing faults. -/
theorem honest_proposal_below_later_upTo_at
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.Growing.CatchRun tr H g (2 * sp.Δ)) {s s' : Nat}
    {P P' : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : Healing.Growing.HonestProposalRun tr H proposer s P)
    (hR : Healing.drainTime sp a ≤ sp.ts s)
    (hP' : Healing.Growing.HonestProposalRun tr H proposer s' P') (hss : s + 2 ≤ s')
    (hb : sp.ts s' ≤ b) : Anc (tr.HonestBlocksAt H) P P' := by
  obtain ⟨k, hk⟩ := proposesAt_of_honestProposalRun_at hp.run hP
  have hPs := honestProposalRun_slot_at hP
  have hΔ := sp.toParams.hΔ
  have h2 : sp.ts (s + 2 : Nat) ≤ sp.ts s' := (SA.ts_le_iff sp).2 (by push_cast; omega)
  have he : sp.ts (s + 2 : Nat) = sp.ts s + 8 * sp.Δ := by
    simp only [SA.SAParams.ts]; push_cast; ring
  have hTb : sp.ts s + 6 * sp.Δ ≤ b := by linarith
  have hy' : proposer s' ∈ H (sp.ts s') := hp.run.antitone
    (le_add_of_nonneg_right hΔ.le) hP'.1
  exact honest_proposal_child_at hp hP' fun hci hcall hd hti =>
    UpTo.operational_proposal_below_later_parent_at hp hc hP.1 rfl hk hPs hR hTb
      (hti ▸ hy') hss hci hcall hd hti (hti ▸ hb)

/-- **No reorg one slot on, through the horizon**, under growing faults, with the service reserve
`t_s + 6Δ ≤ b`. -/
theorem honest_proposal_below_next_upTo_at
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.Growing.CatchRun tr H g (2 * sp.Δ)) {s : Nat}
    {P P' : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : Healing.Growing.HonestProposalRun tr H proposer s P)
    (hR : Healing.drainTime sp a ≤ sp.ts s)
    (hP' : Healing.Growing.HonestProposalRun tr H proposer (s + 1) P')
    (hTb : sp.ts s + 6 * sp.Δ ≤ b) : Anc (tr.HonestBlocksAt H) P P' := by
  obtain ⟨k, hk⟩ := proposesAt_of_honestProposalRun_at hp.run hP
  have hPs := honestProposalRun_slot_at hP
  have hy' : proposer (s + 1) ∈ H (sp.ts (s + 1 : Nat)) := hp.run.antitone
    (le_add_of_nonneg_right sp.toParams.hΔ.le) hP'.1
  exact honest_proposal_child_at hp hP' fun hci hcall hd hti =>
    UpTo.operational_proposal_below_next_parent_at hp hc hP.1 rfl hk hPs hR hTb
      (hti ▸ hy') hci hcall hd hti

end Consensus.Goldilocks.Obligations.Growing

end

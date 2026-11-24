module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HealedC4
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.OperationalReports
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Selection
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Store
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.ReportCover
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.OperationalReports
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Persistence of a bounded operational proposal, under growing faults

The persistence of a bounded operational proposal and the C4 wrappers:

* `UpTo.operational_proposal_below_later_parent_at`: a post-drain operational proposal of slot
  `u`, by its proposer honest through `t_u + hold`, is an honest ancestor of the duty head of every
  bounded proposal call at least two slots later by a node honest at that call;
* `honest_proposal_below_next_upTo_at`, `honest_proposal_below_later_upTo_at`: no reorg of honest
  proposals one slot on (with the service reserve `t_s + 6Δ ≤ b`) and two or more slots on (with
  `t_{s'} ≤ b`). -/

namespace Consensus.Goldilocks.Obligations.Growing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- **A post-drain operational proposal is below every bounded honest proposal parent at least
two slots later**, under growing faults. -/
theorem UpTo.operational_proposal_below_later_parent_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK)
    {p : Fin sp.n} {k u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H (sp.ts u + Regimes.Growing.hold sp)) (hdesignated : p = proposer u)
    (hactual : tr.ProposesAt p k P) (hPs : P.slot = u) (hR : Healing.drainTime sp a ≤ sp.ts u)
    (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    {y : Fin sp.n} {i v : Nat} (hy : y ∈ H (tr.time i)) (huv : u + 2 ≤ v)
    {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt y i ell) (hcall : ell.call = .proposal)
    (hd : (AC.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay))
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
  have hca := hp.cutZ_lt_reset_at
  have ha0 : 0 ≤ a := by
    have := Healing.lt_cutZ sp g
    have := AC.gbar_nonneg g
    linarith
  have hau : sp.slot a + 2 * sp.k + 5 ≤ u := by
    rw [Healing.drainTime_eq] at hR
    exact_mod_cast (AC.ts_le_iff sp).1 hR
  have hu : 0 < u := by omega
  have hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u := by
    have ha' : a < sp.ts ((sp.slot a : Int) + 1) := not_le.1 fun h => by
      have := (AC.ts_le_iff_le_slot sp ha0 _).1 h
      omega
    have hle : sp.ts ((sp.slot a : Int) + 2) ≤ sp.ts u :=
      (AC.ts_le_iff sp).2 (by omega)
    have hgap : sp.ts ((sp.slot a : Int) + 2) =
        sp.ts ((sp.slot a : Int) + 1) + 4 * sp.Δ := by
      simp only [ACParams.ts]; ring
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
  have hun : ∀ z j e, z ∈ H (tr.time j) → AC.VoteAt tr.projAC z j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root := fun z j e hz hv hjb hs =>
    hp.operational_unanimous_at hpH hdesignated hactual hPs hR (by linarith)
      z j e hz hv hs hjb
  have hRnext := hR.trans ((AC.ts_le_iff sp).2 (show (u : Int) ≤ (u + 1 : Nat) by omega))
  obtain ⟨x, q, m, S, ho, _, _, hqt⟩ := hp.reset_seed_before_slot_at hR
  have hSP := Healing.Growing.old_origin_below_unanimous_at hp hPU hun hgu hRnext
    (show sp.ts u + sp.Δ ≤ b by linarith) ho hqt
  have hT0 : 0 ≤ sp.ts u + 6 * sp.Δ := by
    have := hrun.time_nonneg k; rw [htk] at this; linarith
  have hczT : Healing.cutZ sp.toParams g ≤ sp.ts u + 6 * sp.Δ := by
    have ha' : a < sp.ts ((sp.slot a : Int) + 1) := not_le.1 fun h => by
      have := (AC.ts_le_iff_le_slot sp ha0 _).1 h
      omega
    have hle : sp.ts ((sp.slot a : Int) + 1) ≤ sp.ts u := (AC.ts_le_iff sp).2 (by omega)
    linarith [sp.toParams.hΔ]
  obtain ⟨w, hw⟩ : (H (sp.ts u + 6 * sp.Δ)).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have hf := hp.faults _ hT0 hTb
    rw [hne, Set.compl_empty, Set.ncard_univ, Nat.card_eq_fintype_card,
      Fintype.card_fin] at hf
    have := Fin.pos p
    omega
  have hjoin : sp.ts (sp.slot (AC.gbar g) + 1 : Nat) ≤ sp.ts u := by
    have hbase := (AC.ts_le_iff_le_slot sp (AC.gbar_nonneg g)
      (sp.slot (AC.gbar g))).2 le_rfl
    simp only [ACParams.ts] at hbase hgu ⊢
    push_cast at hbase hgu ⊢
    linarith
  obtain ⟨j, ellj, hup⟩ := hp.update_call_of_awake hw hjoin hTb
  have htj : tr.time j = sp.ts u + 6 * sp.Δ := hup.2.2.1
  have hwj : w ∈ H (tr.time j) := htj ▸ hw
  have hjb : tr.time j ≤ b := htj ▸ hTb
  have hafter : a ≤ tr.time j := by
    have ha' : a < sp.ts ((sp.slot a : Int) + 1) := not_le.1 fun h => by
      have := (AC.ts_le_iff_le_slot sp ha0 _).1 h
      omega
    have hle : sp.ts ((sp.slot a : Int) + 1) ≤ sp.ts u :=
      (AC.ts_le_iff sp).2 (by omega)
    rw [htj]
    linarith
  have escape : ∀ z r ellr C,
      z ∈ H (max (Healing.cutZ sp.toParams g) (tr.time r)) →
      AC.ToFGAt tr.projAC z r ellr C → tr.time r ≤ sp.ts u + 6 * sp.Δ →
      Anc (tr.HonestBlocksAt H) P C →
      ∃ z io jo O, Healing.Growing.HighOrigin tr H g z io jo O ∧
        tr.time io ≤ sp.ts u + 6 * sp.Δ ∧ Anc (tr.HonestBlocksAt H) P O := by
    intro z r ellr C hzz hrep hrt hPC
    have hz := hrun.antitone (le_max_right _ _) hzz
    have hCt := Healing.Growing.toFG_mem_tree_at hrun hz hrep
    have hhigh := hp.high_of_anc_at ho (hrun.time_nonneg r)
      (fun _ hq => hrun.time_mono hq.le) hz hCt (hSP.trans hPC)
    obtain ⟨io, hior, jo, O, _, _, hO, _, _, hCO, _⟩ :=
      hp.high_report_origin_at hzz hrep (hrt.trans hTb) hhigh
    exact ⟨z, io, jo, O, hO, (hrun.time_mono hior.le).trans hrt, hPC.trans hCO⟩
  obtain ⟨z, io, jo, O, hO, hOt, hPO⟩ :
      ∃ z io jo O, Healing.Growing.HighOrigin tr H g z io jo O ∧
        tr.time io ≤ sp.ts u + 6 * sp.Δ ∧ Anc (tr.HonestBlocksAt H) P O := by
    rcases Healing.Growing.finality_alternative_before_update_at hp hPU hPs hu hun hgu
        hRnext hTb hwj hafter htj.le with hFP | ⟨z, r, ellr, C, hz, _, hr, ht, hPC, _⟩
    swap
    · exact escape z r ellr C hz hr ht hPC
    rcases Healing.Growing.unanimous_viable_or_higher_report_at hp hPU hPs hu hun hgu
        hRnext hTb hwj hup.1 htj hFP with hPv | ⟨z, r, ellr, C, hz, _, hr, ht, hPC, _⟩
    swap
    · exact escape z r ellr C hz hr ht hPC
    obtain ⟨hPt, hconf, hnv, hfast, _, _⟩ :=
      Healing.Growing.operational_update_selection_at hp hpH hdesignated hactual hPs hR hgu
        hTb hwj hup
    have hPhi := (Healing.Growing.frame_tree_subset_at hrun hnc hwj hup.1).1
    have hD := Obligations.UpTo.deepest_of_subset
      (S := {X | X ∈ {X | X ∈ AC.confirmationPath sp ellj.frame P ∧
        ¬ AC.conflictsWithLock sp (tr.projAC.state w j).locks ellj.frame (tr.time j) X} ∧
        AC.FastTest sp (tr.projAC.state w j) ellj.frame u X}) hfast
      (fun X hX => ⟨hX.1.1, hX.2⟩)
      ⟨⟨(AC.deepest_mem hfast).1.1, hnv⟩, (AC.deepest_mem hfast).1.2⟩
    have hfl : AC.FastLockAt tr.projAC w j u P
        (AC.fastCounted sp (tr.projAC.state w j) ellj.frame u P) :=
      Or.inl ⟨ellj, P, hup, hconf, by
        simpa only [Set.mem_ofPred_eq, and_assoc, RunTrace.projAC] using hD, rfl⟩
    have hwz : w ∈ H (max (Healing.cutZ sp.toParams g) (tr.time j)) := by
      rw [htj, max_eq_right hczT]; exact hw
    have hjoined : tr.JoinedAt w (tr.time j) := by
      intro r hrs hrt
      have hbound := hp.restart_le_before_at (hrun.antitone hrt hwj) hrs (hrt.trans hjb)
      have hslot : sp.slot (tr.time j) = u + 1 := by
        rw [htj]
        apply AC.slot_of_mem sp (u + 1) <;>
          simp only [ACParams.ts] <;> push_cast <;> linarith
      change 0 < sp.slot (tr.time j) ∧ _
      refine ⟨by rw [hslot]; omega, ?_⟩
      change tr.time r ≤ sp.toParams.slotTime (sp.slot (tr.time j) - 1)
      rw [hslot, Nat.add_sub_cancel, sp.slotTime_eq]
      exact hbound.trans hjoin
    have hPm := (Healing.Growing.frame_tree_subset_at hrun hnc hwj hup.1).2 hPt
    have hhigh := hp.high_of_anc_at ho (hrun.time_nonneg j)
      (fun _ hq => hrun.time_mono hq.le) hwj hPm hSP
    exact ⟨w, j, u, P, ⟨hwz, hjoined,
      ⟨_, ellj, P, hup.1, hfl, (AC.viableAncestor_self hPhi hPt (Or.inl hPv)).symm⟩,
      hhigh⟩, htj.le, .refl⟩
  have hTv : sp.ts u + 6 * sp.Δ < sp.ts v := by
    have hle : sp.ts (u + 2 : Nat) ≤ sp.ts v := (AC.ts_le_iff sp).2 (by omega)
    simp only [ACParams.ts] at hle ⊢
    push_cast at hle
    linarith
  have hRv := hR.trans ((AC.ts_le_iff sp).2 (show (u : Int) ≤ v by omega))
  exact hPO.trans (hp.reset_proposal_passes_at hy hRv hci hcall hd hti hib O
    ⟨z, io, jo, hO, hOt.trans_lt hTv⟩)

/-- **No reorg two slots on, through the horizon**, under growing faults. -/
theorem honest_proposal_below_later_upTo_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK)
    {s s' : Nat}
    {P P' : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : Healing.Growing.HonestProposalRun tr H proposer s P)
    (hR : Healing.drainTime sp a ≤ sp.ts s)
    (hP' : Healing.Growing.HonestProposalRun tr H proposer s' P') (hss : s + 2 ≤ s')
    (hb : sp.ts s' ≤ b) : Anc (tr.HonestBlocksAt H) P P' := by
  obtain ⟨k, hk⟩ := proposesAt_of_honestProposalRun_at hp.run hP
  have hPs := honestProposalRun_slot_at hP
  have hΔ := sp.toParams.hΔ
  have h2 : sp.ts (s + 2 : Nat) ≤ sp.ts s' := (AC.ts_le_iff sp).2 (by push_cast; omega)
  have he : sp.ts (s + 2 : Nat) = sp.ts s + 8 * sp.Δ := by
    simp only [AC.ACParams.ts]; push_cast; ring
  have hTb : sp.ts s + 6 * sp.Δ ≤ b := by linarith
  have hy' : proposer s' ∈ H (sp.ts s') := hp.run.antitone
    (le_add_of_nonneg_right hΔ.le) hP'.1
  exact honest_proposal_child_at hp hP' fun hci hcall hd hti =>
    UpTo.operational_proposal_below_later_parent_at hp hP.1 rfl hk hPs hR hTb
      (hti ▸ hy') hss hci hcall hd hti (hti ▸ hb)

/-- **No reorg one slot on, through the horizon**, under growing faults, with the service reserve
`t_s + 6Δ ≤ b`. -/
theorem honest_proposal_below_next_upTo_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK)
    {s : Nat}
    {P P' : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : Healing.Growing.HonestProposalRun tr H proposer s P)
    (hR : Healing.drainTime sp a ≤ sp.ts s)
    (hP' : Healing.Growing.HonestProposalRun tr H proposer (s + 1) P')
    (hTb : sp.ts s + 6 * sp.Δ ≤ b) : Anc (tr.HonestBlocksAt H) P P' := by
  obtain ⟨k, hk⟩ := proposesAt_of_honestProposalRun_at hp.run hP
  have hPs := honestProposalRun_slot_at hP
  have hy' : proposer (s + 1) ∈ H (sp.ts (s + 1 : Nat)) := hp.run.antitone
    (le_add_of_nonneg_right sp.toParams.hΔ.le) hP'.1
  exact honest_proposal_child_at hp hP' fun hci hcall hd hti =>
    UpTo.operational_proposal_below_next_parent_at hp hP.1 rfl hk hPs hR hTb
      (hti ▸ hy') hci hcall hd hti

end Consensus.Goldilocks.Obligations.Growing

end

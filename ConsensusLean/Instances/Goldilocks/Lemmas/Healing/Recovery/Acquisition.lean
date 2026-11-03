module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.Interface
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Pivot
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Suffix

public section

/-! # Goldilocks Recovery: fresh high-proposal acquisition (C1)

Every honest ready proposal of a post-drain slot is high (`ready_proposal_high`). The reset
seed is a high origin written before the slot (`reset_seed_before_slot`), and every such origin
lies below the duty head of the slot's actual `ac_proposal` (`reset_proposal_passes`). The
proposal's parent is that duty head (`honestProposalRun_of_ready`), and heights grow along
ancestry (`high_of_anc`). The acquisition (`fresh_high_proposal`) therefore takes the first
slot `v` of the selected stretch: the budget `acqSlots` is slack, and no report supply is
needed. -/

namespace Consensus.Goldilocks.Healing.Recovery

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF Gp a : Time}

/-- **Every post-drain honest ready proposal is high**: its own acceptance (at its proposal cut)
leaves it at state height at least `H_z + 1`. -/
theorem ready_proposal_high (hp : ResetPremises tr H proposer dg g ΔF a)
    (hc : CatchRun tr H g (2 * sp.Δ)) {p : Fin sp.n} {k u : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hready : ReadyProposal tr H proposer p k u P)
    (hR : drainTime sp a ≤ sp.ts u) :
    ∃ iP, tr.AcceptAt p iP P ∧ HZ tr H g + 1 ≤ ((tr.post iP).fg.σ P.root).h := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hpH : p ∈ H := hready.1
  -- the proposal's `ac_proposal` call and duty head
  obtain ⟨-, i, ell, d, pay, hci, hcall, hd, hti, hPQ, -⟩ :=
    honestProposalRun_of_ready hp.run hp.noColl hready
  rw [← hready.2.1] at hci hd
  have hau : a ≤ sp.ts u := by
    refine le_trans ?_ hR
    rw [drainTime_eq]
    obtain ⟨⟨y, hy, k', att, -, -, hka⟩, -⟩ := hp.reset
    have ha0 : 0 ≤ a := hka ▸ hp.run.time_nonneg k'
    have hlt : a < sp.ts ((sp.slot a : Int) + 1) := by
      by_contra h
      have := (SA.ts_le_iff_le_slot sp ha0 _).1 (not_lt.1 h)
      omega
    exact hlt.le.trans ((SA.ts_le_iff sp).2 (by push_cast; omega))
  have hpu := hp.toUpTo tr H hau
  -- the reset seed, a high origin written before the slot, is below the duty head
  obtain ⟨x, r, l, O, ho, -, -, hrt⟩ := hpu.reset_seed_before_slot hR
  have hOd := hpu.reset_proposal_passes hc hpH hR hci hcall hd hti hti.le O ⟨x, r, l, ho, hrt⟩
  -- the parent edge to `P`
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hpH hci
  obtain ⟨hst, hsQ⟩ := Compose.acProposal_start_anc_head hPhi hd
  have hQt : d.head ∈ ell.frame.tree := by
    rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hsQ with he | ⟨c, -, hc⟩
    · exact he ▸ hst
    · exact hc.2.1
  have hQU := hPhiU hQt
  have hacc := Compose.proposal_accepted hp.run hp.noColl hpH hready.2.2.2.1
  have hPt : P ∈ (tr.state p (k + 1)).fg.tree := by
    rw [tr.state_succ_of_call hacc,
      (Store.tree_grows _ _ _ _ (Compose.fg_reachable hp.run.toLocalRun hpH _)).1 P _
        (hp.run.toLocalRun.cutLaw p hpH _ _ hacc).2.1]
    exact Set.mem_insert _ _
  have hPU : P ∈ tr.HonestBlocks H := ⟨p, hpH, k + 1, hPt⟩
  have hOP : Anc (tr.HonestBlocks H) O P := hOd.trans (.single ⟨hQU, hPU, hPQ⟩)
  refine ⟨k, hacc, ?_⟩
  have h := high_of_anc hp ho hpH hPt hOP
  rwa [tr.state_succ_of_call hacc] at h

/-- **C1, fresh high-proposal acquisition**: the first slot `v` of the selected stretch has an
honest ready proposal, which is high once `v` is after the drain. The budget `acqSlots` is
not needed (`s = v`). -/
theorem fresh_high_proposal {W M cF kF v : Nat}
    (hp : ResetPremises tr H proposer dg g ΔF a)
    (hpat : PatternPremises tr H proposer dg g ΔF Gp W M cF kF)
    (hwindow : ∀ u, v ≤ u → u < v + M →
      ∃ (k : Nat) (B : SA.Blk sp.n (List (FG.Att sp.n))),
        ReadyProposal tr H proposer (proposer u) k u B)
    (hv : drainTime sp a ≤ sp.ts v) :
    ∃ (s : Nat) (p : Fin sp.n) (kP iP : Nat) (P : SA.Blk sp.n (List (FG.Att sp.n))),
      v ≤ s ∧ s ≤ v + acqSlots sp Gp ∧
      ReadyProposal tr H proposer p kP s P ∧ tr.AcceptAt p iP P ∧
      HZ tr H g + 1 ≤ ((tr.post iP).fg.σ P.root).h := by
  have hM : 0 < M := lt_of_lt_of_le (by unfold Mstar; omega) hpat.long
  obtain ⟨k, B, hB⟩ := hwindow v le_rfl (by omega)
  obtain ⟨iP, hacc, hh⟩ := ready_proposal_high hp hpat.catchPremise hB hv
  exact ⟨v, proposer v, k, iP, B, le_rfl, by omega, hB, hacc, hh⟩

end Consensus.Goldilocks.Healing.Recovery

end

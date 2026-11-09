module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.SupplierViews
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.SupplierFrames
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.FiniteSources
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Supplier
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.RootProposal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.ProposalFrame
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.ProposalViable
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.StopAtParent
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.SuffixBest
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.CallLocks
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Pivot
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.Timing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.UpdateCalls
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.HonestProposal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetSource
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.UnanimityWalk
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Unanimity of the post-drain slot under growing faults

The growing form of `Healing.ResetPremisesUpTo.operational_unanimous` (Outcome/Supplier): every
vote of slot `u` by a node honest at its cast, by `b`, is for the actual post-drain proposal. The
proposer's frame is read at its call, and each voter's frame at its cast, on the prefix through
that cut over the validators honest there; the slot arithmetic and the ghost walk are the static
ones (`post_drain_slot`, `voter_head_eq_proposal`). -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)
open Regimes.Growing (hold)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- Every vote of slot `u` by a node honest at its cut, by `b`, is for the post-drain operational
proposal `P` of slot `u`, whose proposer is honest through `t_u + hold`. -/
theorem operational_unanimous_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H (sp.ts u + hold sp)) (hdesignated : p = proposer u)
    (hactual : tr.ProposesAt p k P) (hPs : P.slot = u) (hR : drainTime sp a ≤ sp.ts u)
    (hub : sp.ts u ≤ b) :
    ∀ y j e, y ∈ H (tr.time j) → SA.VoteAt tr.projAC y j e → e.msg.slot = u →
      tr.time j ≤ b → e.msg.head = P.root := by
  have hDelta := sp.toParams.hΔ
  obtain ⟨s, rfl, hu, hg, hgu, hjoin⟩ := post_drain_slot hp.cutZ_lt_reset_at hR
  obtain ⟨_, i, ellp, d, pay, hci, hcall, hd, hti, hPQ, _, _, hpay, _⟩ :=
    honestProposalRun_of_proposesAt_at hp.run hp.noColl hpH hdesignated hactual hPs
  rw [← hdesignated] at hci hd
  change tr.time i = sp.ts (s + 1 : Nat) at hti
  change (SA.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay) at hd
  have hib : tr.time i ≤ b := hti ▸ hub
  obtain ⟨D, hsD, hDQ, hviab, hvot⟩ :=
    hp.reset_pivot_at hc hpH hactual hPs hR hci hcall hd hti hib hPQ
  have hi0 := hp.run.time_nonneg i
  have hpi : p ∈ H (tr.time i) := hp.run.antitone (by rw [hti, hold]; linarith) hpH
  have hrp := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time i)) (tr.upTo (tr.time i))
    proposer (hp.run.upTo hi0) (hp.noColl.upTo _)).localRun
  have hci' : (tr.upTo (tr.time i)).projAC.CallAt p i ellp := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt_of_le _ le_rfl).mpr hci
  obtain ⟨hPhi, hPhiU₀⟩ := SA.frameIn_of_callAt hrp hpi hci'
  have hPhiU : ellp.frame.tree ⊆ tr.HonestBlocksAt H :=
    hPhiU₀.trans (RunTrace.honestBlocks_upTo_subset hp.run.time_mono hi0)
  obtain ⟨hst, hsQ⟩ := Compose.acProposal_start_anc_head hPhi hd
  have hQt : d.head ∈ ellp.frame.tree := by
    rcases eq_or_ne d.start d.head with he | he
    · exact he ▸ hst
    · exact (Anc.mem hsQ he).2
  have hslot : sp.slot (tr.time i) = s + 1 := by
    rw [hti]; simpa using (SA.slot_arithmetic sp (s + 1)).1 0 (by omega)
  intro y j
  induction j using Nat.strong_induction_on generalizing y with
  | _ j ih =>
    intro e hy hv hes hjb
    obtain ⟨elly, hcy, hey⟩ := hv
    have hcy : SA.CastAt tr.projAC y j elly e := ⟨hcy, hey⟩
    have hE : ∀ x j' e', x ∈ H (tr.time j') → j' < j → SA.VoteAt tr.projAC x j' e' →
        e'.msg.slot = s + 1 → e'.msg.head = P.root :=
      fun x j' e' hx hj' hv' hs' => ih j' hj' x e' hx hv' hs'
        ((hp.run.time_mono hj'.le).trans hjb)
    have hj0 := hp.run.time_nonneg j
    have hry := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time j))
      (tr.upTo (tr.time j)) proposer (hp.run.upTo hj0) (hp.noColl.upTo _)).localRun
    have hcy' : SA.CastAt (tr.upTo (tr.time j)).projAC y j elly e := by
      rw [RunTrace.upTo_projAC]
      exact SA.upTo_castAt.mpr ⟨le_rfl, hcy⟩
    obtain ⟨hPsi, hPsiU₀⟩ := SA.frameIn_of_callAt hry hy hcy'.1
    have hPsiU : elly.frame.tree ⊆ tr.HonestBlocksAt H :=
      hPsiU₀.trans (RunTrace.honestBlocks_upTo_subset hp.run.time_mono hj0)
    have hjt : sp.ts (s + 1 : Nat) ≤ tr.time j := by
      apply (SA.ts_le_iff_le_slot sp hj0 _).2
      have := (SA.castAt_spec hry hy hcy').2.1
      rw [hes] at this
      exact_mod_cast this.le
    have hgj := hgu.trans hjt
    have hroot := hp.reset_vote_root_below_proposal_at hc hpH hactual hPs hR hci hcall hd hti hib
      hPQ hy hcy hes hjb
    have hPy := hp.reset_proposal_frame_at hc hpH hdesignated hactual hPs (by omega) hy hcy hes
      hjb hgj (hjoin.trans hjt) ((hPsi.F_anc_fcRoot.mono hPsiU).trans hroot)
    have hPv := hp.reset_proposal_viable_at hc hpH hactual hPs hR hci hcall hd hti hib hPQ
      hy hcy hes hjb hPy
    obtain ⟨hstep, hP₀⟩ := hp.reset_stop_at_parent_at hc hpH hdesignated hactual hPs hR
      hci hcall hd hti hpay hPQ hy hcy hes hib hjb hPv hg (hti ▸ hgu) hgj
      (hti ▸ hjoin) (hjoin.trans hjt) hQt (hviab _ hDQ .refl)
    obtain ⟨X, hXc, haX, hXend⟩ := hvot y j elly e hy hcy hes hjb hE
    have hspec := SA.castAt_head_of_viable hry hy hcy' (hes ▸ ⟨P, hPv⟩)
    rw [hes] at hspec
    exact hspec.trans (congrArg (·.root) (voter_head_eq_proposal hPhi hPsi hd hslot hsD hXc haX
      hXend hPv hstep hP₀ fun B C hXB hDB hBQ hne hCQ hC => hp.reset_suffix_best_at hc hpH
        hdesignated hactual hPs hci hcall hd hti hpay hPQ hy hcy hes hib hjb hPv hg (hti ▸ hgu)
        hgj (hti ▸ hjoin) (hjoin.trans hjt) hQt hBQ hne (hviab _ hDB hBQ) hCQ
        ((haX.mono hPsiU).trans (hXB.mono hPhiU)) hC))

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end

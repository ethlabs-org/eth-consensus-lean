module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PrefixBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Restart
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.SlowVotes
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.FastVotes
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.OperationalReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Ancestry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Confirmed
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Update
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HalfCommittee

public section

/-! # The next result above a clean optimistic source, under growing faults

The next optimistic result above the floor under growing faults: a clean optimistic source, written
by a node honest at its write, above the finalized block of the next update of a node honest at
that update, is extended by its result.

The update side is static: it is read on the healthy AC base of the nodes honest at the update,
on the prefix through it (`healthy_base_of_reset_catch_before_at`), and the honest majority is
counted there over the slot committee. Every member of the slot committee honest at the update is
honest at the slot's vote deadline, so it votes (`honest_votes_in_slot_at`); its vote extends the
source by the source's retention (`fast_source_votes_before_at`), and it is received and resolved in
time. -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}
variable {hold : Time}

/-- A clean optimistic source above the next update's finalized block is extended by that
update's result. -/
theorem optimistic_next_result_of_floor_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x y : Fin sp.n} {r s j : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (AC.Vote sp.n)} (hx : x ∈ H (tr.time r)) (hy : y ∈ H (tr.time j))
    (hop : AC.OptimisticLockAt tr.projAC x r s B CV)
    (hs : cleanLabel sp a + 2 * sp.k + 1 ≤ s) (hrb : tr.time r ≤ b)
    {ell : ACLabel (goldilocksNode sp ro)} (hu : AC.UpdateAt tr.projAC y j (s + 1) ell)
    (hjb : tr.time j ≤ b) (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts (s + 1 : Nat))
    (hR : drainTime sp a ≤ sp.ts (s + 1 + 1 : Nat))
    (hFB : Anc (tr.HonestBlocksAt H) ell.frame.F B) :
    ∃ D DV, AC.ResultAt tr.projAC y j (s + 1) D DV ∧ Anc (tr.HonestBlocksAt H) B D := by
  have hm := hp.run.time_mono
  have hd := sp.toParams.hΔ
  have hj0 := hp.run.time_nonneg j
  have htime : tr.time j = sp.ts (s + 1 : Nat) + 6 * sp.Δ := hu.2.2.1
  have hS := healthy_base_of_reset_catch_before_at hp hj0 hjb
  have hr := hS.run.localRun
  have hU := hr.coherent
  have hUc := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  have hsub := RunTrace.honestBlocks_upTo_subset hm (H := H) hj0
  have hu' : AC.UpdateAt (tr.projAC.upTo (tr.time j)) y j (s + 1) ell :=
    (AC.upTo_updateAt hm).mpr ⟨le_rfl, hu⟩
  have hst : (tr.projAC.upTo (tr.time j)).state y j = tr.projAC.state y j :=
    Trace.upTo_state _ y fun _ hq => hm hq.le
  have hrs : ∀ k ≤ j, ACTrace.RestartAt (tr.projAC.upTo (tr.time j)) y k →
      tr.time k < sp.ts (s + 1 : Nat) := by
    intro k _ hk
    obtain ⟨hkD, hk⟩ := (ACTrace.upTo_restartAt (A := AC.goldilocksAC sp _ ro)).mp hk
    have hh := restart_before_unanimous_slot_at hp hR (hp.run.antitone hkD hy)
      (Compose.projAC_restartAt.mp hk) (hkD.trans hjb)
    exact hh.trans_lt ((AC.ts_lt_iff sp).mpr (by clear * -; omega))
  -- every slot-`s + 1` vote of a node honest at the update extends the source, on the prefix
  have hext : ∀ z ∈ H (tr.time j), ∀ q e, AC.VoteAt (tr.projAC.upTo (tr.time j)) z q e →
      e.msg.slot = s + 1 → AC.VoteExtends ((tr.upTo (tr.time j)).HonestBlocks (H (tr.time j)))
        e.msg B := by
    rintro z hz q e hv hes
    obtain ⟨hqD, ellq, hcast⟩ := AC.upTo_voteAt.mp hv
    have hzq : z ∈ H (tr.time q) := hp.run.antitone hqD hz
    obtain ⟨H', hH', hH'r, hBH'⟩ := hp.fast_source_votes_before_at hx (Or.inr hop)
      (by have := sp.two_le_k; clear * - hs this; omega) hrb q (hqD.trans hjb) z hzq ellq e
      hcast (by clear * - hes; omega)
    have hc' : AC.CastAt (tr.projAC.upTo (tr.time j)) z q ellq e :=
      AC.upTo_castAt.mpr ⟨hqD, hcast⟩
    obtain ⟨⟨Hd, hHd, hHdr, _⟩, _⟩ := Compose.cast_head_fcRoot hr hS.run.vstart hz hc'
    have hHdU := (AC.frameIn_of_callAt hr hz hc'.1).2 hHd
    obtain rfl : H' = Hd := hUc.1 hH' (hsub hHdU) (hH'r.trans hHdr.symm)
    exact ⟨H', hHdU, hH'r, RunTrace.anc_upTo_of_right hp.run.toLocalRun hp.noColl hj0 hHdU hBH'⟩
  -- these votes are received and resolved by the update
  have hPhi := (AC.frameIn_of_callAt hr hy hu'.1).1
  have receipt : ∀ z ∈ H (tr.time j), ∀ q e, AC.VoteAt (tr.projAC.upTo (tr.time j)) z q e →
      e.msg.slot = s + 1 → e.msg ∈ (tr.projAC.state y j).pool (s + 1) ∧
        AC.resolutionTime (tr.projAC.state y j) ell.frame e.msg <
          AC.ETime.of (sp.ts (s + 1 : Nat) + 2 * sp.Δ) := by
    intro z hz q e hv hes
    obtain ⟨D, hD, hDr, hBD⟩ := hext z hz q e hv hes
    obtain ⟨E, hE, hEr, hEu, hmem, hvs, hbs⟩ := AC.late_vote_held_of_frame_before hS
      hy hu'.1 hgu (by change _ ≤ tr.time j; rw [htime]; linarith) le_rfl
      (fun k hkj t _ => Compose.ac_deadline_le_of_restarts
        (fun k' hk' hk => (hrs k' (hk'.trans hkj) hk).le) t) hrs hz hv hes
      (fun E hEU hEr => by
        rw [hU.1 hEU hD (hEr.trans hDr.symm)]
        exact (RunTrace.anc_upTo_of_right hp.run.toLocalRun hp.noColl hj0 hD
          (hFB.trans (hBD.mono hsub))))
    rw [hst] at hmem hvs hbs
    exact ⟨hmem, AC.resolutionTime_lt_of hPhi hE hEr (hes ▸ hEu) hvs hbs⟩
  have hres : ∀ v ∈ ((tr.projAC.upTo (tr.time j)).state y j).pool (s + 1),
      v.val ∈ H (tr.time j) →
      AC.resolutionTime ((tr.projAC.upTo (tr.time j)).state y j) ell.frame v <
        AC.ETime.of (sp.ts (s + 1 : Nat) + 2 * sp.Δ) := by
    intro v hv hvH
    obtain ⟨q, _, e, he, rfl⟩ := hS.run.honest.pool_vote y hy j (s + 1) v hv hvH
    rw [hst]
    exact (receipt _ hvH q e he (AC.state_pool_slotU sp hr.toU hS.run.vstart hy j (s + 1) _ hv)).2
  -- every honest member of the slot-`s + 1` committee votes in it: a majority in the pool
  have hdl : sp.ts (s + 1 : Nat) + sp.Δ ≤ tr.time j := by rw [htime]; linarith
  have hall := honest_votes_in_slot_at hp hgu hR (hdl.trans hjb)
  have hH : (Generic.dictOfTime sp cm).committee (s + 1) ∩ H (tr.time j) ⊆
      {v | v ∈ H (tr.time j) ∧ ∃ vote ∈ ((tr.projAC.upTo (tr.time j)).state y j).pool
        (s + 1), vote.val = v} := by
    rintro z ⟨hzK, hz⟩
    obtain ⟨q, e, ⟨ellq, hcast⟩, hes, hq⟩ := hall z (hp.run.antitone hdl hz) hzK
    have hv : AC.VoteAt (tr.projAC.upTo (tr.time j)) z q e :=
      AC.upTo_voteAt.mpr ⟨hq.trans hdl, ellq, hcast⟩
    refine ⟨hz, e.msg, ?_,
      (AC.castAt_specU hr.toU hz (AC.upTo_castAt.mpr ⟨hq.trans hdl, hcast⟩)).1⟩
    rw [hst]
    exact (receipt z hz q e hv hes).1
  have hcount := Set.ncard_le_ncard hH
  have hf := hp.committee_cs2_at (s := s + 1) (by linarith) (by linarith) hj0 hjb
  have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard
    ((Generic.dictOfTime sp cm).committee (s + 1)) (H (tr.time j)) (Set.toFinite _)
  rw [hp.committeeFacts.hsize, Set.sdiff_eq_compl_inter, Set.inter_comm (H (tr.time j))ᶜ]
    at hsplit
  obtain ⟨D, hconf, hBD, _⟩ := AC.update_extends_of_resolved_votes hS.run _
    (fun v hv => hS.hP.1 y hy j (s + 1) v hv) (hS.cs2 (s + 1) (by linarith) (by linarith))
    hext hy hu' (by omega) hres
  rw [hst] at hconf
  exact ⟨D, _, ⟨ell, hu, hconf, rfl⟩, hBD.mono hsub⟩

end Consensus.Goldilocks.Healing.Growing

end

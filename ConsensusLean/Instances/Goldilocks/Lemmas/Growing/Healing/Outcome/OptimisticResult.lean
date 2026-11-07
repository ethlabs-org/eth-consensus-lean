module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.Pending
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.OperationalReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Ancestry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Confirmed
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Update
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The next result above a clean optimistic source, under growing faults

The growing form of `Healing.optimistic_next_result_of_floor`: a clean optimistic source, written
by a node honest at its write, above the finalized block of the next update of a node honest at
that update, is extended by its result.

The update side is static: it is read on the healthy AC base of the nodes honest at the update,
on the prefix through it (`healthy_base_of_reset_catch_before_at`), and the honest majority is
counted there. Every node honest at the update is honest at the slot's vote deadline, so it votes
(`honest_votes_in_slot_at`); its vote extends the source by the source's retention
(`fast_source_votes_before_at`), and it is received and resolved in time. -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- A clean optimistic source above the next update's finalized block is extended by that
update's result. -/
theorem optimistic_next_result_of_floor_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} {r s j : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (SA.Vote sp.n)} (hx : x ∈ H (tr.time r)) (hy : y ∈ H (tr.time j))
    (hop : SA.OptimisticLockAt tr.projAC x r s B CV)
    (hs : cleanLabel sp a + 2 * sp.k + 1 ≤ s) (hrb : tr.time r ≤ b)
    {ell : ACLabel (goldilocksNode sp ro)} (hu : SA.UpdateAt tr.projAC y j (s + 1) ell)
    (hjb : tr.time j ≤ b) (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts (s + 1 : Nat))
    (hR : drainTime sp a ≤ sp.ts (s + 1 + 1 : Nat))
    (hFB : Anc (tr.HonestBlocksAt H) ell.frame.F B) :
    ∃ D DV, SA.ResultAt tr.projAC y j (s + 1) D DV ∧ Anc (tr.HonestBlocksAt H) B D := by
  have hm := hp.run.time_mono
  have hd := sp.toParams.hΔ
  have hj0 := hp.run.time_nonneg j
  have htime : tr.time j = sp.ts (s + 1 : Nat) + 6 * sp.Δ := hu.2.2.1
  have hS := healthy_base_of_reset_catch_before_at hp hc hj0 hjb
  have hr := hS.run.localRun
  have hU := hr.coherent
  have hUc := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  have hsub := RunTrace.honestBlocks_upTo_subset hm (H := H) hj0
  have hu' : SA.UpdateAt (tr.projAC.upTo (tr.time j)) y j (s + 1) ell :=
    (SA.upTo_updateAt hm).mpr ⟨le_rfl, hu⟩
  have hst : (tr.projAC.upTo (tr.time j)).state y j = tr.projAC.state y j :=
    Trace.upTo_state _ y fun _ hq => hm hq.le
  have hrs : ∀ k ≤ j, ACTrace.RestartAt (tr.projAC.upTo (tr.time j)) y k →
      tr.time k < sp.ts (s + 1 : Nat) := by
    intro k _ hk
    obtain ⟨hkD, hk⟩ := (ACTrace.upTo_restartAt (A := SA.goldilocksSA sp _ ro)).mp hk
    have hh := restart_before_unanimous_slot_at hp hR (hp.run.antitone hkD hy)
      (Compose.projAC_restartAt.mp hk) (hkD.trans hjb)
    exact hh.trans_lt ((SA.ts_lt_iff sp).mpr (by clear * -; omega))
  -- every slot-`s + 1` vote of a node honest at the update extends the source, on the prefix
  have hext : ∀ z ∈ H (tr.time j), ∀ q e, SA.VoteAt (tr.projAC.upTo (tr.time j)) z q e →
      e.msg.slot = s + 1 → SA.VoteExtends ((tr.upTo (tr.time j)).HonestBlocks (H (tr.time j)))
        e.msg B := by
    rintro z hz q e hv hes
    obtain ⟨hqD, ellq, hcast⟩ := SA.upTo_voteAt.mp hv
    have hzq : z ∈ H (tr.time q) := hp.run.antitone hqD hz
    obtain ⟨H', hH', hH'r, hBH'⟩ := hp.fast_source_votes_before_at hc hx (Or.inr hop)
      (by have := sp.two_le_k; clear * - hs this; omega) hrb q (hqD.trans hjb) z hzq ellq e
      hcast (by clear * - hes; omega)
    have hc' : SA.CastAt (tr.projAC.upTo (tr.time j)) z q ellq e :=
      SA.upTo_castAt.mpr ⟨hqD, hcast⟩
    obtain ⟨⟨Hd, hHd, hHdr, _⟩, _⟩ := Compose.cast_head_fcRoot hr hz hc'
    have hHdU := (SA.frameIn_of_callAt hr hz hc'.1).2 hHd
    obtain rfl : H' = Hd := hUc.1 hH' (hsub hHdU) (hH'r.trans hHdr.symm)
    exact ⟨H', hHdU, hH'r, RunTrace.anc_upTo_of_right hp.run.toLocalRun hp.noColl hj0 hHdU hBH'⟩
  -- these votes are received and resolved by the update
  have hPhi := (SA.frameIn_of_callAt hr hy hu'.1).1
  have receipt : ∀ z ∈ H (tr.time j), ∀ q e, SA.VoteAt (tr.projAC.upTo (tr.time j)) z q e →
      e.msg.slot = s + 1 → e.msg ∈ (tr.projAC.state y j).pool (s + 1) ∧
        SA.resolutionTime (tr.projAC.state y j) ell.frame e.msg <
          SA.ETime.of (sp.ts (s + 1 : Nat) + 2 * sp.Δ) := by
    intro z hz q e hv hes
    obtain ⟨D, hD, hDr, hBD⟩ := hext z hz q e hv hes
    obtain ⟨E, hE, hEr, hEu, hmem, hvs, hbs⟩ := SA.late_vote_held_of_frame_before hS
      hy hu'.1 hgu (by change _ ≤ tr.time j; rw [htime]; linarith) le_rfl
      (fun k hkj t _ => Compose.ac_deadline_le_of_restarts
        (fun k' hk' hk => (hrs k' (hk'.trans hkj) hk).le) t) hrs hz hv hes
      (fun E hEU hEr => by
        rw [hU.1 hEU hD (hEr.trans hDr.symm)]
        exact (RunTrace.anc_upTo_of_right hp.run.toLocalRun hp.noColl hj0 hD
          (hFB.trans (hBD.mono hsub))))
    rw [hst] at hmem hvs hbs
    exact ⟨hmem, SA.resolutionTime_lt_of hPhi hE hEr (hes ▸ hEu) hvs hbs⟩
  have hres : ∀ v ∈ ((tr.projAC.upTo (tr.time j)).state y j).pool (s + 1),
      v.val ∈ H (tr.time j) →
      SA.resolutionTime ((tr.projAC.upTo (tr.time j)).state y j) ell.frame v <
        SA.ETime.of (sp.ts (s + 1 : Nat) + 2 * sp.Δ) := by
    intro v hv hvH
    obtain ⟨q, _, e, he, rfl⟩ := hS.run.honest.pool_vote y hy j (s + 1) v hv hvH
    rw [hst]
    exact (receipt _ hvH q e he (SA.state_pool_slot sp hr hy j (s + 1) _ hv)).2
  -- every node honest at the update votes in slot `s + 1`: a majority in the pool
  have hdl : sp.ts (s + 1 : Nat) + sp.Δ ≤ tr.time j := by rw [htime]; linarith
  have hall := honest_votes_in_slot_at hp hc hgu hR (hdl.trans hjb)
  have hH : H (tr.time j) ⊆ {v | v ∈ H (tr.time j) ∧
      ∃ vote ∈ ((tr.projAC.upTo (tr.time j)).state y j).pool (s + 1), vote.val = v} := by
    intro z hz
    obtain ⟨q, e, ⟨ellq, hcast⟩, hes, hq⟩ := hall z (hp.run.antitone hdl hz)
    have hv : SA.VoteAt (tr.projAC.upTo (tr.time j)) z q e :=
      SA.upTo_voteAt.mpr ⟨hq.trans hdl, ellq, hcast⟩
    refine ⟨hz, e.msg, ?_,
      (SA.castAt_spec hr hz (SA.upTo_castAt.mpr ⟨hq.trans hdl, hcast⟩)).1⟩
    rw [hst]
    exact (receipt z hz q e hv hes).1
  have hcount := Set.ncard_le_ncard hH
  have hsum : (H (tr.time j)).ncard + (H (tr.time j))ᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hf := hp.faults _ hj0 hjb
  have hn : 0 < sp.n := sp.toParams.hn
  obtain ⟨D, hconf, hBD, _⟩ := SA.update_extends_of_resolved_votes hS.run
    (by omega) hext hy hu' (by omega) hres
  rw [hst] at hconf
  exact ⟨D, _, ⟨ell, hu, hconf, rfl⟩, hBD.mono hsub⟩

end Consensus.Goldilocks.Healing.Growing

end

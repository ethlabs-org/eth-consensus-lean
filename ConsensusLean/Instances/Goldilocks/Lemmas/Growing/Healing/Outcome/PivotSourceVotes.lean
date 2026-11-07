module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Floor
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ProposalSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.OldSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PrefixBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Restart
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.SlowVotes
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.FastVotes
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.PivotRun
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Proposal start support at independently honest cuts

Local lock provenance is read on the proposer's retained prefix. Source-vote
retention and historical origin comparisons retain their own writing cuts.
-/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- The proposal root is genesis or below a bounded pre-slot historical origin. -/
theorem reset_proposal_root_source_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {p : Fin sp.n} {u i : Nat} (hpH : p ∈ H (tr.time i))
    (hR : drainTime sp a ≤ sp.ts u)
    {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b) :
    ell.frame.fcRoot.root = sp.genesisRoot ∨
      ∃ v r l O, HighOrigin tr H g v r l O ∧ tr.time r < sp.ts u ∧ tr.time r ≤ b ∧
        Anc (tr.HonestBlocksAt H) ell.frame.fcRoot O := by
  have ht := hp.run.time_nonneg i
  have hi : ∀ q < i, tr.time q ≤ tr.time i := fun _ hq => hp.run.time_mono hq.le
  have hU := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  have hr := fg_reachable_at hp.run ht hi hpH
  have hsub : (tr.state p i).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ hX => ⟨p, i, tr.time i, ht, hi, hpH, hX⟩
  have hfr := Outcome.frame_of_call hp.run hpH hci
  obtain ⟨hFm, hJm, hFJ, ⟨B, hBm, hBJ, hBhj⟩, hmax, _⟩ :=
    Store.cache_invariants _ _ _ _ hr
  obtain ⟨E, hEm, hEr, hEB, hcase⟩ := Store.J_entry_of_reachable hr hBm
  obtain rfl : E = (tr.state p i).fg.J := hU.1 (hsub hEm) (hsub hJm) (hEr.trans hBJ)
  have hroot : (tr.state p i).fg.fcRoot = (tr.state p i).fg.J ∨
      (tr.state p i).fg.fcRoot = (tr.state p i).fg.F := by
    unfold Store.fcRoot
    split_ifs <;> simp
  rcases hcase with hg | ⟨hJh, hJT⟩
  · left
    rw [hfr]
    rcases hroot with h | h
    · exact congrArg (·.root) (h.trans hg)
    · have hJF := (Store.accepted_tree _ _ _ _ hr).2.2.2 _ hFm
      rw [← hg] at hJF
      have he := Anc.antisymm hU (hFJ.mono hsub) (hJF.mono hsub)
      exact congrArg (·.root) (h.trans (he.trans hg))
  right
  by_cases hh : HZ tr H g + 1 ≤ (tr.state p i).fg.hj
  · obtain ⟨_, _, _, _, v, _, k', hki, _, _, r, hrk, l, O, ho, hJO⟩ :=
      hp.left_entry_origin_at ht hi hpH hib hJm hJT (by omega) hEB
        (by have := Store.hj_lt_h hr hBm; omega)
    have hlu := hp.origin_label_lt_at_proposal_at hpH hci hcall hti hib (by omega : r < i) ho
    obtain ⟨_, _, _, _, hfl, _⟩ := ho.2.2.1
    have hrt := Outcome.fastLock_time_lt_at hp.run hfl hlu (by
      have := hp.run.time_mono (show r ≤ i by omega)
      rw [hti] at this
      have := sp.toParams.hΔ
      linarith)
    refine ⟨v, r, l, O, ho, hrt, (hp.run.time_mono (by omega)).trans hib, ?_⟩
    rw [hfr]
    change Anc _ (tr.state p i).fg.fcRoot O
    rcases hroot with h | h
    · rw [h]; exact hJO
    · rw [h]; exact (hFJ.mono hsub).trans hJO
  obtain ⟨v, r, l, O, ho, hrb, _, hrt⟩ := hp.reset_seed_before_slot_at hR
  have hFO := hp.low_finalized_below_origin_at ht hi hpH hib (by omega) ho hrb
  refine ⟨v, r, l, O, ho, hrt, hrb, ?_⟩
  rw [hfr]
  change Anc _ (tr.state p i).fg.fcRoot O
  unfold Store.fcRoot
  split_ifs with hchoose
  · have hOt : O ∈ ell.frame.tree := by
      rcases hp.proposal_holds_old_at hpH hci hcall hd hti hib ho hrt with h | h
      · exact h
      · rw [hfr] at h
        have := Outcome.high_of_anc_at hp.run hp.noColl ho ht hi hpH hJm
          (h.trans (hFJ.mono hsub))
        omega
    rw [hfr] at hOt
    have hOh := Outcome.high_of_anc_at hp.run hp.noColl ho ht hi hpH hOt.1 .refl
    have hOm := hmax O hOt.1
    have hJO : (tr.state p i).fg.Anc (tr.state p i).fg.J O := by
      by_contra hn
      exact hchoose.2 ⟨hchoose.1, O, hOt.1, hOt.2, by omega, hn⟩
    exact hJO.mono hsub
  · exact hFO

/-- Actual bounded casts extend the start of a drained operational proposal. -/
theorem proposal_start_supported_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {u i : Nat} (hpH : p ∈ H (tr.time i)) (hR : drainTime sp a ≤ sp.ts u)
    {ellp : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp) (hcall : ellp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {elly : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j elly e) (hes : e.msg.slot = u) (hjb : tr.time j ≤ b) :
    Anc (tr.HonestBlocksAt H) d.start
      (SA.getHead sp e.readPoint elly.frame (tr.time j)
        (elly.frame.viableTree (SA.voteDomain sp e.readPoint elly.frame u))
        (SA.mergedVoteView sp e.readPoint elly.frame u) ((u : Int) - 1)) := by
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := hac.localRun.upTo (hp.run.time_nonneg i)
  have hrj := hac.localRun.upTo (hp.run.time_nonneg j)
  have hPhi := Outcome.frame_realized hp.run hpH hci
  have hPhiU := Outcome.frame_tree_subset hp.run hpH hci
  have hPsi := Outcome.frame_realized hp.run hy hcy.1
  have hPsiU := Outcome.frame_tree_subset hp.run hy hcy.1
  have hU := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  have hstate : (tr.projAC.upTo (tr.time i)).state p i = tr.projAC.state p i :=
    Trace.upTo_state tr.projAC p fun _ hq => hp.run.time_mono hq.le
  have hhead := SA.getHead_mem hPsi
    (T := elly.frame.viableTree (SA.voteDomain sp e.readPoint elly.frame u))
    (fun _ h => SA.voteDomain_subset_tree h.1) e.readPoint (tr.time j)
    (SA.mergedVoteView sp e.readPoint elly.frame u) ((u : Int) - 1)
  have hheadr := (SA.castAt_spec hrj hy ((SA.upTo_castAt).mpr ⟨le_rfl, hcy⟩)).2.2.2
  rw [hes] at hheadr
  have extend : ∀ B, SA.VoteExtends (tr.HonestBlocksAt H) e.msg B →
      Anc (tr.HonestBlocksAt H) B
        (SA.getHead sp e.readPoint elly.frame (tr.time j)
          (elly.frame.viableTree (SA.voteDomain sp e.readPoint elly.frame u))
          (SA.mergedVoteView sp e.readPoint elly.frame u) ((u : Int) - 1)) := by
    rintro B ⟨W, hW, hWr, hBW⟩
    obtain rfl := hU.1 hW (hPsiU hhead) (hWr.trans hheadr)
    exact hBW
  obtain ⟨A₁, hA₁, hstart, _⟩ := Compose.acProposal_walk hd
  rw [hstart]
  rcases Compose.anchor_mem ellp.frame A₁ (tr.time i) with hlock | hroot
  swap
  · rw [Set.mem_singleton_iff.1 hroot]
    rcases hp.reset_proposal_root_source_at hpH hR hci hcall hd hti hib with
      hg | ⟨x, r, l, O, ho, hOld, hrb, hfO⟩
    · exact ProposalImpl.genesis_root_anc_at hp.run hp.noColl (hPhiU hPhi.fcRoot_mem) hg
        (hPsiU hhead)
    apply hfO.trans (extend O ?_)
    have hri : r < i := by
      by_contra hn
      have ht := hp.run.time_mono (Nat.le_of_not_gt hn)
      rw [hti] at ht
      exact (not_lt_of_ge ht) hOld
    have hlu := hp.origin_label_lt_at_proposal_at hpH hci hcall hti hib hri ho
    exact hp.high_origin_votes_before_at j hjb x r l O ho hrb y elly e hy hcy (by omega)
  obtain ⟨hL, l', ⟨l, hl, B, hB, hBr, hlive, rfl⟩, hlL⟩ := hlock
  have heq := hPhi.coherent.1 hL (SA.viableAncestor_anc hPhi hB).1 hlL.symm
  rw [heq]
  rw [hA₁] at hl
  replace hlive : sp.slot (tr.time i) ≤ l.slot + sp.k :=
    hlive.trans (((SA.locksWF_state hr hpH i).unlock _ _ _ _).cap (hstate ▸ hl))
  obtain ⟨l₁, hl₁, hs, _, _, B₁, hB₁, hB₁r, B', hB', hB'r, hBB₁⟩ :=
    ((SA.locks_move_back sp) _ ellp.frame _ (tr.time i) hPhi).2.2 _ _ l hl
  obtain rfl : B' = B := hPhi.coherent.1 hB' hB (hB'r.trans hBr.symm)
  have hlo : cleanLabel sp a + sp.k + 2 ≤ l₁.slot := by
    rw [drainTime_eq] at hR
    have h := (SA.ts_le_iff sp).mp hR
    have hslot : sp.slot (tr.time i) = u := by
      rw [hti]
      exact SA.slot_of_mem sp u le_rfl (by
        have hΔ := sp.toParams.hΔ
        simp only [SA.SAParams.ts]; push_cast; linarith only [hΔ])
    rw [hslot] at hlive
    rw [cleanLabel_eq]
    omega
  obtain ⟨r, hri, D, horig, L, hLU, hLr, hLD⟩ :
      ∃ r < i, ∃ D,
        ((∃ CV, SA.FastLockAt tr.projAC p r l₁.slot D CV) ∨
          SA.SlowLockAt tr.projAC p r l₁.slot D) ∧
        ∃ L ∈ tr.HonestBlocksAt H, L.root = l₁.block ∧ Anc (tr.HonestBlocksAt H) L D := by
    cases hf : l₁.fast with
    | false =>
      obtain ⟨r, hri, D, hsl, hL⟩ := SA.slow_lock_provenance hr hpH i l₁ (hstate ▸ hl₁) hf
      obtain ⟨ell, C, hu, hconf, hdeep⟩ := hsl
      have hs₀ := Trace.upTo_state tr.projAC p (fun _ hq =>
        (hp.run.time_mono hq.le).trans (hp.run.time_mono hri.le))
      rw [hs₀] at hconf hdeep
      exact ⟨r, hri, D, Or.inr ⟨ell, C,
        ((SA.upTo_updateAt hp.run.time_mono).mp hu).2, hconf, hdeep⟩, hL⟩
    | true =>
      obtain ⟨r, hri, D, CV, hfl, hL⟩ := SA.fast_lock_provenance hr hpH i l₁ (hstate ▸ hl₁) hf
      exact ⟨r, hri, D, Or.inl ⟨CV, ((SA.upTo_fastLockAt hp.run.time_mono).mp hfl).2⟩, hL⟩
  obtain rfl : L = B₁ := hU.1 hLU (hPhiU hB₁) (hLr.trans hB₁r.symm)
  have hlt : l₁.slot < u := by
    obtain ⟨r', hri', D', hw, _⟩ := SA.lock_provenance hr hpH i l₁ (hstate ▸ hl₁)
    have hrt : tr.time r' ≤ sp.ts u := hti ▸ hp.run.time_mono hri'.le
    rcases hw with ⟨CV, hop⟩ | ⟨ell, hupd⟩
    · obtain ⟨_, _, _, hsl, _⟩ := id hop
      have hts : sp.ts l₁.slot ≤ tr.time r' :=
        (SA.ts_le_iff_le_slot sp (hr.time_nonneg r') l₁.slot).mpr (by omega)
      have hle := (SA.ts_le_iff sp).mp (hts.trans hrt)
      have hf : 2 * (H (tr.time i))ᶜ.ncard < sp.n := by
        have h3 := hp.faults _ (hp.run.time_nonneg i) hib
        have hn := sp.toParams.hn
        change 0 < sp.n at hn
        omega
      have hcp : (tr.upTo (tr.time i)).projAC.CallAt p i ellp := by
        rw [RunTrace.upTo_projAC]
        exact (Trace.upTo_callAt _).mpr ⟨le_rfl, hci⟩
      have hop' := hop
      rw [← RunTrace.upTo_projAC] at hop'
      have hne : l₁.slot ≠ u := fun he =>
        Healing.proposal_no_optimistic_of_run (hp.run.upTo (hp.run.time_nonneg i))
          (hp.noColl.upTo _) hf hpH hcp hcall hti p hpH r' hri' D' CV (he ▸ hop')
      omega
    · have ht : tr.time r' = sp.ts l₁.slot + 6 * sp.Δ := hupd.2.2.1
      have hΔ := sp.toParams.hΔ
      have ht' : sp.ts l₁.slot < sp.ts u := by linarith only [hrt, ht, hΔ]
      exact_mod_cast (SA.ts_lt_iff sp).mp ht'
  apply (Anc.mono hPhiU ((SA.anc_viableAncestor ellp.frame B').trans hBB₁)).trans
    (hLD.trans (extend D ?_))
  have hpr := hp.run.antitone (hp.run.time_mono hri.le) hpH
  rcases horig with ⟨CV, hf⟩ | hslow
  · exact hp.fast_source_votes_before_at hc hpr hf hlo ((hp.run.time_mono hri.le).trans hib)
      j hjb y hy elly e hcy (by omega)
  · exact hp.slow_source_votes_before_at hc hpr hslow hlo ((hp.run.time_mono hri.le).trans hib)
      j hjb y hy elly e hcy (by omega)

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end

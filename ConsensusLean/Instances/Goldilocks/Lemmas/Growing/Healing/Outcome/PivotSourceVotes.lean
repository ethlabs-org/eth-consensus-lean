module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Floor
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ProposalSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.OldSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PrefixBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Restart
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.RootFloor
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.ProposalStart
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.ProposalEntry
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.SlowVotes
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.FastVotes
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.PivotRun
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HalfCommittee
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetSource
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Committee

public section

/-! # Proposal start support at independently honest cuts

Local lock provenance is read on the proposer's retained prefix. Source-vote
retention and historical origin comparisons retain their own writing cuts.
-/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}
variable {hold : Time}

/-- The proposal root is genesis, below a bounded pre-slot historical origin, or, under the
high-source cover, below a healed member of a label strictly below the proposal slot. -/
theorem reset_proposal_root_source_or_healed_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {p : Fin sp.n} {u i : Nat} (hpH : p ∈ H (tr.time i))
    (hR : drainTime sp a ≤ sp.ts u)
    {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (AC.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b) :
    ell.frame.fcRoot.root = sp.genesisRoot ∨
      (∃ v r l O, HighOrigin tr H g v r l O ∧ tr.time r < sp.ts u ∧ tr.time r ≤ b ∧
        Anc (tr.HonestBlocksAt H) ell.frame.fcRoot O) ∨
      (HighSourceCover tr H g a b ∧ ∃ C s, HealedMemberBefore tr H g a b C s i ∧ s < u ∧
        Anc (tr.HonestBlocksAt H) ell.frame.fcRoot C) := by
  have ht := hp.run.time_nonneg i
  have hi : ∀ q < i, tr.time q ≤ tr.time i := fun _ hq => hp.run.time_mono hq.le
  have hfr := Outcome.frame_of_call hp.run hpH hci
  rw [hfr]
  have hreach := fg_reachable_at hp.run ht hi hpH
  rcases fcRoot_genesis_or_below_source hreach
    (Compose.Growing.honest_blocks_coherent hp.run hp.noColl)
    (fun _ hX => ⟨p, i, tr.time i, ht, hi, hpH, hX⟩)
    (fun O =>
      (∃ v r l, HighOrigin tr H g v r l O ∧ tr.time r < sp.ts u ∧ tr.time r ≤ b) ∨
      (HighSourceCover tr H g a b ∧ ∃ s, HealedMemberBefore tr H g a b O s i ∧ s < u ∧
        ∃ E ∈ (tr.state p i).fg.tree, HZ tr H g + 1 ≤ ((tr.state p i).fg.σ E.root).h ∧
          Anc (tr.HonestBlocksAt H) E O))
    (fun E hE C hET hEh hEC hlt => by
      rcases hp.proposal_entry_below_old_or_healed_at hpH hci hcall hti hib hE hET hEh hEC hlt
        with ⟨O, hO, hEO⟩ | ⟨hc, M, s, hM, hsu, hEM⟩
      · exact ⟨O, Or.inl hO, hEO⟩
      · exact ⟨M, Or.inr ⟨hc, s, hM, hsu, E, hE, hEh, hEM⟩, hEM⟩)
    (fun O hO W hW hOW => by
      rcases hO with ⟨_, _, _, ho, _⟩ | ⟨_, s, _, _, E, hE, hEh, hEO⟩
      · exact Outcome.high_of_anc_at hp.run hp.noColl ho ht hi hpH hW hOW
      · exact hEh.trans (Healing.h_le_of_store_anc hreach
          (store_anc_of_honest_anc_at hp.run hp.noColl ht hi hpH (hEO.trans hOW) hW)))
    (fun hlow => by
      obtain ⟨v, r, l, O, ho, hrb, _, hrt⟩ := hp.reset_seed_before_slot_at hR
      have hheld := hp.proposal_holds_old_at hpH hci hcall hd hti hib ho hrt
      rw [hfr] at hheld
      exact ⟨O, Or.inl ⟨v, r, l, ho, hrt, hrb⟩,
        hp.low_finalized_below_origin_at ht hi hpH hib hlow ho hrb, hheld⟩) with
    hg | ⟨O, hO, hfO⟩
  · exact Or.inl (congrArg Block.root hg)
  · rcases hO with ⟨v, r, l, ho, hrt, hrb⟩ | ⟨hc, s, hM, hsu, -⟩
    · exact Or.inr (Or.inl ⟨v, r, l, O, ho, hrt, hrb, hfO⟩)
    · exact Or.inr (Or.inr ⟨hc, O, s, hM, hsu, hfO⟩)

/-- Actual bounded casts extend the start of a drained operational proposal. -/
theorem proposal_start_supported_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {p : Fin sp.n} {u i : Nat} (hpH : p ∈ H (tr.time i)) (hR : drainTime sp a ≤ sp.ts u)
    {ellp : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp) (hcall : ellp.call = .proposal)
    (hd : (AC.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {elly : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hcy : AC.CastAt tr.projAC y j elly e) (hes : e.msg.slot = u) (hjb : tr.time j ≤ b) :
    Anc (tr.HonestBlocksAt H) d.start
      (AC.getHead sp e.readPoint elly.frame (tr.time j)
        (elly.frame.viableTree (AC.voteDomain sp e.readPoint elly.frame u))
        (AC.mergedVoteView sp e.readPoint elly.frame u) ((u : Int) - 1)) := by
  have hac := Compose.Growing.goldilocks_ac_projection_from hp.run hp.noColl
  have hr := hac.localRun.upTo (hp.run.time_nonneg i)
  have hrj := hac.localRun.upTo (hp.run.time_nonneg j)
  have hPhi := Outcome.frame_realized hp.run hpH hci
  have hPhiU := Outcome.frame_tree_subset hp.run hpH hci
  have hPsi := Outcome.frame_realized hp.run hy hcy.1
  have hPsiU := Outcome.frame_tree_subset hp.run hy hcy.1
  have hU := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  have hstate : (tr.projAC.upTo (tr.time i)).state p i = tr.projAC.state p i :=
    Trace.upTo_state tr.projAC p fun _ hq => hp.run.time_mono hq.le
  have hhead := AC.getHead_mem hPsi
    (T := elly.frame.viableTree (AC.voteDomain sp e.readPoint elly.frame u))
    (fun _ h => AC.voteDomain_subset_tree h.1) e.readPoint (tr.time j)
    (AC.mergedVoteView sp e.readPoint elly.frame u) ((u : Int) - 1)
  have hheadr := (AC.castAt_specU hrj.toU hy ((AC.upTo_castAt).mpr ⟨le_rfl, hcy⟩)).2.2.2
  rw [hes] at hheadr
  have extend : ∀ B, AC.VoteExtends (tr.HonestBlocksAt H) e.msg B →
      Anc (tr.HonestBlocksAt H) B
        (AC.getHead sp e.readPoint elly.frame (tr.time j)
          (elly.frame.viableTree (AC.voteDomain sp e.readPoint elly.frame u))
          (AC.mergedVoteView sp e.readPoint elly.frame u) ((u : Int) - 1)) := by
    rintro B ⟨W, hW, hWr, hBW⟩
    obtain rfl := hU.1 hW (hPsiU hhead) (hWr.trans hheadr)
    exact hBW
  rcases proposal_start_root_or_clean_lock hPhi
      (hstate ▸ AC.locksWF_stateU (hr := hr.toU) hac.vstart hpH i) hR hti hd
    with hroot | ⟨l₁, hl₁, hlo, B₁, hB₁, hB₁r, hsB₁⟩
  · rw [hroot]
    rcases hp.reset_proposal_root_source_or_healed_at hpH hR hci hcall hd hti hib with
      hg | ⟨x, r, l, O, ho, hOld, hrb, hfO⟩ | ⟨hc, C, s, hC, hsu, hfC⟩
    · exact ProposalImpl.genesis_root_anc_at hp.run hp.noColl (hPhiU hPhi.fcRoot_mem) hg
        (hPsiU hhead)
    · apply hfO.trans (extend O ?_)
      have hri : r < i :=
        lt_of_not_ge fun h => (hp.run.time_mono h).not_gt (hOld.trans_eq hti.symm)
      have hlu := hp.origin_label_lt_at_proposal_at hpH hci hcall hti hib hri ho
      exact hp.high_origin_votes_before_at j hjb x r l O ho hrb y elly e hy hcy (by omega)
    · refine hfC.trans (extend C (hc.s2 C s hC.healedOrigin y j e
        (Compose.Growing.hVoteAt_iff.2 ⟨hy, elly, hcy⟩) hjb (by omega)))
  obtain ⟨r, hri, D, horig, L, hLU, hLr, hLD⟩ :
      ∃ r < i, ∃ D,
        ((∃ CV, AC.FastLockAt tr.projAC p r l₁.slot D CV) ∨
          AC.SlowLockAt tr.projAC p r l₁.slot D) ∧
        ∃ L ∈ tr.HonestBlocksAt H, L.root = l₁.block ∧ Anc (tr.HonestBlocksAt H) L D := by
    cases hf : l₁.fast with
    | false =>
      obtain ⟨r, hri, D, hsl, hL⟩ := AC.slow_lock_provenance hr hac.vstart hpH i l₁
        (hstate ▸ hl₁) hf
      obtain ⟨ell, C, hu, hconf, hdeep⟩ := hsl
      have hs₀ := Trace.upTo_state tr.projAC p (fun _ hq =>
        (hp.run.time_mono hq.le).trans (hp.run.time_mono hri.le))
      rw [hs₀] at hconf hdeep
      exact ⟨r, hri, D, Or.inr ⟨ell, C,
        ((AC.upTo_updateAt hp.run.time_mono).mp hu).2, hconf, hdeep⟩, hL⟩
    | true =>
      obtain ⟨r, hri, D, CV, hfl, hL⟩ := AC.fast_lock_provenance hr hac.vstart hpH i l₁
        (hstate ▸ hl₁) hf
      exact ⟨r, hri, D, Or.inl ⟨CV, ((AC.upTo_fastLockAt hp.run.time_mono).mp hfl).2⟩, hL⟩
  obtain rfl : L = B₁ := hU.1 hLU (hPhiU hB₁) (hLr.trans hB₁r.symm)
  have hlt : l₁.slot < u := by
    have hret := hp.run.upTo (hp.run.time_nonneg i)
    have hs : (tr.upTo (tr.time i)).projAC.state p i = tr.projAC.state p i := by
      rw [RunTrace.upTo_projAC]; exact hstate
    refine Compose.proposal_locks_slot_of hret (hp.noColl.upTo _) hpH
      (by rw [RunTrace.upTo_projAC]; exact (Trace.upTo_callAt _).mpr ⟨le_rfl, hci⟩) hcall
      (by rw [hs]; exact hd) hti
      (by rw [RunTrace.upTo_projAC]
          exact AC.CommitteePAt.upTo hp.run.time_mono hp.run.antitone hp.committeeFacts.hP _)
      (hp.committee_cs2_at (hp.gbar_le_ts_of_clean_at (by
          rw [Healing.drainTime_eq] at hR
          have := (AC.ts_le_iff sp).1 hR
          rw [Healing.cleanLabel_eq]
          push_cast at this
          omega)) (hti ▸ hib) (hp.run.time_nonneg i) hib) l₁
      (by rw [← Compose.projAC_state hret.toLocalRun hpH i, hs]; exact hl₁)
  apply (Anc.mono hPhiU hsB₁).trans (hLD.trans (extend D ?_))
  have hpr := hp.run.antitone (hp.run.time_mono hri.le) hpH
  rcases horig with ⟨CV, hf⟩ | hslow
  · exact hp.fast_source_votes_before_at hpr hf hlo ((hp.run.time_mono hri.le).trans hib)
      j hjb y hy elly e hcy (by omega)
  · exact hp.slow_source_votes_before_at hpr hslow hlo ((hp.run.time_mono hri.le).trans hib)
      j hjb y hy elly e hcy (by omega)

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end

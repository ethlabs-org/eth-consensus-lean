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
  have hfr := Outcome.frame_of_call hp.run hpH hci
  rw [hfr]
  refine (fcRoot_genesis_or_below_source (fg_reachable_at hp.run ht hi hpH)
    (Compose.Growing.honest_blocks_coherent hp.run hp.noColl)
    (fun _ hX => ⟨p, i, tr.time i, ht, hi, hpH, hX⟩)
    (fun O => ∃ v r l, HighOrigin tr H g v r l O ∧ tr.time r < sp.ts u ∧ tr.time r ≤ b)
    (fun E hE C hET hEh hEC hlt =>
      hp.proposal_entry_below_old_at hpH hci hcall hti hib hE hET hEh hEC hlt)
    (fun O ⟨_, _, _, ho, _⟩ W hW hOW =>
      Outcome.high_of_anc_at hp.run hp.noColl ho ht hi hpH hW hOW) fun hlow => ?_).imp
    (congrArg Block.root) fun ⟨O, ⟨v, r, l, ho, hrt, hrb⟩, hO⟩ => ⟨v, r, l, O, ho, hrt, hrb, hO⟩
  obtain ⟨v, r, l, O, ho, hrb, _, hrt⟩ := hp.reset_seed_before_slot_at hR
  have hheld := hp.proposal_holds_old_at hpH hci hcall hd hti hib ho hrt
  rw [hfr] at hheld
  exact ⟨O, ⟨v, r, l, ho, hrt, hrb⟩, hp.low_finalized_below_origin_at ht hi hpH hib hlow ho hrb,
    hheld⟩

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
  rcases proposal_start_root_or_clean_lock hPhi (hstate ▸ SA.locksWF_state hr hpH i) hR hti hd
    with hroot | ⟨l₁, hl₁, hlo, B₁, hB₁, hB₁r, hsB₁⟩
  · rw [hroot]
    rcases hp.reset_proposal_root_source_at hpH hR hci hcall hd hti hib with
      hg | ⟨x, r, l, O, ho, hOld, hrb, hfO⟩
    · exact ProposalImpl.genesis_root_anc_at hp.run hp.noColl (hPhiU hPhi.fcRoot_mem) hg
        (hPsiU hhead)
    apply hfO.trans (extend O ?_)
    have hri : r < i :=
      lt_of_not_ge fun h => (hp.run.time_mono h).not_gt (hOld.trans_eq hti.symm)
    have hlu := hp.origin_label_lt_at_proposal_at hpH hci hcall hti hib hri ho
    exact hp.high_origin_votes_before_at j hjb x r l O ho hrb y elly e hy hcy (by omega)
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
    have hret := hp.run.upTo (hp.run.time_nonneg i)
    have hs : (tr.upTo (tr.time i)).projAC.state p i = tr.projAC.state p i := by
      rw [RunTrace.upTo_projAC]; exact hstate
    refine Compose.proposal_locks_slot_of hret (hp.noColl.upTo _) ?_ hpH
      (by rw [RunTrace.upTo_projAC]; exact (Trace.upTo_callAt _).mpr ⟨le_rfl, hci⟩) hcall
      (by rw [hs]; exact hd) hti hp.stock l₁
      (by rw [← Compose.projAC_state hret.toLocalRun hpH i, hs]; exact hl₁)
    have h3 := hp.faults _ (hp.run.time_nonneg i) hib
    have hn := sp.toParams.hn
    change 0 < sp.n at hn
    omega
  apply (Anc.mono hPhiU hsB₁).trans (hLD.trans (extend D ?_))
  have hpr := hp.run.antitone (hp.run.time_mono hri.le) hpH
  rcases horig with ⟨CV, hf⟩ | hslow
  · exact hp.fast_source_votes_before_at hc hpr hf hlo ((hp.run.time_mono hri.le).trans hib)
      j hjb y hy elly e hcy (by omega)
  · exact hp.slow_source_votes_before_at hc hpr hslow hlo ((hp.run.time_mono hri.le).trans hib)
      j hjb y hy elly e hcy (by omega)

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end

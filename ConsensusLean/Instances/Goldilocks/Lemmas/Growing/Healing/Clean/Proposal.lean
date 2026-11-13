module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PrefixBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Restart
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.SlowVotes
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.FastVotes
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.Domain
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.Timing
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Ancestry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.PivotRowSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Confirmed
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.BestChild
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Unlock
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Pivot
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.PivotRun
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The clean-source proposal parent, under growing faults

The growing form of `Healing.ResetPremisesUpTo.clean_source_proposal_parent_before`: the finite
predecessor batch makes the proposal of a node honest at its call extend every clean raw source,
written by a node honest at its write, at least two labels earlier.

The proposal side is static: it is the batch proposal on the healthy AC base of the nodes honest
at the proposal call, on the prefix through it (`healthy_base_of_reset_catch_before_at`). Votes,
locks and the proposer's pool are read there. The source enters only through the votes of its
retention (`fast_source_votes_before_at`, `slow_source_votes_before_at`), each by a node honest
at its vote, and through its proposal domain (`clean_source_proposal_domain_before_at`). -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- **The finite predecessor batch extends every clean source at least two labels earlier**,
under growing faults. -/
theorem clean_source_proposal_parent_before_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {x p : Fin sp.n} {r s i u : Nat}
    (hx : x ∈ H (tr.time r)) (hpH : p ∈ H (tr.time i))
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hsource : (∃ CV, SA.FastLockAt tr.projAC x r s B CV) ∨ SA.SlowLockAt tr.projAC x r s B)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hsu : s + 2 ≤ u) (hrb : tr.time r ≤ b)
    (hR : drainTime sp a ≤ sp.ts u) {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b) : Anc (tr.HonestBlocksAt H) B d.head := by
  have hm := hp.run.time_mono
  have hi0 := hp.run.time_nonneg i
  have hS := healthy_base_of_reset_catch_before_at hp hc hi0 hib
  have hr := hS.run.localRun
  have hU := hr.coherent
  have hUc := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  have hsub := RunTrace.honestBlocks_upTo_subset hm (H := H) hi0
  have hΔ := sp.toParams.hΔ
  have hf : 2 * (H (tr.time i))ᶜ.ncard < sp.n := by
    have := hp.faults _ hi0 hib; have := Fin.pos x; omega
  have hst : (tr.projAC.upTo (tr.time i)).state p i = tr.projAC.state p i :=
    Trace.upTo_state _ p fun _ hq => hm hq.le
  have hci' : (tr.projAC.upTo (tr.time i)).CallAt p i ell :=
    (Trace.upTo_callAt_of_le _ le_rfl).mpr hci
  have hd' : (SA.acProposal sp ((tr.projAC.upTo (tr.time i)).state p i) ell.frame
      ((tr.projAC.upTo (tr.time i)).time i)).2 = some (d, pay) := by
    rw [hst]; exact hd
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hpH hci'
  rcases hp.clean_source_proposal_domain_before_at hc hx hpH hsource hs (by omega) hrb hR
      hci hcall hd hti hib with hBF | hV
  · obtain ⟨_, hhead⟩ := Compose.acProposal_start_anc_head hPhi hd
    obtain ⟨A₁, _, hstart, _⟩ := Compose.acProposal_walk hd
    rw [hstart] at hhead
    exact hBF.trans (Anc.mono (fun _ h => hsub (hPhiU h))
      ((SA.fcRoot_anc_getAnchor hPhi A₁ (tr.time i)).trans hhead))
  have hFB := (hPhi.rooted.2 B hV.1).mono hPhiU
  obtain ⟨σ, rfl⟩ : ∃ σ, u = σ + 1 := ⟨u - 1, by clear * - hsu; omega⟩
  have hσ : sp.ts (σ + 1 : Nat) = sp.ts σ + 4 * sp.Δ := SA.ts_succ σ
  have hσD : sp.ts σ + sp.Δ ≤ tr.time i := by rw [hti, hσ]; linarith
  -- the votes of slot `σ` of nodes honest at the call extend the source
  have votes : ∀ z ∈ H (tr.time i), ∀ q e, SA.VoteAt (tr.projAC.upTo (tr.time i)) z q e →
      e.msg.slot = σ → SA.VoteExtends ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)))
        e.msg B := by
    rintro z hz q e hv hslot
    obtain ⟨hqD, ell', hc'⟩ := SA.upTo_voteAt.mp hv
    have hzq : z ∈ H (tr.time q) := hp.run.antitone hqD hz
    have hqb : tr.time q ≤ b := hqD.trans hib
    have hext : SA.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
      rcases hsource with ⟨CV, hfast⟩ | hslow
      · exact hp.fast_source_votes_before_at hc hx hfast hs hrb q hqb z hzq ell' e hc'
          (by clear * - hsu hslot; omega)
      · exact hp.slow_source_votes_before_at hc hx hslow hs hrb q hqb z hzq ell' e hc'
          (by clear * - hsu hslot; omega)
    have hc'' : SA.CastAt (tr.projAC.upTo (tr.time i)) z q ell' e :=
      SA.upTo_castAt.mpr ⟨hqD, hc'⟩
    obtain ⟨⟨Hd, hHd, hHdr, _⟩, _⟩ := Compose.cast_head_fcRoot hr hz hc''
    have hHdU := (SA.frameIn_of_callAt hr hz hc''.1).2 hHd
    obtain ⟨H', hH', hH'r, hBH'⟩ := hext
    obtain rfl : H' = Hd := hUc.1 hH' (hsub hHdU) (hH'r.trans hHdr.symm)
    exact ⟨H', hHdU, hH'r, RunTrace.anc_upTo_of_right hp.run.toLocalRun hp.noColl hi0 hHdU hBH'⟩
  have hcut := hp.clean_window_timing_at hs s (by have := sp.two_le_k; clear * - this; omega)
  have hσg : SA.gbar g + 4 * sp.Δ ≤ sp.ts σ := by
    have hz := Healing.lt_cutZ sp g
    have hle := (SA.ts_le_iff sp).mpr (show (s : Int) ≤ σ by clear * - hsu; omega)
    linarith only [hcut, hz, hle, hΔ]
  have hrestart : ∀ z ∈ H (tr.time i), ∀ q, ACTrace.RestartAt (tr.projAC.upTo (tr.time i)) z q →
      tr.time q ≤ sp.ts ((σ : Int) - 1) := by
    intro z hz q hrest
    obtain ⟨hqD, hrest⟩ := (ACTrace.upTo_restartAt (A := SA.goldilocksSA sp _ ro)).mp hrest
    apply (hp.restart_le_before_at (hp.run.antitone hqD hz) (Compose.projAC_restartAt.mp hrest)
      (hqD.trans hib)).trans
    rw [Healing.cutZ_eq] at hcut
    have := (SA.ts_le_iff sp).mp hcut
    exact (SA.ts_le_iff sp).mpr (by clear * - hsu this; omega)
  have hrs : ∀ q ≤ i, ACTrace.RestartAt (tr.projAC.upTo (tr.time i)) p q → tr.time q < sp.ts σ := by
    intro q _ hrest
    exact (hrestart p hpH q hrest).trans_lt ((SA.ts_lt_iff sp).mpr (by clear * -; omega))
  have hhalf := SA.honest_voters_half_before hS hσg hσD
    (fun z hz q _ hrest => hrestart z hz q hrest)
  have hhalf' : sp.n ≤ 2 * {z | z ∈ H (tr.time i) ∧ ∃ q e,
      SA.VoteAt (tr.projAC.upTo (tr.time i)) z q e ∧ e.msg.slot = σ}.ncard := by
    have hle := Set.ncard_le_ncard (s := {z | z ∈ H (tr.time i) ∧ ∃ q e,
      SA.VoteAt (tr.projAC.upTo (tr.time i)) z q e ∧ e.msg.slot = σ ∧
        (tr.projAC.upTo (tr.time i)).time q ≤ sp.ts σ + sp.Δ})
      (t := {z | z ∈ H (tr.time i) ∧ ∃ q e,
        SA.VoteAt (tr.projAC.upTo (tr.time i)) z q e ∧ e.msg.slot = σ})
      (by rintro z ⟨hz, q, e, hv, hs, _⟩; exact ⟨hz, q, e, hv, hs⟩)
    omega
  have hpre := hp.run.upTo hi0
  have hnoopt := Healing.proposal_no_optimistic_of_run hpre (hp.noColl.upTo _) hf hpH
    (by rw [RunTrace.upTo_projAC]; exact hci') hcall hti
  have hhigh : SA.HighLocksCompatible ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)))
      ((tr.projAC.upTo (tr.time i)).state p i) ((tr.projAC.upTo (tr.time i)).time i) σ B := by
    refine SA.highLocksCompatible_iff.2 fun l hl _ hlσ X hX hXr => ?_
    obtain ⟨L, hL, hLr, O, hLO, q, hqi, CV, hO⟩ := SA.lock_below_origin hr hpH i l hl
    obtain rfl : X = L := hU.1 hX hL (hXr.trans hLr.symm)
    have hcomp : Compatible ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i))) O B := by
      rcases hO with ⟨ell', ⟨_, _, ht, _⟩, _⟩ | ⟨ellO, A, hpt, hsl, hsel, hCV⟩
      · have htime := hr.time_mono hqi.le
        have hle := (SA.ts_le_iff sp).mpr (show (σ : Int) ≤ l.slot by clear * - hlσ; omega)
        change tr.time q ≤ tr.time i at htime
        change tr.time q = sp.ts l.slot + 6 * sp.Δ at ht
        rw [hti, hσ] at htime
        exfalso
        linarith only [htime, hle, ht, hΔ]
      · have hle : l.slot ≤ σ := by
          have htime := hm hqi.le
          have hne : l.slot ≠ σ + 1 := fun he =>
            hnoopt p hpH q hqi O CV (by
              rw [RunTrace.upTo_projAC]; exact he ▸ ⟨ellO, A, hpt, hsl, hsel, hCV⟩)
          have hstart := (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg q) (l.slot : Int)).mpr
            (by change sp.slot (tr.time q) = l.slot at hsl; clear * - hsl; omega)
          rw [hti] at htime
          have := (SA.ts_le_iff sp).mp (hstart.trans htime)
          clear * - hne this; omega
        have hΦU := (SA.frameIn_of_callAt hr hpH hpt.1).2
        unfold SA.optimisticSelect at hsel
        dsimp only at hsel
        split_ifs at hsel
        have h34 := (SA.deepest_mem hsel).1.2.1
        rw [hsl] at h34
        refine SA.origin_compatible hU hΦU h34
          (by simpa only [hp.stock] using hf) fun v hv hvH => ?_
        obtain ⟨hvs, q', _, e', hv', rfl⟩ := SA.optimisticPoint_pool_vote hS.run hpH hpt hv hvH
        exact votes _ hvH q' e' hv' (by rw [hvs]; clear * - hlσ hle; omega)
    rcases hcomp with h | h
    · exact Or.inl (hLO.trans h)
    · exact SA.anc_total hU hLO h
  have hfin := SA.batch_proposal hS.run hf hhalf' votes hpH hci'
    (SA.proposal_slot hti) hd' ⟨hV.1, Or.inl hV⟩ ?_ hhigh
  · exact hfin.mono hsub
  intro z hz q e hv he
  obtain ⟨H', hH', hHr', hBH⟩ := votes z hz q e hv he
  obtain ⟨Hd, hHd, hHdr, _, hmem, _, hbs⟩ := SA.late_vote_held_of_frame_before hS hpH hci' hσg
    (by change _ ≤ tr.time i; rw [hti, hσ]; linarith only [hΔ]) le_rfl
    (fun k hki t _ => Compose.ac_deadline_le_of_restarts
      (fun k' hk' hr' => (hrs k' (hk'.trans hki) hr').le) t) hrs hz hv he
    (fun Hd hHd hHdr => by
      rw [hU.1 hHd hH' (hHdr.trans hHr'.symm)]
      exact hFB.trans hBH)
  exact SA.heldAtProposal_iff.2 ⟨Or.inl hmem, Hd, hHd, hHdr,
    (hHdr ▸ hbs).trans (WithBot.coe_lt_coe.2 (WithTop.coe_lt_top _))⟩

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end

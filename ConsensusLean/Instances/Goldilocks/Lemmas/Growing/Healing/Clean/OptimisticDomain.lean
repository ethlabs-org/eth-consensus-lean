module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.SlowVotes
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.WriterPending
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.RetentionPending
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Seed
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.FiniteSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The vote domain of a clean optimistic source, under growing faults

The growing form of `Healing.ResetPremisesUpTo.optimistic_vote_domain_before`: a clean optimistic
source, written by a node honest at its write, is below the frame root of a later vote of a node
honest at it, or viable in its voter block tree, given the earlier votes of nodes honest at them.
The held-target vote domain (`held_target_vote_domain_before_at`) receives the source held by its
writer, its availability to the voter (`raw_writer_voterBlockTree_window_before_at`, under the
reset service and the catch-up), the reset seed, and the comparisons with every high origin
written before the vote: an older one through an honest supporter of the source, one of the
source's label through the same-label comparisons, a later one through the earlier votes. -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- **The catch-up on the AC projection**: a block that a node accepted while honest before `ḡ`
is accepted before `ḡ + 2Δ` by a node honest at a later call, by `b`, whose `Σ.F` it extends. -/
private theorem catch_ac (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) :
    ∀ x i B, x ∈ H (tr.time i) → tr.projAC.AcceptAt x i B → tr.time i < SA.gbar g →
      ∀ y j ell, y ∈ H (tr.time j) → tr.projAC.CallAt y j ell →
        SA.gbar g + 2 * sp.Δ ≤ tr.time j → tr.time j ≤ b →
        Anc (tr.HonestBlocksAt H) ell.frame.F B →
        ∃ k ≤ j, tr.projAC.AcceptAt y k B ∧ tr.time k < SA.gbar g + 2 * sp.Δ := by
  intro x q D hqH hq hg p i ell hpH hci hti _ hFD
  have hm := hp.run.time_mono
  have ht0 := hp.run.time_nonneg i
  have subU := RunTrace.honestBlocks_upTo_subset hm (H := H) ht0
  have hcp := (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hci⟩
  have hprex := hp.run.upTo (hp.run.time_nonneg q)
  obtain ⟨ellq, hcq, hblock⟩ := hq
  have hcq' := (Trace.upTo_callAt tr).mpr ⟨le_rfl, Compose.projAC_callAt.mp hcq⟩
  obtain ⟨q', rfl, haq', htime⟩ := Compose.acBlock_prev hprex.toLocalRun hqH hcq' hblock
  obtain ⟨hqq, haq⟩ := (Trace.upTo_callAt tr).mp haq'
  change tr.time q' = tr.time (q' + 1) at htime
  have hex : ∃ k, SA.gbar g + 2 * sp.Δ ≤ tr.time k := ⟨i, hti⟩
  have hfirst : tr.FirstCutFrom (Nat.find hex) (SA.gbar g + 2 * sp.Δ) :=
    ⟨Nat.find_spec hex, fun k hk => not_le.mp (Nat.find_min hex hk)⟩
  have hki : Nat.find hex ≤ i := Nat.find_min' hex hti
  have hpy := hp.run.upTo ht0
  have hFD' : Anc (tr.HonestBlocksAt H) (tr.state p (Nat.find hex)).fg.F D := by
    have hF := Healing.run_F_mono hpy.toLocalRun hpH hki
    rw [RunTrace.upTo_state_of_le hm (hm hki), RunTrace.upTo_state_of_le hm le_rfl] at hF
    have hframe := Compose.frame_of_projAC hpy hpH (by rw [RunTrace.upTo_projAC]; exact hcp)
    rw [RunTrace.upTo_state_of_le hm le_rfl] at hframe
    have hFeq : ell.frame.F = (tr.state p i).fg.F := congrArg Frame.F hframe
    exact (hF.mono subU).trans (by rwa [← hFeq])
  obtain ⟨k, hkk, hak⟩ := hc x q' D (hp.run.antitone hqq hqH) haq
    (by rw [htime]; exact hg) p _
    (hp.run.antitone (hfirst.1.trans (hm hki)) hpH) hfirst hFD'
  have hk := hkk.le.trans hki
  have hak' := (RunTrace.upTo_acceptAt tr).mpr ⟨hm hk, hak⟩
  obtain ⟨ellk, hck, hblock, ht⟩ := Compose.accept_next hpy.toLocalRun hpH hak'
  have hck' := (Trace.upTo_callAt tr).mp hck |>.2
  refine ⟨k + 1, by omega, ⟨ellk, Compose.projAC_callAt.mpr hck', hblock⟩, ?_⟩
  change tr.time (k + 1) = tr.time k at ht
  rw [ht]
  exact hfirst.2 k hkk

/-- **A clean optimistic source has the vote domain** of every later vote of a node honest at it
through the horizon, given the earlier votes of nodes honest at them. -/
theorem optimistic_vote_domain_before_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {x y : Fin sp.n} {r s i : Nat}
    (hx : x ∈ H (tr.time r)) (hy : y ∈ H (tr.time i))
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hop : SA.OptimisticLockAt tr.projAC x r s B CV)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hrb : tr.time r ≤ b)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcast : SA.CastAt tr.projAC y i ell e) (hsi : s < e.msg.slot) (hib : tr.time i ≤ b)
    (hprior : ∀ z q, z ∈ H (tr.time q) → q < i → ∀ e', SA.VoteAt tr.projAC z q e' →
      s < e'.msg.slot → SA.VoteExtends (tr.HonestBlocksAt H) e'.msg B) :
    Anc (tr.HonestBlocksAt H) B ell.frame.fcRoot ∨
      B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot) := by
  have hm := hp.run.time_mono
  have hΔ := sp.toParams.hΔ
  have hU := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  obtain ⟨hBx, z, q, hz, hqr, ev, hv, hvs, hVB⟩ := hp.optimistic_supporter_at hx hrb hop
  have hzq : z ∈ H (tr.time q) := hp.run.antitone (hm hqr) hz
  have hqb := (hm hqr).trans hrb
  obtain ⟨v, d, m, S, hseed, hda, hma⟩ := hp.reset_seed_at
  have hdb := hda.trans hp.reset_le
  have hms : m < s := by rw [cleanLabel_eq] at hs; omega
  have hts := hp.clean_window_timing_at hs s (by have := sp.two_le_k; clear * - this; omega)
  have hgs : SA.gbar g + 8 * sp.Δ < sp.ts s := (Healing.lt_cutZ sp g).trans_le hts
  apply hp.held_target_vote_domain_before_at hx hy hBx hrb hcast hib ?_ hseed hdb (by omega)
    (hp.target_compatible_older_origin_at hseed hdb hzq hv hqb hvs hms hVB) ?_ ?_ ?_
  · intro hF
    have hle := (SA.ts_le_iff sp).mpr (show (s : Int) ≤ e.msg.slot - 1 by omega)
    exact SA.Growing.raw_writer_voterBlockTree_window_before_at hac.localRun
      (hp.sync.ac_service_at hp.run (lo := SA.gbar g) (hi := b) (SA.le_gbar g))
      (catch_ac hp hc) hx hy (Or.inr (Or.inr hop)) .refl hcast (by omega) hib
      (by linarith only [hle, hgs, hΔ]) hF
  · intro w c n O hci ho
    have hcb := (hm hci.le).trans hib
    rcases lt_trichotomy n s with hn | rfl | hn
    · exact hp.target_compatible_older_origin_at ho hcb hzq hv hqb hvs hn hVB
    · obtain ⟨CV', ellD, D, hcD, hfl, hO⟩ := ho.2.2.1
      have hwU : (tr.state w c).fg.tree ⊆ tr.HonestBlocksAt H :=
        fun _ h => ⟨w, c, tr.time c, hp.run.time_nonneg c, fun _ hq => hm hq.le, ho.1, h⟩
      have hOD : Anc (tr.HonestBlocksAt H) O D := by
        rw [hO]
        exact (SA.anc_viableAncestor ellD.frame D).mono
          ((frame_tree_subset_at hp.run hp.noColl ho.1 hcD).2.trans hwU)
      have hcomp : Compatible (tr.HonestBlocksAt H) B D := by
        rcases hfl with ⟨ellD', R, huD, hR, hfast, _⟩ | hop'
        · have hDR := ((SA.deepest_mem hfast).1.1.2.2).mono
            ((frame_tree_subset_at hp.run hp.noColl ho.1 huD.1).2.trans hwU)
          rcases hp.result_source_compatible_at ho.1 hx ⟨ellD', huD, hR, rfl⟩ (Or.inr hop)
              hcb hrb hts with h | h
          · exact Or.inr (hDR.trans h)
          · exact SA.anc_total hU h hDR
        · exact hp.optimistic_sources_compatible_at hx ho.1 hrb hcb hop hop'
      rcases hcomp with h | h
      · exact SA.anc_total hU h hOD
      · exact Or.inr (hOD.trans h)
    · exact hp.target_compatible_later_origin_before_at ho hci hcb hn
        fun z' q' e' hq'i hv' hse => hprior z' q' (Compose.Growing.hVoteAt_iff.mp hv').1 hq'i e'
          (Compose.Growing.hVoteAt_iff.mp hv').2 hse
  · intro w c n O hci ho
    exact hp.origins_compatible_at hseed hdb ho ((hm hci.le).trans hib)
  · intro w c n O hci ho w' c' n' O' hci' ho'
    exact hp.origins_compatible_at ho ((hm hci.le).trans hib) ho' ((hm hci'.le).trans hib)

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end

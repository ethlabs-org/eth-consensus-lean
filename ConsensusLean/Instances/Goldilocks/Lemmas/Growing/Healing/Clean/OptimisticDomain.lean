module
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Relay
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.SlowVotes
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.WriterCompatible
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.RawWriterTree
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.GrowingPremises
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetFacts
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
The held-target vote domain (`held_target_vote_domain_before_of_quarantine_at`) receives the
source held by its writer, its availability to the voter
(`raw_writer_voterBlockTree_window_before_at`, under the
reset service and the catch-up), the reset seed, and the comparisons with every high origin
written before the vote: an older one through an honest supporter of the source, one of the
source's label through the same-label comparisons, a later one through the earlier votes. -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open AC (ACParams ReplayOrder Payload Vote)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}
variable {hold : Time}

/-- **The catch-up on the AC projection**: a block that a node accepted while honest before `ḡ`
is accepted before `ḡ + 2Δ` by a node honest at a later call, by `b`, whose `Σ.F` it extends. -/
private theorem catch_ac {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    :
    ∀ x i B, x ∈ H (tr.time i) → tr.projAC.AcceptAt x i B → tr.time i < AC.gbar g →
      ∀ y j ell, y ∈ H (tr.time j) → tr.projAC.CallAt y j ell →
        AC.gbar g + 2 * sp.Δ ≤ tr.time j → tr.time j ≤ b →
        Anc (tr.HonestBlocksAt H) ell.frame.F B →
        ∃ k ≤ j, tr.projAC.AcceptAt y k B ∧ tr.time k < AC.gbar g + 2 * sp.Δ := by
  intro x q D hqH hq hg p i ell hpH hci hti _ hFD
  exact hp.run.toLocalRun.acCatchAt hp.catchUp hqH hq hg hpH hci hti hFD

/-- **A clean optimistic source has the vote domain** of every later vote of a node honest at it
through the horizon, given the earlier votes of nodes honest at them, inside the deep quarantine
(`hpre`). -/
theorem optimistic_vote_domain_before_of_quarantine_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x y : Fin sp.n} {r s i : Nat}
    (hx : x ∈ H (tr.time r)) (hy : y ∈ H (tr.time i))
    {B : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hop : AC.OptimisticLockAt tr.projAC x r s B CV)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hrb : tr.time r ≤ b)
    {ell : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hcast : AC.CastAt tr.projAC y i ell e) (hsi : s < e.msg.slot) (hib : tr.time i ≤ b)
    (hprior : ∀ z q, z ∈ H (tr.time q) → q < i → ∀ e', AC.VoteAt tr.projAC z q e' →
      s < e'.msg.slot → AC.VoteExtends (tr.HonestBlocksAt H) e'.msg B)
    (hpre : ∀ D, sp.deepDepth = some D → b ≤ cutZ sp.toParams g + 4 * D * sp.Δ) :
    Anc (tr.HonestBlocksAt H) B ell.frame.fcRoot ∨
      B ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot) := by
  have hm := hp.run.time_mono
  have hΔ := sp.toParams.hΔ
  have hU := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  have hac := Compose.Growing.goldilocks_ac_projection_from hp.run hp.noColl
  obtain ⟨hBx, z, q, hz, hqr, ev, hv, hvs, hVB⟩ := hp.optimistic_supporter_at hx hrb
    (hp.gbar_le_ts_of_clean_at (by omega)) hop
  have hzq : z ∈ H (tr.time q) := hp.run.antitone (hm hqr) hz
  have hqb := (hm hqr).trans hrb
  obtain ⟨v, d, m, S, hseed, hda, hma⟩ := hp.reset_seed_at
  have hdb := hda.trans hp.reset_le
  have hms : m < s := by rw [cleanLabel_eq] at hs; omega
  have hts := hp.clean_window_timing_at hs s (by have := sp.two_le_k; clear * - this; omega)
  have hgs : AC.gbar g + 8 * sp.Δ < sp.ts s := (Healing.lt_cutZ sp g).trans_le hts
  apply hp.held_target_vote_domain_before_of_quarantine_at hx hy hBx hrb hcast hib ?_ hseed hdb
    (by omega) (hp.target_compatible_older_origin_at hseed hdb hzq hv hqb hvs hms hVB) ?_ ?_ ?_
    hpre
  · intro hF
    have hle := (AC.ts_le_iff sp).mpr (show (s : Int) ≤ e.msg.slot - 1 by omega)
    exact AC.Growing.raw_writer_voterBlockTree_window_before_at
      hp.committee_pos hac.localRun hac.vstart
      (hp.sync.ac_service_at hp.run (lo := AC.gbar g) (hi := b) (AC.le_gbar g))
      (catch_ac hp ) hx hy (Or.inr (Or.inr hop)) .refl hcast (by omega) hib
      (by linarith only [hle, hgs, hΔ]) hF
  · intro w c n O hci ho
    have hcb := (hm hci.le).trans hib
    rcases lt_trichotomy n s with hn | rfl | hn
    · exact hp.target_compatible_older_origin_at ho hcb hzq hv hqb hvs hn hVB
    · obtain ⟨CV', ellD, D, hcD, hfl, hO⟩ := ho.2.2.1
      have hw := hp.run.antitone (le_max_right _ _) ho.1
      have hwU : (tr.state w c).fg.tree ⊆ tr.HonestBlocksAt H :=
        fun _ h => ⟨w, c, tr.time c, hp.run.time_nonneg c, fun _ hq => hm hq.le, hw, h⟩
      have hOD : Anc (tr.HonestBlocksAt H) O D := by
        rw [hO]
        exact (AC.anc_viableAncestor ellD.frame D).mono
          ((frame_tree_subset_at hp.run hp.noColl hw hcD).2.trans hwU)
      have hcomp : Compatible (tr.HonestBlocksAt H) B D := by
        rcases hfl with ⟨ellD', R, huD, hR, hfast, _⟩ | hop'
        · have hDR := ((AC.deepest_mem hfast).1.1.2.2).mono
            ((frame_tree_subset_at hp.run hp.noColl hw huD.1).2.trans hwU)
          rcases hp.result_source_compatible_at hw hx ⟨ellD', huD, hR, rfl⟩ (Or.inr hop)
              hcb hrb hts with h | h
          · exact Or.inr (hDR.trans h)
          · exact AC.anc_total hU h hDR
        · exact hp.optimistic_sources_compatible_at hx hw hrb hcb
            (hp.gbar_le_ts_of_clean_at (by omega)) hop hop'
      rcases hcomp with h | h
      · exact AC.anc_total hU h hOD
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

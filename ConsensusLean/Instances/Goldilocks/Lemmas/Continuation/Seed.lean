module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Continuation.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HealedSafetyConditional
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.Opening
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PreparationService
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.Sources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.SeedCall
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.RowService
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Local
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The hand-over seed

The healthy facts of a hand-over run up to the hand-over time `T`, packaged as the seed of the
continued label induction. The reset `a` comes from the healed-safety query healthy up to `T`.
The lock floor is `r = cleanLabel a + k + 2` and the origin floor is `r + k − 1 = cleanLabel a +
2k + 1` (`Continuation/Defs`). A split slot `σ` has every vote of a slot `≤ σ + 1` cast by `T`
and every vote of a later slot cast after the drain; the query's seed takes `σ = slot T − 2`.

The family's `P` and `V` rows up to `T` are the reset cluster's: origins compare and are extended
from `cleanLabel + 2k + 1` on, lock writes are extended from `cleanLabel + k + 2` on, and high
origins at every label. Two members of distinct labels compare through the honest supporter of
the later member's origin; two of one label through their underlying origins.

* `Compose.Growing.HandoverSeed`: the reset premises up to `T`, the catch-up, the timing of the
  split slot, the healed frontier `P`/`V` through slot `σ + 1` up to `T`, the high FG rows on the
  family's chain, a reset seed held at every honest call from the reset on up to `T`, and the
  record cover from a time `t₁ ≤ T` on.
* `Compose.Growing.HandoverSeed.of_reset`: the seed from bounded reset premises, the catch-up, the
  split-slot timing and the record cover.
* `Compose.Growing.handover_live_lock_label_at`: every live lock at an honest vote of a slot after
  `σ` has label at least `r` (the drain: the vote is at or after `drainTime a = t_{r+k}`, and a
  live lock expires at most `k` slots after its label).
* `Obligations.Growing.handover_seed_at`: a healed-safety query healthy up to its bound, with
  `heal ≤ bound` and progress on `[ready, heal]`, gives a seed at `T = bound` with the FG service
  delay `protoFGDelay`. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- **The hand-over seed**: the healthy facts up to `T` from the reset `a`, with the lock floor
`r = cleanLabel a + k + 2`, the origin floor `r + k − 1`, and the split slot `σ`.

* `reset`, `catchRun`: the reset premises up to `T` and the catch-up from GST.
* `timing`: every vote of a slot `≤ σ + 1` is cast before `T` (`t_σ + 8Δ ≤ T`); a vote of a slot
  after `σ` is at or after the drain (`r + k ≤ σ + 1`, `drainTime a = t_{r+k}`); the slot counts
  of the labels from `r` on start after GST.
* `frontier`: the healed family within `T` is pairwise compatible through the labels `≤ σ`, and
  extended by every honest vote up to `T` of a later slot `≤ σ + 1`.
* `rows`: a high FG row signed up to `T` by a node honest then names an entry of its store below a
  family member.
* `seedHeld`: a high origin written up to `T` is in the frame of every honest call at a time in
  `[t_{r−k−3}, T]` whose finalized block it extends (`t_{r−k−3} = t_{slot a + 2} ≥ a + Δ`).
* `covered`: from a time `t₁ ≤ T` on, the record of every reader honest at a read point up to `T`
  is its finalized block or below an origin of label `≥ r + k − 1` written before the read. -/
structure HandoverSeed (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (proposer : Nat → Fin sp.n) (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (g ΔF T : Time) (r σ : Nat) : Prop where
  reset : ∃ a, Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a T ∧
    r = Healing.cleanLabel sp a + sp.k + 2
  catchRun : Healing.Growing.CatchRun tr H g (2 * sp.Δ)
  timing : sp.ts σ + 8 * sp.Δ ≤ T ∧ r + sp.k ≤ σ + 1 ∧ SA.gbar g + 20 * sp.Δ ≤ sp.ts r
  frontier : HealedOriginsBelow tr H g r (r + sp.k - 1) (σ + 1) T ∧
    HealedVotesBelow tr H g r (r + sp.k - 1) (σ + 1) T
  rows : ∀ y k att, y ∈ H (tr.time k) → tr.SignAt y k att → tr.time k ≤ T →
    Healing.Growing.HZ tr H g + 1 ≤ att.h →
    ∃ C s, HealedOrigin tr H g r (r + sp.k - 1) C s T ∧ ∃ E ∈ (tr.state y k).fg.tree,
      E.root = att.T ∧ Anc (tr.HonestBlocksAt H) E C
  seedHeld : ∃ x i j B, Healing.Growing.HighOrigin tr H g x i j B ∧ tr.time i ≤ T ∧
    ∀ y c (ell : ACLabel (goldilocksNode sp ro)), y ∈ H (tr.time c) → tr.projAC.CallAt y c ell →
      sp.ts (r - sp.k - 3 : Nat) ≤ tr.time c → tr.time c ≤ T →
      Anc (tr.HonestBlocksAt H) ell.frame.F B → B ∈ ell.frame.tree
  covered : ∃ t₁, t₁ ≤ T ∧ ∀ y n t, t₁ ≤ t → t ≤ T → y ∈ H t → Regimes.ReadPoint tr n t →
    HealedRecordCoverAt tr H (r + sp.k - 1) y n t
      ((SA.lookup (Node.frame (tr.state y n)) (tr.state y n).ac.latestConfirmed).getD
        (tr.state y n).fg.F)

variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-! ### Family members below origins, their supporters and their later votes -/

/-- A lock write is below an origin of its label by the same writer at the same cut: a slow lock
and a fast update keep a prefix of their update's confirmation; an optimistic selection is an
origin. -/
private theorem lock_below_origin (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {x : Fin sp.n} {i s : Nat} (hx : x ∈ H (tr.time i))
    {C : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : (∃ CV, SA.FastLockAt tr.projAC x i s C CV) ∨ SA.SlowLockAt tr.projAC x i s C) :
    ∃ O OV, (SA.ResultAt tr.projAC x i s O OV ∨ SA.OptimisticLockAt tr.projAC x i s O OV) ∧
      Anc (tr.HonestBlocksAt H) C O := by
  have hxU : (tr.state x i).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨x, i, tr.time i, hrun.time_nonneg i, fun _ hq => hrun.time_mono hq.le, hx, h⟩
  rcases h with ⟨CV, ⟨ellX, O, hupd, hconf, hdeep, -⟩ | hop⟩ | ⟨ellX, O, hupd, hconf, hdeep⟩
  · exact ⟨O, _, Or.inl ⟨ellX, hupd, hconf, rfl⟩, ((SA.deepest_mem hdeep).1.1.2.2).mono
      ((Healing.Growing.frame_tree_subset_at hrun hnc hx hupd.1).2.trans hxU)⟩
  · exact ⟨C, CV, Or.inr hop, .refl⟩
  · exact ⟨O, _, Or.inl ⟨ellX, hupd, hconf, rfl⟩, ((SA.deepest_mem hdeep).1.1.2.2).mono
      ((Healing.Growing.frame_tree_subset_at hrun hnc hx hupd.1).2.trans hxU)⟩

/-- The healed family unpacked into its three kinds of members. -/
private theorem healedOrigin_cases {rL rO : Nat} {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (hC : HealedOrigin tr H g rL rO C s b) :
    (rO ≤ s ∧ ∃ x i CV, x ∈ H (tr.time i) ∧ tr.time i ≤ b ∧
      (SA.ResultAt tr.projAC x i s C CV ∨ SA.OptimisticLockAt tr.projAC x i s C CV)) ∨
    (rL ≤ s ∧ ∃ x i, x ∈ H (tr.time i) ∧ tr.time i ≤ b ∧
      ((∃ CV, SA.FastLockAt tr.projAC x i s C CV) ∨ SA.SlowLockAt tr.projAC x i s C)) ∨
    ∃ x i, tr.time i ≤ b ∧ Healing.Growing.HighOrigin tr H g x i s C := by
  rwa [healedOrigin_iff, originWithin_iff, lockWithin_iff] at hC

/-- Every member of the healed family is below an origin of its label, written by a node honest
at its cut, at a time `≤ b`. A high origin is the viable ancestor of a fast lock write. -/
private theorem member_below_origin (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {rL rO : Nat} {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (hC : HealedOrigin tr H g rL rO C s b) :
    ∃ x i O OV, x ∈ H (tr.time i) ∧ tr.time i ≤ b ∧
      (SA.ResultAt tr.projAC x i s O OV ∨ SA.OptimisticLockAt tr.projAC x i s O OV) ∧
      Anc (tr.HonestBlocksAt H) C O := by
  rcases healedOrigin_cases hC with ⟨-, x, i, CV, hx, hib, h⟩ | ⟨-, x, i, hx, hib, h⟩ |
    ⟨x, i, hib, ho⟩
  · exact ⟨x, i, C, CV, hx, hib, h, .refl⟩
  · obtain ⟨O, OV, hO, hCO⟩ := lock_below_origin hrun hnc hx h
    exact ⟨x, i, O, OV, hx, hib, hO, hCO⟩
  · obtain ⟨CV, ell, D, hcall, hfl, rfl⟩ := ho.2.2.1
    obtain ⟨O, OV, hO, hDO⟩ := lock_below_origin hrun hnc ho.1 (Or.inl ⟨CV, hfl⟩)
    have hΦU := (frameIn_at hrun hnc ho.1 hcall).2
    exact ⟨x, i, O, OV, ho.1, hib, hO, (Anc.mono hΦU (SA.anc_viableAncestor _ D)).trans hDO⟩

/-- A block below an origin of a label after the high-origin cutoff has an honest supporting vote
of that slot, cast no later than the origin's cut. -/
private theorem origin_supporter
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.Growing.CatchRun tr H g (2 * sp.Δ)) {x : Fin sp.n} {i s : Nat}
    {O C : SA.Blk sp.n (List (FG.Att sp.n))} {OV : Set (Vote sp.n)} (hx : x ∈ H (tr.time i))
    (hib : tr.time i ≤ b)
    (hO : SA.ResultAt tr.projAC x i s O OV ∨ SA.OptimisticLockAt tr.projAC x i s O OV)
    (hCO : Anc (tr.HonestBlocksAt H) C O) (hts : Healing.cutZ sp.toParams g ≤ sp.ts s) :
    ∃ z j e, z ∈ H (tr.time j) ∧ tr.time j ≤ b ∧ SA.VoteAt tr.projAC z j e ∧
      e.msg.slot = s ∧ SA.VoteExtends (tr.HonestBlocksAt H) e.msg C := by
  have hm := hp.run.time_mono
  rcases hO with hO | hO
  · obtain ⟨z, hz, j, hji, e, hv, -, hes, hCH⟩ :=
      Healing.Growing.ProposalImpl.result_supporter_at hp hc hx hO hCO hib hts
    exact ⟨z, j, e, hp.run.antitone (hm hji.le) hz, (hm hji.le).trans hib, hv, hes, hCH⟩
  · obtain ⟨-, z, j, hz, hji, e, hv, hes, Hd, hHd, he, hOH⟩ :=
      hp.optimistic_supporter_at hx hib hO
    exact ⟨z, j, e, hp.run.antitone (hm hji) hz, (hm hji).trans hib, hv, hes,
      Hd, hHd, he, hCO.trans hOH⟩

/-- **The `V` row of the healed family up to `b`**, at the hand-over floors: every honest vote at
a time `≤ b` of a later slot extends each member. Origins from `cleanLabel + 2k + 1`
(`clean_result_prefix_votes_before_at`, `fast_source_votes_before_at`), lock writes from
`cleanLabel + k + 2` (`fast_source_votes_before_at`, `slow_source_votes_before_at`), high origins
at every label (`high_origin_votes_before_at`). -/
private theorem member_votes (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.Growing.CatchRun tr H g (2 * sp.Δ)) {r : Nat}
    (hr : r = Healing.cleanLabel sp a + sp.k + 2) {C : SA.Blk sp.n (List (FG.Att sp.n))}
    {s : Nat} (hC : HealedOrigin tr H g r (r + sp.k - 1) C s b) :
    ∀ y i e, HVoteAt tr H y i e → tr.time i ≤ b → s < e.msg.slot →
      SA.VoteExtends (tr.HonestBlocksAt H) e.msg C := by
  intro y i e hv hib hse
  obtain ⟨hy, ell, hcast⟩ := hVoteAt_iff.mp hv
  have hk := sp.two_le_k
  rcases healedOrigin_cases hC with ⟨hs, x, q, CV, hx, hqb, hO | hO⟩ | ⟨hs, x, q, hx, hqb,
    ⟨CV, hfl⟩ | hsl⟩ | ⟨x, q, hqb, ho⟩
  · exact hp.clean_result_prefix_votes_before_at hc hx hO .refl (by omega) hqb i hib y hy ell e
      hcast hse
  · exact hp.fast_source_votes_before_at hc hx (Or.inr hO) (by omega) hqb i hib y hy ell e
      hcast hse
  · exact hp.fast_source_votes_before_at hc hx hfl (by omega) hqb i hib y hy ell e hcast hse
  · exact hp.slow_source_votes_before_at hc hx hsl (by omega) hqb i hib y hy ell e hcast hse
  · exact hp.high_origin_votes_before_at i hib x q s C ho hqb y ell e hy hcast hse

/-- **The `P` row of the healed family up to `b`**, at the hand-over floors: any two members are
compatible. Two high origins compare by R1 (`origins_compatible_at`). Otherwise the larger label
is at least the lock floor, after the high-origin cutoff: for distinct labels the honest
supporter of the later member's origin extends both (the earlier member by its `V` row); for one
label the two underlying origins compare (`sources_same_label_compatible_at`) and each member is
below its origin. -/
private theorem member_compatible
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.Growing.CatchRun tr H g (2 * sp.Δ)) {r : Nat}
    (hr : r = Healing.cleanLabel sp a + sp.k + 2) {C C' : SA.Blk sp.n (List (FG.Att sp.n))}
    {s s' : Nat} (hC : HealedOrigin tr H g r (r + sp.k - 1) C s b)
    (hC' : HealedOrigin tr H g r (r + sp.k - 1) C' s' b) :
    Compatible (tr.HonestBlocksAt H) C C' := by
  have hU := honest_blocks_coherent hp.run hp.noColl
  have hk := sp.two_le_k
  have hts : ∀ u, r ≤ u → Healing.cutZ sp.toParams g ≤ sp.ts u := fun u hu =>
    hp.clean_window_timing_at (s := u) (by omega) u (by omega)
  -- a member of a label below a member of a later label at least the lock floor
  have ordered : ∀ {C C' s s'}, HealedOrigin tr H g r (r + sp.k - 1) C s b →
      HealedOrigin tr H g r (r + sp.k - 1) C' s' b → s < s' → r ≤ s' →
      Compatible (tr.HonestBlocksAt H) C C' := by
    intro C C' s s' hC hC' hss hrs
    obtain ⟨x, i, O, OV, hx, hib, hO, hCO⟩ := member_below_origin hp.run hp.noColl hC'
    obtain ⟨z, j, e, hz, hjb, hv, hes, Hd, hHd, he, hCH⟩ :=
      origin_supporter hp hc hx hib hO hCO (hts s' hrs)
    obtain ⟨Hd', hHd', he', hCH'⟩ := member_votes hp hc hr hC z j e
      (hVoteAt_iff.mpr ⟨hz, hv⟩) hjb (by omega)
    obtain rfl : Hd' = Hd := hU.1 hHd' hHd (he'.trans he.symm)
    exact SA.anc_total hU hCH' hCH
  -- a member of a label at least the lock floor
  have floor : ∀ {C s}, HealedOrigin tr H g r (r + sp.k - 1) C s b →
      r ≤ s ∨ ∃ x i, tr.time i ≤ b ∧ Healing.Growing.HighOrigin tr H g x i s C := by
    intro C s hC
    rcases healedOrigin_iff.mp hC with ⟨hs, -⟩ | ⟨hs, -⟩ | h
    · exact Or.inl (by omega)
    · exact Or.inl hs
    · exact Or.inr h
  have high_or : r ≤ s ∨ r ≤ s' ∨ Compatible (tr.HonestBlocksAt H) C C' := by
    rcases floor hC with h | ⟨x, i, hib, ho⟩
    · exact Or.inl h
    rcases floor hC' with h | ⟨x', i', hib', ho'⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (hp.origins_compatible_at ho hib ho' hib'))
  rcases high_or with hrs | hrs | h
  rotate_right
  · exact h
  all_goals
    rcases lt_trichotomy s s' with hlt | rfl | hgt
    · exact ordered hC hC' hlt (by omega)
    · obtain ⟨x, i, O, OV, hx, hib, hO, hCO⟩ := member_below_origin hp.run hp.noColl hC
      obtain ⟨x', i', O', OV', hx', hib', hO', hCO'⟩ := member_below_origin hp.run hp.noColl hC'
      rcases hp.sources_same_label_compatible_at hx hx' hO hO' hib hib' (hts s (by omega)) with
        h | h
      · exact SA.anc_total hU (hCO.trans h) hCO'
      · exact SA.anc_total hU hCO (hCO'.trans h)
    · exact (ordered hC' hC hgt (by omega)).symm

/-! ### The seed from bounded reset premises -/

/-- **The hand-over seed from bounded reset premises.** Reset premises up to `T`, the catch-up,
the split-slot timing and the record cover give the seed: the frontier is the reset cluster's
`P`/`V` rows for the healed family; the rows are `high_row_source_at`; the held seed is
`reset_seed_held_at_call_at` (`t_{slot a + 2} ≥ a + Δ`); the count start follows from
`c_z < a`. -/
theorem HandoverSeed.of_reset {T : Time} {r σ : Nat}
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a T)
    (hc : Healing.Growing.CatchRun tr H g (2 * sp.Δ)) (hr : r = Healing.cleanLabel sp a + sp.k + 2)
    (hσ : sp.ts σ + 8 * sp.Δ ≤ T) (hrσ : r + sp.k ≤ σ + 1)
    (hcov : ∃ t₁, t₁ ≤ T ∧ ∀ y n t, t₁ ≤ t → t ≤ T → y ∈ H t → Regimes.ReadPoint tr n t →
      HealedRecordCoverAt tr H (r + sp.k - 1) y n t
        ((SA.lookup (Node.frame (tr.state y n)) (tr.state y n).ac.latestConfirmed).getD
          (tr.state y n).fg.F)) :
    HandoverSeed tr H proposer dg g ΔF T r σ := by
  have hrun := hp.run
  have hΔ := sp.toParams.hΔ
  have hca := hp.cutZ_lt_reset_at
  have hgz := Healing.lt_cutZ sp g
  have ha0 : 0 ≤ a := by linarith [SA.gbar_nonneg g]
  have hsa : a < sp.ts ((sp.slot a : Int) + 1) := not_le.1 fun h => by
    have := (SA.ts_le_iff_le_slot sp ha0 _).1 h
    omega
  have hts (s j : Nat) : sp.ts (s + j : Nat) = sp.ts ((sp.slot a : Int) + 1) +
      4 * sp.Δ * ((s : Int) + j - (sp.slot a + 1)) := by
    simp only [SAParams.ts]; push_cast; ring
  refine ⟨⟨a, hp, hr⟩, hc, ⟨hσ, hrσ, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, hcov⟩
  · have h := hts (sp.slot a + 1) (sp.k + 4)
    rw [show sp.slot a + 1 + (sp.k + 4) = r by rw [hr, Healing.cleanLabel_eq]; omega] at h
    rw [h]
    have hk : (0 : Time) ≤ sp.k := Nat.cast_nonneg _
    push_cast
    nlinarith
  · rw [healedOriginsBelow_iff]
    intro C j C' j' _ _ hC hC'
    exact member_compatible hp hc hr hC hC'
  · rw [healedVotesBelow_iff]
    intro C j hC y i e hv hib hje _
    exact member_votes hp hc hr hC y i e hv hib hje
  · intro y k att hy hs hkT hh
    obtain ⟨q, hqk, l, O, ho, E, hE, hEO, hEr, -⟩ := hp.high_row_source_at hy hs hh
    have hqT := (hrun.time_mono hqk.le).trans hkT
    refine ⟨O, l, HealedOrigin.of_high hqT ho, E,
      tree_mono_at hrun (hrun.time_nonneg k) hy (fun _ h => hrun.time_mono h.le) hqk.le hE, hEr,
      hEO.mono fun _ h => ⟨y, q, tr.time q, hrun.time_nonneg q,
        fun _ h' => hrun.time_mono h'.le, ho.1, h⟩⟩
  · obtain ⟨v, q, l, S, hS, -, hqT, hheld⟩ := hp.reset_seed_held_at_call_at hc
    refine ⟨v, q, l, S, hS, hqT, fun y c ell hy hcall hc0 hcT hF =>
      hheld y c ell hy hcall ?_ hcT hF⟩
    have h := hts (sp.slot a + 1) 1
    rw [show sp.slot a + 1 + 1 = r - sp.k - 3 by rw [hr, Healing.cleanLabel_eq]; omega] at h
    rw [h] at hc0
    push_cast at hc0
    linarith

/-- **After the drain, every live lock at an honest vote of a slot after `σ` has label at least
`r`.** The vote is in its own slot (`castAt_spec_at`), at least `r + k`, so at or after
`drainTime a = t_{r+k}`; the read point's locks expire at most `k` slots after their labels
(`castAt_readPoint_locksWF`), so `drain_live_locks` applies. -/
theorem handover_live_lock_label_at {T : Time} {r σ : Nat}
    (hseed : HandoverSeed tr H proposer dg g ΔF T r σ) {y : Fin sp.n} {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hy : y ∈ H (tr.time i)) (hc : SA.CastAt tr.projAC y i ℓ e) (hs : σ < e.msg.slot) :
    ∀ l ∈ SA.liveLocks sp e.readPoint.locks ℓ.frame (tr.time i), r ≤ l.slot := by
  obtain ⟨a, hp, hr⟩ := hseed.reset
  have hrσ := hseed.timing.2.1
  have hrun := hp.run
  have hnc := hp.noColl
  have hd := hrun.time_nonneg i
  have hsl : e.msg.slot = sp.slot (tr.time i) := (castAt_spec_at hrun hnc hy hc).2.1
  have hdrain : Healing.drainTime sp a ≤ tr.time i := by
    rw [Healing.drainTime_eq]
    refine (SA.ts_le_iff_le_slot sp hd _).mpr ?_
    rw [hr, Healing.cleanLabel_eq] at hrσ
    push_cast
    omega
  have hwf := SA.castAt_readPoint_locksWF (acRun_upTo hrun hnc hd).localRun hy
    (sa_castAt_upTo.mpr ⟨le_rfl, hc⟩)
  intro l hl
  rw [hr]
  exact Healing.drain_live_locks (a := a) hwf hdrain l hl

end Consensus.Goldilocks.Compose.Growing

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- **The hand-over seed of a healed-safety query** healthy up to its bound `T`, with
`0 ≤ heal ≤ T` and progress on `[ready, heal]`. The repair schedule supplies the reset `a` and the
record cover from `query + (4i + 6)Δ < heal − 1` on; its reset premises take the run's FG service
at `protoFGDelay`. The lock floor is `r = cleanLabel a + k + 2` and the split slot is
`σ = slot T − 2`, so `t_σ + 8Δ = t_{slot T} ≤ T`. The schedule puts `drainTime a = t_{r+k}` at or
before the query, so `t_{r+k+2} < T` and `r + k ≤ σ`. -/
theorem handover_seed_at (Q : HealthyPreparationQueryAt S A V) (h0 : 0 ≤ Q.heal)
    (hb : Q.heal ≤ Q.bound)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run) :
    ∃ r σ, Compose.Growing.HandoverSeed Q.trace Q.keys (runProposer S Q.run.2 Q.hn)
      (digestOf S Q.run.2) Q.gst (protoFGDelay (Model.pubOf Q.run.1)) Q.bound r σ := by
  obtain ⟨D⟩ := healthy_repair_schedule_at S A V Q h0 hb hp
  obtain ⟨O, hrepair⟩ := healthy_bounded_repairing_opening_at S A V Q hb hp D
  have hreset : Healing.Growing.ResetPremisesUpTo Q.trace Q.keys (runProposer S Q.run.2 Q.hn)
      (digestOf S Q.run.2) Q.gst (protoFGDelay (Model.pubOf Q.run.1)) D.resetTime Q.bound :=
    { D.reset with sync := healthy_preparation_service_at S A V Q }
  have hΔ := Q.params.toParams.hΔ
  have hX : (1 : Time) ≤ (Q.index : Time) := by exact_mod_cast Q.index.pos
  have hdrain : Healing.drainTime Q.params D.resetTime ≤ D.query :=
    (le_max_left _ _).trans ((le_max_right _ _).trans D.lower)
  have hres := D.reserve
  have hkk : Q.params.k = (S.params (Model.pubOf Q.run.1) Q.hn).k := rfl
  have hT0 : 0 ≤ Q.bound := h0.trans hb
  -- the drain slot `r + k` ends two slots before the slot of `T`
  have hslot : Healing.cleanLabel Q.params D.resetTime + 2 * Q.params.k + 4 ≤
      Q.params.slot Q.bound := by
    have h := (SA.ts_le_iff_le_slot Q.params hT0
      ((Q.params.slot D.resetTime + 2 * Q.params.k + 7 : Nat) : Int)).mp (by
        rw [Healing.drainTime_eq] at hdrain
        have h : Q.params.ts (Q.params.slot D.resetTime + 2 * Q.params.k + 7 : Nat) =
            Q.params.ts (Q.params.slot D.resetTime + 2 * Q.params.k + 5 : Nat) +
              8 * Q.params.Δ := by
          simp only [SA.SAParams.ts]; push_cast; ring
        nlinarith)
    rw [Healing.cleanLabel_eq]
    omega
  refine ⟨Healing.cleanLabel Q.params D.resetTime + Q.params.k + 2, Q.params.slot Q.bound - 2,
    Compose.Growing.HandoverSeed.of_reset hreset (healthy_schedule_catch_at S A V Q D) rfl ?_
      (by omega) ⟨D.query + (4 * (Q.index : Time) + 6) * Q.params.Δ + 1, by linarith, ?_⟩⟩
  · have h : Q.params.ts ((Q.params.slot Q.bound - 2 : Nat) : Int) + 8 * Q.params.Δ =
        Q.params.ts (Q.params.slot Q.bound : Int) := by
      simp only [SA.SAParams.ts]; push_cast [show 2 ≤ Q.params.slot Q.bound by omega]; ring
    rw [h]
    exact (SA.ts_le_iff_le_slot Q.params hT0 _).mpr le_rfl
  · intro y n t ht htb hy hrp
    have hcover := healthy_current_record_sources_before_now_at S A V Q D O hrepair hrp htb hy
      (by linarith)
    rw [healthyRecordCoverAt_iff, D.cleanLabel_eq] at hcover
    rw [Compose.Growing.healedRecordCoverAt_iff]
    rcases hcover with h | ⟨x, q, s, C, CV, hx, hqn, hqt, hs, hC, hRC⟩
    · exact Or.inl h
    · exact Or.inr ⟨x, q, s, C, CV, hx, hqn, hqt, by omega, hC, hRC⟩

end Consensus.Goldilocks.Obligations.Growing

end

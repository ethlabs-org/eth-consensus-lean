module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.RunCommittee
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Frontier.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PreparationService
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.Sources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.SeedCall
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.RowService
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Local
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Family
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HSSharedRun
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.SignCalendar
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.SignGap
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Attest
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.HealedMembers
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.SignGap

public section

/-! # The hand-over seed

The healthy facts of a hand-over run up to the hand-over time `T`, packaged as the seed of the
continued label induction. The reset `a` comes from the healed-safety query healthy up to `T`.
The lock floor is `r = cleanLabel a + k + 2` and the origin floor is `r + k − 1 = cleanLabel a +
2k + 1` (`Healing/Frontier/Defs`). A split slot `σ` has every vote of a slot `≤ σ + 1` cast by `T`
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
The seed of a healed-safety query is `Continuation/SeedCover` (`handover_seed_cover_at`). -/

namespace Consensus.Goldilocks.Compose.Growing

open AC (ACParams Vote Payload)

variable {sp : ACParams}
variable {hold : Time}

variable {cm : Time → Finset (Fin sp.n)} {βK : ℚ}

/-- **The hand-over seed core**: the healthy facts up to `T` from the reset `a`, with the lock floor
`r = cleanLabel a + k + 2`, the origin floor `r + k − 1`, and the split slot `σ`.

* `reset`, `catchRun`: the reset premises up to `T` and the catch-up from GST.
* `timing`: every vote of a slot `≤ σ + 1` is cast before `T` (`t_σ + 8Δ ≤ T`); a vote of a slot
  after `σ` is at or after the drain (`r + k ≤ σ + 1`, `drainTime a = t_{r+k}`); the slot counts
  of the labels from `r` on start after GST.
* `frontier`: the healed family within `T` is pairwise compatible through the labels `≤ σ`, and
  extended by every honest vote up to `T` of a later slot `≤ σ + 1`.
* `rows`: a high FG row signed up to `T` by a node honest then and at `c_z` names an entry of its
  store below a family member.
* `seedHeld`: a high origin written up to `T` is in the frame of every honest call at a time in
  `[t_{r−k−3}, T]` whose finalized block it extends (`t_{r−k−3} = t_{slot a + 2} ≥ a + Δ`). -/
structure HandoverCore (tr : GoldilocksTrace sp) (H : Time → Set (Fin sp.n))
    (proposer : Nat → Fin sp.n) (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (g ΔF T : Time) (r σ : Nat)
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ} : Prop where
  reset : ∃ a hold, Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a T cm βK hold ∧
    r = Healing.cleanLabel sp a + sp.k + 2
  catchRun : Healing.Growing.CatchRun tr H g (2 * sp.Δ)
  timing : sp.ts σ + 8 * sp.Δ ≤ T ∧ r + sp.k ≤ σ + 1 ∧ AC.gbar g + 20 * sp.Δ ≤ sp.ts r
  frontier : HealedOriginsBelow tr H g r (r + sp.k - 1) (σ + 1) T ∧
    HealedVotesBelow tr H g r (r + sp.k - 1) (σ + 1) T
  rows : ∀ y k att, y ∈ H (max (Healing.cutZ sp.toParams g) (tr.time k)) → tr.SignAt y k att →
    tr.time k ≤ T →
    Healing.Growing.HZ tr H g + 1 ≤ att.h →
    ∃ C s, HealedOrigin tr H g r (r + sp.k - 1) C s T ∧ ∃ E ∈ (tr.state y k).fg.tree,
      E.root = att.T ∧ Anc (tr.HonestBlocksAt H) E C
  seedHeld : ∃ x i j B, Healing.Growing.HighOrigin tr H g x i j B ∧ tr.time i ≤ T ∧
    ∀ y c (ell : ACLabel (goldilocksNode sp)), y ∈ H (tr.time c) → tr.projAC.CallAt y c ell →
      sp.ts (r - sp.k - 3 : Nat) ≤ tr.time c → tr.time c ≤ T →
      Anc (tr.HonestBlocksAt H) ell.frame.F B → B ∈ ell.frame.tree

/-- **The hand-over seed**: the core (`HandoverCore`) and `covered`: from a time `t₁ ≤ T` on, the
record of every reader honest at a read point up to `T` is its finalized block or below an origin
of label `≥ r + k − 1` written before the read. The healed frontier (`healed_frontier_at`) needs
only the core. -/
structure HandoverSeed (tr : GoldilocksTrace sp) (H : Time → Set (Fin sp.n))
    (proposer : Nat → Fin sp.n) (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (g ΔF T : Time) (r σ : Nat)
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ} : Prop
    extends HandoverCore tr H proposer dg g ΔF T r σ (cm := cm) (βK := βK) where
  covered : ∃ t₁, t₁ ≤ T ∧ ∀ y n t, t₁ ≤ t → t ≤ T → y ∈ H t → Regimes.ReadPoint tr n t →
    HealedRecordCoverAt tr H (r + sp.k - 1) y n t
      ((AC.lookup (Node.frame (tr.state y n)) (tr.state y n).ac.latestConfirmed).getD
        (tr.state y n).fg.F)

variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-! ### Family members below origins, their supporters and their later votes -/

/-- The healed family unpacked into its three kinds of members. -/
private theorem healedOrigin_cases {rL rO : Nat} {C : AC.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (hC : HealedOrigin tr H g rL rO C s b) :
    (rO ≤ s ∧ ∃ x i CV, x ∈ H (tr.time i) ∧ tr.time i ≤ b ∧
      (AC.ResultAt tr.projAC x i s C CV ∨ AC.OptimisticLockAt tr.projAC x i s C CV)) ∨
    (rL ≤ s ∧ ∃ x i, x ∈ H (tr.time i) ∧ tr.time i ≤ b ∧
      ((∃ CV, AC.FastLockAt tr.projAC x i s C CV) ∨ AC.SlowLockAt tr.projAC x i s C)) ∨
    ∃ x i, tr.time i ≤ b ∧ Healing.Growing.HighOrigin tr H g x i s C := by
  rwa [healedOrigin_iff, originWithin_iff, lockWithin_iff] at hC

/-- Every member of the healed family is below an origin of its label, written by a node honest
at its cut, at a time `≤ b` (`HealedOrigin.below_origin`). -/
private theorem member_below_origin {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {rL rO : Nat} {C : AC.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (hC : HealedOrigin tr H g rL rO C s b) :
    ∃ x i O OV, x ∈ H (tr.time i) ∧ tr.time i ≤ b ∧
      (AC.ResultAt tr.projAC x i s O OV ∨ AC.OptimisticLockAt tr.projAC x i s O OV) ∧
      Anc (tr.HonestBlocksAt H) C O := by
  obtain ⟨O, hO, hCO⟩ := hC.below_origin hrun hnc
  obtain ⟨x, i, OV, hx, hib, hO⟩ := originWithin_iff.1 hO
  exact ⟨x, i, O, OV, hx, hib, hO, hCO⟩

/-- A block below an origin of a label after the high-origin cutoff has an honest supporting vote
of that slot, cast no later than the origin's cut. -/
private theorem origin_supporter
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x : Fin sp.n} {i s : Nat}
    {O C : AC.Blk sp.n (List (FG.Att sp.n))} {OV : Set (Vote sp.n)} (hx : x ∈ H (tr.time i))
    (hib : tr.time i ≤ b)
    (hO : AC.ResultAt tr.projAC x i s O OV ∨ AC.OptimisticLockAt tr.projAC x i s O OV)
    (hCO : Anc (tr.HonestBlocksAt H) C O) (hts : Healing.cutZ sp.toParams g ≤ sp.ts s) :
    ∃ z j e, z ∈ H (tr.time j) ∧ tr.time j ≤ b ∧ AC.VoteAt tr.projAC z j e ∧
      e.msg.slot = s ∧ AC.VoteExtends (tr.HonestBlocksAt H) e.msg C := by
  have hm := hp.run.time_mono
  rcases hO with hO | hO
  · obtain ⟨z, hz, j, hji, e, hv, -, hes, hCH⟩ :=
      Healing.Growing.ProposalImpl.result_supporter_at hp hx hO hCO hib hts
    exact ⟨z, j, e, hp.run.antitone (hm hji.le) hz, (hm hji.le).trans hib, hv, hes, hCH⟩
  · obtain ⟨-, z, j, hz, hji, e, hv, hes, Hd, hHd, he, hOH⟩ :=
      hp.optimistic_supporter_at hx hib (Healing.gbar_le_of_cutZ_le sp hts) hO
    exact ⟨z, j, e, hp.run.antitone (hm hji) hz, (hm hji).trans hib, hv, hes,
      Hd, hHd, he, hCO.trans hOH⟩

/-- **The `V` row of the healed family up to `b`**, at the hand-over floors: every honest vote at
a time `≤ b` of a later slot extends each member. Origins from `cleanLabel + 2k + 1`
(`clean_result_prefix_votes_before_at`, `fast_source_votes_before_at`), lock writes from
`cleanLabel + k + 2` (`fast_source_votes_before_at`, `slow_source_votes_before_at`), high origins
at every label (`high_origin_votes_before_at`). -/
private theorem member_votes {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {r : Nat}
    (hr : r = Healing.cleanLabel sp a + sp.k + 2) {C : AC.Blk sp.n (List (FG.Att sp.n))}
    {s : Nat} (hC : HealedOrigin tr H g r (r + sp.k - 1) C s b) :
    ∀ y i e, HVoteAt tr H y i e → tr.time i ≤ b → s < e.msg.slot →
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg C := by
  intro y i e hv hib hse
  obtain ⟨hy, ell, hcast⟩ := hVoteAt_iff.mp hv
  have hk := sp.two_le_k
  rcases healedOrigin_cases hC with ⟨hs, x, q, CV, hx, hqb, hO | hO⟩ | ⟨hs, x, q, hx, hqb,
    ⟨CV, hfl⟩ | hsl⟩ | ⟨x, q, hqb, ho⟩
  · exact hp.clean_result_prefix_votes_before_at hx hO .refl (by omega) hqb i hib y hy ell e
      hcast hse
  · exact hp.fast_source_votes_before_at hx (Or.inr hO) (by omega) hqb i hib y hy ell e
      hcast hse
  · exact hp.fast_source_votes_before_at hx hfl (by omega) hqb i hib y hy ell e hcast hse
  · exact hp.slow_source_votes_before_at hx hsl (by omega) hqb i hib y hy ell e hcast hse
  · exact hp.high_origin_votes_before_at i hib x q s C ho hqb y ell e hy hcast hse

/-- **The `P` row of the healed family up to `b`**, at the hand-over floors: any two members are
compatible. Two high origins compare by R1 (`origins_compatible_at`). Otherwise the larger label
is at least the lock floor, after the high-origin cutoff: for distinct labels the honest
supporter of the later member's origin extends both (the earlier member by its `V` row); for one
label the two underlying origins compare (`sources_same_label_compatible_at`) and each member is
below its origin. -/
private theorem member_compatible
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {r : Nat}
    (hr : r = Healing.cleanLabel sp a + sp.k + 2) {C C' : AC.Blk sp.n (List (FG.Att sp.n))}
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
      origin_supporter hp hx hib hO hCO (hts s' hrs)
    obtain ⟨Hd', hHd', he', hCH'⟩ := member_votes hp hr hC z j e
      (hVoteAt_iff.mpr ⟨hz, hv⟩) hjb (by omega)
    obtain rfl : Hd' = Hd := hU.1 hHd' hHd (he'.trans he.symm)
    exact AC.anc_total hU hCH' hCH
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
      · exact AC.anc_total hU (hCO.trans h) hCO'
      · exact AC.anc_total hU hCO (hCO'.trans h)
    · exact (ordered hC' hC hgt (by omega)).symm

/-! ### The seed from bounded reset premises -/

/-- **A high row signed after the drain is below a healed member** (fast or slow lock write, label
past the drain), through its own source: the signed target is the source's entry. -/
private theorem signed_row_on_healed_chain_at {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Growing.GoldilocksRun proposer dg H tr ini) (hnc : NoCollRun dg tr) {rO : Nat}
    {b : Time} {y : Fin sp.n} {k : Nat} {att : FG.Att sp.n} (hy : y ∈ H (tr.time k))
    (hs : tr.SignAt y k att) (hdk : Healing.drainTime sp a ≤ tr.time k) (hkb : tr.time k ≤ b) :
    ∃ C s, HealedOrigin tr H g (Healing.cleanLabel sp a + sp.k + 2) rO C s b ∧
      ∃ E ∈ (tr.state y k).fg.tree, E.root = att.T ∧ Anc (tr.HonestBlocksAt H) E C := by
  obtain ⟨src, hcall⟩ := hs
  obtain ⟨j, rfl, ℓ, hcj, hcl, htj, hC, hfg⟩ := attest_source hrun hy hcall
  have hyj : y ∈ H (tr.time j) := htj ▸ hy
  have hto : AC.ToFGAt tr.projAC y j ℓ src :=
    ⟨Compose.projAC_callAt.mpr hcj, hcl, by rw [projAC_state_at hrun hyj]; exact hC⟩
  obtain ⟨C, s, hCo, hsC⟩ := onHealedChain_iff.1 (deep_source_on_healed_chain_at (rO := rO)
    hrun hnc hyj (htj ▸ hdk) (htj ▸ hkb) hto)
  have hsk : src ∈ (tr.state y (j + 1)).fg.tree := by
    rw [hfg]; exact Healing.Growing.toFG_mem_tree_at hrun hyj hto
  have hT := Compose.createAtt_T (hrun.cutLaw y (j + 1) _ hcall hy).1
  have h0 := hrun.time_nonneg (j + 1)
  have hle : ∀ q < j + 1, tr.time q ≤ tr.time (j + 1) := fun _ h => hrun.time_mono h.le
  obtain ⟨⟨E, hE, hEr, hEs, -, hET⟩, -⟩ := Goldilocks.Store.entry_state_of_source _ _ _ _
    (Healing.Growing.fg_reachable_at hrun h0 hle hy) _ hsk
  rw [← hEr, hET] at hT
  exact ⟨C, s, hCo, E, hE, hEr.trans hT.symm,
    (Healing.Growing.honest_anc_of_store_anc_at h0 hle hy hEs).trans hsC⟩

/-- **The hand-over seed from bounded reset premises.** Reset premises up to `T`, the catch-up,
the split-slot timing and the record cover give the seed: the frontier is the reset cluster's
`P`/`V` rows for the healed family; the rows are `high_row_source_at`; the held seed is
`reset_seed_held_at_call_at` (`t_{slot a + 2} ≥ a + Δ`); the count start follows from
`c_z < a`. -/
theorem HandoverCore.of_reset {T : Time} {r σ : Nat}
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a T cm βK hold)
    (hr : r = Healing.cleanLabel sp a + sp.k + 2)
    (hσ : sp.ts σ + 8 * sp.Δ ≤ T) (hrσ : r + sp.k ≤ σ + 1) :
    HandoverCore tr H proposer dg g ΔF T r σ (cm := cm) (βK := βK) := by
  have hrun := hp.run
  have hΔ := sp.toParams.hΔ
  have hca := hp.cutZ_lt_reset_at
  have hgz := Healing.lt_cutZ sp g
  have ha0 : 0 ≤ a := by linarith [AC.gbar_nonneg g]
  have hsa : a < sp.ts ((sp.slot a : Int) + 1) := not_le.1 fun h => by
    have := (AC.ts_le_iff_le_slot sp ha0 _).1 h
    omega
  have hts (s j : Nat) : sp.ts (s + j : Nat) = sp.ts ((sp.slot a : Int) + 1) +
      4 * sp.Δ * ((s : Int) + j - (sp.slot a + 1)) := by
    simp only [ACParams.ts]; push_cast; ring
  refine ⟨⟨a, _, hp, hr⟩, hp.catchUp, ⟨hσ, hrσ, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · have h := hts (sp.slot a + 1) (sp.k + 4)
    rw [show sp.slot a + 1 + (sp.k + 4) = r by rw [hr, Healing.cleanLabel_eq]; omega] at h
    rw [h]
    have hk : (0 : Time) ≤ sp.k := Nat.cast_nonneg _
    push_cast
    linarith [mul_nonneg (show (0 : Time) ≤ 4 * sp.Δ by linarith) hk]
  · rw [healedOriginsBelow_iff]
    intro C j C' j' _ _ hC hC'
    exact member_compatible hp hr hC hC'
  · rw [healedVotesBelow_iff]
    intro C j hC y i e hv hib hje _
    exact member_votes hp hr hC y i e hv hib hje
  · intro y k att hyz hs hkT hh
    -- past the deep quarantine the cover ends it after the drain: a healed member by the
    -- signing's own lock source; inside it the reset cluster's high row
    by_cases hq : ∀ D, sp.deepDepth = some D →
        tr.time k ≤ Healing.cutZ sp.toParams g + 4 * D * sp.Δ
    swap
    · push Not at hq
      obtain ⟨D, hD, hlt⟩ := hq
      rcases hp.deepCover D hD with hbq | hc
      · exact absurd (hkT.trans hbq) (not_le.2 hlt)
      have := hc.drain_le D hD
      rw [hr]
      exact signed_row_on_healed_chain_at hrun hp.noColl
        (hrun.antitone (le_max_right _ _) hyz) hs (by linarith) hkT
    obtain ⟨q, hqk, l, O, ho, E, hE, hEO, hEr, -⟩ := hp.high_row_source_at hyz hs hh hq
    have hqT := (hrun.time_mono hqk.le).trans hkT
    refine ⟨O, l, HealedOrigin.of_high hqT ho, E,
      tree_mono_at hrun (hrun.time_nonneg k) (hrun.antitone (le_max_right _ _) hyz)
        (fun _ h => hrun.time_mono h.le) hqk.le hE, hEr,
      hEO.mono fun _ h => ⟨y, q, tr.time q, hrun.time_nonneg q,
        fun _ h' => hrun.time_mono h'.le, hrun.antitone (le_max_right _ _) ho.1, h⟩⟩
  · obtain ⟨v, q, l, S, hS, -, hqT, hheld⟩ := hp.reset_seed_held_at_call_at
    refine ⟨v, q, l, S, hS, hqT, fun y c ell hy hcall hc0 hcT hF =>
      hheld y c ell hy hcall ?_ hcT hF⟩
    have h := hts (sp.slot a + 1) 1
    rw [show sp.slot a + 1 + 1 = r - sp.k - 3 by rw [hr, Healing.cleanLabel_eq]; omega] at h
    rw [h] at hc0
    push_cast at hc0
    linarith

/-- **The hand-over seed from bounded reset premises and the record cover**
(`HandoverCore.of_reset`). -/
theorem HandoverSeed.of_reset {T : Time} {r σ : Nat}
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a T cm βK hold)
    (hr : r = Healing.cleanLabel sp a + sp.k + 2)
    (hσ : sp.ts σ + 8 * sp.Δ ≤ T) (hrσ : r + sp.k ≤ σ + 1)
    (hcov : ∃ t₁, t₁ ≤ T ∧ ∀ y n t, t₁ ≤ t → t ≤ T → y ∈ H t → Regimes.ReadPoint tr n t →
      HealedRecordCoverAt tr H (r + sp.k - 1) y n t
        ((AC.lookup (Node.frame (tr.state y n)) (tr.state y n).ac.latestConfirmed).getD
          (tr.state y n).fg.F)) :
    HandoverSeed tr H proposer dg g ΔF T r σ (cm := cm) (βK := βK) :=
  ⟨HandoverCore.of_reset hp hr hσ hrσ, hcov⟩

/-- **After the drain, every live lock at an honest vote of a slot after `σ` has label at least
`r`.** The vote is in its own slot (`castAt_spec_at`), at least `r + k`, so at or after
`drainTime a = t_{r+k}`; the read point's locks expire at most `k` slots after their labels
(`castAt_readPoint_locksWF`), so `drain_live_locks` applies. -/
theorem handover_live_lock_label_at {T : Time} {r σ : Nat}
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hseed : HandoverCore tr H proposer dg g ΔF T r σ (cm := cm) (βK := βK))
    {y : Fin sp.n} {i : Nat} {ℓ : ACLabel (goldilocksNode sp)}
    {e : AC.Em sp (List (FG.Att sp.n))}
    (hy : y ∈ H (tr.time i)) (hc : AC.CastAt tr.projAC y i ℓ e) (hs : σ < e.msg.slot) :
    ∀ l ∈ AC.liveLocks sp e.readPoint.locks ℓ.frame (tr.time i), r ≤ l.slot := by
  obtain ⟨a, _, hp, hr⟩ := hseed.reset
  have hrσ := hseed.timing.2.1
  have hrun := hp.run
  have hnc := hp.noColl
  have hd := hrun.time_nonneg i
  have hsl : e.msg.slot = sp.slot (tr.time i) := (castAt_spec_at hrun hnc hy hc).2.1
  have hdrain : Healing.drainTime sp a ≤ tr.time i := by
    rw [Healing.drainTime_eq]
    refine (AC.ts_le_iff_le_slot sp hd _).mpr ?_
    rw [hr, Healing.cleanLabel_eq] at hrσ
    push_cast
    omega
  have hwf := AC.castAt_readPoint_locksWFU (hr := (acRun_upTo hrun hnc hd).localRun.toU)
    hrun.vstart hy (ac_castAt_upTo.mpr ⟨le_rfl, hc⟩)
  intro l hl
  rw [hr]
  exact Healing.drain_live_locks (a := a) hwf hdrain l hl

end Consensus.Goldilocks.Compose.Growing


end

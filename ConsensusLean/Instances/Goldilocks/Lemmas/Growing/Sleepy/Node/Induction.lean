module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.VotesBelow
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Compare

public section

/-! # Goldilocks under `Sleepy` with growing faults: the record invariant up to `b`

The bounded frontier under growing faults, over the healed family from the floors `rL`, `rO`:
from a seed `P_{s₀}`, `V_{s₀}`, the steps `P_s, V_s ⊢ P_{s+1}` (`origins_below_succ_at`) and
`P_{s+1}, V_s ⊢ V_{s+1}` (`votes_below_succ_at`) give every finite frontier (`frontier_at`),
given the slot counts and the service from `s₀`, the live locks of the votes after `s₀` from the
lock floor on, and the frozen witness at those votes from `P` up to their slot. From genesis
(floors `0`, `s₀ = 0`) the seed is vacuous and the frozen witness is `vote_frame_at`. With the
provenance of records, caches, locks and sources, and full viability at the read time, this is
`SleepyInvariantUpTo` (`sleepy_invariant_at`). Every quantifier of the induction ranges over events
of nodes honest at them, so a later compromise removes nothing from it. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-! ### The frontier and the invariant -/

/-- **Every finite frontier up to `b` from a seed** under growing faults, over the healed family
from the floors `rL`, `rO ≤ s₀`: the seed `P_{s₀}`, `V_{s₀}`; the committee slot counts from
`σ₀ ≤ s₀` and the service from `a` (`a + κ ≤ t_{s₀}`); at every honest vote of a slot
`s + 1 > s₀`, the live locks of slot at most `s` from the lock floor on (`hlive`), and, given
`P_{s+1}`, the frozen witness for a member of label at most `s` with an honest slot-`s` supporter
(`hframe`). -/
theorem frontier_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {K : SA.CommitteeDict sp.n} (hKB : CommitteeFacts tr H K)
    {a κ b : Time} (hsync : SleepyServiceFrom tr H ΔF a κ b) {σ₀ : Nat}
    (hBK : CommitteeBoundsFrom tr H K σ₀ b) {g : Time} {rL rO s₀ : Nat} (hσ₀ : σ₀ ≤ s₀)
    (hrO : rO ≤ s₀) (hsa : a + κ ≤ sp.ts s₀)
    (hlive : ∀ s, s₀ ≤ s → ∀ y i ℓ e, y ∈ H (tr.time i) → SA.CastAt tr.projAC y i ℓ e →
      e.msg.slot = s + 1 → tr.time i ≤ b →
      ∀ l ∈ SA.liveLocks sp e.readPoint.locks ℓ.frame (tr.time i), l.slot ≤ s → rL ≤ l.slot)
    (hframe : ∀ s, s₀ ≤ s → HealedOriginsBelow tr H g rL rO (s + 1) b →
      ∀ y i ℓ e, y ∈ H (tr.time i) → SA.CastAt tr.projAC y i ℓ e → e.msg.slot = s + 1 →
      tr.time i ≤ b → ∀ B j, HealedOrigin tr H g rL rO B j b → j ≤ s →
      (∃ x k e', HVoteAt tr H x k e' ∧ e'.msg.slot = s ∧
        SA.VoteExtends (tr.HonestBlocksAt H) e'.msg B) →
      B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame (s + 1)) ∨
        Anc (tr.HonestBlocksAt H) B ℓ.frame.fcRoot)
    (hseed : HealedOriginsBelow tr H g rL rO s₀ b ∧ HealedVotesBelow tr H g rL rO s₀ b) :
    ∀ s, HealedOriginsBelow tr H g rL rO s b ∧ HealedVotesBelow tr H g rL rO s b := by
  have ha : a ≤ sp.ts s₀ := (le_add_of_nonneg_right hsync.kappa).trans hsa
  have step : ∀ n, HealedOriginsBelow tr H g rL rO (s₀ + n) b ∧
      HealedVotesBelow tr H g rL rO (s₀ + n) b := by
    intro n
    induction n with
    | zero => exact hseed
    | succ n ih =>
      have hs : s₀ ≤ s₀ + n := Nat.le_add_right _ _
      have hts := ts_le_ts (sp := sp) hs
      have hP := origins_below_succ_at hrun hnc hKB hsync hBK (hσ₀.trans hs) (ha.trans hts)
        ih.1 ih.2
      exact ⟨hP, votes_below_succ_at hrun hnc hKB hsync hBK (hσ₀.trans hs) (hrO.trans hs)
        (hsa.trans hts) (hlive _ hs) (hframe _ hs hP) hP ih.2⟩
  intro s
  rcases le_total s s₀ with h | h
  · exact ⟨hseed.1.of_le h, hseed.2.of_le h⟩
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
    exact step n

/-- **S3 at a held origin, read at `t`**: a reader honest at `t ∈ [0, b]` (every earlier cut at or
before `t`), holding a block compatible with every origin before the cut, when the origins within
`t` are pairwise compatible (`held_origin_viable_before` on the prefix through `t`). -/
private theorem held_origin_viable_read {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {i : Nat} {t : Time} (ht0 : 0 ≤ t)
    (hi : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t) (hf : 2 * (H t)ᶜ.ncard < sp.n)
    (hP : ∀ C s C' s', OriginWithin tr H C s t → OriginWithin tr H C' s' t →
      Compatible (tr.HonestBlocksAt H) C C')
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBc : ∀ C s, OriginBefore tr H C s i → Compatible (tr.HonestBlocksAt H) B C)
    (hBt : B ∈ (Node.frame (tr.state y i)).tree) :
    (Node.frame (tr.state y i)).Anc B (Node.frame (tr.state y i)).fcRoot ∨
      B ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree := by
  have hst := Trace.upTo_state tr y (d := t) hi
  have hBU : B ∈ (tr.upTo t).HonestBlocks (H t) := ⟨y, hy, i, by rw [hst]; exact hBt.1⟩
  have h := held_origin_viable_before (hrun.upTo ht0) (hnc.upTo _) (b := t) hf
    (fun _ => Compose.originsBelowUpTo_iff.2 fun C j C' j' _ _ hC hC' =>
      compatible_upTo hrun hnc ht0 (originWithin_upTo_mem hrun hC)
        (originWithin_upTo_mem hrun hC')
        (hP C j C' j' (originWithin_of_upTo hrun hC) (originWithin_of_upTo hrun hC')))
    hy i hi
    (fun C s hC => by
      have hCw := hC.within (b := t) hi
      exact compatible_upTo hrun hnc ht0 hBU (originWithin_upTo_mem hrun hCw)
        (hBc C s (originBefore_of_upTo hrun hC)))
    (by rw [hst]; exact hBt)
  rwa [hst] at h

/-- **The healed frontier from genesis**: the floors `0` and the seed label `0` (vacuous seed),
with the frozen witness `vote_frame_at`; every origin is a member. -/
private theorem frontier_zero_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {K : SA.CommitteeDict sp.n} (hKB : CommitteeFacts tr H K) {b : Time}
    (hb : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b) (hB : SleepyBoundsFrom tr H 0 b)
    (hBK : CommitteeBoundsFrom tr H K 0 b) (g : Time) :
    ∀ s, HealedOriginsBelow tr H g 0 0 s b ∧ HealedVotesBelow tr H g 0 0 s b := by
  refine frontier_at hrun hnc hKB (hsync.toFrom hrun) hBK le_rfl le_rfl
    (by rw [add_zero]; exact ts_natCast_nonneg 0) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => Nat.zero_le _)
    (fun s _ hP y i ℓ e hy hc hs hib B j hBm hj hw => ?_)
    ⟨healedOriginsBelow_iff.2 fun _ _ _ _ h => absurd h (Nat.not_lt_zero _),
      healedVotesBelow_iff.2 fun _ _ _ _ _ _ _ _ h₁ h₂ => by omega⟩
  have hP' := healedOriginsBelow_iff.1 hP
  refine vote_frame_at hrun hnc hKB hb hsync hB hBK
    (originsBelowUpTo_iff.2 fun C j C' j' hj hj' hC hC' =>
      hP' C j C' j' hj hj' (.of_origin (Nat.zero_le _) hC) (.of_origin (Nat.zero_le _) hC'))
    hy hc hs hib (hBm.mem hrun hnc)
    (fun C j' hC hj' => hP' B j C j' (by omega) (by omega) hBm (.of_origin (Nat.zero_le _) hC)) hw

/-- **The Sleepy record invariant up to `b` under growing faults** (S1–S3), from the finite
service, the count shapes and the committee count shapes through `b`: the healed frontier from
genesis (`frontier_zero_at`) restricted to the origins. -/
theorem sleepy_invariant_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {K : SA.CommitteeDict sp.n} (hKB : CommitteeFacts tr H K) {b : Time}
    (hb : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b) (hB : SleepyBoundsFrom tr H 0 b)
    (hBK : CommitteeBoundsFrom tr H K 0 b) : SleepyInvariantUpTo tr H b := by
  have hF := frontier_zero_at hrun hnc hKB hb hsync hB hBK 0
  have hcomp : ∀ C s C' s', OriginWithin tr H C s b → OriginWithin tr H C' s' b →
      Compatible (tr.HonestBlocksAt H) C C' := fun C s C' s' h h' =>
    healedOriginsBelow_iff.1 (hF (max s s' + 1)).1 C s C' s' (by omega) (by omega)
      (.of_origin (Nat.zero_le _) h) (.of_origin (Nat.zero_le _) h')
  refine ⟨hcomp, fun C s hC y i e he hib hs => ?_,
    fun y i t ht0 hi htb hy => record_origin_at hrun hnc ht0 hi htb hy,
    fun y i t ht0 hi htb hy => caches_on_chain_at hrun hnc ht0 hi htb hy (hB.two t ht0 htb),
    fun y i t ht0 hi htb hy l hl => ?_,
    fun y i hy hi ℓ C h => source_on_chain_at hrun hnc hy hi h,
    fun y i t ht0 hi htb hy C s hC hCt => held_origin_viable_read hrun hnc ht0 hi hy
      (hB.two t ht0 htb) (fun C₁ s₁ C₂ s₂ h₁ h₂ => hcomp C₁ s₁ C₂ s₂ (h₁.mono htb) (h₂.mono htb))
      (fun C' s' hC' => hcomp C s C' s' hC (hC'.within fun k hk => (hi k hk).trans htb)) hCt⟩
  · exact healedVotesBelow_iff.1 (hF e.msg.slot).2 C s (.of_origin (Nat.zero_le _) hC) y i e he
      hib hs le_rfl
  · obtain ⟨L, hL, hLr, D, hD, hLD⟩ := lock_write_at hrun hnc ht0 hi hy l hl
    obtain ⟨C, hC, hDC⟩ := hD.below_origin hrun hnc
    exact ⟨L, hL, hLr, onOriginChainWithin_iff.2 (Or.inr ⟨C, l.slot, hC.mono htb,
      hLD.trans hDC⟩)⟩

end Consensus.Goldilocks.Compose.Growing

end

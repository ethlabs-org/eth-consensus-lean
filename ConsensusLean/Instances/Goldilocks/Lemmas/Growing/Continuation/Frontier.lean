module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Continuation.Seed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Continuation.VoteFrame
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Induction
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Continuation.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Family
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ProposalService
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The healed frontier after a hand-over

The sleepy label induction (`frontier_at`) run from the hand-over seed instead of genesis, over the
healed family at the floors `(r, r + k − 1)`, through any bound `b ≥ T`.

* `HandoverSeed.frontier_upTo`: the seed's frontier through `σ + 1` up to `T` is the frontier
  through `σ + 1` up to every `b ≥ T`: every family member of label `≤ σ` is written by
  `t_σ + 6Δ ≤ T`, and every vote of a slot `≤ σ + 1` is cast before `t_{σ+2} = t_σ + 8Δ ≤ T`.
* `healed_frontier_at`: `frontier_at` from `s₀ = σ + 1` with the counts from `r`, the service
  from `ḡ` (`ḡ + 2Δ ≤ t_r ≤ t_{σ+1}`), the drain bound on the live locks
  (`handover_live_lock_label_at`) and the seeded frozen witness (`seeded_vote_frame_at`). -/

namespace Consensus.Goldilocks.Compose.Growing

open AC (ACParams ReplayOrder Vote Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

variable {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}
  {ini : Fin sp.n → (goldilocksNode sp ro).State} {g ΔF : Time}

/-! ### The seed through `b` -/

/-- An optimistic selection of slot `s` is made before `t_{s+1} = t_s + 4Δ`. -/
private theorem optimistic_time_lt (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    {x : Fin sp.n}
    {i s : Nat} {C : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (h : AC.OptimisticLockAt tr.projAC x i s C CV) : tr.time i < sp.ts s + 4 * sp.Δ := by
  obtain ⟨-, -, -, hsl, -⟩ := h
  have hts : sp.ts ((s + 1 : Nat) : Int) = sp.ts s + 4 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  rw [← hts]
  refine lt_of_not_ge fun hge => ?_
  have := (AC.ts_le_iff_le_slot sp (hrun.time_nonneg i) _).1 hge
  change sp.slot (tr.time i) = s at hsl
  omega

/-- A fast lock write of label `s` is written by `t_s + 6Δ`. -/
private theorem fastLockAt_time_le (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    {x : Fin sp.n}
    {i s : Nat} {C : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (h : AC.FastLockAt tr.projAC x i s C CV) : tr.time i ≤ sp.ts s + 6 * sp.Δ := by
  rcases h with ⟨ℓ, C', hu, -⟩ | h
  · exact hu.2.2.1.le
  · linarith [optimistic_time_lt hrun h, sp.toParams.hΔ]

/-- **A member of label `s` is written by `t_s + 6Δ`**: it is a member within every bound from
there on. -/
private theorem HealedOrigin.within_label (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    {rL rO : Nat} {C : AC.Blk sp.n (List (FG.Att sp.n))} {s : Nat} {b T : Time}
    (hC : HealedOrigin tr H g rL rO C s b) (hT : sp.ts s + 6 * sp.Δ ≤ T) :
    HealedOrigin tr H g rL rO C s T := by
  rcases healedOrigin_iff.1 hC with ⟨hs, h⟩ | ⟨hs, h⟩ | ⟨x, i, -, ho⟩
  · obtain ⟨x, i, CV, hx, -, hO⟩ := originWithin_iff.1 h
    have hi : tr.time i ≤ sp.ts s + 6 * sp.Δ := by
      rcases hO with ⟨ℓ, hu, -⟩ | hO
      · exact hu.2.2.1.le
      · linarith [optimistic_time_lt hrun hO, sp.toParams.hΔ]
    exact .of_origin hs (originWithin_iff.2 ⟨x, i, CV, hx, hi.trans hT, hO⟩)
  · obtain ⟨x, i, hx, -, hw⟩ := lockWithin_iff.1 h
    have hi : tr.time i ≤ sp.ts s + 6 * sp.Δ := by
      rcases hw with ⟨CV, hw⟩ | ⟨ℓ, C', hu, -⟩
      · exact fastLockAt_time_le hrun hw
      · exact hu.2.2.1.le
    exact .of_lock hs (lockWithin_iff.2 ⟨x, i, hx, hi.trans hT, hw⟩)
  · obtain ⟨CV, -, D, -, hfl, -⟩ := ho.2.2.1
    exact .of_high ((fastLockAt_time_le hrun hfl).trans hT) ho

/-- An honest vote of slot `m` is cast before `t_{m+1}`. -/
private theorem vote_time_lt (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {i : Nat} {e : AC.Em sp (List (FG.Att sp.n))}
    (hv : HVoteAt tr H y i e) : tr.time i < sp.ts ((e.msg.slot + 1 : Nat) : Int) := by
  obtain ⟨hy, ℓ, hc⟩ := hVoteAt_iff.1 hv
  have h := (castAt_spec_at hrun hnc hy hc).2.1
  refine lt_of_not_ge fun hge => ?_
  have := (AC.ts_le_iff_le_slot sp (hrun.time_nonneg i) _).1 hge
  push_cast at this
  omega

/-- **The seed's frontier holds through any bound `b ≥ T`**: every member of a label `≤ σ` is
written by `t_σ + 6Δ ≤ T`, and every honest vote of a slot `≤ σ + 1` is cast before
`t_{σ+2} = t_σ + 8Δ ≤ T`. -/
theorem HandoverSeed.frontier_upTo (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {T : Time} {r σ : Nat}
    (hseed : HandoverSeed tr H proposer dg g ΔF T r σ (cm := cm) (βK := βK)) {b : Time} :
    HealedOriginsBelow tr H g r (r + sp.k - 1) (σ + 1) b ∧
      HealedVotesBelow tr H g r (r + sp.k - 1) (σ + 1) b := by
  have hT := hseed.timing.1
  have hΔ := sp.toParams.hΔ
  have hdown : ∀ C j, HealedOrigin tr H g r (r + sp.k - 1) C j b → j < σ + 1 →
      HealedOrigin tr H g r (r + sp.k - 1) C j T := fun C j hC hj =>
    hC.within_label hrun (by linarith [ts_le_ts (sp := sp) (show j ≤ σ by omega)])
  have hts2 : sp.ts ((σ + 2 : Nat) : Int) = sp.ts σ + 8 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  refine ⟨healedOriginsBelow_iff.2 fun C j C' j' hj hj' hC hC' =>
    healedOriginsBelow_iff.1 hseed.frontier.1 C j C' j' hj hj' (hdown C j hC hj)
      (hdown C' j' hC' hj'), healedVotesBelow_iff.2 fun C j hC y i e hv _ hj hm => ?_⟩
  refine healedVotesBelow_iff.1 hseed.frontier.2 C j (hdown C j hC (by omega)) y i e hv ?_ hj hm
  have h := vote_time_lt hrun hnc hv
  have := ts_le_ts (sp := sp) (show e.msg.slot + 1 ≤ σ + 2 by omega)
  linarith

/-! ### The healed frontier -/

/-- The committee counts from `σ₀` give the committee counts from every `σ₁ ≥ σ₀`. -/
private theorem CommitteeBoundsFrom.of_le {K : AC.CommitteeDict sp.n} {σ₀ σ₁ : Nat} {b : Time}
    (h : CommitteeBoundsFrom tr H K σ₀ b) (hσ : σ₀ ≤ σ₁) : CommitteeBoundsFrom tr H K σ₁ b :=
  ⟨fun s d hs => h.slotK s d (hσ.trans hs), fun s d hs => h.twoK s d (hσ.trans hs)⟩

/-- **The healed frontier from the floor through the horizon** (at the floors
`(r, r + k − 1)`): from the hand-over seed, with the reset service and the slot counts
from `r` through `b ≥ T`, every finite frontier of the healed family holds up to `b`. The label
induction (`frontier_at`) starts at `σ + 1`: the seed's frontier holds up to `b`
(`HandoverSeed.frontier_upTo`); `r + k − 1 ≤ σ + 1`; the service is the sleepy service from `ḡ`
with the seed's catch-up (`sleepyServiceFrom_of_reset`, `ḡ + 2Δ ≤ t_r ≤ t_{σ+1}`); the live locks
at the votes after `σ` have labels `≥ r` (`handover_live_lock_label_at`); the frozen witness is
`seeded_vote_frame_at`. -/
theorem healed_frontier_at (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {T : Time} {r σ : Nat} (hseed : HandoverSeed tr H proposer dg g ΔF T r σ (cm := cm) (βK := βK))
      {b : Time}
    (hTb : T ≤ b) (hsvc : Healing.Growing.ACResetService tr H g ΔF)
    (hB : SleepyBoundsFrom tr H r b) (hcv : ChainConvictedBelow tr H)
    {K : AC.CommitteeDict sp.n} (hK : CommitteeFacts tr H K)
    (hKB : CommitteeBoundsFrom tr H K r b) :
    ∀ s, HealedOriginsBelow tr H g r (r + sp.k - 1) s b ∧
      HealedVotesBelow tr H g r (r + sp.k - 1) s b := by
  have hΔ := sp.toParams.hΔ
  obtain ⟨-, hrσ, hgr⟩ := hseed.timing
  have hsync := sleepyServiceFrom_of_reset hrun hsvc hseed.catchRun (b := b) (by linarith)
  have htr := ts_le_ts (sp := sp) (show r ≤ σ + 1 by omega)
  refine frontier_at hrun hnc hK hsync (hKB.of_le (show r ≤ σ + 1 by omega)) le_rfl (by omega)
    (by linarith) (fun s hs y i ℓ e hy hc hes _ l hl _ =>
      handover_live_lock_label_at hseed hy hc (by omega) l hl)
    (fun s hs hP y i ℓ e hy hc hes hib B j hBm hj hw =>
      seeded_vote_frame_at hrun hnc hseed hTb hsvc hB hcv hs hP hy hc hes hib hBm hj hw hK hKB)
    (hseed.frontier_upTo hrun hnc)

end Consensus.Goldilocks.Compose.Growing

end

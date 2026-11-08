module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Continuation.Seed
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Local
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The held reset seed past the hand-over

The hand-over seed holds its reset seed `S` (a high origin written by `T`) in the frame of every
honest call at a time in `[t_{r−k−3}, T]` whose finalized block it extends. Past `T` no healthy
relay is needed: a node honest at a later call `c` was honest at `t_{r−k−3} ≤ T`, and awake then
(the reset premises keep every honest node awake on `[ḡ, T]`), so it ticks at `t_{r−k−3}`, an
earlier call `c₀`. Its finalized block only grows, so `Σ.F` at `c₀` is below `Σ.F` at `c`, hence
below `S`, and the bounded field puts `S` in the frame at `c₀`. The FG tree only grows along the
node's run, so `S` is in the tree at `c`, and the frame there holds every tree block above its
`Σ.F`.

* `Compose.Growing.seed_held_through_at`: the held seed through any `b ≥ T`. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF : Time}

/-- **The held seed through `b ≥ T`**: the seed's high origin `S` is in the frame of every honest
call at a time in `[t_{r−k−3}, b]` whose `Σ.F` it extends. Up to `T` this is the seed's bounded
field. After `T`, the caller's tick at `t_{r−k−3}` is an earlier call whose `Σ.F` is below the
later one, hence below `S`; there `S` is in the frame, so in the FG tree, which only grows. -/
theorem seed_held_through_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {T : Time} {r σ : Nat}
    (hseed : HandoverSeed tr H proposer dg g ΔF T r σ) {b : Time} (hTb : T ≤ b) :
    ∃ x i j B, Healing.Growing.HighOrigin tr H g x i j B ∧ tr.time i ≤ b ∧
      ∀ y c (ell : ACLabel (goldilocksNode sp ro)), y ∈ H (tr.time c) →
        tr.projAC.CallAt y c ell → sp.ts (r - sp.k - 3 : Nat) ≤ tr.time c → tr.time c ≤ b →
        Anc (tr.HonestBlocksAt H) ell.frame.F B → B ∈ ell.frame.tree := by
  obtain ⟨x, i, j, B, hB, hiT, hheld⟩ := hseed.seedHeld
  refine ⟨x, i, j, B, hB, hiT.trans hTb, fun y c ell hy hcall hc0 _ hF => ?_⟩
  rcases le_or_gt (tr.time c) T with hcT | hTc
  · exact hheld y c ell hy hcall hc0 hcT hF
  obtain ⟨a, hp, hr⟩ := hseed.reset
  obtain ⟨hσT, hrσ, -⟩ := hseed.timing
  have hΔ := sp.toParams.hΔ
  -- the tick time `u = t_{r−k−3} = t_{slot a + 2}` is after `ḡ` and at most `T`
  set u := sp.ts (r - sp.k - 3 : Nat) with hu_def
  have hca := hp.cutZ_lt_reset_at
  have hgz := Healing.lt_cutZ sp g
  have ha0 : 0 ≤ a := by linarith [SA.gbar_nonneg g]
  have hsa : a < sp.ts ((sp.slot a : Int) + 1) := not_le.1 fun h => by
    have := (SA.ts_le_iff_le_slot sp ha0 _).1 h
    omega
  have hgu : SA.gbar g ≤ u := by
    have hu : u = sp.ts ((sp.slot a : Int) + 1) + 4 * sp.Δ := by
      rw [hu_def, show r - sp.k - 3 = sp.slot a + 1 + 1 by rw [hr, Healing.cleanLabel_eq]; omega]
      simp only [SAParams.ts]; push_cast; ring
    linarith
  have huT : u ≤ T := by
    have h := ts_le_ts (sp := sp) (show r - sp.k - 3 ≤ σ by omega)
    linarith
  have hu0 : 0 ≤ u := ts_natCast_nonneg _
  have hpub : sp.toParams.IsPublic u :=
    ⟨4 * ((r - sp.k - 3 : Nat) : Int), by simp only [hu_def, SAParams.ts]; ring⟩
  -- the caller ticks at `u`, an earlier call
  have hyu : y ∈ H u := hrun.antitone (huT.trans hTc.le) hy
  obtain ⟨c₀, z, hg⟩ := hrun.tick_of_awake y u hyu hu0 hpub (hp.awake y u hyu hgu huT)
  obtain ⟨hc₀, htc₀⟩ := Healing.tick_first_cut hg
  have hcall₀ := Compose.projAC_callAt.2 hc₀
  have hy₀ : y ∈ H (tr.time c₀) := by rw [htc₀]; exact hyu
  have hc₀c : c₀ ≤ c := by
    by_contra h
    have := hrun.time_mono (Nat.le_of_not_le h)
    linarith
  have hd := hrun.time_nonneg c
  have hi : ∀ k < c, tr.time k ≤ tr.time c := fun _ hk => hrun.time_mono hk.le
  have hfr := frame_of_projAC_at hrun hy hcall
  have hfr₀ := frame_of_projAC_at hrun hy₀ hcall₀
  -- `Σ.F` at `c₀` is below `Σ.F` at `c`, hence below the seed
  have hFc : Anc (tr.HonestBlocksAt H) (tr.state y c).fg.F B := by
    rw [hfr] at hF
    exact hF
  have hF₀ : Anc (tr.HonestBlocksAt H) _ B := (F_mono_at hrun hd hy hi hc₀c).trans hFc
  have hB₀ := hheld y c₀ _ hy₀ hcall₀ htc₀.ge (htc₀.le.trans huT) (by rw [hfr₀]; exact hF₀)
  have hBc := tree_mono_at hrun hd hy hi hc₀c
    ((Healing.Growing.frame_tree_subset_at hrun hnc hy₀ hcall₀).2 hB₀)
  rw [hfr]
  exact frame_mem_of_tree_at hrun hnc hd hy hi hBc hFc

end Consensus.Goldilocks.Compose.Growing

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.FrameWindowExists
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.M1.FrameLag
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameLag
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Quorum
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Finality
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FGProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.HeldSafety
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.HeldSafetyAt
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.StoreCache
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameLagCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameWindowCore
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Safety
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Step 2 of the growing drain kernel: a frame window from per-cut service

`exists_frameWindow_seq_of_service_proof_at`: per-cut height range and relay calls give a frame
window (`FrameWindow`) of the requested length. The sequential pigeonhole
(`exists_const_window_seq`) runs over the cuts of nodes honest at them; its lag is the merged
frame-key lag between two independently honest observations (`frameKey'_lag_obs`): the source
`x` is honest at its cut `i`, the receiver `z` at its cut `m`, and the source need not stay honest.
The frame data of a window agree across its honest cuts (`frameWindow_of_frameKey'_eq_obs`).

Every cross-node fact is charged at the later of the two observations: certificate
intersection for `Σ.F` below a crossing (`finalized_anc_obs`, and inside the lag
`frameKey_le_of_relay`) and justification agreement (`J_eq_of_hj_eq_obs`), the static
store-level arguments with `held_atts_safe_at` as their safety premise. Each chain's signatures
are recovered at its own reader's time; no global cache invariant of a terminal honest cohort is
used. -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-! ### Cross-node facts at two independently honest observations -/

/-- **`Σ.F` below a crossing**: a finalized block `F` of `y`'s chain to `X` (observed while honest
at `u`) is below a block `W` held by `x` (observed while honest at `t`) whose state height exceeds
the finalized height of `X`. Certificate intersection is charged at `max u t`. -/
theorem finalized_anc_obs
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y x : Fin sp.n} {m i : Nat} {u t : Time}
    (hu : 0 ≤ u) (hytime : ∀ k < m, tr.time k ≤ u) (hy : y ∈ H u)
    (ht : 0 ≤ t) (hxtime : ∀ k < i, tr.time k ≤ t) (hx : x ∈ H t)
    (hf : (H (max u t))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {X F W : SA.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state y m).fg.tree)
    (hFt : F ∈ (tr.state y m).fg.tree) (hFr : F.root = ((tr.state y m).fg.σ X.root).F)
    (hW : W ∈ (tr.state x i).fg.tree)
    (hlt : ((tr.state y m).fg.σ X.root).hF < ((tr.state x i).fg.σ W.root).h) :
    Anc (tr.HonestBlocksAt H) F W :=
  honest_anc_of_store_anc_at ht hxtime hx <| Store.finalized_anc_of_safe
    (fg_reachable_at hrun hu hytime hy) (fg_reachable_at hrun ht hxtime hx)
    (Compose.Growing.honest_blocks_coherent hrun hnc) (fun _ h => ⟨y, m, u, hu, hytime, hy, h⟩)
    (fun _ h => ⟨x, i, t, ht, hxtime, hx, h⟩) hf
    (held_atts_safe_at hrun hnc hu hytime hy ht hxtime hx (le_max_left _ _) (le_max_right _ _))
    hX hFt hFr hW hlt

/-- `Σ.J` of two stores observed while honest with equal `h_j` agree: two justification quorums
of one height meet in a validator honest at `max u t`, whose two attestations would be an E2
pair. -/
private theorem J_eq_of_hj_eq_obs
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y x : Fin sp.n} {m i : Nat} {u t : Time}
    (hu : 0 ≤ u) (hytime : ∀ k < m, tr.time k ≤ u) (hy : y ∈ H u)
    (ht : 0 ≤ t) (hxtime : ∀ k < i, tr.time k ≤ t) (hx : x ∈ H t)
    (hf : (H (max u t))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (he : (tr.state y m).fg.hj = (tr.state x i).fg.hj) :
    (tr.state y m).fg.J = (tr.state x i).fg.J :=
  Store.J_eq_of_cache_hj_eq_of_safe (fg_reachable_at hrun hu hytime hy)
    (fg_reachable_at hrun ht hxtime hx) (Compose.Growing.honest_blocks_coherent hrun hnc)
    (fun _ h => ⟨y, m, u, hu, hytime, hy, h⟩) (fun _ h => ⟨x, i, t, ht, hxtime, hx, h⟩) hf
    (held_atts_safe_at hrun hnc hu hytime hy ht hxtime hx (le_max_left _ _) (le_max_right _ _))
    he

/-- `h_j < h_max` at a store observed while honest. -/
private theorem hj_lt_hmax_obs (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {i : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ k < i, tr.time k ≤ t)
    (hy : y ∈ H t) : (tr.state y i).fg.hj < (tr.state y i).fg.hmax :=
  Store.hj_lt_hmax_of_reachable (fg_reachable_at hrun ht hle hy)

/-! ### The frame-key lag between independently honest observations -/

/-- **The frame-key lag** with the source `x` honest at its cut `i` and the receiver `z` honest at
its cut `m`, after a call of `z` at or after the relay deadline of `i`. -/
theorem frameKey_lag_obs (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b κ : Time}
    (hf : ∀ t, 0 ≤ t → t ≤ b → (H t)ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hsvc : ResetService tr H g ΔF b) (hcatch : CatchRun tr H g κ)
    {x z : Fin sp.n} {i m : Nat} (hx : x ∈ H (tr.time i)) (hz : z ∈ H (tr.time m))
    (him : tr.time i ≤ tr.time m) (hmb : tr.time m ≤ b)
    (hcall : ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max (tr.time i) g) sp.Δ ≤ tr.time j)
    (hcm : gbar g + κ ≤ tr.time m) :
    frameKey (tr.state x i).fg ≤ frameKey (tr.state z m).fg := by
  have hi0 := hrun.time_nonneg i
  have hm0 := hrun.time_nonneg m
  have hxle : ∀ k < i, tr.time k ≤ tr.time i := fun k hk => hrun.time_mono hk.le
  have hzle : ∀ k < m, tr.time k ≤ tr.time m := fun k hk => hrun.time_mono hk.le
  have hfmi : (H (max (tr.time i) (tr.time m)))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    rw [max_eq_right him]; exact hf _ hm0 hmb
  exact frameKey_le_of_relay (fg_reachable_at hrun hi0 hxle hx) (fg_reachable_at hrun hm0 hzle hz)
    (Compose.Growing.honest_blocks_coherent hrun hnc)
    (fun _ h => ⟨x, i, tr.time i, hi0, hxle, hx, h⟩)
    (fun _ h => ⟨z, m, tr.time m, hm0, hzle, hz, h⟩) (hf _ hm0 hmb)
    (held_atts_safe_at hrun hnc hm0 hzle hz hi0 hxle hx le_rfl him)
    (held_atts_safe_at hrun hnc hm0 hzle hz hm0 hzle hz le_rfl le_rfl)
    (fun _ _ h hC => store_anc_of_honest_anc_at hrun hnc hi0 hxle hx h hC)
    (fun _ _ h hC => store_anc_of_honest_anc_at hrun hnc hm0 hzle hz h hC)
    (fun _ hB hh => held_of_relay_le_at hrun hnc hsvc hcatch hi0 hx hz hfmi hB hh hxle hcall hcm)

/-- **The merged-key lag** between independently honest observations. -/
theorem frameKey'_lag_obs (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b κ : Time}
    (hf : ∀ t, 0 ≤ t → t ≤ b → (H t)ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hsvc : ResetService tr H g ΔF b) (hcatch : CatchRun tr H g κ)
    {x z : Fin sp.n} {i m : Nat} (hx : x ∈ H (tr.time i)) (hz : z ∈ H (tr.time m))
    (him : tr.time i ≤ tr.time m) (hmb : tr.time m ≤ b)
    (hcall : ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max (tr.time i) g) sp.Δ ≤ tr.time j)
    (hcm : gbar g + κ ≤ tr.time m) :
    frameKey' (tr.state x i).fg ≤ frameKey' (tr.state z m).fg :=
  (frameKey'_def _).symm ▸ (frameKey'_def _).symm ▸ keyMerge_mono
    (frameKey_lag_obs hrun hnc hf hsvc hcatch hx hz him hmb hcall hcm)

/-! ### The frame window -/

/-- A merged key that is constant over the cuts of `[lo, hi]` of nodes honest at them gives a
`FrameWindow`, when `hi ≤ b`. -/
theorem frameWindow_of_frameKey'_eq_obs
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {b : Time}
    (hf : ∀ t, 0 ≤ t → t ≤ b → (H t)ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {lo hi : Time} (hhi : hi ≤ b)
    (hK : ∀ y z i m, y ∈ H (tr.time i) → z ∈ H (tr.time m) → lo ≤ tr.time i →
      tr.time i ≤ hi → lo ≤ tr.time m → tr.time m ≤ hi →
      frameKey' (tr.state y i).fg = frameKey' (tr.state z m).fg) :
    ∃ floor kindJ J, FrameWindow tr H lo hi floor kindJ J := by
  have hle : ∀ i k, k < i → tr.time k ≤ tr.time i := fun _ _ hk => hrun.time_mono hk.le
  obtain ⟨floor, kindJ, J, h1, h2, h3⟩ := frameData_of_frameKey'_eq
    (fun y i => y ∈ H (tr.time i)) tr.time (fun y i => (tr.state y i).fg)
    (sp.toParams.genesisBlock ([], []))
    (fun y i hy => hj_lt_hmax_obs hrun (hrun.time_nonneg i) (hle i) hy) hK
    (fun y z i m hy hz _ hi _ hm he => J_eq_of_hj_eq_obs hrun hnc (hrun.time_nonneg i) (hle i) hy
      (hrun.time_nonneg m) (hle m) hz
      (hf _ ((hrun.time_nonneg i).trans (le_max_left _ _)) (max_le (hi.trans hhi) (hm.trans hhi)))
      he)
  exact ⟨floor, kindJ, J, ⟨h1, h2, h3⟩⟩

/-- **Step 2 (proof of `exists_frameWindow_seq_of_service_at`)**: per-cut height range and relay
calls produce a frame window, by the sequential pigeonhole over the cuts of nodes honest at them
with the merged-key lag between independently honest observations. -/
theorem exists_frameWindow_seq_of_service_proof_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b κ : Time}
    (hf : ∀ t, 0 ≤ t → t ≤ b → (H t)ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hsvc : ResetService tr H g ΔF b) (hcatch : CatchRun tr H g κ)
    {lo lam T : Time} {hz : Nat} (len : Nat → Time)
    (hlen : ∀ v, 0 ≤ len v) (hlam : 0 ≤ lam) (hlo : gbar g + κ ≤ lo) (hTb : T ≤ b)
    (hrange : ∀ y i, y ∈ H (tr.time i) → lo ≤ tr.time i → tr.time i < T →
      hz ≤ (tr.state y i).fg.hmax ∧ (tr.state y i).fg.hmax ≤ hz + 1)
    (hcall : ∀ z i m, z ∈ H (tr.time m) → lo ≤ tr.time i →
      tr.time i + lam ≤ tr.time m → tr.time m < T →
      ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max (tr.time i) g) sp.Δ ≤ tr.time j)
    (hT : lo + ∑ j ∈ Finset.range 5, (len (2 * hz + j) + lam) < T) :
    ∃ v, 2 * hz ≤ v ∧ v ≤ 2 * hz + 4 ∧ ∃ a, lo + lam ≤ a ∧
      a + len v ≤ lo + ∑ j ∈ Finset.range (v - 2 * hz + 1), (len (2 * hz + j) + lam) ∧
      (∀ y i, y ∈ H (tr.time i) → a ≤ tr.time i → tr.time i ≤ a + len v →
        frameKey' (tr.state y i).fg = v) ∧
      ∃ floor kindJ J, FrameWindow tr H a (a + len v) floor kindJ J := by
  obtain ⟨v, hv1, hv2, a, h1, h2, hK⟩ := exists_const_window_seq
    (fun y i => y ∈ H (tr.time i)) tr.time (fun y i => frameKey' (tr.state y i).fg) (2 * hz) 4
    len hlen hlam
    (fun y i hy h1 h2 => by
      have := hrange y i hy h1 h2
      exact frameKey'_bounds this.1 this.2)
    (fun x z i m hx hz' hi _ him hmT => frameKey'_lag_obs hrun hnc hf hsvc hcatch hx hz'
      ((le_add_of_nonneg_right hlam).trans him) (hmT.le.trans hTb)
      (hcall z i m hz' hi him hmT) (hlo.trans (hi.trans ((le_add_of_nonneg_right hlam).trans him))))
    hT
  -- the window ends before `T`
  have hS : ∀ j, j ≤ 4 → ∑ i ∈ Finset.range (j + 1), (len (2 * hz + i) + lam) ≤
      ∑ i ∈ Finset.range 5, (len (2 * hz + i) + lam) := fun j hj =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      fun i _ _ => add_nonneg (hlen _) hlam
  have hend : a + len v < T := by
    have := hS (v - 2 * hz) (by omega)
    linarith
  refine ⟨v, hv1, hv2, a, h1, h2, hK, frameWindow_of_frameKey'_eq_obs hrun hnc hf
    (hend.le.trans hTb) ?_⟩
  intro y z i m hy hz' hi1 hi2 hm1 hm2
  rw [hK y i hy hi1 hi2, hK z m hz' hm1 hm2]

end Consensus.Goldilocks.Healing.Growing

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.FrameWindowExists
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.M1.FrameLag
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingLeaves
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
frame-key lag between two independently honest observations (`Generic.frameKey'_lag_obs_from`):
the source `x` is honest at its cut `i`, the receiver `z` at its cut `m`, and the source need not
stay honest. The frame data of a window agree across its honest cuts
(`Generic.frameWindow_of_frameKey'_eq_obs_from`).

Every cross-node fact is charged at the later of the two observations: certificate
intersection for `Σ.F` below a crossing (`finalized_anc_obs`, and inside the lag
`frameKey_le_of_relay`) and justification agreement, the static
store-level arguments with `held_atts_safe_at` as their safety premise. Each chain's signatures
are recovered at its own reader's time; no global cache invariant of a terminal honest cohort is
used. -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload gbar)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
  {ini : Fin sp.n → (goldilocksNode sp ro).State}
variable {hold : Time}

/-! ### Cross-node facts at two independently honest observations -/

/-- **`Σ.F` below a crossing**: a finalized block `F` of `y`'s chain to `X` (observed while honest
at `u`) is below a block `W` held by `x` (observed while honest at `t`) whose state height exceeds
the finalized height of `X`. Certificate intersection is charged at `max u t`. -/
theorem finalized_anc_obs
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y x : Fin sp.n} {m i : Nat} {u t : Time}
    (hu : 0 ≤ u) (hytime : ∀ k < m, tr.time k ≤ u) (hy : y ∈ H u)
    (ht : 0 ≤ t) (hxtime : ∀ k < i, tr.time k ≤ t) (hx : x ∈ H t)
    (hf : (H (max u t))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {X F W : AC.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state y m).fg.tree)
    (hFt : F ∈ (tr.state y m).fg.tree) (hFr : F.root = ((tr.state y m).fg.σ X.root).F)
    (hW : W ∈ (tr.state x i).fg.tree)
    (hlt : ((tr.state y m).fg.σ X.root).hF < ((tr.state x i).fg.σ W.root).h) :
    Anc (tr.HonestBlocksAt H) F W :=
  honest_anc_of_store_anc_at ht hxtime hx <| Store.finalized_anc_of_safe
    (fg_reachable_at hrun hu hytime hy) (fg_reachable_at hrun ht hxtime hx)
    (Compose.Growing.honest_blocks_coherent hrun hnc) (fun _ h => ⟨y, m, u, hu, hytime, hy, h⟩)
    (fun _ h => ⟨x, i, t, ht, hxtime, hx, h⟩) hf
    (held_atts_safe_at hrun hu hytime hy ht hxtime hx (le_max_left _ _) (le_max_right _ _))
    hX hFt hFr hW hlt

/-! ### The frame window -/

/-- A generic frame window (`Generic.FrameWindow`) of a Goldilocks run is its frame window, field
for field. -/
theorem FrameWindow.of_generic {lo hi : Time} {floor : Nat} {kindJ : Prop}
    {J : AC.Blk sp.n (List (FG.Att sp.n))} (h : Generic.FrameWindow tr H lo hi floor kindJ J) :
    FrameWindow tr H lo hi floor kindJ J :=
  ⟨h.floor_eq, h.kind_iff, h.root_eq⟩

/-- **Step 2**: per-cut height range and relay calls produce a frame window, by the sequential
pigeonhole over the cuts of nodes honest at them with the merged-key lag between independently
honest observations. -/
theorem exists_frameWindow_seq_of_service_proof_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b κ : Time}
    (hf : ∀ t, 0 ≤ t → t ≤ b → (H t)ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hsvc : ResetService tr H g ΔF b hold) (hcatch : CatchRun tr H g κ)
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
      ∃ floor kindJ J, FrameWindow tr H a (a + len v) floor kindJ J :=
  let ⟨v, hv1, hv2, a, h1, h2, hK, floor, kindJ, J, hW⟩ :=
    Generic.exists_frameWindow_seq_of_service_at_from hrun.toLocalRun hnc hf hsvc.toService hcatch
      len hlen hlam hlo hTb hrange hcall hT
  ⟨v, hv1, hv2, a, h1, h2, fun y i hy hi1 hi2 => Generic.frameKey'_eq _ ▸ hK y i hy hi1 hi2,
    floor, kindJ, J, .of_generic hW⟩

end Consensus.Goldilocks.Healing.Growing

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameLag
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.PreAdvance
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameWindowCore
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # At most 5 global frame changes, and the pigeonhole to a `FrameWindow`

The bound and the window. Two layers:

* `exists_const_window_seq` is pure counting: a sequential pigeonhole for a per-node monotone
  key with lag `Δ` and a window length per key value (`exists_const_window_seq_of_mem` with
  eligibility `y ∈ H`).
* `exists_frameWindow_seq` applies it to the merged key `frameKey'` (monotone by `keyMerge_mono`)
  and builds a `FrameWindow` from the constant key (`frameWindow_of_frameKey'_eq`, from
  `frameData_of_frameKey'_eq`).

The range (`hmax_le_of_noAdvance` and the lower bound `h_max ≥ HZ` after `cutZ + Δ`) and the lag
(`frameKey_lag`) are hypotheses here. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

/-- **Sequential pigeonhole (generic).** A key in `[base, base + m]` with lag `Δ` and a window
length `len v` per key value `v`. Attempt `j` starts at `lo + S j`, with
`S j = ∑_{i<j} (len (base + i) + Δ)`, and tests the window `[lo + S j + Δ, lo + S (j + 1)]` for
the value `base + j`. If the test fails, some node holds a key above `base + j` in that window,
so after the lag every node does. Thus one of the `m + 1` attempts succeeds: some value `v`
holds at every honest cut of a window of length `len v` that ends by `lo + S (v - base + 1)`. -/
theorem exists_const_window_seq {α : Type*} (H : Set α) (time : Nat → Time)
    (key : α → Nat → Nat) (base m : Nat) (len : Nat → Time) {lo Δ T : Time}
    (hlen : ∀ v, 0 ≤ len v) (hΔ : 0 ≤ Δ)
    (hrange : ∀ y ∈ H, ∀ i, lo ≤ time i → time i < T → base ≤ key y i ∧ key y i ≤ base + m)
    (hlag : ∀ x ∈ H, ∀ z ∈ H, ∀ i k, lo ≤ time i → time i < T → time i + Δ ≤ time k →
      time k < T → key x i ≤ key z k)
    (hT : lo + ∑ j ∈ Finset.range (m + 1), (len (base + j) + Δ) < T) :
    ∃ v, base ≤ v ∧ v ≤ base + m ∧ ∃ a, lo + Δ ≤ a ∧
      a + len v ≤ lo + ∑ j ∈ Finset.range (v - base + 1), (len (base + j) + Δ) ∧
      ∀ y ∈ H, ∀ i, a ≤ time i → time i ≤ a + len v → key y i = v := by
  obtain ⟨v, h1, h2, a, h3, h4, hK⟩ := exists_const_window_seq_of_mem (fun y _ => y ∈ H) time
    key base m len hlen hΔ (fun y i hy => hrange y hy i)
    (fun x z i k hx hz => hlag x hx z hz i k) hT
  exact ⟨v, h1, h2, a, h3, h4, fun y hy i => hK y i hy⟩

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- A merged key that is constant over the honest cuts of `[lo, hi]` gives a `FrameWindow`. -/
theorem frameWindow_of_frameKey'_eq (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {lo hi : Time}
    (hK : ∀ y ∈ H, ∀ z ∈ H, ∀ i m, lo ≤ tr.time i → tr.time i ≤ hi → lo ≤ tr.time m →
      tr.time m ≤ hi → frameKey' (tr.state y i).fg = frameKey' (tr.state z m).fg) :
    ∃ floor kindJ J, FrameWindow (tr := tr) (H := H) lo hi floor kindJ J := by
  obtain ⟨floor, kindJ, J, h1, h2, h3⟩ := frameData_of_frameKey'_eq (fun y _ => y ∈ H) tr.time
    (fun y i => (tr.state y i).fg) (sp.toParams.genesisBlock ([], []))
    (fun y i hy => hj_lt_hmax hrun hy i) (fun y z i m hy hz => hK y hy z hz i m)
    (fun _ _ _ _ hy hz _ _ _ _ he => J_eq_of_hj_eq_run hrun hnc hf hy hz he)
  exact ⟨floor, kindJ, J, fun y hy i => h1 y i hy, fun y hy i => h2 y i hy,
    fun y hy i => h3 y i hy⟩

/-- **Sequential pigeonhole → ∃ FrameWindow.** `exists_const_window_seq` on the merged key
`frameKey'` (5 values `2HZ, …, 2HZ + 4` on `HZ ≤ h_max ≤ HZ + 1`), with a window length
`len v` per key value. It returns the key value `v` of the window, the window `[a, a + len v]`
with `a + len v ≤ lo + ∑_{j ≤ v - 2HZ} (len (2HZ + j) + Δ)`, and a `FrameWindow` on it. -/
theorem exists_frameWindow_seq (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {lo Δ T : Time} {HZ : Nat} (len : Nat → Time) (hlen : ∀ v, 0 ≤ len v) (hΔ : 0 ≤ Δ)
    (hrange : ∀ y ∈ H, ∀ i, lo ≤ tr.time i → tr.time i < T →
      HZ ≤ (tr.state y i).fg.hmax ∧ (tr.state y i).fg.hmax ≤ HZ + 1)
    (hlag : ∀ x ∈ H, ∀ z ∈ H, ∀ i m, lo ≤ tr.time i → tr.time i < T →
      tr.time i + Δ ≤ tr.time m → tr.time m < T →
        frameKey' (tr.state x i).fg ≤ frameKey' (tr.state z m).fg)
    (hT : lo + ∑ j ∈ Finset.range 5, (len (2 * HZ + j) + Δ) < T) :
    ∃ v, 2 * HZ ≤ v ∧ v ≤ 2 * HZ + 4 ∧ ∃ a, lo + Δ ≤ a ∧
      a + len v ≤ lo + ∑ j ∈ Finset.range (v - 2 * HZ + 1), (len (2 * HZ + j) + Δ) ∧
      (∀ y ∈ H, ∀ i, a ≤ tr.time i → tr.time i ≤ a + len v →
        frameKey' (tr.state y i).fg = v) ∧
      ∃ floor kindJ J, FrameWindow (tr := tr) (H := H) a (a + len v) floor kindJ J := by
  obtain ⟨v, hv1, hv2, a, h1, h2, hK⟩ := exists_const_window_seq H tr.time
    (fun y i => frameKey' (tr.state y i).fg) (2 * HZ) 4 len hlen hΔ
    (fun y hy i h1 h2 => by
      have := hrange y hy i h1 h2
      exact frameKey'_bounds this.1 this.2)
    hlag hT
  refine ⟨v, hv1, hv2, a, h1, h2, hK, frameWindow_of_frameKey'_eq hrun hnc hf ?_⟩
  intro y hy z hz i m hi1 hi2 hm1 hm2
  rw [hK y hy i hi1 hi2, hK z hz m hm1 hm2]

/-- `exists_frameWindow_seq` with the lag discharged by `frameKey'_lag`. -/
theorem exists_frameWindow_seq_of_service (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {g ΔF b κ : Time} (hsvc : ResetService tr H g ΔF b) (hcatch : CatchRun tr H g κ)
    {lo lam T : Time} {HZ : Nat} (len : Nat → Time) (hlen : ∀ v, 0 ≤ len v) (hlam : 0 ≤ lam)
    (hlo : gbar g + κ ≤ lo)
    (hrange : ∀ y ∈ H, ∀ i, lo ≤ tr.time i → tr.time i < T →
      HZ ≤ (tr.state y i).fg.hmax ∧ (tr.state y i).fg.hmax ≤ HZ + 1)
    (hcall : ∀ z ∈ H, ∀ i m, lo ≤ tr.time i → tr.time i + lam ≤ tr.time m → tr.time m < T →
      ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max (tr.time i) g) sp.Δ ≤ tr.time j)
    (hT : lo + ∑ j ∈ Finset.range 5, (len (2 * HZ + j) + lam) < T) :
    ∃ v, 2 * HZ ≤ v ∧ v ≤ 2 * HZ + 4 ∧ ∃ a, lo + lam ≤ a ∧
      a + len v ≤ lo + ∑ j ∈ Finset.range (v - 2 * HZ + 1), (len (2 * HZ + j) + lam) ∧
      (∀ y ∈ H, ∀ i, a ≤ tr.time i → tr.time i ≤ a + len v →
        frameKey' (tr.state y i).fg = v) ∧
      ∃ floor kindJ J, FrameWindow (tr := tr) (H := H) a (a + len v) floor kindJ J :=
  exists_frameWindow_seq hrun hnc hf len hlen hlam hrange
    (fun x hx z hz i m hi _ him hmT => frameKey'_lag hrun hnc hf hsvc hcatch hx hz
      (hcall z hz i m hi him hmT) (by linarith)) hT

end Consensus.Goldilocks.Healing

end

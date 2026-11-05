module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameLag
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.PreAdvance
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # At most 5 global frame changes, and the pigeonhole to a `FrameWindow`

O2 and the window. Two layers:

* `exists_const_window_seq` is pure counting: a sequential pigeonhole for a per-node monotone
  key with lag `Δ` and a window length per key value.
* `exists_frameWindow_seq` applies it to the merged key `frameKey'` (MONO) and builds a
  `FrameWindow` from the constant key (`frameWindow_of_frameKey'_eq`).

The range (F1 and the lower bound `h_max ≥ HZ` after `cutZ + Δ`) and the lag (L-H/L-J/L-C) are
hypotheses here. -/

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
  classical
  obtain ⟨S, hSdef⟩ : ∃ S : Nat → Time,
      ∀ j, S j = ∑ i ∈ Finset.range j, (len (base + i) + Δ) := ⟨_, fun _ => rfl⟩
  have hS0 : ∀ j, 0 ≤ S j := fun j => by
    rw [hSdef]
    exact Finset.sum_nonneg fun i _ => add_nonneg (hlen _) hΔ
  have hSmono : ∀ j k, j ≤ k → S j ≤ S k := fun j k hjk => by
    rw [hSdef, hSdef]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hjk)
      fun i _ _ => add_nonneg (hlen _) hΔ
  have hSsucc : ∀ j, S (j + 1) = S j + (len (base + j) + Δ) := fun j => by
    rw [hSdef, hSdef, Finset.sum_range_succ]
  rw [← hSdef] at hT
  by_contra hno
  -- a failed attempt `j` leaves a key above `base + j` in its window
  have step : ∀ j ≤ m,
      (∀ z ∈ H, ∀ k, lo + S j + Δ ≤ time k → time k < T → base + j ≤ key z k) →
      ∃ y ∈ H, ∃ i, lo + S j + Δ ≤ time i ∧ time i ≤ lo + S (j + 1) ∧ time i < T ∧
        base + j + 1 ≤ key y i := by
    intro j hj hinvj
    have hTj : lo + S (j + 1) < T := by
      have := hSmono (j + 1) (m + 1) (by omega)
      linarith
    by_contra hall
    push Not at hall
    apply hno
    refine ⟨base + j, by omega, by omega, lo + S j + Δ, by linarith [hS0 j], ?_, ?_⟩
    · rw [show base + j - base + 1 = j + 1 by omega, ← hSdef, hSsucc]
      linarith
    · intro y hy i hi1 hi2
      have hiT : time i < T := by linarith [hSsucc j]
      have h1 := hinvj y hy i hi1 hiT
      have h2 := hall y hy i hi1 (by linarith [hSsucc j]) hiT
      omega
  have hinv : ∀ j, j ≤ m →
      ∀ z ∈ H, ∀ k, lo + S j + Δ ≤ time k → time k < T → base + j ≤ key z k := by
    intro j
    induction j with
    | zero =>
      intro _ z hz k hk hkT
      have := (hrange z hz k (by linarith [hS0 0]) hkT).1
      omega
    | succ j ih =>
      intro hj z hz k hk hkT
      obtain ⟨y, hy, i, hi1, hi2, hiT, hkey⟩ := step j (by omega) (ih (by omega))
      have := hlag y hy z hz i k (by linarith [hS0 j]) hiT (by linarith) hkT
      omega
  obtain ⟨y, hy, i, hi1, -, hiT, hkey⟩ := step m le_rfl (hinv m le_rfl)
  have := (hrange y hy i (by linarith [hS0 m]) hiT).2
  omega

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
  classical
  have hpos : ∀ y ∈ H, ∀ i, 1 ≤ (tr.state y i).fg.hmax := fun y hy i => by
    have := hj_lt_hmax hrun hy i
    omega
  by_cases hex : ∃ y ∈ H, ∃ i, lo ≤ tr.time i ∧ tr.time i ≤ hi
  · obtain ⟨y₀, hy₀, i₀, h₁, h₂⟩ := hex
    let st := (tr.state y₀ i₀).fg
    refine ⟨st.headHeightFloor, st.hmax = st.hj + 1 ∧ ¬st.Contest, st.J, ⟨?_, ?_, ?_⟩⟩
    · intro y hy i hlo hhi
      exact (frameKey'_eq_floor_kind (hpos y hy i) (hpos y₀ hy₀ i₀)
        (hK y hy y₀ hy₀ i i₀ hlo hhi h₁ h₂)).1
    · intro y hy i hlo hhi
      exact (frameKey'_eq_floor_kind (hpos y hy i) (hpos y₀ hy₀ i₀)
        (hK y hy y₀ hy₀ i i₀ hlo hhi h₁ h₂)).2
    · intro y hy i hlo hhi hk
      have he := hK y hy y₀ hy₀ i i₀ hlo hhi h₁ h₂
      exact frameKey'_eq_J hrun hnc hf hy hy₀ he
        ((frameKey'_eq_floor_kind (hpos y hy i) (hpos y₀ hy₀ i₀) he).2.2 hk)
  · push Not at hex
    refine ⟨0, True, sp.toParams.genesisBlock ([], []), ⟨?_, ?_, ?_⟩⟩ <;>
      intro y hy i hlo hhi <;> exact absurd hhi (not_le.2 (hex y hy i hlo))

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

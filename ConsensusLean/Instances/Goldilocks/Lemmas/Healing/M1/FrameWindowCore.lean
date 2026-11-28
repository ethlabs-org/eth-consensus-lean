module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameKey
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The sequential pigeonhole and the frame data of a constant key

Two facts over observations `(y, i)` (a node and a cut) selected by an eligibility predicate
`mem y i`. Eligibility may change between cuts: in the static application it is honesty
(`y ∈ H`), in the growing one honesty at the time of the cut.

* `exists_const_window_seq_of_mem`: a bounded key with pairwise lag between eligible observations
  is constant over the eligible cuts of a window.
  The frame data of a constant milestone key are `Generic.frameData_of_frameKey''_eq`. -/

namespace Consensus.Goldilocks.Healing

/-- **Sequential pigeonhole over eligible observations.** A key in `[base, base + m]` with lag `Δ`
and a window length `len v` per key value `v`. Attempt `j` starts at `lo + S j`, with
`S j = ∑_{i<j} (len (base + i) + Δ)`, and tests the window `[lo + S j + Δ, lo + S (j + 1)]` for
the value `base + j`. If the test fails, some eligible observation has a key above `base + j` in
that window, so after the lag every eligible observation does. Thus one of the `m + 1` attempts
succeeds: some value `v` holds at every eligible cut of a window of length `len v` that ends by
`lo + S (v - base + 1)`. No witness must remain eligible after supplying its lower bound. -/
theorem exists_const_window_seq_of_mem {α : Type*} (mem : α → Nat → Prop) (time : Nat → Time)
    (key : α → Nat → Nat) (base m : Nat) (len : Nat → Time) {lo Δ T : Time}
    (hlen : ∀ v, 0 ≤ len v) (hΔ : 0 ≤ Δ)
    (hrange : ∀ y i, mem y i → lo ≤ time i → time i < T →
      base ≤ key y i ∧ key y i ≤ base + m)
    (hlag : ∀ x z i k, mem x i → mem z k → lo ≤ time i → time i < T →
      time i + Δ ≤ time k → time k < T → key x i ≤ key z k)
    (hT : lo + ∑ j ∈ Finset.range (m + 1), (len (base + j) + Δ) < T) :
    ∃ v, base ≤ v ∧ v ≤ base + m ∧ ∃ a, lo + Δ ≤ a ∧
      a + len v ≤ lo + ∑ j ∈ Finset.range (v - base + 1), (len (base + j) + Δ) ∧
      ∀ y i, mem y i → a ≤ time i → time i ≤ a + len v → key y i = v := by
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
      (∀ z k, mem z k → lo + S j + Δ ≤ time k → time k < T → base + j ≤ key z k) →
      ∃ y i, mem y i ∧ lo + S j + Δ ≤ time i ∧ time i ≤ lo + S (j + 1) ∧ time i < T ∧
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
    · intro y i hy hi1 hi2
      have hiT : time i < T := by linarith [hSsucc j]
      have h1 := hinvj y i hy hi1 hiT
      have h2 := hall y i hy hi1 (by linarith [hSsucc j]) hiT
      omega
  have hinv : ∀ j, j ≤ m →
      ∀ z k, mem z k → lo + S j + Δ ≤ time k → time k < T → base + j ≤ key z k := by
    intro j
    induction j with
    | zero =>
      intro _ z k hz hk hkT
      have := (hrange z k hz (by linarith [hS0 0]) hkT).1
      omega
    | succ j ih =>
      intro hj z k hz hk hkT
      obtain ⟨y, i, hy, hi1, hi2, hiT, hkey⟩ := step j (by omega) (ih (by omega))
      have := hlag y z i k hy hz (by linarith [hS0 j]) hiT (by linarith) hkT
      omega
  obtain ⟨y, i, hy, hi1, _, hiT, hkey⟩ := step m le_rfl (hinv m le_rfl)
  have := (hrange y i hy (by linarith [hS0 m]) hiT).2
  omega

end Consensus.Goldilocks.Healing

end

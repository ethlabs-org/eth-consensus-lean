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
* `frameData_of_frameKey'_eq`: a merged key that is constant over the eligible cuts of `[lo, hi]`
  determines the head height floor and the root kind there, and, in kind J, `Σ.J` when eligible
  observations with equal `h_j` have equal `Σ.J`. -/

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

variable {P : Params} {ACP : Type}

/-- **The frame data of a constant merged key.** Equal merged keys give equal head height floors
and root kinds (`frameKey'_eq_floor_kind`); in kind J (`h_max = h_j + 1` without a contest)
equal floors give equal `h_j`, hence equal `Σ.J` by `hJ`. Without an eligible observation in
`[lo, hi]` any data serve, with `J := dflt`. -/
theorem frameData_of_frameKey'_eq {α : Type*} (mem : α → Nat → Prop) (time : Nat → Time)
    (st : α → Nat → Store P ACP) (dflt : NodeBlock P ACP) {lo hi : Time}
    -- Reachability: `h_j < h_max` at every eligible observation.
    (hlt : ∀ y i, mem y i → (st y i).hj < (st y i).hmax)
    (hK : ∀ y z i m, mem y i → mem z m → lo ≤ time i → time i ≤ hi → lo ≤ time m →
      time m ≤ hi → frameKey' (st y i) = frameKey' (st z m))
    -- Agreement: eligible observations in `[lo, hi]` with equal `h_j` have equal `Σ.J`.
    (hJ : ∀ y z i m, mem y i → mem z m → lo ≤ time i → time i ≤ hi → lo ≤ time m →
      time m ≤ hi → (st y i).hj = (st z m).hj → (st y i).J = (st z m).J) :
    ∃ floor kindJ J,
      (∀ y i, mem y i → lo ≤ time i → time i ≤ hi → (st y i).headHeightFloor = floor) ∧
      (∀ y i, mem y i → lo ≤ time i → time i ≤ hi →
        (((st y i).hmax = (st y i).hj + 1 ∧ ¬ (st y i).Contest) ↔ kindJ)) ∧
      (∀ y i, mem y i → lo ≤ time i → time i ≤ hi → kindJ → (st y i).J = J) := by
  classical
  by_cases hex : ∃ y i, mem y i ∧ lo ≤ time i ∧ time i ≤ hi
  · obtain ⟨y₀, i₀, hy₀, h₁, h₂⟩ := hex
    have hkey : ∀ y i, mem y i → lo ≤ time i → time i ≤ hi →
        (st y i).headHeightFloor = (st y₀ i₀).headHeightFloor ∧
          (((st y i).hmax = (st y i).hj + 1 ∧ ¬ (st y i).Contest) ↔
            ((st y₀ i₀).hmax = (st y₀ i₀).hj + 1 ∧ ¬ (st y₀ i₀).Contest)) :=
      fun y i hy hlo hhi => frameKey'_eq_floor_kind (by have := hlt y i hy; omega)
        (by have := hlt y₀ i₀ hy₀; omega) (hK y y₀ i i₀ hy hy₀ hlo hhi h₁ h₂)
    refine ⟨_, _, (st y₀ i₀).J, fun y i hy hlo hhi => (hkey y i hy hlo hhi).1,
      fun y i hy hlo hhi => (hkey y i hy hlo hhi).2, fun y i hy hlo hhi hk => ?_⟩
    obtain ⟨hfl, hkd⟩ := hkey y i hy hlo hhi
    have hk' := hkd.2 hk
    have hj1 := hlt y i hy
    have hj2 := hlt y₀ i₀ hy₀
    apply hJ y y₀ i i₀ hy hy₀ hlo hhi h₁ h₂
    unfold Store.headHeightFloor at hfl
    simp [hk.2, hk'.2] at hfl
    omega
  · push Not at hex
    exact ⟨0, True, dflt, fun y i hy hlo hhi => absurd hhi (not_le.2 (hex y i hy hlo)),
      fun y i hy hlo hhi => absurd hhi (not_le.2 (hex y i hy hlo)),
      fun y i hy hlo hhi => absurd hhi (not_le.2 (hex y i hy hlo))⟩

end Consensus.Goldilocks.Healing

end

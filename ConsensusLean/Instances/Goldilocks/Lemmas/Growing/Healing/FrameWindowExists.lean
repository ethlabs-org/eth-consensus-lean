module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameLag
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.PreAdvance
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameWindowCore

public section

/-! # Sequential frame windows with honesty at each cut

The pigeonhole argument uses pairwise lag between eligible observations. Eligibility can
change between cuts: no witness must remain eligible after supplying its lower bound. The
argument is the static `exists_const_window_seq_of_mem`.
-/

namespace Consensus.Goldilocks.Healing.Growing

/-- A bounded key with pairwise lag has a constant window over the eligible cuts.
In the healing application `mem y i` means honesty at the time of cut `i`. -/
theorem exists_const_window_seq {α : Type*} (mem : α → Nat → Prop) (time : Nat → Time)
    (key : α → Nat → Nat) (base m : Nat) (len : Nat → Time) {lo Δ T : Time}
    (hlen : ∀ v, 0 ≤ len v) (hΔ : 0 ≤ Δ)
    (hrange : ∀ y i, mem y i → lo ≤ time i → time i < T →
      base ≤ key y i ∧ key y i ≤ base + m)
    (hlag : ∀ x z i k, mem x i → mem z k → lo ≤ time i → time i < T →
      time i + Δ ≤ time k → time k < T → key x i ≤ key z k)
    (hT : lo + ∑ j ∈ Finset.range (m + 1), (len (base + j) + Δ) < T) :
    ∃ v, base ≤ v ∧ v ≤ base + m ∧ ∃ a, lo + Δ ≤ a ∧
      a + len v ≤ lo + ∑ j ∈ Finset.range (v - base + 1), (len (base + j) + Δ) ∧
      ∀ y i, mem y i → a ≤ time i → time i ≤ a + len v → key y i = v :=
  exists_const_window_seq_of_mem mem time key base m len hlen hΔ hrange hlag hT

end Consensus.Goldilocks.Healing.Growing

end

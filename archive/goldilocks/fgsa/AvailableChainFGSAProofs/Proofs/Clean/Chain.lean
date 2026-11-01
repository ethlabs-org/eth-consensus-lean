module
public import AvailableChainFGSAProofs.Statements.CleanInvariant
public import AvailableChainFGSAProofs.Proofs.Clean.GateEpoch

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open AvailableChain.Gen.Pure

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- Earlier results remain in every larger history. -/
theorem cleanResults_mono {j i : Nat} (hji : j ≤ i) :
    cleanResults p c E rho j ⊆ cleanResults p c E rho i := by
  rintro sB ⟨k, hk, x, hx, hB⟩
  exact ⟨k, Nat.lt_of_lt_of_le hk hji, x, hx, hB⟩

/-- A labelled origin remains valid at a larger history index. -/
theorem belowLabel_mono_index {j i : Nat} {r : Slot} {X : Block}
    (hji : j ≤ i) (hX : BelowLabel p c E rho j r X) :
    BelowLabel p c E rho i r X := by
  rcases hX with hX | ⟨s, B, hB, hs, hXB⟩
  · exact Or.inl hX
  · exact Or.inr ⟨s, B, cleanResults_mono hji hB, hs, hXB⟩

/-- A labelled origin remains valid at a larger label bound. -/
theorem belowLabel_mono_label {i : Nat} {r s : Slot} {X : Block}
    (hrs : r ≤ s) (hX : BelowLabel p c E rho i r X) :
    BelowLabel p c E rho i s X := by
  rcases hX with hX | ⟨t, B, hB, ht, hXB⟩
  · exact Or.inl hX
  · exact Or.inr ⟨t, B, hB, Nat.le_trans ht hrs, hXB⟩

/-- Prefixes retain the same labelled origin. -/
theorem belowLabel_of_preceq {i : Nat} {r : Slot} {X Y : Block}
    (hXY : Block.Preceq X Y) (hY : BelowLabel p c E rho i r Y) :
    BelowLabel p c E rho i r X := by
  rcases hY with rfl | ⟨s, B, hB, hs, hYB⟩
  · exact Or.inl (block_preceq_antisymm hXY (block_genesis_preceq X))
  · exact Or.inr ⟨s, B, hB, hs, block_preceq_trans hXY hYB⟩

/-- Genesis needs no result witness. -/
theorem belowLabel_genesis (i : Nat) (r : Slot) :
    BelowLabel p c E rho i r .genesis := Or.inl rfl

/-- A member is its own labelled origin. -/
theorem belowLabel_of_mem {i : Nat} {s r : Slot} {B : Block}
    (hB : (s, B) ∈ cleanResults p c E rho i) (hsr : s ≤ r) :
    BelowLabel p c E rho i r B :=
  Or.inr ⟨s, B, hB, hsr, block_preceq_refl B⟩

/-- A completed gate result supplies a labelled origin. -/
theorem belowLabel_of_gateResultAt {j i : Nat} {x : V} {s r : Slot} {B : Block}
    (hsch : V2.D.ScheduleWellFormed E rho)
    (hji : j < i) (hx : IsGateTick p c rho j x s)
    (hB : gateResultAt p c E rho j = some (some B)) (hsr : s ≤ r) :
    BelowLabel p c E rho i r B :=
  belowLabel_of_mem ⟨j, hji, x, hx, (clean_gate_enabled_of_result hsch hx hB).2, hB⟩ hsr

/-- All four history fields restrict to an earlier index. -/
theorem cleanHist_restrict {j i : Nat} (hji : j ≤ i) (hh : CleanHist p c E rho i) :
    CleanHist p c E rho j := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s r B C hB hC hsr
    exact hh.ordered s r B C (cleanResults_mono hji hB) (cleanResults_mono hji hC) hsr
  · intro s B C hB hC
    exact hh.same s B C (cleanResults_mono hji hB) (cleanResults_mono hji hC)
  · intro k x s hk hx
    exact hh.nonempty k x s (Nat.lt_of_lt_of_le hk hji) hx
  · intro k l x y s B hk hl hx hy hJ hB
    exact hh.continues k l x y s B (Nat.lt_of_lt_of_le hk hji) hl hx hy hJ hB

/-- Only the ordered and same-label fields are used. -/
theorem cleanHist_results_compatible {i : Nat} (hh : CleanHist p c E rho i)
    {s r : Slot} {B C : Block} (hB : (s, B) ∈ cleanResults p c E rho i)
    (hC : (r, C) ∈ cleanResults p c E rho i) : Block.Compatible B C := by
  rcases lt_trichotomy s r with hsr | rfl | hrs
  · exact block_compatible_of_common (hh.ordered s r B C hB hC hsr) (block_preceq_refl C)
  · exact hh.same s B C hB hC
  · exact block_compatible_of_common (block_preceq_refl B) (hh.ordered r s C B hC hB hrs)

/-- Label bounds can differ; both origins belong to the same history. -/
theorem cleanHist_belowLabel_compatible {i : Nat} (hh : CleanHist p c E rho i)
    {r s : Slot} {X Y : Block} (hX : BelowLabel p c E rho i r X)
    (hY : BelowLabel p c E rho i s Y) : Block.Compatible X Y := by
  rcases hX with rfl | ⟨t, B, hB, _, hXB⟩
  · exact block_compatible_of_common (block_genesis_preceq Y) (block_preceq_refl Y)
  rcases hY with rfl | ⟨u, C, hC, _, hYC⟩
  · exact block_compatible_of_common (block_preceq_refl X) (block_genesis_preceq X)
  have hXC := block_compatible_of_preceq_compatible hXB (cleanHist_results_compatible hh hB hC)
  have hCX : Block.Compatible C X := by
    change Block.compatible C X = true
    rw [block_compatible_comm]
    exact hXC
  have hYX := block_compatible_of_preceq_compatible hYC hCX
  change Block.compatible X Y = true
  rw [block_compatible_comm]
  exact hYX

/-- The later-labelled result must belong to the same history; only ordered is used. -/
theorem cleanHist_belowLabel_preceq_result {i : Nat} (hh : CleanHist p c E rho i)
    {r s : Slot} {X B : Block} (hX : BelowLabel p c E rho i r X)
    (hB : (s, B) ∈ cleanResults p c E rho i) (hrs : r < s) : Block.Preceq X B := by
  rcases hX with rfl | ⟨t, C, hC, htr, hXC⟩
  · exact block_genesis_preceq B
  · exact block_preceq_trans hXC (hh.ordered t s C B hC hB (Nat.lt_of_le_of_lt htr hrs))

/-- F2 initialization needs the empty history, without state premises. -/
theorem cleanHist_zero : CleanHist p c E rho 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro s r B C ⟨j, hj, _⟩
    exact (Nat.not_lt_zero j hj).elim
  · rintro s B C ⟨j, hj, _⟩
    exact (Nat.not_lt_zero j hj).elim
  · intro j x s hj
    exact (Nat.not_lt_zero j hj).elim
  · intro j k x y s B hj
    exact (Nat.not_lt_zero j hj).elim

/-- F2.5a can separate old results from the result at the new gate index. -/
theorem cleanResults_mem_succ_iff {i : Nat} {s : Slot} {B : Block} :
    (s, B) ∈ cleanResults p c E rho (i + 1) ↔
      (s, B) ∈ cleanResults p c E rho i ∨
        ∃ x, enabledGateAt p c E rho i x s ∧ gateResultAt p c E rho i = some (some B) := by
  constructor
  · rintro ⟨j, hj, x, hx, hB⟩
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hji | rfl
    · exact Or.inl ⟨j, hji, x, hx, hB⟩
    · exact Or.inr ⟨x, ⟨hx, hB.1⟩, hB.2⟩
  · rintro (hB | ⟨x, hx, hB⟩)
    · exact cleanResults_mono (Nat.le_succ i) hB
    · exact ⟨i, Nat.lt_succ_self i, x, hx.1, hx.2, hB⟩

end AvailableChain.FGSA.Run
end

module
public import AvailableChainFGSAProofs.Proofs.Shared.Reads
public import AvailableChainGeneric.Proofs.Pure.BlockOrder

public section

namespace AvailableChain.FGSA.Run

open Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Blueprint 03:354–416; spec 2548–2551; plan I-EXACT, G1 step 2.
Class (iii). DC: INTENTIONAL; finite event indices produce a comparison
prefix. Only the field-level order and same-label compatibility facts are
used. The result is genesis or a genuine gate result with label at most r.
This does not assume a comparison prefix or retained geometry. -/
theorem inclusion_comparison_prefix
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho)
    (hordered : ∀ x y r s B C, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams r ≤ rho.horizon → SA.gateTime p.toParams s ≤ rho.horizon →
      gateResult p c E rho x r = some (some B) →
      gateResult p c E rho y s = some (some C) →
      (r < s → Block.Preceq B C) ∧ (r = s → Block.Compatible B C))
    (i : Nat) (r : Slot) :
    ∃ D : Block, BelowLabel p c E rho i r D ∧
      ∀ X, BelowLabel p c E rho i r X → Block.Preceq X D := by
  classical
  let candidates : Finset Block := (Finset.range i).image
    (fun j => ((gateResultAt p c E rho j).getD none).getD .genesis)
  let genuine : Finset Block := candidates.filter
    (fun B => ∃ s, (s, B) ∈ cleanResults p c E rho i ∧ s ≤ r)
  let pool := insert Block.genesis genuine
  have hmem {s : Slot} {B : Block} (hB : (s, B) ∈ cleanResults p c E rho i)
      (hsr : s ≤ r) : B ∈ genuine := by
    obtain ⟨j, hj, x, htick, hguard, hresult⟩ := hB
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, ?_⟩,
      s, ⟨j, hj, x, htick, hguard, hresult⟩, hsr⟩
    simp only [hresult, Option.getD_some]
  have hcompatible {s t : Slot} {B C : Block}
      (hB : (s, B) ∈ cleanResults p c E rho i)
      (hC : (t, C) ∈ cleanResults p c E rho i) : Block.Compatible B C := by
    obtain ⟨j, _, x, hx, _, hB⟩ := hB
    obtain ⟨k, _, y, hy, _, hC⟩ := hC
    have hmj := List.mem_of_getElem? hx
    have hmk := List.mem_of_getElem? hy
    have hxy := hordered x y s t B C (hs.honest_only _ hmj) (hs.honest_only _ hmk)
      (hs.in_horizon _ hmj).2 (hs.in_horizon _ hmk).2
      ((gateResultAt_eq_gateResult p c E rho hs hx) ▸ hB)
      ((gateResultAt_eq_gateResult p c E rho hs hy) ▸ hC)
    rcases lt_trichotomy s t with hlt | heq | hgt
    · exact block_compatible_of_common (hxy.1 hlt) (block_preceq_refl C)
    · exact hxy.2 heq
    · have hyx := hordered y x t s C B (hs.honest_only _ hmk) (hs.honest_only _ hmj)
        (hs.in_horizon _ hmk).2 (hs.in_horizon _ hmj).2
        ((gateResultAt_eq_gateResult p c E rho hs hy) ▸ hC)
        ((gateResultAt_eq_gateResult p c E rho hs hx) ▸ hB)
      exact block_compatible_of_common (block_preceq_refl B) (hyx.1 hgt)
  have hpool : ∀ B ∈ pool, ∀ C ∈ pool, Block.Compatible B C := by
    intro B hB C hC
    rcases Finset.mem_insert.mp hB with rfl | hB
    · exact block_compatible_of_common (block_genesis_preceq C) (block_preceq_refl C)
    rcases Finset.mem_insert.mp hC with rfl | hC
    · exact block_compatible_of_common (block_preceq_refl B) (block_genesis_preceq B)
    obtain ⟨s, hB, _⟩ := (Finset.mem_filter.mp hB).2
    obtain ⟨t, hC, _⟩ := (Finset.mem_filter.mp hC).2
    exact hcompatible hB hC
  obtain ⟨D, hD, hmax⟩ := deepest_of_compatible pool ⟨.genesis, Finset.mem_insert_self ..⟩ hpool
  refine ⟨D, ?_, ?_⟩
  · rcases Finset.mem_insert.mp hD with hD | hD
    · exact Or.inl hD
    · obtain ⟨s, hs, hsr⟩ := (Finset.mem_filter.mp hD).2
      exact Or.inr ⟨s, D, hs, hsr, block_preceq_refl D⟩
  · intro X hX
    rcases hX with rfl | ⟨s, B, hB, hsr, hXB⟩
    · exact block_genesis_preceq D
    · exact block_preceq_trans hXB (hmax B (Finset.mem_insert_of_mem (hmem hB hsr)))

end AvailableChain.FGSA.Run
end

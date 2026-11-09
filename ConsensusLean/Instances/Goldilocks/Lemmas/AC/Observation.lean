module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.Observation
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance

public section

/-! # Structural SA observations

These facts use frame and input laws, not execution. They therefore need no step-law
contract field and apply to projected observations of every family member.
-/

namespace Consensus.Goldilocks.ACObsRun

open SA

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}
  {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
  (hr : ACObsRun (goldilocksSA sp FGP ro) H U tr)

include hr

/-- An honest call's frame is well formed and inside the coherent universe. -/
theorem frameIn {x : Fin sp.n} (hx : x ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ) :
    FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ U := by
  rcases hr.frameLaw x hx i ℓ hc with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1

/-- Frame payload validity follows from admission, independently of AC execution. -/
theorem frame_validPayload {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ℓ) :
    ∀ B ∈ ℓ.frame.tree, validPayload B := by
  have step : ∀ (Φ Φ' : Frm sp.n FGP) (t : Time) (c : (goldilocksSA sp FGP ro).Call),
      (goldilocksSA sp FGP ro).CallOK U Φ t c Φ' → (∀ B ∈ Φ.tree, validPayload B) →
      ∀ B ∈ Φ'.tree, validPayload B := by
    intro Φ Φ' t c hok hv X hX
    obtain ⟨-, hc⟩ := hok
    cases c with
    | block B =>
      obtain ⟨hs, hB, -⟩ := hc
      rw [hs.tree_eq] at hX
      rcases hX.1 with rfl | hX
      · exact hB
      · exact hv X hX
    | message m => exact hv X (hc.1 ▸ hX)
    | tick => exact hv X (hc ▸ hX)
    | proposal => exact hv X (hc ▸ hX)
    | toFG => exact hv X (hc ▸ hX)
    | restart => exact hv X (hc ▸ hX)
  induction i using Nat.strong_induction_on generalizing ℓ with
  | _ i ih =>
    rcases hr.frameLaw y hy i ℓ hc with
      ⟨-, Φ₀, ⟨htree, -, -, -, hpay⟩, -, hok⟩ | ⟨j, ℓ', hj, hc', -, hok⟩
    · refine step Φ₀ _ _ _ hok fun B hB => ?_
      rw [htree, Set.mem_singleton_iff] at hB
      subst hB
      refine ⟨fun v hv => ?_, fun v hv => ?_⟩ <;>
        simp [blockVotes, blockSupport, hpay] at hv
    · exact step _ _ _ _ hok (ih j hj hc')

end Consensus.Goldilocks.ACObsRun

end

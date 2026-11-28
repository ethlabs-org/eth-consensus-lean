module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.Events
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy`: the restarts of a joined updater -/

namespace Consensus.Goldilocks.Compose

open AC (ACParams)

variable {FGP : Type} {sp : ACParams} {H : Set (Fin sp.n)}
  {U : Set (AC.Blk sp.n FGP)} {T : AC.GTrace sp FGP}

/-- The restarts of an honest node up to its update of slot `s` (joined) are at or before
`t_s`. -/
theorem update_restarts {ini : Fin sp.n → AC.ACState sp.n}
    (hr : ACLocalRun (AC.goldilocksAC sp FGP) H U T ini)
    {y : Fin sp.n} (hy : y ∈ H) {k₀ s : Nat} {ℓ : ACLabel (AC.goldilocksAC sp FGP)}
    (hu : AC.UpdateAt T y k₀ s ℓ) : ∀ k ≤ k₀, T.RestartAt y k → T.time k ≤ sp.ts s := by
  obtain ⟨hc, hcall, ht, hj⟩ := hu
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  have hts₂ : sp.ts (s + 2 : Nat) = sp.ts s + 8 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  have he := hr.exec k₀ ℓ hc.2 (hc.1 ▸ hy)
  rw [hc.1] at he
  have hpost : AC.joined sp (T.post k₀) (T.time k₀) := by
    have hp : T.post k₀ =
        ((AC.goldilocksAC sp FGP).step y (T.state y k₀) ℓ.frame (T.time k₀) ℓ.call).1 := by
      rw [he]
    unfold AC.joined at hj ⊢
    rw [hp, AC.step_restartTime y _ _ _ _ (by rw [hcall]; simp)]
    exact hj
  have hsl : sp.slot (T.time k₀) = s + 1 :=
    AC.slot_of_mem sp (s + 1) (by rw [ht, hts]; linarith) (by rw [ht, hts₂]; linarith)
  intro k hk hrk
  have := (AC.joined_awakeU sp FGP H U T hr.toU y hy k₀ ℓ hc hpost).2 k hk hrk
  rwa [hsl, show ((s + 1 : Nat) : Int) - 1 = s by push_cast; ring] at this

end Consensus.Goldilocks.Compose

end

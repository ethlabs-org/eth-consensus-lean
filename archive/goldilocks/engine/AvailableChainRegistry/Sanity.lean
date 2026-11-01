module
public import AvailableChainFramework
public import AvailableChainWitnesses.Sanity

@[expose] public section

namespace AvailableChain.Registry.Sanity

open AvailableChain AvailableChain.Generic AvailableChain.Framework
open AvailableChain.Witnesses.Sanity

theorem hooks : HooksSound (alwaysGenesis 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro st o _; rfl
  · intro V _ _ E rho _ v o i j _ _; rfl
  · intro V _ _ E rho _ v o i j _ h; exact h
  · intro V _ _ E rho _ v o i j _ h; exact h
  · intro st o o' h; exact Or.inl h

/-- The Sanity protocol as an instance. -/
def sanity : Instance where
  n := 1
  P := alwaysGenesis 1
  Δ := 1
  Δ_pos := by decide
  iface := interface 1
  hooks := hooks

example : sanity.Δ = exampleEnv.Δ := rfl

open AvailableChain.Framework.Catalog

/-- A run horizon of `max 1 (1 + max H 0)` covers every bound `H`. `omega`
does not unfold the `Time` abbreviation from another module in this
toolchain, so the bound uses order lemmas and `linarith` instead. -/
private theorem horizon_ge (H : Time) : H ≤ max 1 (1 + max H 0) :=
  calc H ≤ max H 0 := le_max_left _ _
    _ ≤ 1 + max H 0 := by linarith
    _ ≤ max 1 (1 + max H 0) := le_max_right _ _

/-- The Sleepy regime of Sanity has runs of every horizon. -/
theorem sleepyInhabited (H : Time) :
    ∃ (W : Validators) (E : Env W.V) (rho : Run W.V sanity.P) (t₀ : Time),
      E.Δ = sanity.Δ ∧ H ≤ rho.horizon ∧ sleepy sanity W E rho t₀ := by
  refine ⟨⟨Fin 1, inferInstance, inferInstance⟩, exampleEnv, exampleRun (max H 0),
    0, rfl, ?_, exampleSleepy (max H 0)⟩
  change H ≤ max 1 (1 + max H 0)
  exact horizon_ge H

def certSafeConfirmed : Cert safeConfirmed sanity where
  const := ()
  valid := trivial
  inhabited := by
    intro H
    obtain ⟨W, E, rho, t₀, hΔ, hH, hs⟩ := sleepyInhabited H
    exact ⟨W, ⟨E, rho⟩, t₀, hΔ, hH, hs, trivial⟩
  proof := by
    intro W x _ t₀ _
    exact safe 1 W.V x.rho t₀

def certSafeStable : Cert safeStable sanity where
  const := ()
  valid := trivial
  inhabited := by
    intro H
    obtain ⟨W, E, rho, t₀, hΔ, hH, hs⟩ := sleepyInhabited H
    exact ⟨W, ⟨E, rho⟩, t₀, hΔ, hH, hs, trivial⟩
  proof := by
    intro W x _ t₀ _
    exact safe 1 W.V x.rho t₀

def certPrefix : Cert prefixOrder sanity where
  const := ()
  valid := trivial
  inhabited := by
    intro H
    exact ⟨⟨Fin 1, inferInstance, inferInstance⟩, ⟨exampleEnv, exampleRun (max H 0)⟩,
      (), rfl, horizon_ge H, trivial, trivial⟩
  proof := by
    intro W x _ _ _
    exact nested 1 W.V x.rho

theorem refutedIncluded : RefutationFamily includedConfirmed sanity := by
  refine ⟨fun D _ h => ?_⟩
  exact confirmedIncluded_fails D
    (h ⟨Fin 1, inferInstance, inferInstance⟩ ⟨exampleEnv, exampleRun D⟩ rfl (0 : Time)
      (exampleSleepy D))

theorem not_candidate : Candidate sanity → False := by
  have he : (⟨includedConfirmed, fun D => D⟩ : Profile.Entry ClaimDomain.v1 Time) ∈
      core.entries := by
    exact .tail _ (.tail _ (.tail _ (.head _)))
  exact not_candidate_of_family he refutedIncluded

end AvailableChain.Registry.Sanity

end

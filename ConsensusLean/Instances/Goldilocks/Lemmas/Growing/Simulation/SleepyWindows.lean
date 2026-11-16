module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.RunMap
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.ClaimTransports
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.WalkFacts
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Sleepy window discharge at the canonical engine map

Local threshold and look-ahead fits are explicit: an arbitrary local-correctness
witness does not fix its data.
The population quorum is a separate consequence of the half-threshold population
regime, not of the committee count. No stored-clock read transport is asserted.
-/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape Blocks Generic
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Transport both sleepy regime clauses through the canonical validator map.
The same point witnesses both windows; their look-aheads remain independent.
Catch-up domination belongs to `ClaimDeadlineFit`, not to this head. -/
def GoldilocksSleepyWindowSupply : Prop :=
  ∀ (S : Setup) (E : Env V) (rho : Model.Run (compiled (goldilocks S)) E)
    (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid) (K : Contract ProgressReq)
    (C : ACCorrectLocal (goldilocksNode (S.params (pubOf E) hn) (S.ro _))
      (goldilocksRunMap S rho hn hv).signer),
    C.θ = K.params.θ → 0 ≤ C.θ → C.θ ≤ 1 →
    C.look = (Sys (goldilocks S) V).aheadDur K ⟨E, rho⟩ →
    C.committeeLook = (Sys (goldilocks S) V).committeeAheadDur K ⟨E, rho⟩ →
    SleepyWindowSupply (goldilocksRunMap S rho hn hv) K C

/-- The population clause at threshold at least one half supplies the shared FG
quorum at each bounded time. Committee participation alone does not suffice. -/
def GoldilocksPopulationQuorumSupply : Prop :=
  ∀ (S : Setup) (E : Env V) (rho : Model.Run (compiled (goldilocks S)) E)
    (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid) (K : Contract ProgressReq),
    (1 / 2 : ℚ) ≤ K.params.θ →
    PopulationQuorumSupply (goldilocksRunMap S rho hn hv) K

/-- The canonical run committee is constant from a slot start to its vote time.
This is an instance obligation, not a law of arbitrary committee functions. -/
def GoldilocksSlotConstancy : Prop :=
  ∀ (S : Setup) (E : Env V) (rho : Model.Run (compiled (goldilocks S)) E)
    (hn : 1 ≤ Fintype.card V) (s : Int),
    runCommittee S rho hn ((S.params (pubOf E) hn).ts s + (S.params (pubOf E) hn).Δ) =
      runCommittee S rho hn ((S.params (pubOf E) hn).ts s)

omit [DecidableEq V] in
/-- Slot selection is unchanged at the vote offset, including negative slot indices. -/
theorem goldilocks_slot_constancy : GoldilocksSlotConstancy (V := V) := by
  intro S E rho hn s
  let sp := S.params (pubOf E) hn
  change runCommittee S rho hn (sp.ts s + sp.Δ) = runCommittee S rho hn (sp.ts s)
  have hd : 0 < sp.Δ := sp.toParams.hΔ
  have hs : sp.slot (sp.ts s + sp.Δ) = sp.slot (sp.ts s) := by
    by_cases h : 0 ≤ s
    · lift s to Nat using h
      rw [SA.slot_of_mem sp s (by linarith) (by
        simp only [SA.SAParams.ts]
        push_cast
        linarith), SA.slot_of_mem sp s le_rfl (by
        simp only [SA.SAParams.ts]
        push_cast
        linarith)]
    · have hn : s ≤ -1 := by omega
      have ht : sp.ts s + sp.Δ < 0 := by
        have := mul_le_mul_of_nonneg_left hn (show 0 ≤ 4 * sp.Δ by positivity)
        simp only [SA.SAParams.ts]
        linarith
      rw [SA.slot_of_neg ht, SA.slot_of_neg (by linarith : sp.ts s < 0)]
  exact runCommittee_eq_of_slot_eq S rho hn hs

end Consensus.Goldilocks.Simulation

end

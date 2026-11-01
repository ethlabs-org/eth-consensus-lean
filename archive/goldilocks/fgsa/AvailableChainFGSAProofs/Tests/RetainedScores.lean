module
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedScores

set_option linter.privateModule false

namespace AvailableChain.FGSA.Run.Tests.RetainedScores

open AvailableChain.SimplexFG
open Gen.Pure

/-- Blueprint 21 H.5:856–914; spec 1350–1360. Class (iii).
DC: INTENTIONAL; finite parameters for the two eligibility cases. -/
private abbrev params : Params :=
  { Δ := 1, n := 1, k := 2, η := 0, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide, digest := fun d => ⟨d.slot + 1⟩ }

/-- Blueprint 21 H.5:856–914; spec 1350–1360. Class (iii).
DC: INTENTIONAL; common immutable parent. -/
private def parentFG : FGBlock (Fin 1) := .node .genesis 1 ⟨1⟩ 0 []

/-- Blueprint 21 H.5:856–914; spec 1350–1360. Class (iii).
DC: INTENTIONAL; retained candidate child. -/
private def candidateFG : FGBlock (Fin 1) := .node parentFG 2 ⟨2⟩ 0 []

/-- Blueprint 21 H.5:856–914; spec 1350–1360. Class (iii).
DC: INTENTIONAL; extra target block makes the two stores different. -/
private def extraFG : FGBlock (Fin 1) := .node parentFG 2 ⟨3⟩ 1 []

/-- Blueprint 21 H.5:856–914; spec 1530–1538. Class (iii).
DC: INTENTIONAL; source store with one resolved signed HEAD. -/
private def sourceStore : State 1 :=
  { initial 1 with
    base := { (initial 1).base with
      now := 12
      blocks := [.genesis, eraseFG parentFG, eraseFG candidateFG]
      votes := [⟨.seat 2 0, .head (eraseFG candidateFG).root⟩]
      voteStamp := [(⟨.seat 2 0, .head (eraseFG candidateFG).root⟩, 0)]
      blockStamp := [(.genesis, 0), (eraseFG parentFG, 0), (eraseFG candidateFG, 0)] }
    fg := {
      TF := {.genesis, parentFG, candidateFG}
      F := .genesis
      J := .genesis
      h_j := 0
      h_max := 1 } }

/-- Blueprint 21 H.5:856–914; spec 1554–1577. Class (iii).
DC: INTENTIONAL; target has higher F and lo, and an extra zero-score child. -/
private def targetStore : State 1 :=
  { sourceStore with
    base := { sourceStore.base with
      blocks := [.genesis, eraseFG parentFG, eraseFG candidateFG, eraseFG extraFG]
      blockStamp := sourceStore.base.blockStamp ++ [(eraseFG extraFG, 0)] }
    fg := { sourceStore.fg with
      TF := {.genesis, parentFG, candidateFG, extraFG}
      F := parentFG
      h_max := 2 } }

/-- Blueprint 21 H.5:856–886; spec 1350–1360. Class (iii).
DC: INTENTIONAL; only the band arm makes this old zero-score child eligible. -/
private theorem fixed_phase_eligibility :
    let src := { sourceStore with fg := { sourceStore.fg with h_max := 3 } }
    let dst := { targetStore with fg := { targetStore.fg with h_max := 3 } }
    eligible params src [] [] (eraseFG candidateFG) =
      eligible params dst [] [] (eraseFG candidateFG) ∧
    eligible params dst [] [] (eraseFG candidateFG) = true := by
  refine ⟨fgsa_eligible_eq_of_same_floor params _ _ [] [] [] []
    (eraseFG candidateFG) parentFG ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  all_goals decide +kernel

/-- Blueprint 21 H.17:2976–2985; spec 1350–1360. Class (iii).
DC: INTENTIONAL; the floors differ, both bands are false, and majority keeps the child. -/
private theorem floor_neutral_eligibility :
    RetainedWalk.es params sourceStore 3 (eraseFG candidateFG) =
      RetainedWalk.et params targetStore 3 (eraseFG candidateFG) ∧
    RetainedWalk.et params targetStore 3 (eraseFG candidateFG) = true ∧
    (controls params sourceStore).lo ≠ (controls params targetStore).lo := by
  refine ⟨fgsa_eligible_eq_of_parent_height params sourceStore targetStore
    (proposerVotes sourceStore 3) (proposerSupport sourceStore 3)
    (headVotes params targetStore 3) (headSupport params targetStore 3)
    (eraseFG candidateFG) ?_ ?_ ?_ ?_ ?_, ?_⟩
  all_goals decide +kernel

/-- Blueprint 21 H.5:886–914; spec 1290–1297,1520–1523. Class (iii).
DC: INTENTIONAL; candidate-local geometry follows from both actual domains. -/
private theorem candidate_floors :
    ScoreRunGeometry sourceStore targetStore (eraseFG candidateFG) := by
  apply fgsa_score_geometry_of_domains params sourceStore targetStore
    sourceStore.fg.TF (voterBlocks params targetStore 3) (eraseFG candidateFG)
  all_goals decide +kernel

/-- Blueprint 03:293–331; 21 H.5:886–914; spec 1530–1538,1554–1577.
Class (iii). DC: INTENTIONAL; two distinct stores give candidate score one,
with different F values and a zero-score target rival. -/
private theorem candidate_score :
    sourceStore.fg.F ≠ targetStore.fg.F ∧
    RetainedWalk.ss sourceStore 3 (eraseFG candidateFG) = 1 ∧
    RetainedWalk.ss sourceStore 3 (eraseFG candidateFG) =
      RetainedWalk.ts params targetStore 3 (eraseFG candidateFG) ∧
    RetainedWalk.ts params targetStore 3 (eraseFG extraFG) = 0 := by decide +kernel

/-- Blueprint 21 H.5:886–914; spec 1330–1360. Class (iii).
DC: INTENTIONAL; a nonempty retained suffix uses the exact scores supplier. -/
private theorem retained_scores :
    SuffixScoresAgree (eraseFG parentFG) (eraseFG candidateFG)
      (RetainedWalk.T params targetStore 3) (RetainedWalk.ss sourceStore 3)
      (RetainedWalk.ts params targetStore 3) (RetainedWalk.et params targetStore 3) := by
  apply fgsa_retained_scores_of_candidates
  intro C hC
  obtain ⟨X, -, -, hm, -, -, -⟩ := hC
  have hT : RetainedWalk.T params targetStore 3 =
      [eraseFG parentFG, eraseFG candidateFG, eraseFG extraFG] := by decide +kernel
  rw [hT] at hm
  have hc : C = eraseFG parentFG ∨ C = eraseFG candidateFG ∨ C = eraseFG extraFG := by
    simpa using hm
  rcases hc with rfl | rfl | rfl <;> decide +kernel

end AvailableChain.FGSA.Run.Tests.RetainedScores

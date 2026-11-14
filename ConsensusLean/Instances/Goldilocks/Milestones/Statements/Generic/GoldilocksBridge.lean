module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.Obligations
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.CorrectLocal
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Persist

@[expose] public section

/-! # Goldilocks supplier contracts

These admission-free propositions specify intended suppliers; they construct no supplier and are
not evidence. The source-origin and truncation obligations remain open along with the other
fields. The local correctness contract does not assert the missing engine, healing or regime
edges. No stronger ready-majority premise replaces an original Goldilocks premise.
-/

namespace Consensus.Goldilocks.Generic

open SA (SAParams ReplayOrder)

/-- Exact data equations for the intended Goldilocks supplier, not its field evidence. -/
def GoldilocksHealingData (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (O : ACHealing (goldilocksNode sp ro) (fun v => v.val)) : Prop :=
  O.Run = (fun proposer dg H tr =>
      sp.committeeSize = sp.n ∧ Growing.GoldilocksRun proposer dg H tr) ∧
    O.warmup = 2 * sp.k ∧ O.follow = 3 ∧ O.drain = 2 * sp.k + 5 ∧
    O.Warm = (fun _ _ s₀ u => s₀ + 2 * sp.k ≤ u) ∧
    O.Origin = (fun tr x i j B => tr.JoinedAt x (tr.time i) ∧
      ∃ CV, Compose.StoredFastLockAt tr x i j B CV)

/-- Intended full-set Goldilocks healing supplier, with its original run and arithmetic warmth.
The existential is an unproved contract, never a definition of a supplier instance.
`Run` is the original growing run, for population-sized committees (`sp.committeeSize = sp.n`).
`warmup` and `Warm` come from the warmth premise in
`Growing/Healing/Kernel/ResetRounds.lean:328`; `follow = 3` is the skeleton choice,
with no upstream standalone statement; `drain` is the skeleton choice `2 * sp.k + 5`,
not a newly proved upstream bound. `Origin` is the joined stored-fast-lock source
used by `Growing/Healing/RowService.lean` (the new source supplier remains unproved).
The `warm_truncate` supplier is immediate arithmetic after the displayed `Warm` equation:
neither side reads honesty. This observation supplies no field evidence here. -/
def goldilocksACHealing (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n))) : Prop :=
  ∃ O : ACHealing (goldilocksNode sp ro) (fun v => v.val),
    GoldilocksHealingData sp ro O

/-- INCOMPLETE intended Goldilocks local supplier, not a completed specialisation.
All seven data equations remain open: `look`, `catchUp`, `margin`, `latency`, `hold`,
`recovery`, and `payload`. The healing equation below supplies no recovery equation
or adequacy of the guarded outage field. A witness alone does not fix Goldilocks data.
The original local field equations also remain open; no supplier evidence is inferred.
The ready-majority counterpattern is not discharged by this skeleton. -/
def goldilocksACCorrectLocal (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n))) : Prop :=
  ∃ C : ACCorrectLocal (goldilocksNode sp ro) (fun v => v.val),
    GoldilocksHealingData sp ro C.healing

end Consensus.Goldilocks.Generic

end

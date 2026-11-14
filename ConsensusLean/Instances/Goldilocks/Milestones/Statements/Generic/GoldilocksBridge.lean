module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.Obligations
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.CorrectLocal
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Persist

@[expose] public section

/-! # Goldilocks supplier contracts

These admission-free propositions specify intended suppliers; they construct no supplier and are
not evidence. The source-origin obligations remain open along with the other fields. The local
correctness contract does not assert the missing engine, healing or regime edges. No stronger
ready-majority premise replaces an original Goldilocks premise.
-/

namespace Consensus.Goldilocks.Generic

open SA (SAParams ReplayOrder)

/-- Read a time-indexed committee at each slot's start. -/
def dictOfTime (sp : SAParams) (cm : Time → Finset (Fin sp.n)) : SA.CommitteeDict sp.n :=
  ⟨fun s => ↑(cm (sp.toParams.slotTime s))⟩

/-- The run and start equations of the committee-indexed Goldilocks supplier. -/
def GoldilocksRunData (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (R : ACRun (goldilocksNode sp ro) (fun v => v.val)) : Prop :=
  R.Run = (fun cm proposer dg H tr => Growing.GoldilocksRun proposer dg H tr
    (SA.committeeStart sp.genesisRoot (dictOfTime sp cm))) ∧
  R.start = (fun cm => SA.committeeStart sp.genesisRoot (dictOfTime sp cm))

/-- Exact data equations for the intended Goldilocks supplier, not its field evidence. -/
def GoldilocksHealingData (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    {R : ACRun (goldilocksNode sp ro) (fun v => v.val)}
    (O : ACHealing (goldilocksNode sp ro) (fun v => v.val) R) : Prop :=
  GoldilocksRunData sp ro R ∧
    O.warmup = 2 * sp.k ∧ O.follow = 3 ∧ O.drain = 2 * sp.k + 5 ∧
    O.Origin = (fun tr x i j B => tr.JoinedAt x (tr.time i) ∧
      ∃ CV, Compose.StoredFastLockAt tr x i j B CV)

/-- Intended committee-indexed Goldilocks healing supplier, with arithmetic warmth.
The existential is an unproved contract, never a definition of a supplier instance.
`Run` uses the canonical committee start. `warmup` comes from the warmth premise in
`Growing/Healing/Kernel/ResetRounds.lean:328`; `follow = 3` is the skeleton choice,
with no upstream standalone statement; `drain` is the skeleton choice `2 * sp.k + 5`,
not a newly proved upstream bound. `Origin` is the joined stored-fast-lock source
used by `Growing/Healing/RowService.lean` (the new source supplier remains unproved).
The data equations supply no healing field evidence. -/
def goldilocksACHealing (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n))) : Prop :=
  ∃ R : ACRun (goldilocksNode sp ro) (fun v => v.val),
    ∃ O : ACHealing (goldilocksNode sp ro) (fun v => v.val) R,
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

module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.Obligations
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.CorrectLocal
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Persist
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Family.Service
public import ConsensusLean.Spec.Blocks.Payload

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

/-- The run and start equations of the committee-indexed Goldilocks supplier.
Committee sizes are positive and match the threshold parameter. Membership facts are required
under collision freedom, so engine execution validity alone still transports to `Run`. -/
def GoldilocksRunData (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (R : ACRun (goldilocksNode sp ro) (fun v => v.val)) : Prop :=
  R.Run = (fun cm proposer dg H tr => Growing.GoldilocksRun proposer dg H tr
    (SA.committeeStart sp.genesisRoot (dictOfTime sp cm)) ∧
    0 < sp.committeeSize ∧
    (∀ s, ((dictOfTime sp cm).committee s).ncard = sp.committeeSize) ∧
    (Compose.NoCollRun dg tr → Compose.Growing.CommitteeFacts tr H (dictOfTime sp cm))) ∧
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
The data equations supply no healing field evidence. The explicit timeout bound is needed
for `follow = 3`; the service-delay inequality alone does not imply it. -/
def goldilocksACHealing (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (_hδ : 3 ≤ sp.toParams.δt) : Prop :=
  ∃ R : ACRun (goldilocksNode sp ro) (fun v => v.val),
    ∃ O : ACHealing (goldilocksNode sp ro) (fun v => v.val) R,
    GoldilocksHealingData sp ro O

/-- Exact local data equations for the intended Goldilocks local supplier, not its field evidence.
The durations are the contract's at `ΔAC = Δ`: catch-up `18Δ`, satisfying `18Δ + 1 ≤ 19Δ`
against the contract's `19Δ`, look-aheads `5Δ`, proposer hold `Δ`, margin and latency `6Δ`
(a proposal at `t_s` is confirmed by `t_s + 6Δ`), outage recovery `9Δ`, look-back
`(12k + 7)Δ`, arming lag `(4k + 6)Δ` and budget `(4k − 5)Δ`; the participation threshold is
`1/2`. The payload is the block input's transactions. Message service is fresh processing
before the deadline or retained timestamped pool evidence
(`SA.FamilyFacts.MessageServedBefore` on the AC projection). -/
def GoldilocksLocalData (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (C : ACCorrectLocal (goldilocksNode sp ro) (fun v => v.val)) : Prop :=
  GoldilocksHealingData sp ro C.healing ∧
    C.θ = 1 / 2 ∧ C.catchUp = 18 * sp.Δ ∧
    C.look = 5 * sp.Δ ∧ C.committeeLook = 5 * sp.Δ ∧
    C.hold = sp.Δ ∧ C.margin = 6 * sp.Δ ∧ C.latency = 6 * sp.Δ ∧
    C.recovery = 9 * sp.Δ ∧ C.outageEta = ((12 * sp.k + 7 : Nat) : Time) * sp.Δ ∧
    C.outageLag = ((4 * sp.k + 6 : Nat) : Time) * sp.Δ ∧
    C.outageBudget = ((4 * sp.k - 5 : Nat) : Time) * sp.Δ ∧
    C.payload = (fun B => {tx | tx ∈ Blocks.decodeTxs B.input}) ∧
    C.served = (fun tr y j τ m => SA.FamilyFacts.MessageServedBefore tr.projAC y j τ m)

/-- Intended Goldilocks local supplier with its exact data equations (`GoldilocksLocalData`).
The existential is an unproved contract, never a definition of a supplier instance; the data
equations supply no field evidence. The ready-majority counterpattern is not discharged by
this skeleton. -/
def goldilocksACCorrectLocal (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (_hδ : 3 ≤ sp.toParams.δt) : Prop :=
  ∃ C : ACCorrectLocal (goldilocksNode sp ro) (fun v => v.val), GoldilocksLocalData sp ro C

end Consensus.Goldilocks.Generic

end

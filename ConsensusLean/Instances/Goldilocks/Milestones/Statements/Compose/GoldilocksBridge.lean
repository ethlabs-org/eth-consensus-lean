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

open AC (ACParams ReplayOrder)

/-- Read a time-indexed committee at each slot's start. -/
def dictOfTime (sp : ACParams) (cm : Time → Finset (Fin sp.n)) : AC.CommitteeDict sp.n :=
  ⟨fun s => ↑(cm (sp.toParams.slotTime s))⟩

/-- The run and start equations of the committee-indexed Goldilocks supplier.
Committee sizes are positive and match the threshold parameter. Membership facts are required
under collision freedom, so engine execution validity alone still transports to `Run`. -/
def GoldilocksRunData (sp : ACParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (R : ACRun (goldilocksNode sp ro) (fun v => v.val))
    (sign : Fin sp.n → Time → Bool := fun _ _ => true) (G : Nat := 0) : Prop :=
  R.Run = (fun cm proposer dg H tr => Growing.GoldilocksRun proposer dg H tr
    (AC.committeeStart sp.genesisRoot (dictOfTime sp cm)) ∧
    0 < sp.committeeSize ∧
    (∀ s, ((dictOfTime sp cm).committee s).ncard = sp.committeeSize) ∧
    (Compose.NoCollRun dg tr → Compose.Growing.CommitteeFacts tr H (dictOfTime sp cm)) ∧
    tr.SignCalendarAt proposer dg H sign ∧ SignGapAt sp.toParams sign G 0) ∧
  R.start = (fun cm => AC.committeeStart sp.genesisRoot (dictOfTime sp cm))

/-- Exact data equations for the intended Goldilocks supplier, not its field evidence. -/
def GoldilocksHealingData (sp : ACParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    {R : ACRun (goldilocksNode sp ro) (fun v => v.val)} {hold : Time}
    (O : ACHealing (goldilocksNode sp ro) (fun v => v.val) R hold)
    (sign : Fin sp.n → Time → Bool := fun _ _ => true) (G : Nat := 0) : Prop :=
  GoldilocksRunData sp ro R sign G ∧
    O.warmup = 2 * sp.k ∧ O.follow = 3 + (G + 3) / 4 ∧ O.reportDelay = G ∧ O.drain = 2 * sp.k + 5 ∧
    O.Origin = (fun tr x i j B => tr.JoinedAt x (tr.time i) ∧
      ∃ CV, Compose.StoredFastLockAt tr x i j B CV)

/-- Committee-indexed Goldilocks healing supplier, proved for the canonical committee-start
interface by `goldilocks_ac_healing` in `Lemmas/Growing/Healing/Supply/Fields.lean`.
Its witness has `warmup = 2 * sp.k`, `follow = 3 + (G + 3) / 4`, `reportDelay = G`,
`drain = 2 * sp.k + 5` and the
joined stored-fast-lock origin, at the release hold `Rg·Δ` of a release gap `Rg`. This
supplies healing only, not `ACCorrectLocal` or the endpoint. The theorem takes the timeout bound
`follow ≤ δ_t`; the service-delay inequality alone does not imply it. -/
def goldilocksACHealing (sp : ACParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (sign : Fin sp.n → Time → Bool := fun _ _ => true) (G : Nat := 0) (Rg : Nat := 0) : Prop :=
  ∃ R : ACRun (goldilocksNode sp ro) (fun v => v.val),
    ∃ O : ACHealing (goldilocksNode sp ro) (fun v => v.val) R ((Rg : Time) * sp.Δ),
    GoldilocksHealingData sp ro O sign G

/-- Exact local data equations for the intended Goldilocks local supplier, not its field evidence.
The durations are the contract's at `ΔAC = Δ`: catch-up `18Δ`, satisfying `18Δ + 1 ≤ 19Δ`
against the contract's `19Δ`, look-aheads `5Δ`, proposer hold `Δ`, margin and latency `6Δ`
(a proposal at `t_s` is confirmed by `t_s + 6Δ`), outage recovery `9Δ`, look-back
`(12k + 7)Δ`, arming lag `(4k + 6)Δ` and budget `(4k − 5)Δ`; the participation threshold is
`1/2`. The payload is the block input's transactions. Message service is fresh processing
before the deadline or retained timestamped pool evidence
(`AC.FamilyFacts.MessageServedBefore` on the AC projection). The release hold of `C` is
`Rg·Δ` for a release gap `Rg` (`0` at the default). -/
structure GoldilocksLocalData (sp : ACParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    {fgHold : Time} (C : ACCorrectLocal (goldilocksNode sp ro) (fun v => v.val) fgHold)
    (sign : Fin sp.n → Time → Bool := fun _ _ => true) (G : Nat := 0) (Rg : Nat := 0) :
    Prop where
  healing : GoldilocksHealingData sp ro C.healing sign G
  θ : C.θ = 1 / 2
  catchUp : C.catchUp = 18 * sp.Δ
  look : C.look = 5 * sp.Δ
  committeeLook : C.committeeLook = 5 * sp.Δ
  hold : C.hold = sp.Δ
  margin : C.margin = 6 * sp.Δ
  latency : C.latency = 6 * sp.Δ
  recovery : C.recovery = 9 * sp.Δ
  outageEta : C.outageEta = ((12 * sp.k + 7 : Nat) : Time) * sp.Δ
  outageLag : C.outageLag = ((4 * sp.k + 6 : Nat) : Time) * sp.Δ
  outageBudget : C.outageBudget = ((4 * sp.k - 5 : Nat) : Time) * sp.Δ
  payload : C.payload = (fun B => {tx | tx ∈ Blocks.decodeTxs B.input})
  served : C.served = (fun tr y j τ m => AC.FamilyFacts.MessageServedBefore tr.projAC y j τ m)
  fgHold_eq : fgHold = (Rg : Time) * sp.Δ

/-- Goldilocks local supplier with its exact data equations (`GoldilocksLocalData`), proved by
`goldilocksACCorrectLocal_of_healing` from `goldilocks_ac_healing`. The data equations alone supply
no field evidence; the healing witness and the local read-point proofs supply that evidence. -/
def goldilocksACCorrectLocal (sp : ACParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (sign : Fin sp.n → Time → Bool := fun _ _ => true) (G : Nat := 0) (Rg : Nat := 0) : Prop :=
  ∃ C : ACCorrectLocal (goldilocksNode sp ro) (fun v => v.val) ((Rg : Time) * sp.Δ),
    GoldilocksLocalData sp ro C sign G Rg

end Consensus.Goldilocks.Generic

end

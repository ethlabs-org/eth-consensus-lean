module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.EngineRepresentation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.RunMapFields
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.RunCommittee
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Schedule
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.State
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Endpoint.Outputs
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Chains
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Shape
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Trace

public section

/-! # The Goldilocks run map

`goldilocksRunMap S rho hn hv` represents a valid engine run of `goldilocksWith S` by its
canonical growing trace `simTraceAt`: keys are the run's PKI, states and the output clock are read
at `hn`, the cut map is `cutMap`, and the output chains are `blocksTo` up to `outTip`. Its data
fields that the run transport reads are characterised by the `goldilocksRunMap_*` lemmas. -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape Blocks
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] (S : BoundSetup) {E : Env V}
  (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)

/-- **The Goldilocks run map** of a valid engine run, through its canonical growing trace. -/
noncomputable def goldilocksRunMap (hv : rho.ExecutionValid) :
    Generic.RunMap (A := goldilocksNode (S.params (pubOf E) hn) (S.ro _)) rho (payloadOf S) where
  validator := rho.key
  keyIndex := Equiv.refl _
  key_eq _ := rfl
  trace := simTraceAt S rho hn
  proposer := runProposer S rho hn
  digest := digestOf S rho
  signer := fun v => v.val
  honest := honestKeysAt S rho
  committee := runCommittee S rho hn
  committee_eq := runCommittee_eq S rho hn hv
  cut := cutMap S rho hn
  cut_mono := cutMap_mono S rho hn
  event := eventOf S rho hn
  event_bound := eventOf_lt S rho hn
  event_group := eventOf_group S rho hn
  before_time _ hi := cutMap_time_le S rho hn hv hi
  after_time := cutTime_le_cutMap_time S rho hn hv
  event_time := eventOf_time S rho hn
  state s := (s hn).node
  state_eq v i hi _ := by
    rw [← stateAt_eq]
    exact simTraceAt_state_all S rho hn hv v i hi
  honest_eq y t := mem_honestKeysAt_iff S rho t y
  awake_eq := simTraceAt_awake_bounds S rho hn
  horizon_eq := simTraceAt_inHorizon_iff_le S rho hn hv
  delta_eq := rfl
  header := headerOf _
  header_input _ := rfl
  payload_eq := payloadOf_eq S
  proposalObject := blockObj _
  proposal_role B := ⟨.proposer B.slot, _, rfl, rfl⟩
  attObject := attObj
  att_signer _ := rfl
  att_conflict a b hab := (conflictsIff_iff.mp conflicts_iff S.vote _ _ _).mpr ⟨a, b, rfl, rfl, hab⟩
  tip := outTip _ _
  chain st B := blocksTo st.fg.blocks (B.slot + 1) B
  clock s := (s hn).now
  output_eq g v i _ := by
    have h := read_eq_out S rho hn g v i
    rw [stateAt_eq] at h
    exact h.trans (outOf_eq_blocksTo _ _ _ _ g)
  available_tip g hg := by
    obtain rfl : Out.confirmed = g := Option.some.inj hg
    exact outTip_confirmed _ _

variable (hv : rho.ExecutionValid)

/-- The run map's trace is the canonical growing trace. -/
@[simp] theorem goldilocksRunMap_trace :
    (goldilocksRunMap S rho hn hv).trace = simTraceAt S rho hn := by rfl

/-- The run map's proposer is the run's selected proposer. -/
@[simp] theorem goldilocksRunMap_proposer :
    (goldilocksRunMap S rho hn hv).proposer = runProposer S rho hn := by rfl

/-- The run map's digest is the tagged engine hash. -/
@[simp] theorem goldilocksRunMap_digest :
    (goldilocksRunMap S rho hn hv).digest = digestOf S rho := by rfl

/-- A vote's signer is its validator index. -/
@[simp] theorem goldilocksRunMap_signer :
    (goldilocksRunMap S rho hn hv).signer = fun v => v.val := by rfl

/-- The run map's honest sets are the clamped honest keys. -/
@[simp] theorem goldilocksRunMap_honest :
    (goldilocksRunMap S rho hn hv).honest = honestKeysAt S rho := by rfl

/-- The run map's committee is the run committee. -/
@[simp] theorem goldilocksRunMap_committee :
    (goldilocksRunMap S rho hn hv).committee = runCommittee S rho hn := by rfl

end Consensus.Goldilocks.Simulation

end

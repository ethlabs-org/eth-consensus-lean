module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ContractDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.Sleepy
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transfer
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.PivotBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameLabels
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.SuffixBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ViewAgree
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.WalkEnd
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.BestChild
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.NetworkTransport
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.QuerySlot
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Lemmas.Model.Constant

public section

/-! # Finite sleepy service facts for the growing queries

`sleepy_raw_syncUntil` (bounded synchrony of a sleepy run) and `half_ready_of_duration` (a shorter
readiness duration keeps a half-ready population) serve the growing queries. -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation
open Blocks Shape

/-- Sleepy network service survives removal of the system's environment tags.
Validity supplies nonnegative send times before converting PSync at zero. -/
theorem sleepy_raw_syncUntil (S : Setup) (A : ContractAssumptions S) (V : Type)
    [Fintype V] [DecidableEq V] (r : (Sys (goldilocks S) V).Run)
    (hv : (Sys (goldilocks S) V).Valid r)
    (hsleepy : (Sys (goldilocks S) V).Sleepy
        (shapeProgress (goldilocks S) V).toExternal (K S A) r) (b : Time) :
    r.2.log.SyncUntil r.2.point b := by
  have hp : r.2.log.PSync r.2.point 0 := (Model.sysOf_delivers_iff _ _ _ _).mp hsleepy.1
  apply hp.syncUntil_zero ?_ b
  rw [CommLog.sendsFromZero_iff]
  intro x m t hs hx
  obtain ⟨i, he | ⟨o, he⟩, -⟩ := hs
  · exact (hv.in_horizon _ (List.mem_of_getElem? he)).1
  · exact (hv.in_horizon _ (List.mem_of_getElem? he)).1

variable (V : Type) [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- Shortening the readiness duration preserves a strict half-ready population. -/
theorem half_ready_of_duration (p : EnvPoint V) {c d t : Time} (hd : c ≤ d)
    (hh : p.ReadyAbove (1 / 2) d t) : p.ReadyAbove (1 / 2) c t := by
  classical
  have hsub : p.readyAt d t ⊆ p.readyAt c t := by
    intro v hv
    obtain ⟨hhon, hr⟩ := Finset.mem_filter.mp hv
    refine Finset.mem_filter.mpr ⟨hhon, hr.1, ?_⟩
    intro u hu hut
    exact hr.2 u ((max_le_max_left 0 (by linarith)).trans hu) hut
  have hc := Finset.card_le_card hsub
  unfold EnvPoint.ReadyAbove at hh ⊢
  have hc' : ((p.readyAt d t).card : ℚ) ≤ (p.readyAt c t).card := by exact_mod_cast hc
  linarith

end Consensus.Goldilocks.Obligations
end

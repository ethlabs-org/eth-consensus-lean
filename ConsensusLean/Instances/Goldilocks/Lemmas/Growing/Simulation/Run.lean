module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Attestations
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Blocks
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Restart
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Wire
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Interface

public section

/-! # The canonical growing trace is a Goldilocks run

Node-local schedule facts reuse the canonical static trace. Origin laws instead use
honesty at processing, proved separately without reconstructing a static invariant.
-/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : BoundSetup)
  (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)

private theorem honest_zero (hv : rho.ExecutionValid) {y : Fin (Fintype.card V)} {t : Time}
    (ht : 0 ≤ t) (hy : y ∈ honestKeysAt S rho t) : y ∈ honestKeys S rho := by
  rw [mem_honestKeys_iff]
  rw [mem_honestKeysAt_iff] at hy
  exact fun hf => hy (rho.faultyAt_mono (le_min ht hv.horizon_nonneg) hf)

/-- The AC start of each node of the canonical trace: the initial state with the node's
own-role vote permission installed by the binding (`simTrace_init`). For the population
binding it is the default start. -/
noncomputable abbrev simIni :
    Fin (Fintype.card V) → (goldilocksNode (S.params (pubOf E) hn) (S.ro _)).State :=
  fun y => S.vote.installVote (fun r => decide (y ∈ rho.sel r))
    (goldilocksNode (S.params (pubOf E) hn) (S.ro _)).initial

omit [DecidableEq V] in
/-- `simIni` changes only the own-role vote permission (`VoteBinding.installVote`): its pools
are the initial, empty ones. -/
theorem simIni_pool (y : Fin (Fintype.card V)) (σ : Nat) : (simIni S rho hn y).pool σ = [] := by
  unfold simIni VoteBinding.installVote
  split <;> rfl

omit [DecidableEq V] in
/-- TEMP(C2): without a participation kind the engine's starts are the default start. Only the
consumers that are not yet start-generic (C2 step 2 remaining list) use it; removed with the Fact
binders at C2 records phase 2 (G9). -/
theorem simIni_eq_initial [hstock : Fact (S.vote.participationKind = none)] : -- TEMP(C2)
    simIni S rho hn = fun _ => (goldilocksNode (S.params (pubOf E) hn) (S.ro _)).initial :=
  funext fun _ => installVote_of_participationKind_none hstock.out _ _

/-- The canonical event expansion obeys all Goldilocks run laws under growing compromise, from
the engine's own starts `simIni`. The instance premise `hstock` is interim, `TEMP(C2)`: it feeds
only the record's interim `stock` field; stock callers get it from
`stock_participationKind_none`. -/
theorem simTraceAt_goldilocksRun (hv : rho.ExecutionValid)
    [hstock : Fact (S.vote.participationKind = none)] : -- TEMP(C2)
    Growing.GoldilocksRun (runProposer S rho hn) (digestOf S rho)
      (honestKeysAt S rho) (simTraceAt S rho hn) (simIni S rho hn) where
  stock := committeeSize_of_participationKind_none hstock.out _
  antitone := honestKeysAt_antitone S rho
  init := by
    intro y hy
    rw [simTraceAt_eq, simTrace_init S rho hn y (honest_zero S rho hv le_rfl hy)]
  grouped := fun y i c hc _ => simTraceAt_grouped S rho hn hv y i c hc
  cutLaw := fun y i c hc _ => simTraceAt_cutLaw S rho hn hv y i c hc
  wire := fun y j t e _ hg => simTraceAt_wire S rho hn hv y j t e hg
  proposerCredential := by
    intro y j t B hy hg
    have ht : 0 ≤ t := by
      have ht := (hg.2.1 0 (List.length_pos_of_ne_nil hg.1)).2.1
      rw [Nat.add_zero] at ht
      exact ht ▸ simTraceAt_time_nonneg S rho hn hv j
    rw [simTraceAt_eq] at hg
    exact simTrace_proposerCredential S rho hn hv y (honest_zero S rho hv ht hy) j t B hg
  time_nonneg := simTraceAt_time_nonneg S rho hn hv
  time_mono := simTraceAt_time_mono S rho hn hv
  finite := by rw [simTraceAt_eq]; exact simTrace_finite S rho hn hv
  phase_order := by
    intro y y' j j' t e e' hy hy' hg hg' hj
    have ht : 0 ≤ t := by
      have ht := (hg.2.1 0 (List.length_pos_of_ne_nil hg.1)).2.1
      rw [Nat.add_zero] at ht
      exact ht ▸ simTraceAt_time_nonneg S rho hn hv j
    rw [simTraceAt_eq] at hg hg'
    exact simTrace_phase_order S rho hn hv y (honest_zero S rho hv ht hy)
      y' (honest_zero S rho hv ht hy') j j' t e e' hg hg' hj
  tick_public := by
    intro y j t hy hg
    have ht : 0 ≤ t := by
      obtain ⟨x, hg⟩ := hg
      have ht := (hg.2.1 0 (List.length_pos_of_ne_nil hg.1)).2.1
      rw [Nat.add_zero] at ht
      exact ht ▸ simTraceAt_time_nonneg S rho hn hv j
    rw [simTraceAt_eq] at hg
    exact simTrace_tick_public S rho hn hv y (honest_zero S rho hv ht hy) j t hg
  tick_unique := by
    intro y j j' t hy hg hg'
    have ht : 0 ≤ t := by
      obtain ⟨x, hg⟩ := hg
      have ht := (hg.2.1 0 (List.length_pos_of_ne_nil hg.1)).2.1
      rw [Nat.add_zero] at ht
      exact ht ▸ simTraceAt_time_nonneg S rho hn hv j
    rw [simTraceAt_eq] at hg hg'
    exact simTrace_tick_unique S rho hn hv y (honest_zero S rho hv ht hy) j j' t hg hg'
  tick_of_awake := fun y t hy ht hp hw => simTraceAt_tick_of_awake S rho hn hv hy ht hp hw
  awake_in_horizon := by
    intro y t hy hw
    have ht := (simTraceAt_awake_bounds S rho hn y t).mp hw
    rw [simTraceAt_eq] at hw ⊢
    exact simTrace_awake_in_horizon S rho hn y (honest_zero S rho hv ht.2.1 hy) t hw
  awake_of_call := fun _ _ _ hc => simTraceAt_awake_of_call S rho hn hv hc
  restart_of_sleep := simTraceAt_restart_of_sleep S rho hn hv
  restart_at_wake := simTraceAt_restart_at_wake S rho hn hv
  sleep_of_restart := simTraceAt_sleep_of_restart S rho hn hv
  block_unforgeable := simTraceAt_block_unforgeable S rho hn hv
  att_unforgeable := simTraceAt_att_unforgeable S rho hn hv
  msg_unforgeable := simTraceAt_msg_unforgeable S rho hn hv
  genesis_root_ok := simTrace_genesis_root_ok S rho hn
  carried_vote_unforgeable := simTraceAt_carried_vote_unforgeable S rho hn hv

/-- TEMP(C2): `simTraceAt_goldilocksRun` at the default start, for the consumers that are not
yet start-generic (C2 step 2 remaining list). Removed at C2 records phase 2 (G9). -/
theorem simTraceAt_goldilocksRun_initial (hv : rho.ExecutionValid)
    [Fact (S.vote.participationKind = none)] : -- TEMP(C2)
    Growing.GoldilocksRun (runProposer S rho hn) (digestOf S rho)
      (honestKeysAt S rho) (simTraceAt S rho hn) :=
  simIni_eq_initial S rho hn ▸ simTraceAt_goldilocksRun S rho hn hv

end Consensus.Goldilocks.Simulation

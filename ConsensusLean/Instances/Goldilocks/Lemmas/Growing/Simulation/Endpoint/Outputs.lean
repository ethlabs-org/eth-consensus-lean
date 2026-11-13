module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Chains
public import ConsensusLean.Spec.Shape.Claims
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.State
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Publication
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Evidence
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.BlockView
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.ReadTransport
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.Sleepy
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.Outputs

public section

/-! # Engine output transport under growing faults

The growing-fault forms of the static engine transports `engine_outputValid`, `engine_nested`
and `engine_finalMonotone`, without a constant-fault premise. An engine reader honest at its
engine cut `i` is read at the trace cut `cutMap i`. Every trace cut before it is at a time no
later than `rho.cutTime i` (`cutMap_time_le`), so the prefix of the canonical trace through
`rho.cutTime i` is a static run for the keys honest then (`prefix_reader_at`), and the static
node rows apply there:

* `accepted_in_view_at`, `held_in_view_at`, `held_att_in_view_at`: held blocks and their
  attestations are in the reader's engine view (no honesty premise for the acceptance itself);
* `engine_outputValid_at`, `engine_nested_at`, `engine_finalMonotone_at`. -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : BoundSetup)
  (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)

/-- Every trace cut before the mapped cut `cutMap i` is at a time no later than the engine cut's
time `rho.cutTime i`. -/
theorem cutMap_time_le (hv : rho.ExecutionValid) {i : Nat} (hi : i ≤ rho.events.length) :
    ∀ k < cutMap S rho hn i, (simTraceAt S rho hn).time k ≤ rho.cutTime i := by
  cases i with
  | zero =>
    intro k hk
    rw [cutMap_zero] at hk
    exact absurd hk (Nat.not_lt_zero k)
  | succ i =>
    obtain ⟨e, he⟩ : ∃ e, rho.events[i]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hct : rho.cutTime (i + 1) = e.time := by simp [Model.Run.cutTime, he]
    intro k hk
    rw [hct, simTraceAt_eq]
    exact (Obligations.readPoint_after_event S rho hn hv he).1 k hk

/-- Engine cut times lie in `[0, horizon]`. -/
theorem cutTime_bounds (hv : rho.ExecutionValid) {i : Nat} (hi : i ≤ rho.events.length) :
    0 ≤ rho.cutTime i ∧ rho.cutTime i ≤ rho.horizon := by
  have hlaws := (Model.sysOf_laws schema (compiled (goldilocksWith S)) V).trace ⟨E, rho⟩ hv
  have h0 := hlaws.cutTime_mono 0 i (Nat.zero_le i) hi
  have hh := hlaws.cutTime_le_horizon i hi
  change rho.cutTime 0 ≤ rho.cutTime i at h0
  change rho.cutTime i ≤ rho.horizon at hh
  exact ⟨h0, hh⟩

/-- **The reader's prefix run.** For a node honest at `rho.cutTime i`, the prefix of the canonical
trace through `rho.cutTime i` is a static run for the keys honest then, the node's key is one of
them, and the prefix agrees with the trace on the node's state at `cutMap i`. -/
theorem prefix_reader_at {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
    (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) {v : V} {i : Nat}
    (hi : i ≤ rho.events.length) (hh : v ∉ rho.faultyAt (rho.cutTime i)) :
    GoldilocksRun (runProposer S rho hn) (digestOf S rho) (honestKeysAt S rho (rho.cutTime i))
        ((simTraceAt S rho hn).upTo (rho.cutTime i)) ∧
      rho.ownKey v ∈ honestKeysAt S rho (rho.cutTime i) ∧
      ∀ y, ((simTraceAt S rho hn).upTo (rho.cutTime i)).state y (cutMap S rho hn i) =
        (simTraceAt S rho hn).state y (cutMap S rho hn i) := by
  obtain ⟨h0, hh'⟩ := cutTime_bounds S rho hv hi
  exact ⟨(simTraceAt_goldilocksRun S rho hn hv).upTo h0, honest_ownKey_at S rho hh hh',
    fun y => Trace.upTo_state _ y (cutMap_time_le S rho hn hv hi)⟩

/-- An accepted block is in its reader's engine view at every later mapped cut. The acceptance
is an honest event; no honesty of the reader at the later cut is needed. -/
theorem accepted_in_view_at (hv : rho.ExecutionValid) {v : V} {k i : Nat}
    {B : Blk (S.params (pubOf E) hn)}
    (hacc : (simTraceAt S rho hn).AcceptAt (rho.ownKey v) k B)
    (hki : k < cutMap S rho hn i) :
    blockObj (S.params (pubOf E) hn) B ∈ rho.ViewIdx v i := by
  rw [simTraceAt_eq] at hacc
  exact accepted_in_view_of_releases S rho hn hv
    (fun he hp r hr => (tick_block_vote_releases_at S rho hn hv he hp r hr).1) hacc hki

/-- A held non-genesis block of a node honest at its engine cut is in its engine view there. -/
theorem held_in_view_at {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
    (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) {v : V} {i : Nat}
    (hi : i ≤ rho.events.length) (hh : v ∉ rho.faultyAt (rho.cutTime i))
    {B : Blk (S.params (pubOf E) hn)}
    (hB : B ∈ ((simTraceAt S rho hn).state (rho.ownKey v) (cutMap S rho hn i)).fg.tree)
    (hg : B.root ≠ (S.params (pubOf E) hn).genesisRoot) :
    blockObj (S.params (pubOf E) hn) B ∈ rho.ViewIdx v i := by
  obtain ⟨hrun, hy, hs⟩ := prefix_reader_at S rho hn hv hi hh
  rw [← hs] at hB
  rcases Compose.tree_cases hrun.toLocalRun hy hB with hgen | ⟨k, hk, hacc⟩
  · exact (hg (congrArg Block.root hgen)).elim
  · exact accepted_in_view_at S rho hn hv ((RunTrace.upTo_acceptAt _).mp hacc).2 hk

/-- Attestations carried by a held block of a node honest at its engine cut are in its view. -/
theorem held_att_in_view_at {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
    (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) {v : V} {i : Nat}
    (hi : i ≤ rho.events.length) (hh : v ∉ rho.faultyAt (rho.cutTime i))
    {B : Blk (S.params (pubOf E) hn)}
    (hB : B ∈ ((simTraceAt S rho hn).state (rho.ownKey v) (cutMap S rho hn i)).fg.tree)
    {a : FG.Att (Fintype.card V)} (ha : a ∈ B.fgPayload) : attObj a ∈ rho.ViewIdx v i := by
  obtain ⟨hrun, hy, hs⟩ := prefix_reader_at S rho hn hv hi hh
  rw [← hs] at hB
  rcases Compose.tree_cases hrun.toLocalRun hy hB with hgen | ⟨k, hk, hacc⟩
  · subst B
    simp [Params.genesisBlock] at ha
  · have hb := accepted_in_view_at S rho hn hv ((RunTrace.upTo_acceptAt _).mp hacc).2 hk
    obtain ⟨j, o, hj, ho, hc⟩ := rho.mem_viewIdx_iff.mp hb
    refine rho.mem_viewIdx_iff.mpr ⟨j, o, hj, ho, hc.trans (.step ?_ (.refl _))⟩
    change attObj a ∈ payloadObjs B.fgPayload B.acPayload
    exact List.mem_append_left _ (List.mem_map.mpr ⟨a, ha, rfl⟩)

/-- **R.8 output validity under growing faults.** Every read of a node honest at its engine cut
is linked, has increasing positions and proposal-role provenance. The growing form of
`engine_outputValid`: the static argument on the reader's prefix run. -/
theorem engine_outputValid_at {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
    (rho : Model.Run (compiled (goldilocks S)) E)
    (hv : rho.ExecutionValid)
    (g : Out) : OutputValid rho g := by
  intro v i hi hh
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  obtain ⟨hrun, hy, hs⟩ := prefix_reader_at S rho hn hv hi hh
  set T := (simTraceAt S rho hn).upTo (rho.cutTime i)
  have hr := Compose.fg_reachable hrun.toLocalRun hy (cutMap S rho hn i)
  have hvalid := reader_chains_valid S rho hn (cutMap S rho hn i) i hr
    (fun X hX hg => by
      obtain ⟨hroot, _, _, P, _, hpar, _⟩ :=
        (Regimes.validOutput_of_mem hrun hy hX).2 X .refl hg
      exact ⟨hroot, P, hpar⟩)
    fun X hX hg => by
      rw [hs] at hX
      exact held_in_view_at S rho hn hv hi hh hX hg
  rw [read_eq_out S rho hn]
  simp only [outOf, ← simTraceAt_state S rho hn hv hh hi, ← hs]
  cases g with
  | finalized => exact hvalid _ (Store.cache_invariants _ _ _ _ hr).1
  | confirmed =>
    have hΦ := (Store.frame_realization _ _ _ _ hr).1
    exact hvalid _ (Regimes.sa_tips hΦ (stateAt S rho hn v i).now).1.1

/-- **R.8 nesting under growing faults.** At every engine cut of a node honest there, its
finalized read is a prefix of its confirmed read. -/
theorem engine_nested_at {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
    (rho : Model.Run (compiled (goldilocks S)) E)
    (hv : rho.ExecutionValid)
    :
    (chainTrace rho).Nested .finalized .confirmed := by
  intro v i hi hh
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  change i ≤ rho.events.length at hi
  change v ∉ rho.faultyAt (rho.cutTime i) at hh
  obtain ⟨hrun, hy, hs⟩ := prefix_reader_at S rho hn hv hi hh
  have hr := Compose.fg_reachable hrun.toLocalRun hy (cutMap S rho hn i)
  have hΦ := (Store.frame_realization _ _ _ _ hr).1
  have hC := (Regimes.sa_tips (A := (((simTraceAt S rho hn).upTo (rho.cutTime i)).state
    (rho.ownKey v) (cutMap S rho hn i)).ac) hΦ (stateAt S rho hn v i).now).1
  have ha := hΦ.rooted.2 _ hC
  rw [read_eq_out S rho hn, read_eq_out S rho hn]
  simp only [outOf, ← simTraceAt_state S rho hn hv hh hi, ← hs]
  exact chainTo_prefix hr (ha.mono (fun _ h => h.1))

/-- **R.8 final monotonicity under growing faults.** The finalized reads of a node at two ordered
engine cuts at which it is honest only extend. Both cuts are read on the prefix through the later
one. -/
theorem engine_finalMonotone_at {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
    (rho : Model.Run (compiled (goldilocks S)) E)
    (hv : rho.ExecutionValid)
    :
    (chainTrace rho).Monotone .finalized 0 := by
  intro v i j hi hij hj _ hh
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  have hi' : i ≤ rho.events.length := hi.1
  have hj' : j ≤ rho.events.length := hj.1
  change v ∉ rho.faultyAt (rho.cutTime j) at hh
  obtain ⟨hrun, hy, hs⟩ := prefix_reader_at S rho hn hv hj' hh
  have hsi : ((simTraceAt S rho hn).upTo (rho.cutTime j)).state (rho.ownKey v)
      (cutMap S rho hn i) = (simTraceAt S rho hn).state (rho.ownKey v) (cutMap S rho hn i) := by
    have hlaws := (Model.sysOf_laws schema (compiled (goldilocksWith S)) V).trace ⟨E, rho⟩ hv
    have hct : rho.cutTime i ≤ rho.cutTime j := hlaws.cutTime_mono i j hij hj'
    exact Trace.upTo_state _ _ fun k hk => (cutMap_time_le S rho hn hv hi' k hk).trans hct
  have hri := Compose.fg_reachable hrun.toLocalRun hy (cutMap S rho hn i)
  have hrj := Compose.fg_reachable hrun.toLocalRun hy (cutMap S rho hn j)
  rw [read_eq_out S rho hn, read_eq_out S rho hn]
  simp only [outOf]
  rw [simTraceAt_state_all S rho hn hv v i hi', simTraceAt_state_all S rho hn hv v j hj', ← hsi,
    ← hs]
  have hmono := cutMap_mono S rho hn hij
  rw [chainTo_mono hri (Compose.tree_mono hrun.toLocalRun hy hmono)
    (Store.cache_invariants _ _ _ _ hri).1]
  exact chainTo_prefix hrj (Regimes.finalized_monotone _ _ _ _ _ _ hrun _ hy _ _ hmono)

end Consensus.Goldilocks.Simulation

end

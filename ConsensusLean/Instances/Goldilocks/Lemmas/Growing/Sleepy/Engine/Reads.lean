module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.Safety
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Trace
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.State
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Regimes.Inclusion
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Shape
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Chains
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Engine reads at the end of a time, under growing faults

The engine-side read and proposal bridges of the finite sleepy rows, on the canonical growing
trace with the time-indexed honest keys:

* `cutAfter_boundary_at`: the first cut after a time is a boundary of every node;
* `ready_read_cut_at`: an engine node ready at `t ∈ [0, horizon]` reads at the end of `t` the
  state before the first trace cut after `t`, with its stored clock at `t`;
* `ready_proposal_at`: an honest proposal of the trace by a proposer ready at `τ` is an engine
  proposal released at `τ` by a key ready at `τ`;
* `finalized_inBy_at`, `confirmed_inBy_at`: node ancestry of a proposal in the final cache or
  the confirmed read of every ready reader at `t` is engine membership in the corresponding
  output at the end of `t`.

Each is the static bridge of `Obligations/Sleepy` without a constant-fault premise: readers and
proposers are honest at their own read or release time. -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation
open Blocks Shape
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- The first cut after a time is a boundary of every node of the canonical growing trace: a call
there is honest at its time (event-local honesty), and the static boundary applies on the prefix
through it. -/
theorem cutAfter_boundary_at (hv : rho.ExecutionValid) {y : Fin (Fintype.card V)}
    {j : Nat} {t : Time} (hj : Regimes.CutAfter (simTraceAt S rho hn) j t) :
    Regimes.Boundary (simTraceAt S rho hn) y j := by
  rintro ⟨c, hc⟩
  have hy := simTraceAt_call_honest S rho hn hv hc
  have hrun := simTraceAt_goldilocksRun S rho hn hv
  exact Regimes.cutAfter_boundary (hrun.upTo (hrun.time_nonneg j)) hy hj
    ⟨c, (Trace.upTo_callAt_of_le _ le_rfl).2 hc⟩

/-- The engine cut at the end of `t ≥ 0` is at a time `≤ t`. -/
private theorem cutTime_endCut_le {t : Time} (ht : 0 ≤ t) :
    rho.cutTime ((chainTrace rho).endCut t) ≤ t :=
  Nat.findGreatest_spec (P := fun i => rho.cutTime i ≤ t) (Nat.zero_le _)
    (by simpa [Model.Run.cutTime] using ht)

/-- **End-of-time cut under growing faults.** For an engine node ready at `t ∈ [0, horizon]`, the
trace cut of the engine cut at the end of `t` is the first trace cut after `t`, a boundary of the
node, and the node's stored clock there is `t`. -/
theorem ready_read_cut_at (hv : rho.ExecutionValid) {c : Time} (hc : 0 ≤ c) {v : V} {t : Time}
    (ht : 0 ≤ t) (hth : t ≤ rho.horizon) (hr : rho.point.Ready c v t) :
    Regimes.CutAfter (simTraceAt S rho hn) (cutMap S rho hn ((chainTrace rho).endCut t)) t ∧
      Regimes.Boundary (simTraceAt S rho hn) (rho.ownKey v)
        (cutMap S rho hn ((chainTrace rho).endCut t)) ∧
      (stateAt S rho hn v ((chainTrace rho).endCut t)).now = t := by
  classical
  let n := (chainTrace rho).endCut t
  let j := cutMap S rho hn n
  have hnle : n ≤ rho.events.length := Nat.findGreatest_le _
  have hca : Regimes.CutAfter (simTraceAt S rho hn) j t := by
    rw [simTraceAt_eq]
    refine ⟨fun k hk => ?_, ?_⟩
    · have hlen : k < (allCuts S rho hn).length := by
        rw [length_allCuts]
        exact hk.trans_le (cutMap_mono S rho hn hnle)
      have hl : (simTrace S rho hn).label k ≠ none := by
        rw [simTrace_label, List.getElem?_eq_getElem hlen]
        simp
      obtain ⟨_, i, e, _, he, hi, _, _, _, htime, _⟩ := simTrace_cut S rho hn hl
      have hin : i < n := by
        by_contra h
        have := cutMap_mono S rho hn (Nat.le_of_not_gt h)
        omega
      rw [htime]
      exact (event_before_endCut S rho hv ht he).mp hin
    · cases hrj : (allCuts S rho hn)[j]? with
      | none =>
        rw [(simTrace_of_getElem?_none S rho hn hrj).2]
        linarith
      | some r =>
        have hl : (simTrace S rho hn).label j ≠ none := by
          rw [simTrace_label, hrj]; simp
        obtain ⟨_, i, e, _, he, _, hi, _, _, htime, _⟩ := simTrace_cut S rho hn hl
        have hni : n ≤ i := by
          by_contra h
          have := cutMap_mono S rho hn (show i + 1 ≤ n by omega)
          omega
        rw [htime]
        exact lt_of_not_ge fun het => by
          have := (event_before_endCut S rho hv ht he).mpr het
          omega
  refine ⟨hca, cutAfter_boundary_at S rho hn hv hca, ?_⟩
  have hw : E.awake v t = true := hr.2 t (by
    apply max_le ht
    linarith) le_rfl
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (hv.tick_total v t ht hth hr.1 hw)
  have hin : i < n := (event_before_endCut S rho hv ht hi).mpr le_rfl
  rw [now_eq_lastClock S rho hn hv]
  apply lastClock_of_between S rho v t i (Or.inl hi) n hin
  intro k hik hkn e he
  have hlo := keyLe_of_lt S rho hv hi he hik
  have hhi := (event_before_endCut S rho hv ht he).mp hkn
  rcases hlo with hlo | ⟨hlo, _⟩
  · exact le_antisymm hhi hlo.le
  · exact hlo.symm

/-- **Proposal evidence under growing faults.** An honest proposal of the canonical trace by a
proposer ready at `τ ∈ [0, horizon]` (with any hold) is a proposal released at `τ` by a key ready
at `τ` in the engine. -/
theorem ready_proposal_at (hv : rho.ExecutionValid) {c τ h : Time} (hτh : τ ≤ rho.horizon)
    {P : SA.Blk (Fintype.card V) (List (FG.Att (Fintype.card V)))}
    (hP : Regimes.Growing.ReadyProposalAt (simTraceAt S rho hn) (honestKeysAt S rho) c τ h P) :
    ∃ k, rho.point.Ready c (rho.key k) τ ∧
      Shape.HonestProposal rho τ k (headerOf (S.params (pubOf E) hn) P) := by
  obtain ⟨p, k, hr, -, hP, htime⟩ := hP
  have hp := hP.2.1
  subst p
  have hhon : rho.point.HonestAt (rho.key P.proposer) τ := by
    have h := (mem_honestKeysAt_iff S rho τ P.proposer).mp hr.1
    rwa [min_eq_left hτh] at h
  refine ⟨P.proposer, ⟨hhon, ?_⟩, hhon, .proposer P.slot, payloadObjs P.fgPayload P.acPayload,
    rfl, ?_⟩
  · intro u hu hut
    have h := hr.2 u hu hut
    rw [simTraceAt_awake_iff, awakeAt_iff] at h
    exact h.1
  · have hrel := (simTraceAt_simulates S rho hn hv).block_released P.proposer k P
      (by rw [htime]; exact hr.1) hP.1
    rw [htime] at hrel
    exact hrel

/-- **Final-cache ancestry is engine finalized output** under growing faults: if a non-genesis
block is an ancestor of the final cache of every node ready at `t ∈ [0, horizon]` after all
events at `t`, its header is in the finalized read of every engine node ready at `t`. -/
theorem finalized_inBy_at (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn))
    {c t : Time} (hc : 0 ≤ c) (ht : 0 ≤ t) (hth : t ≤ rho.horizon)
    {P : SA.Blk (Fintype.card V) (List (FG.Att (Fintype.card V)))}
    (hroot : P.root ≠ (S.params (pubOf E) hn).genesisRoot)
    (hinc : ∀ y j, Regimes.Growing.ReadyAt (simTraceAt S rho hn) (honestKeysAt S rho) c y t →
      Regimes.CutAfter (simTraceAt S rho hn) j t →
      Anc ((simTraceAt S rho hn).HonestBlocksAt (honestKeysAt S rho)) P
        ((simTraceAt S rho hn).state y j).fg.F) :
    InBy rho c .finalized (headerOf (S.params (pubOf E) hn) P) t := by
  intro v hr
  let i := (chainTrace rho).endCut t
  let j := cutMap S rho hn i
  have hrun := simTraceAt_goldilocksRun S rho hn hv
  have hi : i ≤ rho.events.length := Nat.findGreatest_le _
  have hcut := ready_read_cut_at S rho hn hv hc ht hth hr
  have hready := ready_transport_at S rho hn hv ht hth hr
  obtain ⟨hreach, -, hsub⟩ := held_state hrun ht hcut.1.1 hready.1
  have htip := (Store.cache_invariants _ _ _ _ hreach).1
  have ha := hinc _ j hready hcut.1
  have hanc := anc_in_store hreach (Compose.Growing.honest_blocks_coherent hrun hnc) hsub ha htip
  have hprefix := chainTo_prefix hreach hanc
  have hmem : headerOf (S.params (pubOf E) hn) P ∈
      chainTo ((simTraceAt S rho hn).state (rho.ownKey v) j).fg.blocks (P.slot + 1) P := by
    simp only [chainTo, ite_eq_right hroot]
    split <;> simp
  have hout := hprefix.subset hmem
  have hh : v ∉ rho.faultyAt (rho.cutTime i) := fun h =>
    hr.1 (rho.faultyAt_mono (cutTime_endCut_le S rho ht) h)
  change headerOf (S.params (pubOf E) hn) P ∈ (chainTrace rho).read .finalized v i
  rw [read_eq_out S rho hn, outOf, ← simTraceAt_state S rho hn hv hh hi]
  exact hout

/-- **Inclusion is engine confirmed output** under growing faults: if a proposal released at
`τ ∈ [0, t]` by a proposer ready at `τ` (with any hold) is an ancestor of the confirmed read of
every node ready at `t ≤ horizon` after all events at `t`, its header is in the confirmed read of
every engine node ready at `t`. -/
theorem confirmed_inBy_at (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn))
    {c : Time} (hc : 0 ≤ c) {τ t h : Time} (hτ : 0 ≤ τ) (hτt : τ ≤ t) (hth : t ≤ rho.horizon)
    {P : SA.Blk (Fintype.card V) (List (FG.Att (Fintype.card V)))}
    (hP : Regimes.Growing.ReadyProposalAt (simTraceAt S rho hn) (honestKeysAt S rho) c τ h P)
    (hinc : ∀ y j, Regimes.Growing.ReadyAt (simTraceAt S rho hn) (honestKeysAt S rho) c y t →
      Regimes.CutAfter (simTraceAt S rho hn) j t →
      Anc ((simTraceAt S rho hn).HonestBlocksAt (honestKeysAt S rho)) P
        (Regimes.readAfter (simTraceAt S rho hn) y j t)) :
    InBy rho c .confirmed (headerOf (S.params (pubOf E) hn) P) t := by
  have hrun := simTraceAt_goldilocksRun S rho hn hv
  have hroot : P.root ≠ (S.params (pubOf E) hn).genesisRoot := by
    obtain ⟨p, k, hp, -, hprop, hk⟩ := hP
    obtain ⟨⟨acc, hc⟩, hpos⟩ := hprop.1
    have hr := (hrun.upTo hτ).toLocalRun
    have hc' := (Trace.upTo_callAt_of_le (simTraceAt S rho hn) (d := τ) hk.le).2 hc
    rcases Compose.blockCall_cases hr hp.1 hc' with hg | hg
    · have h0 : (simTraceAt S rho hn).pos k = 0 :=
        (hg.2.1 0 (List.length_pos_iff.mpr hg.1)).2.2.2.1
      exact False.elim (hpos (by simpa using h0))
    · obtain ⟨j, x, _, _, _, d, p', _, hB, _⟩ := hg
      rw [hB, digestOf_eq]
      simp only [Node.mkBlock]
      erw [dgOf_eq]
      exact taggedRoot_ne _ _
  intro v hr
  let i := (chainTrace rho).endCut t
  let j := cutMap S rho hn i
  have hi : i ≤ rho.events.length := Nat.findGreatest_le _
  have ht : 0 ≤ t := hτ.trans hτt
  have hcut := ready_read_cut_at S rho hn hv hc ht hth hr
  have hready := ready_transport_at S rho hn hv ht hth hr
  obtain ⟨hreach, hframe, hsub⟩ := held_state hrun ht hcut.1.1 hready.1
  have htip := (Regimes.sa_tips
    (A := ((simTraceAt S rho hn).state (rho.ownKey v) j).ac) hframe t).1.1
  have ha := hinc _ j hready hcut.1
  have hanc := anc_in_store hreach (Compose.Growing.honest_blocks_coherent hrun hnc) hsub ha htip
  have hprefix := chainTo_prefix hreach hanc
  have hmem : headerOf (S.params (pubOf E) hn) P ∈
      chainTo ((simTraceAt S rho hn).state (rho.ownKey v) j).fg.blocks (P.slot + 1) P := by
    simp only [chainTo, ite_eq_right hroot]
    split <;> simp
  have hout := hprefix.subset hmem
  have hh : v ∉ rho.faultyAt (rho.cutTime i) := fun h =>
    hr.1 (rho.faultyAt_mono (cutTime_endCut_le S rho ht) h)
  change headerOf (S.params (pubOf E) hn) P ∈ (chainTrace rho).read .confirmed v i
  rw [read_eq_out S rho hn, outOf, ← simTraceAt_state S rho hn hv hh hi, hcut.2.2]
  exact hout

end Consensus.Goldilocks.Obligations.Growing

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.RunMap
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.ClaimTransports
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Concrete.Final
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.HealedReadAncestry
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Final-window production at the advertised Goldilocks binding -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape Blocks Generic Obligations

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The extracted four anchors jointly supply the final production window and its evidence. -/
theorem goldilocks_finalWindowSupply (S : Setup) (A : ContractAssumptions S) {E : Env V}
    (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) :
    FinalWindowSupply (goldilocksRunMap S rho hn hv) (K S A) (18 * E.ΔAC) E.ΔAC := by
  classical
  intro hv' hc idx gst t hhealthy hp hm hb hr
  let Q : Growing.FinalQueryAt S A V :=
    { run := ⟨E, rho⟩, hn := hn, index := idx, gst := gst, query := t,
      valid := hv', noCollision := hc, healthy := hhealthy, progress := hp,
      mature := hm, bounded := hb, reader := hr }
  obtain ⟨W, hslack, hrunW, hsteps⟩ := Growing.final_window_extract_at S A V Q
  have hrun := simTraceAt_goldilocksRun S rho hn hv'
  have htime (i : Fin 4) : Q.trace.time (W.cut i) = Q.params.ts (W.block i).slot := by
    rw [(W.proposals i).2.2, Q.params.slotTime_eq]
    rfl
  have hhold (i : Fin 4) : (W.block i).proposer ∈ Q.keys
      (Q.trace.time (W.cut i) + E.ΔAC) := by
    obtain ⟨p, dg, g, d, a, b, -, _, _, hP, _, _⟩ := W.anchorRun_iff.mp hrunW
    obtain ⟨hh, _, _, _, _, _, _, _, _, _, hs, hpr, _⟩ := hP i
    rw [htime i, hs, hpr]
    exact hh
  have hready (i : Fin 4) : ReadyCut Q.trace Q.keys (18 * E.ΔAC)
      (W.block i).proposer (W.cut i) := by
    refine ⟨(W.ready i).1, fun τ hlo hhi => (W.ready i).2 τ ?_ hhi⟩
    have hdur := Growing.final_catchUp_le_cDur_at S A V Q
    apply le_trans (max_le_max_left 0 ?_) hlo
    change Q.trace.time (W.cut i) - _ - 1 ≤ Q.trace.time (W.cut i) - _ - 1
    change 18 * E.ΔAC ≤ _ at hdur
    linarith
  let W' : FinalProductionWindow (goldilocksRunMap S rho hn hv) (18 * E.ΔAC) E.ΔAC t
      (t + ((K S A).params.latency .final idx : Time) * E.ΔAC) :=
    { start := W.start, gap := W.gap, gap_two := W.gap_two, gap_span := W.gap_span,
      block := W.block, cut := W.cut,
      slots := fun i => by
        have hs := W.slots i
        fin_cases i <;> dsimp at hs ⊢ <;> simpa only [Nat.zero_mul, Nat.add_zero,
          Nat.one_mul] using hs,
      proposals := by simpa only [goldilocksRunMap_trace] using W.proposals,
      ready := by simpa only [goldilocksRunMap_trace, goldilocksRunMap_honest] using hready,
      honest_hold := by simpa only [goldilocksRunMap_trace, goldilocksRunMap_honest] using hhold,
      fresh := by simpa only [goldilocksRunMap_trace] using W.fresh,
      ordered := W.ordered,
      bounded := by simpa only [goldilocksRunMap_trace] using W.bounded,
      publication := by simpa only [goldilocksRunMap_trace] using hslack }
  have hroot : (W.block 0).root ≠ Q.params.genesisRoot := by
    exact (Compose.accept_facts (hrun.upTo (hrun.time_nonneg (W.cut 0))).toLocalRun
      (W.ready 0).1 ((RunTrace.upTo_acceptAt _).mpr ⟨le_rfl, W.accepted 0⟩)).2.2.2
  have hengine : rho.point.Ready ((Sys (goldilocks S) V).cDur (K S A) ⟨E, rho⟩)
      (rho.key (W.block 0).proposer) (Q.trace.time (W.cut 0)) := by
    refine ⟨?_, fun τ hlo hhi => ?_⟩
    · have hh := (W.ready 0).1
      rw [mem_honestKeysAt_iff S rho] at hh
      rw [min_eq_left ((W.bounded 0).trans Q.bounded)] at hh
      simpa only [EnvPoint.HonestAt, Model.Run.point] using hh
    · have hh := (W.ready 0).2 τ hlo hhi
      exact ((simTraceAt_awake_bounds S rho hn _ τ).mp hh).1
  refine ⟨W', hroot, ?_, ?_⟩
  · simpa only [goldilocksRunMap_validator, goldilocksRunMap_trace] using hengine
  · simp only [FinalHeightSupply, goldilocksRunMap_trace, goldilocksRunMap_honest]
    exact ⟨W.accepted, W.chain,
      fun i => Growing.anchorStepAt_iff.mp (W.anchorSteps_iff.mp hsteps i)⟩

end Consensus.Goldilocks.Simulation

end

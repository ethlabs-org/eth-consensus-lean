module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Forwarding

public section

/-! # Goldilocks Refinement: the engine simulates the node

`EngineSimulatesNode` (`Statements/Refinement`) assembled from its steps: the trace `simTrace`
with the cut map `cutMap` (`Trace`), a Goldilocks run by `simTrace_goldilocksRun` and agreeing
with the engine by the `Simulates` steps (`Run`). Signed fresh-admission publication remains
an explicit open supplier below; simulation inherits that obligation. -/

namespace Consensus.Goldilocks.Refinement

open Shape
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

omit [DecidableEq V] in
/-- Vote envelopes drain after the actual ordinary/block release prefix when their canonical
votes are held there. No success assumption is imposed on the prefix candidates themselves. -/
theorem releaseAll_voteForward_suffix (hash : Blocks.Header Info → Nat)
    (x : Fin (Fintype.card V))
    (nd : Model.Node (Model.protoOf (compiled (family S)) E))
    (pre : List (Model.protoOf (compiled (family S)) E).Object)
    (vs : List (Time × SA.Vote (Fintype.card V)))
    (hheld : ∀ tv ∈ vs, voteObj tv.2 ∈ Model.closure
      (Model.releaseAll (Model.protoOf (compiled (family S)) E) hash x nd pre).1.seen) :
    let cs : List (Model.protoOf (compiled (family S)) E).Object := vs.map fun tv =>
      .mk (.signed x .poll) (.data (.voteForward tv.1 (encodeVote tv.2))) [voteObj tv.2]
    (Model.releaseAll (Model.protoOf (compiled (family S)) E) hash x nd (pre ++ cs)).2 =
      (Model.releaseAll (Model.protoOf (compiled (family S)) E) hash x nd pre).2 ++ cs := by
  dsimp only
  erw [Model.releaseAll_append (P := Model.protoOf (compiled (family S)) E)]
  dsimp only
  congr 1
  apply (releaseAll_of_prefix_guards (Model.protoOf (compiled (family S)) E)
    hash x _ _ ?_).1
  intro i o hi
  obtain ⟨tv, htv, rfl⟩ := List.mem_map.mp (List.mem_of_getElem? hi)
  refine ⟨releasable_voteForward S x _ tv.1 tv.2 ?_,
    protects_voteForward S x x _ tv.1 tv.2, dependencies_voteForward _ x tv.1 tv.2⟩
  exact Model.closure_mono (fun _ h => List.mem_append_left _ h) (hheld tv htv)

/-- An honest emission cut cannot be a restart, even though `EmitAt` permits that call
syntactically. This uses the actual cut law and the run's nonnegative clock. -/
theorem simTrace_emission_not_restart (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys S rho) {k : Nat}
    {ℓ : ACLabel (goldilocksNode (S.params (pubOf E) hn) (S.ro _))}
    (hc : (simTrace S rho hn).CallAt y k (.ac ℓ))
    {e : SA.Em (S.params (pubOf E) hn) (List (FG.Att (Fintype.card V)))}
    (he : e ∈ ℓ.emits) : ℓ.call ≠ .restart := by
  intro hr
  have hrun := simTrace_goldilocksRun S rho hn hv
  have hstep := (hrun.cutLaw y hy k _ hc).2.1
  rw [hr] at hstep
  have hnil := restart_emits_nil (S.ro _) y (simTrace S rho hn |>.state y k).ac
    ℓ.frame ((simTrace S rho hn).time k) (hrun.time_nonneg k)
  have hemits := congrArg Prod.snd hstep
  rw [hnil] at hemits
  have hempty : ℓ.emits = [] := hemits.symm
  rw [hempty] at he
  exact List.not_mem_nil he

/-- Option C's outstanding publication supplier: actual same-event release and first release,
not merely candidate construction or pool membership. -/
theorem simTrace_vote_forwarded (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ k (m : SA.Vote (Fintype.card V)),
    let tr := simTrace S rho hn
    (tr.EmitAt y k m ∨
      ((tr.MsgCallAt y k m ∨ ∃ ℓ B, tr.CallAt y k (.ac ℓ) ∧ ℓ.call = .block B ∧
          m ∈ SA.blockVotes B) ∧
        m ∉ (tr.state y k).ac.pool m.slot ∧ m ∈ (tr.post k).ac.pool m.slot)) →
    let envelope : (Model.protoOf (compiled (family S)) E).Object :=
      .mk (.signed y .poll) (.data (.voteForward (tr.time k) (encodeVote m))) [voteObj m]
    ∃ i, cutMap S rho hn i ≤ k ∧ k < cutMap S rho hn (i + 1) ∧
      rho.SendsAt (rho.key y) i (tr.time k) ∧ envelope ∈ rho.releasesAt i ∧
      ∀ j < i, envelope ∉ rho.releasesAt j := by
  sorry

/-- The simulating trace and cut map of a valid engine run simulate it. -/
theorem simTrace_simulates (hv : rho.ExecutionValid) :
    Simulates S rho hn (simTrace S rho hn) (cutMap S rho hn) where
  run := simTrace_goldilocksRun S rho hn hv
  ι_zero := cutMap_zero S rho hn
  ι_mono := cutMap_mono S rho hn
  covered := simTrace_covered S rho hn
  state := simTrace_state S rho hn hv
  now := now_eq_lastClock S rho hn hv
  tick_public := simTrace_tick_public_group S rho hn hv
  tick_other := simTrace_tick_other S rho hn hv
  deliver := simTrace_deliver S rho hn hv
  restart := simTrace_restart S rho hn hv
  awake_of := simTrace_awake_of S rho hn hv
  awake_to := simTrace_awake_to S rho hn hv
  block_released := simTrace_block_released S rho hn hv (simTrace_goldilocksRun S rho hn hv)
  vote_released := simTrace_vote_released S rho hn hv (simTrace_goldilocksRun S rho hn hv)
  att_released := simTrace_att_released S rho hn hv (simTrace_goldilocksRun S rho hn hv)
  block_relayed := simTrace_block_relayed S rho hn hv
  vote_forwarded := simTrace_vote_forwarded S rho hn hv
  att_relayed := simTrace_att_relayed S rho hn hv

variable (V) in
/-- **The engine simulates the node** (`EngineSimulatesNode`): every valid engine run of the
family is simulated by `simTrace` with `cutMap`. -/
theorem engineSimulatesNode : EngineSimulatesNode V S :=
  fun _ rho hn hv => ⟨simTrace S rho hn, cutMap S rho hn, simTrace_simulates S rho hn hv⟩

end Consensus.Goldilocks.Refinement

end

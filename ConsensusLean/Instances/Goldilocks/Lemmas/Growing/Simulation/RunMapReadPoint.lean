module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.RunMapRepresentation
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.ClaimTransports
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.ReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Endpoint.Outputs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.Reads

public section

/-! # Goldilocks read points and the stored-read context

`goldilocksRunMap_engineReadPoint` stays at the engine cut time `rho.cutTime i` and the mapped
cut `M.cut i`. `goldilocksStoredReadContext` is the read the protocol makes: its source cut is the
trace cut after the reader's last own event (`lastOwn`), its time the reader's stored clock.
`goldilocksRunMap_storedReadTransport` binds every engine output to that read: the tips and the
reader's states at the two cuts coincide, and under engine readiness with catch-up `c + 1` the
source cut is a ready read point with catch-up `c` at the stored clock, at most one unit before the
cut time (`engine_read_point`). At a claim time `t`, a reader ready at `t` has stored clock `t` at
`endCut t`, read strictly before the mapped cut (`ready_read_cut_at`). Neither `R.cut = M.cut` nor
`R.now = rho.cutTime i` is asserted.
-/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape Blocks Generic
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] (S : Setup) {E : Env V}
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
  (hv : rho.ExecutionValid)

/-- The actual confirmed read at the cut after the last own event and the stored clock. -/
noncomputable def goldilocksStoredReadContext :
    StoredReadContext (goldilocksRunMap S rho hn hv) where
  cut v i := cutMap S rho hn (Obligations.Growing.lastOwn S rho v i)
  now v i := (stateAt S rho hn v i).now
  tip v i := confirmedRead (simTraceAt S rho hn) (rho.ownKey v)
    (cutMap S rho hn (Obligations.Growing.lastOwn S rho v i))
    (stateAt S rho hn v i).now

/-- The source cut is the trace cut after the reader's last own event. -/
theorem goldilocksStoredReadContext_cut (v : V) (i : Nat) :
    (goldilocksStoredReadContext S rho hn hv).cut v i =
      cutMap S rho hn (Obligations.Growing.lastOwn S rho v i) := by rfl

/-- The evaluation time is the reader's stored clock. -/
theorem goldilocksStoredReadContext_now (v : V) (i : Nat) :
    (goldilocksStoredReadContext S rho hn hv).now v i = (stateAt S rho hn v i).now := by rfl

/-- The source tip is the confirmed read at the source cut and the stored clock. -/
theorem goldilocksStoredReadContext_tip (v : V) (i : Nat) :
    (goldilocksStoredReadContext S rho hn hv).tip v i =
      confirmedRead (simTraceAt S rho hn) (rho.ownKey v)
        (cutMap S rho hn (Obligations.Growing.lastOwn S rho v i)) (stateAt S rho hn v i).now := by
  rfl

/-- At the engine cut time `rho.cutTime i`, a node honest there has an honest read point and a
read boundary at its mapped cut `M.cut i`; a mapped `ReadyRead` is a ready read point. Engine
readiness is not transported here (`RegimeTransport.ready` is a separate supplier), and no read
point at the stored clock `M.clock` is supplied. -/
theorem goldilocksRunMap_engineReadPoint :
    EngineReadPoint (goldilocksRunMap S rho hn hv) where
  honest hv' v i hi hh := by
    obtain ⟨h0, hh'⟩ := cutTime_bounds S rho hv' hi
    refine ⟨?_, ⟨(goldilocksRunMap S rho hn hv).before_time i hi,
      (goldilocksRunMap S rho hn hv).after_time i hi⟩, h0, hh'⟩
    rw [goldilocksRunMap_honest, goldilocksRunMap_validator]
    exact honest_ownKey_at S rho hh hh'
  boundary _ v i _ _ := by
    rw [goldilocksRunMap_trace, goldilocksRunMap_validator, goldilocksRunMap_cut]
    exact Obligations.Growing.cutMap_boundary S rho hn (rho.ownKey v) i
  ready _ _ _ _ h := ⟨⟨h.1, ⟨h.2.1, h.2.2.1⟩, h.2.2.2.1, h.2.2.2.2.1⟩, h.2.2.2.2.2⟩

/-- The last-own-event read is the read behind every engine output of the reader. -/
theorem goldilocksRunMap_storedReadTransport :
    StoredReadTransport (goldilocksRunMap S rho hn hv)
      (goldilocksStoredReadContext S rho hn hv) where
  source_tip v i := by
    rw [goldilocksStoredReadContext_tip, goldilocksStoredReadContext_cut,
      goldilocksStoredReadContext_now, goldilocksRunMap_trace, goldilocksRunMap_validator]
    rfl
  current_tip hv' v i hi _ := by
    rw [goldilocksStoredReadContext_tip, goldilocksRunMap_trace, goldilocksRunMap_validator,
      goldilocksRunMap_cut, goldilocksRunMap_clock, ← stateAt_eq]
    exact Obligations.Growing.readAfter_lastOwn S rho hn hv' v hi _
  source_state hv' v i hi := by
    have h₁ := simTraceAt_state_all S rho hn hv' v _
      ((Obligations.Growing.lastOwn_spec S rho v i).1.trans hi)
    rw [← Obligations.Growing.stateAt_lastOwn] at h₁
    rw [goldilocksStoredReadContext_cut, goldilocksRunMap_trace, goldilocksRunMap_validator,
      goldilocksRunMap_cut]
    exact h₁.symm.trans (simTraceAt_state_all S rho hn hv' v i hi)
  now_bound hv' v i hi _ := by
    rw [goldilocksStoredReadContext_now]
    exact (Obligations.now_bounds_cut S rho hn hv' v hi).2.trans (cutTime_bounds S rho hv' hi).2
  now_mono hv' v := Obligations.now_mono S rho hn hv' v
  cut_mono v _ _ h := cutMap_mono S rho hn (Obligations.Growing.lastOwn_mono S rho v h)
  ready_point hv' c hc v i hi hr := by
    obtain ⟨hrp, hn0, hnh, hready, -⟩ :=
      Obligations.Growing.engine_read_point S rho hn hv' hc hi hr
    simp only [goldilocksRunMap_trace, goldilocksRunMap_honest, goldilocksRunMap_validator,
      goldilocksStoredReadContext_cut, goldilocksStoredReadContext_now]
    exact ⟨⟨⟨hready.1, hrp, hn0, hnh⟩, hready.2⟩,
      Obligations.Growing.cutMap_boundary S rho hn (rho.ownKey v) _,
      Obligations.stored_now_ge_cutTime_sub_one S rho hn hv' hi hc hr⟩
  end_read hv' c hc v t ht hth hr := by
    obtain ⟨hca, hb, hnow⟩ := Obligations.Growing.ready_read_cut_at S rho hn hv' hc ht hth hr
    have hrd := Obligations.Growing.ready_transport_at S rho hn hv' ht hth hr
    simp only [goldilocksRunMap_trace, goldilocksRunMap_cut, goldilocksRunMap_honest,
      goldilocksRunMap_validator, goldilocksStoredReadContext_now]
    exact ⟨hnow, hca.2, ⟨⟨hrd.1, ⟨hca.1, hca.2.le⟩, ht, hth⟩, hrd.2⟩, hb⟩

end Consensus.Goldilocks.Simulation

end

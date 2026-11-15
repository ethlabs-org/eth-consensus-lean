module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.RunMapRepresentation
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.ClaimTransports
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.ReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Endpoint.Outputs

public section

/-! # Goldilocks read points and the stored-read context

`goldilocksRunMap_engineReadPoint` stays at the engine cut time `rho.cutTime i` and the mapped
cut `M.cut i`. `goldilocksStoredReadContext` is the read the protocol makes: its source cut is the
trace cut after the reader's last own event (`lastOwn`), its time the reader's stored clock.
`goldilocksRunMap_storedReadTransport` only identifies the two tips. It asserts neither
`R.cut = M.cut` nor `R.now = rho.cutTime i`, and no readiness, read point or boundary at the
source cut.

OPEN, not supplied here: the ready read point at the stored clock. Engine readiness with catch-up
`c + 1` at `rho.cutTime i` gives local readiness with catch-up `c` at `(R.cut v i, R.now v i)`
(`Obligations.Growing.engine_read_point`, `ready_at_stored_now`). No generic contract states it,
and `ClaimDeadlineFit.catchUp` is one unit short for it (ledger row "stored-clock read point").
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

/-- The last-own-event read equals the current mapped confirmed tip at the stored clock. -/
theorem goldilocksRunMap_storedReadTransport :
    StoredReadTransport (goldilocksRunMap S rho hn hv)
      (goldilocksStoredReadContext S rho hn hv) := by
  constructor
  · intro v i
    rw [goldilocksStoredReadContext_tip, goldilocksStoredReadContext_cut,
      goldilocksStoredReadContext_now, goldilocksRunMap_trace, goldilocksRunMap_validator]
    rfl
  · intro hv' v i hi _
    rw [goldilocksStoredReadContext_tip, goldilocksRunMap_trace, goldilocksRunMap_validator,
      goldilocksRunMap_cut, goldilocksRunMap_clock, ← stateAt_eq]
    exact Obligations.Growing.readAfter_lastOwn S rho hn hv' v hi _
  · intro hv' v i hi _
    rw [goldilocksStoredReadContext_now]
    exact (Obligations.now_bounds_cut S rho hn hv' v hi).2.trans (cutTime_bounds S rho hv' hi).2

/-- The stored context of a public-indexed binding map: the fields of
`goldilocksStoredReadContext`, which do not depend on the map. -/
noncomputable def goldilocksEngineStoredReadContext (pub : Model.Public) (hn : 1 ≤ pub.n)
    (E : Env V) (hE : pubOf E = pub)
    (rho : Model.Run (compiled (goldilocks S)) E) (hv : rho.ExecutionValid) :
    StoredReadContext ((goldilocksEngineBinding S pub hn).map E hE rho hv) := by
  subst pub
  exact ⟨(goldilocksStoredReadContext S rho hn hv).cut,
    (goldilocksStoredReadContext S rho hn hv).now, (goldilocksStoredReadContext S rho hn hv).tip⟩

/-- The public-indexed binding supplies engine cut-time read points. -/
theorem goldilocksEngineBinding_engineReadPoint (pub : Model.Public) (hn : 1 ≤ pub.n)
    (E : Env V) (hE : pubOf E = pub)
    (rho : Model.Run (compiled (goldilocks S)) E) (hv : rho.ExecutionValid) :
    EngineReadPoint ((goldilocksEngineBinding S pub hn).map E hE rho hv) := by
  subst pub
  rw [goldilocksEngineBinding_map]
  exact goldilocksRunMap_engineReadPoint S rho hn hv

/-- The public-indexed binding supplies the actual stored-read correspondence. -/
theorem goldilocksEngineBinding_storedReadTransport (pub : Model.Public) (hn : 1 ≤ pub.n)
    (E : Env V) (hE : pubOf E = pub)
    (rho : Model.Run (compiled (goldilocks S)) E) (hv : rho.ExecutionValid) :
    StoredReadTransport ((goldilocksEngineBinding S pub hn).map E hE rho hv)
      (goldilocksEngineStoredReadContext S pub hn E hE rho hv) := by
  subst pub
  have key : ∀ (M : Generic.RunMap (A := goldilocksNode (S.params (pubOf E) hn) (S.ro _)) rho
      (payloadOf S)) (_ : M = goldilocksRunMap S rho hn hv),
      StoredReadTransport M
        ⟨(goldilocksStoredReadContext S rho hn hv).cut,
          (goldilocksStoredReadContext S rho hn hv).now,
          (goldilocksStoredReadContext S rho hn hv).tip⟩ := by
    intro M h
    subst h
    exact goldilocksRunMap_storedReadTransport S rho hn hv
  exact key _ (goldilocksEngineBinding_map S E hn rho hv)

end Consensus.Goldilocks.Simulation

end

module
public import ConsensusModelProofs.Canonical.Network
public import ConsensusModelProofs.Credentials

@[expose] public section

/-! # A canonical execution for every protocol

At every integer time through the horizon, schedule honest wake restarts,
then awake honest ticks, then deliveries of the finite pool of all
objects released so far to all awake honest nodes. Objects are deduplicated
within each recipient's delivery batch. Delivering again at later times makes
the network service independent of sleep history.

With a GST `g` (`canonical_run_from`), the delivery layer is empty at times
before `g`: the log is eager from `g` (`CommLog.EagerFrom`), so `g ≤ 0` is a
synchronous run and `g` past the horizon a silent one. Transactions are
relayed eagerly in every case.

The construction uses no laws about the protocol. `unforgeable_of_causal`
and `credentials_of_causal` use only the engine's signing and seen filter;
`delivers_of_eager` applies to every deadline at or after its start,
including both contract deadlines (receipt at the deadline is L0 holding).
-/

namespace Consensus.Model

/-- All submissions accepted by awake honest sources through time `a`,
relayed eagerly to every awake honest recipient. -/
noncomputable def eagerRelay {V : Type} [Fintype V] [DecidableEq V]
    (E : Env V) (honest : Finset V) (submit : V → Time → List Tx)
    (w : V) (a : Time) : List Tx :=
  if w ∈ honest ∧ E.awake w a = true then
    honest.toList.flatMap fun u =>
      mempool (fun v τ => if E.awake v τ then submit v τ else []) u a
  else []

/-- The eager relay serves every awake honest recipient at every time from
the submission on, whatever the event list. -/
theorem eagerRelay_txs {O : OutputSchema} {F : Family O} {V : Type} [Fintype V] [DecidableEq V]
    {E : Env V} (rho : Run F E) (hrel : rho.relay = eagerRelay E rho.honest rho.submit) :
    rho.EagerTxDelivery := by
  intro u hu x τ hτ haw hx w hw a hτa hwa
  dsimp only [Time] at *
  change x ∈ rho.submit w a ++ rho.relay w a
  apply List.mem_append_right
  rw [hrel]
  simp only [eagerRelay, hw, hwa, and_self, ↓reduceIte]
  apply List.mem_flatMap.mpr
  refine ⟨u, Finset.mem_toList.mpr hu, ?_⟩
  rw [mempool, ite_eq_right (not_lt.mpr (le_trans hτ hτa))]
  apply List.mem_flatMap.mpr
  refine ⟨τ, ?_, ?_⟩
  · rw [List.bind_eq_flatMap]
    apply List.mem_flatMap.mpr
    refine ⟨τ.toNat, List.mem_range.mpr ?_, ?_⟩
    · have := Int.toNat_le_toNat hτa; omega
    · change τ ∈ [(τ.toNat : Int)]
      simp [Int.toNat_of_nonneg hτ]
  · simpa [haw] using hx

/-- The canonical schedule with GST `g` is a valid execution. -/
theorem Run.canonical_valid {O : OutputSchema} {F : Family O} {V : Type} [Fintype V]
    [DecidableEq V] {E : Env V} (base : Run F E) (hh : 0 ≤ base.horizon) (hsel : base.SelValid)
    (g : Time) : (base.withEvents (base.canonicalEvents g)).ExecutionValid :=
  ⟨base.canonical_schedule g hh, base.canonical_sleep g,
    (base.withEvents (base.canonicalEvents g)).unforgeable_of_causal (base.canonical_causal g),
    hsel,
    (base.withEvents (base.canonicalEvents g)).credentials_of_causal (base.canonical_causal g)⟩

/-- `canonical_run_from` with one more fact about the schedule: its network
is causal (every delivery is an earlier release), so it carries no object
that no honest node released. -/
theorem canonical_run_from_causal (O : OutputSchema) (F : Family O) (V : Type) [Fintype V]
    [DecidableEq V] (E : Env V) (honest : Finset V) (horizon : Time) (hh : 0 ≤ horizon)
    (key : Fin (Fintype.card V) ≃ V) (sel : (protoOf F E).Role → Finset (Fin (Fintype.card V)))
    (hsel : ∀ r, ((protoOf F E).selSpec r).Admits (sel r))
    (submit : V → Time → List Tx) (hash : (protoOf F E).Item → Nat) (g : Time) :
    ∃ (relay : V → Time → List Tx) (events : List (Event V (protoOf F E).Object)),
      let rho := mkRun (F := F) (E := E) honest horizon key sel submit relay hash events
      rho.ExecutionValid ∧ CommLog.EagerFrom rho.point rho.log g ∧ rho.Causal := by
  classical
  let relay := eagerRelay E honest submit
  let base := mkRun (F := F) (E := E) honest horizon key sel submit relay hash []
  refine ⟨relay, base.canonicalEvents g, ?_⟩
  change (base.withEvents (base.canonicalEvents g)).ExecutionValid ∧
    CommLog.EagerFrom (base.withEvents (base.canonicalEvents g)).point
      (base.withEvents (base.canonicalEvents g)).log g ∧
    (base.withEvents (base.canonicalEvents g)).Causal
  exact ⟨base.canonical_valid hh hsel g, ⟨base.canonical_eagerFrom g hh, base.canonical_quiet g,
    eagerRelay_txs (base.withEvents (base.canonicalEvents g)) rfl⟩, base.canonical_causal g⟩

/-- The synchronous case (`g = 0`) of `canonical_run_from_causal`. -/
theorem canonical_run_causal (O : OutputSchema) (F : Family O) (V : Type) [Fintype V]
    [DecidableEq V] (E : Env V) (honest : Finset V) (horizon : Time) (hh : 0 ≤ horizon)
    (key : Fin (Fintype.card V) ≃ V) (sel : (protoOf F E).Role → Finset (Fin (Fintype.card V)))
    (hsel : ∀ r, ((protoOf F E).selSpec r).Admits (sel r))
    (submit : V → Time → List Tx) (hash : (protoOf F E).Item → Nat) :
    ∃ (relay : V → Time → List Tx) (events : List (Event V (protoOf F E).Object)),
      let rho := mkRun (F := F) (E := E) honest horizon key sel submit relay hash events
      rho.ExecutionValid ∧ CommLog.PSync rho.point rho.log 0 ∧
        (∀ cut, CommLog.SyncUntil rho.point rho.log cut) ∧ rho.Causal := by
  obtain ⟨relay, events, hv, he, hc⟩ :=
    canonical_run_from_causal O F V E honest horizon hh key sel hsel submit hash 0
  have hns : CommLog.SendsFromZero (mkRun (F := F) (E := E) honest horizon key sel submit relay
      hash events).point (mkRun (F := F) (E := E) honest horizon key sel submit relay
      hash events).log := by
    rintro v - o t ⟨i, hi, -⟩
    exact (hv.in_horizon _ (List.mem_of_getElem? hi)).1
  exact ⟨relay, events, hv, he.psync le_rfl, fun cut => he.syncUntil hns le_rfl cut, hc⟩

/-- A canonical run from every GST: the canonical schedule with its delivery
layer empty before `g` is a valid execution whose log is eager from `g`. -/
theorem canonical_run_from : CanonicalRunFrom := by
  intro O F V _ _ E honest horizon hh key sel hsel submit hash g
  classical
  let relay := eagerRelay E honest submit
  let base := mkRun (F := F) (E := E) honest horizon key sel submit relay hash []
  refine ⟨relay, base.canonicalEvents g, ?_⟩
  change (base.withEvents (base.canonicalEvents g)).ExecutionValid ∧
    CommLog.EagerFrom (base.withEvents (base.canonicalEvents g)).point
      (base.withEvents (base.canonicalEvents g)).log g
  refine ⟨base.canonical_valid hh hsel g, ⟨?_, ?_, ?_⟩⟩
  · exact base.canonical_eagerFrom g hh
  · exact base.canonical_quiet g
  · exact eagerRelay_txs (base.withEvents (base.canonicalEvents g)) rfl

/-- Every choice of protocol, environment, PKI, admissible selection and run
data admits a valid synchronous run. -/
theorem canonical_run : CanonicalRun := by
  intro O F V _ _ E honest horizon hh key sel hsel submit hash
  obtain ⟨relay, events, hv, hs, hp, -⟩ :=
    canonical_run_causal O F V E honest horizon hh key sel hsel submit hash
  exact ⟨relay, events, hv, hs, hp⟩

end Consensus.Model
end

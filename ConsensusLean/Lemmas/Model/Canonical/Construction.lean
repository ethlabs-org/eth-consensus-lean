module
public import ConsensusLean.Lemmas.Model.Canonical.Network
public import ConsensusLean.Lemmas.Model.Credentials

public section

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
and `credentials_of_causal` use only the engine's signing and seen filter.
-/

namespace Consensus.Model

/-- All submissions accepted by awake honest sources through time `a`,
relayed eagerly to every awake honest recipient. -/
noncomputable def eagerRelay {V : Type} [Fintype V] [DecidableEq V]
    (E : Env V) (faultyAt : Time → Finset V) (submit : V → Time → List Tx)
    (w : V) (a : Time) : List Tx :=
  if w ∉ faultyAt a ∧ E.awake w a = true then
    Finset.univ.toList.flatMap fun u =>
      mempool (fun v τ => if v ∉ faultyAt τ ∧ E.awake v τ = true then submit v τ else []) u a
  else []

theorem eagerRelay_apply {V : Type} [Fintype V] [DecidableEq V]
    (E : Env V) (faultyAt : Time → Finset V) (submit : V → Time → List Tx) (w : V) (a : Time) :
    eagerRelay E faultyAt submit w a =
      if w ∉ faultyAt a ∧ E.awake w a = true then
        Finset.univ.toList.flatMap fun u =>
          mempool (fun v τ => if v ∉ faultyAt τ ∧ E.awake v τ = true then submit v τ else []) u a
      else [] := by rfl

/-- The eager relay serves every awake honest recipient at every time from
the submission on, whatever the event list. -/
theorem eagerRelay_txs {O : OutputSchema} {F : ProtocolFamily O} {V : Type} [Fintype V]
    [DecidableEq V]
    {E : Env V} (rho : Run F E) (hrel : rho.relay = eagerRelay E rho.faultyAt rho.submit) :
    rho.EagerTxDelivery := by
  rw [Run.eagerTxDelivery_iff]
  intro u x τ hτ hu haw hx w a hτa hw hwa
  dsimp only [Time] at *
  change x ∈ rho.submit w a ++ rho.relay w a
  apply List.mem_append_right
  rw [hrel]
  simp only [eagerRelay_apply, hw, hwa]
  apply List.mem_flatMap.mpr
  refine ⟨u, Finset.mem_toList.mpr (Finset.mem_univ u), ?_⟩
  rw [mempool, ite_eq_right (not_lt.mpr (le_trans hτ hτa))]
  apply List.mem_flatMap.mpr
  refine ⟨τ, ?_, ?_⟩
  · rw [List.bind_eq_flatMap]
    apply List.mem_flatMap.mpr
    refine ⟨τ.toNat, List.mem_range.mpr ?_, ?_⟩
    · have := Int.toNat_le_toNat hτa; omega
    · change τ ∈ [(τ.toNat : Int)]
      simp [Int.toNat_of_nonneg hτ]
  · simpa [hu, haw] using hx

/-- The canonical schedule with GST `g` is a valid execution. -/
theorem Run.canonical_valid {O : OutputSchema} {F : ProtocolFamily O} {V : Type} [Fintype V]
    [DecidableEq V] {E : Env V} (base : Run F E) (hh : 0 ≤ base.horizon) (hsel : base.SelValid)
    (g : Time) : (base.withEvents (base.canonicalEvents g)).ExecutionValid :=
  base.canonical_valid_of g hh
    ((base.withEvents (base.canonicalEvents g)).unforgeable_of_causal (base.canonical_causal g))
    (by rw [Run.withEvents_eq]; exact hsel)
    ((base.withEvents (base.canonicalEvents g)).credentials_of_causal (base.canonical_causal g))

/-- `canonical_run_from` with one more fact about the schedule: its network
is causal (every delivery is an earlier release), so it carries no object
that no honest node released. -/
theorem canonical_run_from_causal (O : OutputSchema) (F : ProtocolFamily O) (V : Type) [Fintype V]
    [DecidableEq V] (E : Env V) (faultyAt : Time → Finset V) (hmono : Monotone faultyAt)
    (horizon : Time) (hh : 0 ≤ horizon)
    (key : Fin (Fintype.card V) ≃ V) (sel : (protoOf F E).Role → Finset (Fin (Fintype.card V)))
    (hsel : (protoOf F E).SelAdmits sel)
    (submit : V → Time → List Tx) (hash : (protoOf F E).Item → Nat) (g : Time) :
    ∃ (relay : V → Time → List Tx) (events : List (Event V (protoOf F E).Object)),
      let rho := Run.mk (F := F) (E := E) faultyAt hmono horizon events key sel submit relay hash
      rho.ExecutionValid ∧ CommLog.EagerFrom rho.point rho.log g ∧ rho.Causal := by
  classical
  let relay := eagerRelay E faultyAt submit
  let base := Run.mk (F := F) (E := E) faultyAt hmono horizon [] key sel submit relay hash
  refine ⟨relay, base.canonicalEvents g, ?_⟩
  have hb : Run.mk (F := F) (E := E) faultyAt hmono horizon (base.canonicalEvents g)
      key sel submit relay hash = base.withEvents (base.canonicalEvents g) := by
    rw [Run.withEvents_eq]
  simp only [hb]
  exact ⟨base.canonical_valid hh hsel g,
    ⟨by rw [Run.withEvents_point]; exact base.canonical_eagerFrom g hh, base.canonical_quiet g,
    Run.eagerTxDelivery_iff.mp <|
      eagerRelay_txs (base.withEvents (base.canonicalEvents g)) (by rw [Run.withEvents_eq])⟩,
    base.canonical_causal g⟩

/-- Every PKI, admissible selection, submission function, hash and GST `g`
admits a valid run whose log is eager from `g` (L0 `CommLog.EagerFrom`): no
message is received before `g`, and from `g` on every honest send is received
by every awake honest node. `g ≤ 0` is a synchronous run; `g` past the horizon
is a silent run (no receipts at all); in between, the network is asynchronous
before `g`. -/
theorem canonical_run_from (O : OutputSchema) (F : ProtocolFamily O) (V : Type) [Fintype V]
    [DecidableEq V] (E : Env V) (faultyAt : Time → Finset V) (hmono : Monotone faultyAt)
    (horizon : Time) (hh : 0 ≤ horizon)
    (key : Fin (Fintype.card V) ≃ V) (sel : (protoOf F E).Role → Finset (Fin (Fintype.card V)))
    (hsel : (protoOf F E).SelAdmits sel)
    (submit : V → Time → List Tx) (hash : (protoOf F E).Item → Nat) (g : Time) :
    ∃ (relay : V → Time → List Tx) (events : List (Event V (protoOf F E).Object)),
      let rho := Run.mk (F := F) (E := E) faultyAt hmono horizon events key sel submit relay hash
      rho.ExecutionValid ∧ CommLog.EagerFrom rho.point rho.log g := by
  obtain ⟨relay, events, hv, he, -⟩ :=
    canonical_run_from_causal O F V E faultyAt hmono horizon hh key sel hsel submit hash g
  exact ⟨relay, events, hv, he⟩

end Consensus.Model
end

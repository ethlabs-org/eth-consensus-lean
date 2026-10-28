module
public import ConsensusModelProofs.Canonical.Network
public import ConsensusModelProofs.Credentials

@[expose] public section

/-! # A canonical execution for every protocol

At every integer time through the horizon, schedule honest wake restarts,
then awake honest public ticks, then deliveries of the finite pool of all
objects released so far to all awake honest nodes. Objects are deduplicated
within each recipient's delivery batch. Delivering again at later times makes
the network service independent of sleep history.

The construction uses no laws about the protocol. `unforgeable_of_causal`
and `credentials_of_causal` use only the engine's signing and seen filter;
`delivers_of_eager` applies to every deadline strictly after its start,
including both contract deadlines.
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

/-- Every choice of protocol, environment, PKI, admissible selection and run
data admits a valid run
with partial synchrony and healthy delivery on every prefix. -/
theorem canonical_run : CanonicalRun := by
  intro O F V _ _ E honest horizon hh key sel hsel submit hash
  classical
  let relay := eagerRelay E honest submit
  let base := mkRun (F := F) (E := E) honest horizon key sel submit relay hash []
  refine ⟨relay, base.canonicalEvents, ?_⟩
  change (base.withEvents base.canonicalEvents).ExecutionValid ∧
    (base.withEvents base.canonicalEvents).PartialSynchrony ∧
    ∀ cut, (base.withEvents base.canonicalEvents).HealthyPrefixDelivery cut
  have hs := base.canonical_schedule hh
  have hw := base.canonical_sleep
  have he := base.canonical_eager hh
  have ht : (base.withEvents base.canonicalEvents).EagerTxDelivery := by
    intro u hu x τ hτ haw hx w hw a hτa hwa
    change u ∈ honest at hu
    change w ∈ honest at hw
    change x ∈ submit u τ at hx
    dsimp only [Time] at *
    change x ∈ submit w a ++ relay w a
    apply List.mem_append_right
    simp only [relay, eagerRelay, hw, hwa, and_self, ↓reduceIte]
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
  refine ⟨⟨hs, hw, ?_, hsel, ?_⟩, ?_, ?_⟩
  · exact (base.withEvents base.canonicalEvents).unforgeable_of_causal base.canonical_causal
  · exact (base.withEvents base.canonicalEvents).credentials_of_causal base.canonical_causal
  · exact (base.withEvents base.canonicalEvents).partialSynchrony_of_eager hw he ht
  · exact (base.withEvents base.canonicalEvents).healthyPrefixDelivery_of_eager hw he ht

end Consensus.Model
end

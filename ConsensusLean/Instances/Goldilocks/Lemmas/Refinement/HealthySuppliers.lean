module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.NonfinalSuppliers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.WeakBase

public section
namespace Consensus.Goldilocks.Refinement
open Blocks Shape

variable (S : Setup) (A : AcceptanceAssumptions S) (V : Type)
  [Fintype V] [DecidableEq V]

/-- Healthy context carries no progress beyond the separately supplied interval. -/
structure HealthyPreparationQuery where
  run : (Sys (family S) V).Run
  hn : 1 ≤ Fintype.card V
  cap : Capability
  nonfinal : cap = .available ∨ cap = .stable
  index : (K S A).Idx
  gst : Time
  valid : (Sys (family S) V).Valid run
  noCollision : ¬ run.2.HashCollision
  healthy : (Sys (family S) V).Healthy (K S A) gst run

namespace HealthyPreparationQuery
variable {S A V}
abbrev params (Q : HealthyPreparationQuery S A V) := S.params (Model.pubOf Q.run.1) Q.hn
noncomputable abbrev trace (Q : HealthyPreparationQuery S A V) := simTrace S Q.run.2 Q.hn
noncomputable abbrev heal (Q : HealthyPreparationQuery S A V) :=
  (Sys (family S) V).heal (K S A) Q.cap Q.index Q.gst Q.run
noncomputable abbrev ready (Q : HealthyPreparationQuery S A V) :=
  (Sys (family S) V).ready (K S A) Q.gst Q.run
noncomputable abbrev cut (Q : HealthyPreparationQuery S A V) :=
  cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut Q.heal)
end HealthyPreparationQuery

/-- Global inventory obligation, exactly the initialization required by
oldHonest_inventory_preserved. OldHonest includes signed entries not yet held by
the receiver. OldEntryCovered has an eventual whole-run origin: this predicate
is NOT prefix-local preparation and supplies no vote-label/causal strengthening. -/
def HealthyOldInventory (Q : HealthyPreparationQuery S A V) (s₀ i : Nat) : Prop :=
  ∀ y ∈ honestKeys S Q.run.2, ∀ E h,
    Healing.OldHonest Q.trace (honestKeys S Q.run.2) s₀ E h →
      Healing.OldEntryCovered Q.trace (honestKeys S Q.run.2) s₀ E ∨
        h < (Q.trace.state y i).fg.hj

/-- Arithmetic required by the existing weak-base consumers. This records
explicit lower/upper timing, not an unconstrained existential reset label.
The production of these margins is part of the joint coefficient obligation. -/
structure HealthyBaseTiming (Q : HealthyPreparationQuery S A V) where
  slot : Nat
  ready_le : Q.ready ≤ Q.params.ts slot
  records : Q.params.ts slot + 6 * Q.params.Δ ≤ Q.heal
  caches : Q.params.ts (slot + 2 : Nat) ≤ Q.heal
  expiry : Q.params.ts (slot + Q.params.k : Nat) ≤ Q.heal
  service : Q.params.ts (slot + 2 : Nat) + 6 * Q.params.Δ ≤ Q.heal

/-- OPEN base production (healing §§27/28, OldHonest initialization). No argument
from monotone hj establishes this leaf. It selects timing and initializes the
all-honest global inventory, including later first arrivals. No new Healthy
premise, whole-run progress, or prefix-causal coverage is asserted. -/
theorem healthy_old_inventory_initialize (Q : HealthyPreparationQuery S A V)
    (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.run.2.horizon)
    (hp : (Sys (family S) V).prog (shapeProgress (family S) V) (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run) :
    ∃ W : HealthyBaseTiming S A V Q, HealthyOldInventory S A V Q W.slot Q.cut := by
  sorry

/-- Existing proven preservation consumes exactly the OPEN initialization.
It ranges over ALL later cuts, not merely end-of-time observations. It does not
turn eventual coverage into prefix-produced coverage or give a vote label bound. -/
theorem healthy_old_inventory_preserve (Q : HealthyPreparationQuery S A V)
    {s₀ : Nat} (base : HealthyOldInventory S A V Q s₀ Q.cut) :
    ∀ i, Q.cut ≤ i → HealthyOldInventory S A V Q s₀ i := by
  exact Healing.oldHonest_inventory_preserved
    (simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid) base

/-- OPEN first-arrival realization: a held honest row with the consumer's exact
old-source antecedent identifies an OldHonest self-entry at its actual replay
height. This does not posit ToFGAt for the particular D from that antecedent.
The entry E is distinct from D and has root a.T. -/
theorem healthy_old_row_realize (Q : HealthyPreparationQuery S A V) {s₀ : Nat}
    {y : Fin Q.params.n} (hy : y ∈ honestKeys S Q.run.2) {i : Nat}
    {X : SA.Blk Q.params.n (List (FG.Att Q.params.n))}
    (hX : X ∈ (Q.trace.state y i).fg.tree) {a : FG.Att Q.params.n}
    (ha : a ∈ X.fgPayload) (hav : a.val ∈ honestKeys S Q.run.2)
    (hold : ∃ D C l, Compose.IsHonestSource Q.trace (honestKeys S Q.run.2) D a.T ∧
      Compose.Origin Q.trace (honestKeys S Q.run.2) C l ∧ l < s₀ ∧
      Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) D C) :
    ∃ E, E.root = a.T ∧
      Healing.OldHonest Q.trace (honestKeys S Q.run.2) s₀ E
        ((Q.trace.state y i).fg.σ a.T).h := by
  sorry

/-- Consumer-facing state facts at an arbitrary canonical cut, including cuts
inside a timestamp. These have eventual origin witnesses, explicitly not causal
prefix witnesses. No stronger OriginBefore is inferred from a label bound. -/
structure HealthyStateFacts (Q : HealthyPreparationQuery S A V) (s₀ i : Nat) : Prop where
  records : ∀ y ∈ honestKeys S Q.run.2,
    ∃ C ∈ (Q.trace.state y i).fg.tree,
      C.root = (Q.trace.state y i).ac.latestConfirmed ∧
      (Compose.OnOriginChainFrom Q.trace (honestKeys S Q.run.2) C s₀ ∨
        Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) C (Q.trace.state y i).fg.F)
  caches : ∀ y ∈ honestKeys S Q.run.2,
    Compose.OnOriginChainFrom Q.trace (honestKeys S Q.run.2) (Q.trace.state y i).fg.F s₀ ∧
    Compose.OnOriginChainFrom Q.trace (honestKeys S Q.run.2) (Q.trace.state y i).fg.J s₀
  locks : ∀ y ∈ honestKeys S Q.run.2, ∀ l ∈ (Q.trace.state y i).ac.locks,
    s₀ ≤ l.slot → ∃ L ∈ (Q.trace.state y i).fg.tree, L.root = l.block ∧
      Compose.OnOriginChainFrom Q.trace (honestKeys S Q.run.2) L s₀
  inventory : HealthyOldInventory S A V Q s₀ i

/-- OPEN preparation consumes global initialization. Records/caches/locks are
separate mathematical obligations, not consequences of hj monotonicity.
This statement promises only the actual heal boundary, not all earlier states. -/
theorem healthy_prepare (Q : HealthyPreparationQuery S A V)
    (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.run.2.horizon)
    (hp : (Sys (family S) V).prog (shapeProgress (family S) V) (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run)
    (W : HealthyBaseTiming S A V Q)
    (base : HealthyOldInventory S A V Q W.slot Q.cut) :
    HealthyStateFacts S A V Q W.slot Q.cut := by
  sorry

/-- OPEN state preservation under health alone, at every later canonical cut
within the engine horizon (not just end-of-time cuts). The cut's own timestamp
is not bounded: the last cut can be a next-event/filler boundary. No progress
argument is available. Event/vote adapters below remain distinct obligations. -/
theorem healthy_preserve (Q : HealthyPreparationQuery S A V)
    (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.run.2.horizon)
    (W : HealthyBaseTiming S A V Q)
    (base : HealthyStateFacts S A V Q W.slot Q.cut) :
    ∀ i, Q.cut ≤ i → i ≤ cutMap S Q.run.2 Q.hn Q.run.2.events.length →
      HealthyStateFacts S A V Q W.slot i := by
  sorry

/-- OPEN vote-row adapter from the preserved inventory. The replacement origin
may be pending at this vote: ONLY label ≤ predecessor is claimed, matching
BaseFacts.vote_rows. No causal OriginBefore or source holding-cut bound is added.
The old-source antecedent has no additional ToFGAt requirement on D. -/
theorem healthy_vote_row_replacement (Q : HealthyPreparationQuery S A V)
    (W : HealthyBaseTiming S A V Q)
    (base : HealthyStateFacts S A V Q W.slot Q.cut)
    {y : Fin Q.params.n} (hy : y ∈ honestKeys S Q.run.2) {i : Nat}
    (hi : Q.cut ≤ i) (hih : i < cutMap S Q.run.2 Q.hn Q.run.2.events.length)
    {ℓ e} (hc : SA.CastAt Q.trace.projAC y i ℓ e) {s : Nat}
    (hs : e.msg.slot = s + 1) (hs₀ : W.slot ≤ s)
    {X : SA.Blk Q.params.n (List (FG.Att Q.params.n))}
    (hX : X ∈ (Q.trace.state y i).fg.tree) {a : FG.Att Q.params.n}
    (ha : a ∈ X.fgPayload) (hav : a.val ∈ honestKeys S Q.run.2)
    (hh : (Q.trace.state y i).fg.hj ≤ ((Q.trace.state y i).fg.σ a.T).h)
    (hold : ∃ D C l, Compose.IsHonestSource Q.trace (honestKeys S Q.run.2) D a.T ∧
      Compose.Origin Q.trace (honestKeys S Q.run.2) C l ∧ l < W.slot ∧
      Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) D C) :
    ∃ D C l, Compose.IsHonestSource Q.trace (honestKeys S Q.run.2) D a.T ∧
      Compose.OriginFrom Q.trace (honestKeys S Q.run.2) C l W.slot ∧ l ≤ s ∧
      Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) D C := by
  sorry

end Consensus.Goldilocks.Refinement
end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.NonfinalSuppliers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.WeakBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealthyEffective
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealthyRecordGeometry
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.NetworkTransport
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Quorum
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Regimes.Inclusion

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

/-- ResetService's message/block/relay fields quantify actual receiver calls, not
arbitrary observation cuts. On the finite engine trace all such calls are within
the horizon; the terminal filler at horizon+1 has no call label. This does not
justify restricting service to a smaller bound while retaining later calls. -/
theorem healthy_query_call_time_le (Q : HealthyPreparationQuery S A V)
    {y : Fin Q.params.n} {j : Nat} (hj : Q.trace.IsCall y j) :
    Q.trace.time j ≤ Q.run.2.horizon := by
  obtain ⟨ell, _, hlabel⟩ := hj
  exact simTrace_labelled_time_le S Q.run.2 Q.hn Q.valid (by rw [hlabel]; simp)

/-- The finite engine query supplies run validity, collision freedom, awake participation
and the fault bound. Service, actual reset existence and its snapshot remain explicit.
The service horizon is the full engine horizon, so `healthy_query_call_time_le`
supplies the receiver bound for the unguarded AC service fields. -/
theorem reset_premises_of_healthy_query (Q : HealthyPreparationQuery S A V)
    {ΔF a : Time}
    (hsync : Healing.ResetService Q.trace (honestKeys S Q.run.2)
      Q.gst ΔF Q.run.2.horizon)
    (hreset : Healing.IsReset Q.trace (honestKeys S Q.run.2) Q.gst a)
    (ha : a ≤ Q.run.2.horizon)
    (hsnapshot : ∃ k, Healing.FirstCutAfter Q.trace k
      (Healing.cutZ Q.params.toParams Q.gst) ∧ Q.trace.time k ≤ Q.run.2.horizon) :
    Healing.ResetPremisesUpTo Q.trace (honestKeys S Q.run.2)
      (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2) Q.gst ΔF a Q.run.2.horizon := by
  refine ⟨simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid,
    noCollTransport V S Q.run.1 Q.run.2 Q.hn Q.valid Q.noCollision,
    hsync, ?_, ?_, hreset, ha, hsnapshot⟩
  · intro y hy t ht htb
    rw [simTrace_awake_iff, awakeAt_iff]
    exact ⟨Q.healthy.2.2 (Q.run.2.key y) hy t ht htb,
      (le_max_right Q.gst 0).trans ht, htb⟩
  · have hpop := Q.healthy.2.1
    change (Q.run.2.point.faulty.card : ℚ) < (K S A).params.β * Fintype.card V at hpop
    rw [acceptanceContract_params_eq] at hpop
    change (Q.run.2.point.faulty.card : ℚ) < 1 / 3 * Fintype.card V at hpop
    have hfault : (honestKeys S Q.run.2)ᶜ.ncard = Q.run.2.point.faulty.card := by
      have heq : (honestKeys S Q.run.2)ᶜ = Q.run.2.key ⁻¹' (↑Q.run.2.point.faulty : Set V) := by
        ext k
        simp [honestKeys, EnvPoint.faulty, Model.Run.point]
      rw [heq, Set.ncard_preimage_of_injective_subset_range Q.run.2.key.injective
        (by simp [Q.run.2.key.surjective.range_eq]), Set.ncard_coe_finset]
    rw [hfault]
    have hnat : 3 * Q.run.2.point.faulty.card < Fintype.card V := by
      exact_mod_cast (show (3 : ℚ) * Q.run.2.point.faulty.card < Fintype.card V by linarith)
    change 3 * Q.run.2.point.faulty.card ≤ Fintype.card V - 1
    omega

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

/-- Initialization chooses a base with enough time for an actual reset seed and
bounded repairing opening. The activation floor names that seed, not a free time.
Existence of this certificate remains part of initialization's proof obligation. -/
structure HealthyPreparationSchedule (Q : HealthyPreparationQuery S A V)
    (W : HealthyBaseTiming S A V Q) where
  resetTime : Time
  deltaF : Time
  reset : Healing.ResetPremisesUpTo Q.trace (honestKeys S Q.run.2)
    (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2) Q.gst deltaF resetTime Q.run.2.horizon
  seedNode : Fin Q.params.n
  seedCut : Nat
  seedLabel : Nat
  seed : SA.Blk Q.params.n (List (FG.Att Q.params.n))
  seed_origin : Healing.HighOrigin Q.trace (honestKeys S Q.run.2) Q.gst
    seedNode seedCut seedLabel seed
  seed_time : Q.trace.time seedCut ≤ resetTime
  seed_label : seedLabel ≤ Q.params.slot resetTime
  query : Time
  lower : max Q.ready (max (Healing.drainTime Q.params resetTime)
    (max (Q.params.ts W.slot) (max (SA.gbar Q.gst + 4 * Q.params.Δ)
      (max 0 (Q.params.ts (seedLabel + 1 : Nat)))))) ≤ query
  reserve : query + (4 * (Q.index : Time) + 6) * Q.params.Δ < Q.heal - 1

/-- Compatibility with an actual fresh origin covers an old entry. The slot
cap is a separate producer; coverage adds no causal or upper label bound. -/
theorem old_entry_covered_of_fresh_origin (Q : HealthyPreparationQuery S A V)
    {s₀ p : Nat} {E P : SA.Blk Q.params.n (List (FG.Att Q.params.n))}
    (hP : Compose.OriginFrom Q.trace (honestKeys S Q.run.2) P p s₀)
    (hPs : s₀ ≤ P.slot) (hEs : E.slot < s₀)
    (hcomp : Goldilocks.Compatible (Q.trace.HonestBlocks (honestKeys S Q.run.2)) E P) :
    Healing.OldEntryCovered Q.trace (honestKeys S Q.run.2) s₀ E := by
  apply (Healing.oldEntryCovered_iff s₀ E).2
  refine ⟨P, p, hP, ?_⟩
  rcases hcomp with hEP | hPE
  · exact hEP
  · have hU := Compose.honest_blocks_coherent
      (simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid).toLocalRun
      (noCollTransport V S Q.run.1 Q.run.2 Q.hn Q.valid Q.noCollision)
    have := (Goldilocks.Anc.slot_le hU hPE).1
    omega

/-- Conditional initialization at any cut, including equality of the entry
and cache heights. The missing comparison ranges over all authentic old entries,
not just entries held or signed before the cut. -/
theorem healthy_old_inventory_of_fresh_origin (Q : HealthyPreparationQuery S A V)
    {s₀ p i : Nat} {P : SA.Blk Q.params.n (List (FG.Att Q.params.n))}
    (hP : Compose.OriginFrom Q.trace (honestKeys S Q.run.2) P p s₀)
    (hPs : s₀ ≤ P.slot)
    (hcap : ∀ E h, Healing.OldHonest Q.trace (honestKeys S Q.run.2) s₀ E h → E.slot < s₀)
    (hcomp : ∀ y ∈ honestKeys S Q.run.2, ∀ E h,
      Healing.OldHonest Q.trace (honestKeys S Q.run.2) s₀ E h →
      (Q.trace.state y i).fg.hj ≤ h →
      Goldilocks.Compatible (Q.trace.HonestBlocks (honestKeys S Q.run.2)) E P) :
    HealthyOldInventory S A V Q s₀ i := by
  intro y hy E h hold
  by_cases hh : h < (Q.trace.state y i).fg.hj
  · exact Or.inr hh
  · exact Or.inl (old_entry_covered_of_fresh_origin S A V Q hP hPs
      (hcap E h hold) (hcomp y hy E h hold (by omega)))

/-- OPEN base production (healing §§27/28, OldHonest initialization). No argument
from monotone hj establishes this leaf. It selects timing and initializes the
all-honest global inventory, including later first arrivals. No new Healthy
premise, whole-run progress, or prefix-causal coverage is asserted. -/
theorem healthy_old_inventory_initialize (Q : HealthyPreparationQuery S A V)
    (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.run.2.horizon)
    (hp : (Sys (family S) V).prog (shapeProgress (family S) V) (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run) :
    ∃ W : HealthyBaseTiming S A V Q, HealthyOldInventory S A V Q W.slot Q.cut ∧
      Nonempty (HealthyPreparationSchedule S A V Q W) := by
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

/-- Every recent stored lock has a recent origin, at any canonical cut.
The witness is archival tree membership, not membership in a filtered frame. -/
theorem healthy_locks (Q : HealthyPreparationQuery S A V) (s₀ i : Nat)
    {y : Fin Q.params.n} (hy : y ∈ honestKeys S Q.run.2)
    {l : SA.Lock} (hl : l ∈ (Q.trace.state y i).ac.locks)
    (hs : s₀ ≤ l.slot) :
    ∃ L ∈ (Q.trace.state y i).fg.tree, L.root = l.block ∧
      Compose.OnOriginChainFrom Q.trace (honestKeys S Q.run.2) L s₀ := by
  obtain ⟨L, hL, hr, C, hC, hLC⟩ := Compose.lock_origin
    (simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid)
    (noCollTransport V S Q.run.1 Q.run.2 Q.hn Q.valid Q.noCollision) hy i l hl
  exact ⟨L, hL, hr, Compose.onOriginChainFrom_iff.2
    (Or.inr ⟨C, l.slot, Compose.originFrom_iff.2 ⟨hC.origin, hs⟩, hLC⟩)⟩

/-- The global inventory covers the current justification: its own entry has
height exactly hj, so the exclusion alternative is impossible. F follows J. -/
theorem healthy_caches_of_inventory (Q : HealthyPreparationQuery S A V) (s₀ i : Nat)
    (hf : (honestKeys S Q.run.2)ᶜ.ncard < Q.params.toParams.fg.q)
    (inv : HealthyOldInventory S A V Q s₀ i)
    {y : Fin Q.params.n} (hy : y ∈ honestKeys S Q.run.2) :
    Compose.OnOriginChainFrom Q.trace (honestKeys S Q.run.2) (Q.trace.state y i).fg.F s₀ ∧
      Compose.OnOriginChainFrom Q.trace (honestKeys S Q.run.2) (Q.trace.state y i).fg.J s₀ := by
  have hrun := simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid
  have hnc := noCollTransport V S Q.run.1 Q.run.2 Q.hn Q.valid Q.noCollision
  have hr := Compose.fg_reachable hrun.toLocalRun hy i
  let st := (Q.trace.state y i).fg
  have hsub : st.tree ⊆ Q.trace.HonestBlocks (honestKeys S Q.run.2) := fun _ h => ⟨y, hy, i, h⟩
  obtain ⟨hF, hJ, hFJ, ⟨Z, hZ, hZJ, hZj⟩, _⟩ := Store.cache_invariants _ _ _ _ hr
  have hJchain : Compose.OnOriginChainFrom Q.trace (honestKeys S Q.run.2) st.J s₀ := by
    rcases Compose.cache_quorum hr st.J (Or.inl rfl) with hg | ⟨q, hq, hrows⟩
    · exact Compose.onOriginChainFrom_iff.2 (Or.inl hg)
    have hex : ∃ v ∈ q, v ∈ honestKeys S Q.run.2 := by
      by_contra h
      have hsubq : (↑q : Set (Fin Q.params.n)) ⊆ (honestKeys S Q.run.2)ᶜ := by
        intro v hv hvH
        exact h ⟨v, hv, hvH⟩
      have hn := Set.ncard_le_ncard hsubq (Set.toFinite _)
      rw [Set.ncard_coe_finset] at hn
      exact (not_lt_of_ge (hq.trans hn)) hf
    obtain ⟨v, hvq, hv⟩ := hex
    obtain ⟨X, hX, a, ha, hav, haT⟩ := hrows v hvq
    have haH : a.val ∈ honestKeys S Q.run.2 := hav ▸ hv
    obtain ⟨m, _, _, k, _, hsign⟩ := Compose.honest_row_signed_before hrun hnc hy hX ha haH
    obtain ⟨D, _, hD, C, l, hC, hDC⟩ := Compose.attestation_source hrun hnc haH hsign
    obtain ⟨x, hx, c, _, hJe, hJD, _, hJT⟩ :=
      Compose.honest_source_entry hrun hnc hD (hsub hJ) haT.symm
    have hsubx : (Q.trace.state x c).fg.tree ⊆ Q.trace.HonestBlocks (honestKeys S Q.run.2) :=
      fun _ h => ⟨x, hx, c, h⟩
    have hJC : Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) st.J C :=
      (hJD.mono hsubx).trans hDC
    by_cases hl : s₀ ≤ l
    · exact Compose.onOriginChainFrom_iff.2
        (Or.inr ⟨C, l, Compose.originFrom_iff.2 ⟨hC.origin, hl⟩, hJC⟩)
    obtain ⟨E, hE, hEr, _, hentry⟩ := Healing.Store.J_entry_of_reachable hr hZ
    have hEJ : E = st.J := (Store.accepted_tree _ _ _ _ hr).2.1.1 hE hJ (hEr.trans hZJ)
    subst E
    rcases hentry with hg | ⟨hh, hT⟩
    · exact Compose.onOriginChainFrom_iff.2 (Or.inl (congrArg Block.root hg))
    have hold : Healing.OldHonest Q.trace (honestKeys S Q.run.2) s₀ st.J st.hj :=
      ⟨⟨a.val, haH, k, a, hsign, haT.symm⟩,
        ⟨y, hy, i, hJ, hT, hh.trans hZj⟩,
        ⟨D, C, l, by simpa only [haT] using (Compose.isHonestSource_iff.1 hD),
          hC.origin, Nat.lt_of_not_ge hl, hDC⟩⟩
    rcases inv y hy st.J st.hj hold with hcov | hlt
    · obtain ⟨C', l', hC', hJC'⟩ := (Healing.oldEntryCovered_iff _ _).1 hcov
      exact Compose.onOriginChainFrom_iff.2 (Or.inr ⟨C', l', hC', hJC'⟩)
    · exact False.elim ((lt_irrefl st.hj) hlt)
  refine ⟨?_, hJchain⟩
  rcases Compose.onOriginChainFrom_iff.1 hJchain with hg | ⟨C, l, hC, hJC⟩
  · have he := Compose.honest_eq_genesis hrun
      (Compose.honest_blocks_coherent hrun.toLocalRun hnc) (hsub hJ) hg
    rw [he] at hFJ
    rcases Relation.ReflTransGen.cases_tail hFJ with heq | ⟨Y, _, hY⟩
    · exact Compose.onOriginChainFrom_iff.2 (Or.inl (congrArg Block.root heq.symm))
    · exact absurd hY.2.2 (by simp [Params.genesisBlock])
  · exact Compose.onOriginChainFrom_iff.2
      (Or.inr ⟨C, l, hC, (hFJ.mono hsub).trans hJC⟩)

/-- Preparation consumes global initialization and the supplied finite reset schedule.
An operational update repairs archival record provenance before the heal boundary.
This statement promises only the actual heal boundary, not all earlier states. -/
theorem healthy_prepare (Q : HealthyPreparationQuery S A V)
    (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.run.2.horizon)
    (hp : (Sys (family S) V).prog (shapeProgress (family S) V) (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run)
    (W : HealthyBaseTiming S A V Q)
    (base : HealthyOldInventory S A V Q W.slot Q.cut)
    (D : HealthyPreparationSchedule S A V Q W) :
    HealthyStateFacts S A V Q W.slot Q.cut := by
  classical
  have hnet : Q.run.2.log.PSync Q.run.2.point Q.gst := by
    constructor
    · intro v hv o s hs w hw a hsa hc hh haw
      have h := Q.healthy.1.msgs v hv ⟨Q.run.1, o⟩ s ⟨o, rfl, hs⟩ w hw a hsa hc hh haw
      rcases h with ⟨u, hu, hsent | hrecv, hnowake⟩
      · obtain ⟨o', he, hs'⟩ := hsent
        cases he
        exact ⟨u, hu, Or.inl hs', hnowake⟩
      · obtain ⟨o', he, hr'⟩ := hrecv
        cases he
        exact ⟨u, hu, Or.inr hr', hnowake⟩
    · exact Q.healthy.1.txs
  have hcatch := catchRun_of_psync S Q.run.2 Q.hn Q.valid
    (noCollTransport V S Q.run.1 Q.run.2 Q.hn Q.valid Q.noCollision)
    hnet Q.healthy.2.2
  have hduration : Regimes.catchUp Q.params ≤ (Sys (family S) V).cDur (K S A) Q.run := by
    have hc : (37 : Time) ≤ (accepted_catchUp S A : Nat) := by
      exact_mod_cast accepted_catchUp_ge_sleepy S A
    have hd : (1 : Time) ≤ Q.run.1.Δ := Q.run.1.Δ_pos
    simp only [System.cDur, Params.standard, accepted_coefficients_catchUp]
    change 18 * (Q.run.1.Δ + 1) ≤ (accepted_catchUp S A : Nat) * Q.run.1.Δ
    nlinarith
  have hcap : Q.cap ≠ .final := by rcases Q.nonfinal with h | h <;> simp [h]
  have hrec : PatternRecurrence Q.run.2.point Q.run.2.key
      (fun s => Q.run.2.sel (.proposer s)) (family S (Model.pubOf Q.run.1)).skel.grid
      ⟨Pattern.single, Q.index⟩ ((Sys (family S) V).cDur (K S A) Q.run)
      Q.ready Q.heal := by
    simpa only [System.prog, shapeProgress, shapeHolds, acceptanceContract, ite_eq_right hcap,
      Model.sysExternal, System.cDur, System.pt, Sys, Model.sysOf, Model.Run.point] using hp
  have hq0 : 0 ≤ D.query := (le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans D.lower))))
  have hq : max Q.ready 0 ≤ D.query := max_le ((le_max_left _ _).trans D.lower) hq0
  have hDelta := Q.params.toParams.hΔ
  have hwin : D.query + (Q.index : Time) * (4 * Q.params.Δ) ≤ Q.heal := by
    nlinarith [D.reserve]
  obtain ⟨u, hlo, hhi, hr⟩ := hrec D.query hq
    (by simpa [Recurrence.len, Pattern.single, Pattern.span, family, skeleton] using hwin)
    (by simpa [Recurrence.len, Pattern.single, Pattern.span, family, skeleton,
      Model.Run.point] using hwin.trans hb)
  have htime : (family S (Model.pubOf Q.run.1)).skel.grid.slotTime u = Q.params.ts u := by
    change (u : Time) * (4 * (Q.run.1.Δ + 1)) = 4 * (Q.run.1.Δ + 1) * u
    ring
  rw [htime] at hlo hhi
  have hbound : Q.params.ts u ≤ D.query + 4 * (Q.index : Time) * Q.params.Δ := by
    change Q.params.ts u ≤ D.query + (Q.index : Time) * (4 * Q.params.Δ) at hhi
    nlinarith
  have hT : Q.params.ts u + 6 * Q.params.Δ < Q.heal - 1 := by nlinarith [D.reserve]
  have hTb : Q.params.ts u + 6 * Q.params.Δ ≤ Q.run.2.horizon := by linarith
  have hready := hr 0 (by simp [Pattern.single])
  simp only [Nat.add_zero] at hready
  have hmem : runProposer S Q.run.2 Q.hn u ∈ Q.run.2.sel (.proposer u) := by
    simp only [runProposer, dite_eq_left hready.1]
    exact Finset.min'_mem _ _
  have hR := hready.2 _ hmem
  rw [htime] at hR
  have hnode := ready_transport S Q.run.2 Q.hn Q.valid (hq0.trans hlo.le)
    (show Q.params.ts u ≤ Q.run.2.horizon by linarith) hR
  rw [show Q.run.2.ownKey (Q.run.2.key (runProposer S Q.run.2 Q.hn u)) =
    runProposer S Q.run.2 Q.hn u from Q.run.2.key.symm_apply_apply _] at hnode
  have hWu : W.slot < u := by
    exact_mod_cast (SA.ts_lt_iff Q.params).mp
      (lt_of_le_of_lt ((le_max_left _ _).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans D.lower))) hlo)
  have hshort : Regimes.ReadyAt Q.trace (honestKeys S Q.run.2) (Regimes.catchUp Q.params)
      (runProposer S Q.run.2 Q.hn u) (Q.params.ts u) := by
    refine ⟨hnode.1, fun t ht hts => hnode.2 t ?_ hts⟩
    apply le_trans _ ht
    apply max_le_max_left
    linarith
  obtain ⟨k, P, hP, ht⟩ := Regimes.ready_proposer_proposes D.reset.run D.reset.noColl
    (s := u) (Nat.zero_le W.slot |>.trans_lt hWu) hshort
  have hPs : P.slot = u := by
    have := hP.2.2
    rw [ht, Q.params.slotTime_eq] at this
    have he : (P.slot : Time) = (u : Time) := by
      simp only [SA.SAParams.ts] at this
      nlinarith
    exact_mod_cast he
  have hdrain : Healing.drainTime Q.params D.resetTime ≤ Q.params.ts u :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans D.lower)).trans hlo.le
  have hgu : SA.gbar Q.gst + 4 * Q.params.Δ ≤ Q.params.ts u :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans D.lower)))).trans hlo.le
  have hslot := (SA.ts_le_iff_le_slot Q.params (SA.gbar_nonneg Q.gst)
    (Q.params.slot (SA.gbar Q.gst))).mpr (by omega)
  have hjoin : Q.params.ts (Q.params.slot (SA.gbar Q.gst) + 1 : Nat) ≤ Q.params.ts u := by
    simp only [SA.SAParams.ts] at hslot hgu ⊢
    push_cast
    linarith
  have hf : (honestKeys S Q.run.2)ᶜ.ncard < Q.params.toParams.fg.q := by
    have hpop : 3 * (honestKeys S Q.run.2)ᶜ.ncard ≤ Q.params.n - 1 := D.reset.faults
    have hn : 1 ≤ Q.params.n := Q.hn
    change (honestKeys S Q.run.2)ᶜ.ncard < (2 * Q.params.n + 2) / 3
    omega
  refine ⟨?_, fun y hy => healthy_caches_of_inventory S A V Q W.slot Q.cut hf base hy,
    fun y hy l hl hs => healthy_locks S A V Q W.slot Q.cut hy hl hs, base⟩
  intro y hy
  obtain ⟨j, ell, _, hup, _⟩ := D.reset.update_toFG_calls hy hjoin hTb
  have hjlabel : Q.trace.label j ≠ none := by
    obtain ⟨_, hl⟩ := hup.1
    intro hn
    simp [RunTrace.projAC, hn] at hl
  obtain ⟨_, m, e, _, he, _, hjend, _, _, hte, _⟩ :=
    simTrace_cut S Q.run.2 Q.hn hjlabel
  have hjt : Q.trace.time j = Q.params.ts u + 6 * Q.params.Δ := hup.2.2.1
  have hte' : Q.trace.time j = e.time := hte
  have hm : m < (chainTrace Q.run.2).endCut Q.heal :=
    (event_before_endCut S Q.run.2 Q.valid h0 he).2 (by rw [← hte', hjt]; linarith)
  have hjcut : j < Q.cut := hjend.trans_le
    (cutMap_mono S Q.run.2 Q.hn (show m + 1 ≤ (chainTrace Q.run.2).endCut Q.heal by omega))
  obtain ⟨C, hC, hCr, l, hl, hsource⟩ :=
    UpTo.archival_record_source_after_operational_update D.reset hcatch hnode.1 rfl hP hPs
      hdrain hgu hTb hy hup hjcut
  exact ⟨C, hC, hCr, Or.inl (Compose.onOriginChainFrom_iff.2
    (Or.inr ⟨C, l, Compose.originFrom_iff.2 ⟨hsource.origin, hWu.le.trans hl⟩, .refl⟩))⟩

set_option linter.unusedVariables false in
/-- State preservation under health alone, at every later canonical cut
within the engine horizon (not just end-of-time cuts). The cut's own timestamp
is not bounded: the last cut can be a next-event/filler boundary. No progress
argument is available. Event/vote adapters below remain distinct obligations. -/
theorem healthy_preserve (Q : HealthyPreparationQuery S A V)
    (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.run.2.horizon)
    (W : HealthyBaseTiming S A V Q)
    (base : HealthyStateFacts S A V Q W.slot Q.cut) :
    ∀ i, Q.cut ≤ i → i ≤ cutMap S Q.run.2 Q.hn Q.run.2.events.length →
      HealthyStateFacts S A V Q W.slot i := by
  have hrun := simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid
  have hf : (honestKeys S Q.run.2)ᶜ.ncard < Q.params.toParams.fg.q := by
    have hpop := Q.healthy.2.1
    change (Q.run.2.point.faulty.card : ℚ) < (K S A).params.β * Fintype.card V at hpop
    rw [acceptanceContract_params_eq] at hpop
    change (Q.run.2.point.faulty.card : ℚ) < 1 / 3 * Fintype.card V at hpop
    have hfault : (honestKeys S Q.run.2)ᶜ.ncard = Q.run.2.point.faulty.card := by
      have heq : (honestKeys S Q.run.2)ᶜ = Q.run.2.key ⁻¹' (↑Q.run.2.point.faulty : Set V) := by
        ext k
        simp [honestKeys, EnvPoint.faulty, Model.Run.point]
      rw [heq, Set.ncard_preimage_of_injective_subset_range Q.run.2.key.injective
        (by simp [Q.run.2.key.surjective.range_eq]), Set.ncard_coe_finset]
    rw [hfault]
    have hnat : 3 * Q.run.2.point.faulty.card < Fintype.card V := by exact_mod_cast (show
        (3 : ℚ) * Q.run.2.point.faulty.card < Fintype.card V by linarith)
    change Q.run.2.point.faulty.card < (2 * Fintype.card V + 2) / 3
    omega
  have htime : ∀ k, Q.cut ≤ k → Q.trace.label k ≠ none → Q.heal ≤ Q.trace.time k := by
    intro k hk hl
    obtain ⟨_, m, e, _, he, _, hmk, _, _, ht, _⟩ := simTrace_cut S Q.run.2 Q.hn hl
    rw [ht]
    apply le_of_not_gt
    intro het
    have hm := (event_before_endCut S Q.run.2 Q.valid h0 he).2 het.le
    have hcut := cutMap_mono S Q.run.2 Q.hn
      (show m + 1 ≤ (chainTrace Q.run.2).endCut Q.heal by omega)
    change cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut Q.heal) ≤ k at hk
    omega
  intro i hi hih
  have hinv := healthy_old_inventory_preserve S A V Q base.inventory i hi
  refine ⟨?_, fun y hy => healthy_caches_of_inventory S A V Q W.slot i hf hinv hy,
    fun y hy l hl hs => healthy_locks S A V Q W.slot i hy hl hs, hinv⟩
  clear hinv
  induction i, hi using Nat.le_induction with
  | base => exact base.records
  | succ j hj ih =>
    have prev := ih (by omega)
    intro y hy
    have htree := Compose.tree_mono hrun.toLocalRun hy (Nat.le_succ j)
    rcases Compose.record_step_origin hrun hy j with heq | ⟨C, hC, hr, s, CV, hsource⟩
    · obtain ⟨C, hC, hr, hcov⟩ := prev y hy
      refine ⟨C, htree hC, hr.trans heq.symm, ?_⟩
      exact hcov.imp_right fun h => h.trans (Healing.run_F_mono hrun.toLocalRun hy (Nat.le_succ j))
    · have hs : W.slot ≤ s := by
        have hw := W.records
        rcases hsource with ⟨ℓ, hup, _, _⟩ | ⟨ℓ, A₀, hp, hslot, _, _⟩
        · have ht := htime j hj (by
            obtain ⟨_, hl⟩ := hup.1
            intro hn
            simp [RunTrace.projAC, hn] at hl)
          have ht' := hup.2.2.1
          change Q.trace.time j = Q.params.ts (s : Int) + 6 * Q.params.Δ at ht'
          have htt : Q.params.ts (W.slot : Int) ≤ Q.params.ts (s : Int) := by linarith
          exact_mod_cast (SA.ts_le_iff Q.params).1 htt
        · have hc := hp.1
          have ht := htime j hj (by
            obtain ⟨_, hl⟩ := hc
            intro hn
            simp [RunTrace.projAC, hn] at hl)
          have htt : Q.params.ts (W.slot : Int) ≤ Q.trace.time j := by
            have := Q.params.toParams.hΔ
            linarith
          have hle := (SA.ts_le_iff_le_slot Q.params (hrun.time_nonneg j) (W.slot : Int)).1 htt
          have hle' : W.slot ≤ Q.params.slot (Q.trace.time j) := by exact_mod_cast hle
          exact hslot ▸ hle'
      exact ⟨C, htree hC, hr, Or.inl (Compose.onOriginChainFrom_iff.2
        (Or.inr ⟨C, s, Compose.originFrom_iff.2
          ⟨Compose.origin_iff.2 ⟨y, hy, j, CV, hsource⟩, hs⟩, .refl⟩))⟩

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

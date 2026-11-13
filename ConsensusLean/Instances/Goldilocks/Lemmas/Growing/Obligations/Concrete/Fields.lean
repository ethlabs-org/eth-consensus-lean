module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Queries.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Sleepy
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Endpoint.Outputs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Endpoint.Accountable
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Concrete.Final
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.Safety
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Engine.Repair
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.ReadySafety
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Queries.Sleepy
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.NonfinalEndpoints
public import ConsensusLean.Spec.Shape.Claims
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.ConfirmedSupply
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The growing-fault endpoint: the nine chain-level claims

Each theorem is the field of `ShapeClaimsAt (goldilocks S) (K S A) V` of the same name, verbatim:
no constant-fault premise and no other premise beyond the field's own.

* `outputValid`, `nested`, `finalMonotone`, `finalAccountable`: the engine output transports;
* `sleepySafe`: finite engine sleepy safety, with the finite service from raw synchrony
  (`Simulation.sleepyServiceBefore_of_syncUntil_at`) and the L0 budget at the contract's sleepy
  look-ahead `5Δ` and catch-up `≥ 19Δ`;
* `healedSafe`: healed safety of a healthy preparation query;
* `persists`: outage protection of an outage query;
* `healthyLive`: the final branch from `meetsObligations_healthyLive_final_growing`, the
  confirmed branch from the healthy confirmed supply;
* `sleepyLive`: the sleepy serviced proposal of the selected slot, with the proposer's hold. -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation Obligations
open Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

theorem meetsObligations_outputValid_growing : (Sys (goldilocks S) V).HoldsAlways fun r =>
    ∀ c g, schema.output c = some g → OutputValid r.2 g := by
  intro r hv c g _
  exact engine_outputValid_at S r.2 hv g

theorem meetsObligations_nested_growing : ∀ c₁ c₂ g₁ g₂, c₁.rank < c₂.rank →
    schema.output c₁ = some g₁ → schema.output c₂ = some g₂ →
    (Sys (goldilocks S) V).HoldsAlways fun r => (chainTrace r.2).Nested g₁ g₂ := by
  intro c₁ c₂ g₁ g₂ hr h₁ h₂ r hv
  cases c₁ <;> cases c₂ <;> simp only [Capability.rank] at hr <;> try omega
  all_goals have he₁ := Option.some.inj h₁
  all_goals have he₂ := Option.some.inj h₂
  all_goals cases he₁; cases he₂
  · intro v _ i _
    exact ⟨[], by simp⟩
  · exact engine_nested_at S r.2 hv
  · exact engine_nested_at S r.2 hv

theorem meetsObligations_finalMonotone_growing : ∀ g, schema.output .final = some g →
    (Sys (goldilocks S) V).HoldsAlways fun r => (chainTrace r.2).Monotone g 0 := by
  intro g hg r hv
  have hg' : g = .finalized := (Option.some.inj hg).symm
  subst g
  exact engine_finalMonotone_at S r.2 hv

theorem meetsObligations_finalAccountable_growing : ∀ g, schema.output .final = some g →
    (Sys (goldilocks S) V).Holds (fun _ => True) fun r =>
      (chainTrace r.2).AccountablySafe r.2.ViewIdx r.2.Slashable (K S A).params.α g 0 := by
  intro g hg r hv _
  have hg' : g = .finalized := (Option.some.inj hg).symm
  subst g
  exact engine_finalAccountable_at S r.2 hv (by norm_num [Params.standard])

theorem meetsObligations_sleepySafe_growing : ∀ cap g, (cap = .available ∨ cap = .stable) →
    schema.output cap = some g → (Sys (goldilocks S) V).Holds
      ((Sys (goldilocks S) V).Sleepy (K S A)) fun r =>
        (chainTrace r.2).ReadySafe ((Sys (goldilocks S) V).cDur (K S A) r) g 0 := by
  intro cap g hcap hg r hv hs
  have hg' : g = Out.confirmed := by
    rcases hcap with rfl | rfl <;> exact Option.some.inj hg.symm
  subst g
  by_cases hc : r.2.HashCollision
  · exact Or.inr hc
  left
  by_cases hn : 1 ≤ Fintype.card V
  · have hd : Regimes.catchUp (S.params (Model.pubOf r.1) hn) + 1 ≤
        (Sys (goldilocks S) V).cDur (K S A) r := by
      have hc19 : (19 : Time) ≤ (contract_catchUp S A : Nat) := by
        exact_mod_cast contract_catchUp_ge_sleepy S A
      have hd : (1 : Time) ≤ r.1.ΔAC := r.1.ΔAC_pos
      simp only [System.cDur, Params.standard, contract_coefficients_catchUp]
      change 18 * r.1.ΔAC + 1 ≤ (contract_catchUp S A : Nat) * r.1.ΔAC
      linarith [mul_le_mul_of_nonneg_right hc19 (by linarith : (0 : Time) ≤ r.1.ΔAC)]
    have hnc := noCollRun_simTraceAt S r.2 hn hv hc
    have hsync := sleepyServiceBefore_of_syncUntil_at S r.2 hn hv hnc le_rfl
      (sleepy_raw_syncUntil S A V r hv hs r.2.horizon)
    have hhalf : r.2.point.SleepyOn (1 / 2) (Regimes.catchUp (S.params (Model.pubOf r.1) hn))
        (5 * (S.params (Model.pubOf r.1) hn).Δ) 0 r.2.horizon :=
      sleepyOn_of_duration V _ ((le_add_of_nonneg_right zero_le_one).trans hd) hs.2
    have safe := sleepy_safe_engine_at S r.2 hn hv hnc hsync hhalf
    have ready : ∀ v t, r.2.point.Ready ((Sys (goldilocks S) V).cDur (K S A) r) v t →
        r.2.point.Ready (Regimes.catchUp (S.params (Model.pubOf r.1) hn) + 1) v t := by
      intro v t h
      refine ⟨h.1, fun τ hlo hhi => h.2 τ ?_ hhi⟩
      exact (max_le_max_left 0 (sub_le_sub_right (sub_le_sub_left hd t) 1)).trans hlo
    exact ⟨fun u v i j hi hj hu hv => safe.1 u v i j hi hj (ready _ _ hu) (ready _ _ hv),
      fun v i j hi hij hj hvi hvj => safe.2 v i j hi hij hj (ready _ _ hvi) (ready _ _ hvj)⟩
  · have hempty : IsEmpty V :=
      Fintype.card_eq_zero_iff.mp (Nat.lt_one_iff.mp (Nat.lt_of_not_le hn))
    exact ⟨fun u => (hempty.false u).elim, fun v => (hempty.false v).elim⟩

theorem meetsObligations_healedSafe_growing : ∀ cap g, (cap = .available ∨ cap = .stable) →
    schema.output cap = some g → ∀ (i : (K S A).Idx) (gst : Time),
      (Sys (goldilocks S) V).Holds
        (fun r => (Sys (goldilocks S) V).Healthy (K S A) gst r ∧
          (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) cap i
            ((Sys (goldilocks S) V).ready (K S A) gst r)
            ((Sys (goldilocks S) V).heal (K S A) cap i gst r) r)
        fun r => (chainTrace r.2).ReadySafe ((Sys (goldilocks S) V).cDur (K S A) r)
          g ((Sys (goldilocks S) V).heal (K S A) cap i gst r) := by
  intro cap g hcap hg idx gst r hv ⟨hh, hp⟩
  have hg' : g = Out.confirmed := by
    rcases hcap with rfl | rfl <;> exact Option.some.inj hg.symm
  subst g
  by_cases hcollision : r.2.HashCollision
  · exact Or.inr hcollision
  left
  have htime : ∀ k, k ≤ (chainTrace r.2).cuts →
      (chainTrace r.2).cutTime k ≤ r.2.horizon :=
    (Model.sysOf_laws schema (compiled (goldilocks S)) V).trace r hv |>.cutTime_le_horizon
  let heal := (Sys (goldilocks S) V).heal (K S A) cap idx gst r
  by_cases hb : heal ≤ r.2.horizon
  · by_cases hn : 1 ≤ Fintype.card V
    · let Q : HealthyPreparationQueryAt S A V := ⟨r, hn, cap, hcap, idx, gst, r.2.horizon, hv,
        hcollision, le_rfl, hh⟩
      have h0 : 0 ≤ Q.heal :=
        add_nonneg (le_max_right gst 0)
          (mul_nonneg (Int.natCast_nonneg _) r.1.ΔAC_pos.le)
      exact healthy_ready_safety_at S A V Q h0 hb le_rfl hp
    · have hempty : IsEmpty V :=
        Fintype.card_eq_zero_iff.mp (Nat.lt_one_iff.mp (Nat.lt_of_not_le hn))
      exact ⟨fun u => (hempty.false u).elim, fun v => (hempty.false v).elim⟩
  · have hnone : ∀ k, ¬ (chainTrace r.2).InCuts heal k :=
      fun k hk => hb (hk.2.trans (htime k hk.1))
    exact ⟨fun _ _ i _ hi => (hnone i hi).elim,
      fun _ i _ hi => (hnone i hi).elim⟩

theorem meetsObligations_persists_growing (S : BoundSetup) (A : ContractAssumptions S.toSetup)
    (V : Type) [Fintype V] [DecidableEq V]
    [Fact (S.vote.participationKind = none)] : -- TEMP(C2)
    ∀ g, schema.output .stable = some g → ∀ T b₀ b₁,
    (Sys (goldilocksWith S) V).Holds ((Sys (goldilocksWith S) V).Outage
      (shapeProgress (goldilocksWith S) V).toExternal (K S.toSetup A) T b₀ b₁) fun r =>
      (chainTrace r.2).ProtectedReadyFrom ((Sys (goldilocksWith S) V).cDur (K S.toSetup A) r) g
        (resilienceTarget schema g) T
        ((Sys (goldilocksWith S) V).recoveryAt (K S.toSetup A) b₁ r) := by
  intro g hg T b₀ b₁ r hv ho
  have hg' : g = Out.confirmed := Option.some.inj hg.symm
  subst g
  by_cases hcollision : r.2.HashCollision
  · exact Or.inr hcollision
  left
  intro v hvr t ht hth w hw
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  let Q : OutageQueryAt S A V := ⟨r, hn, T, b₀, b₁, hv, hcollision, ho⟩
  exact outage_protected_at Q v hvr t ht hth w hw

/-- Healthy liveness of the nonfinal (confirmed) capabilities: the healthy confirmed supply and
the payload projection. -/
theorem meetsObligations_healthyLive_confirmed_growing : ∀ cap g, cap ≠ .final →
    schema.output cap = some g →
    ∀ (i : (K S A).Idx) (gst : Time), (Sys (goldilocks S) V).Holds
      (fun r => (Sys (goldilocks S) V).Healthy (K S A) gst r ∧
        (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) cap i
          ((Sys (goldilocks S) V).ready (K S A) gst r) ((Sys (goldilocks S) V).pt r).horizon r)
      fun r => ProposalLiveReady r.2 ((Sys (goldilocks S) V).cDur (K S A) r) g
        ((Sys (goldilocks S) V).heal (K S A) cap i gst r) ((K S A).params.latency cap i) := by
  intro cap g hf hg idx gst r hv ⟨hh, hp⟩
  have hcap : cap = .available ∨ cap = .stable := by cases cap <;> simp_all
  have hg' : g = Out.confirmed := by
    rcases hcap with rfl | rfl <;> exact Option.some.inj hg.symm
  subst g
  by_cases hc : r.2.HashCollision
  · exact Or.inr hc
  left
  intro t ht hb hr
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨hr.choose⟩
  let Q : ConfirmedQueryAt S A V := ⟨r, hn, cap, hcap, idx, gst, t, hv, hc,
    Or.inr (Or.inl ⟨hh, hp, ht⟩), hb, hr⟩
  obtain ⟨P, cover⟩ := healthy_confirmed_supply_at S A V Q hh hp ht
  have h0 : 0 ≤ t :=
    (add_nonneg (le_max_right gst 0)
      (mul_nonneg (Int.natCast_nonneg _) r.1.ΔAC_pos.le)).trans ht
  exact confirmed_payload_projection_at S A V Q h0 P cover

theorem meetsObligations_healthyLive_growing : ∀ cap g, schema.output cap = some g →
    ∀ (i : (K S A).Idx) (gst : Time), (Sys (goldilocks S) V).Holds
      (fun r => (Sys (goldilocks S) V).Healthy (K S A) gst r ∧
        (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) cap i
          ((Sys (goldilocks S) V).ready (K S A) gst r) ((Sys (goldilocks S) V).pt r).horizon r)
      fun r => ProposalLiveReady r.2 ((Sys (goldilocks S) V).cDur (K S A) r) g
        ((Sys (goldilocks S) V).heal (K S A) cap i gst r) ((K S A).params.latency cap i) := by
  intro cap g hg
  by_cases hf : cap = .final
  · subst cap
    exact meetsObligations_healthyLive_final_growing S A V g hg
  · exact meetsObligations_healthyLive_confirmed_growing S A V cap g hf hg

theorem meetsObligations_sleepyLive_growing : ∀ cap g, (cap = .available ∨ cap = .stable) →
    schema.output cap = some g → ∀ i : (K S A).Idx, (Sys (goldilocks S) V).Holds
      (fun r => (Sys (goldilocks S) V).Sleepy (K S A) r ∧
        (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) cap i 0
          ((Sys (goldilocks S) V).pt r).horizon r)
      fun r => ProposalLiveReady r.2 ((Sys (goldilocks S) V).cDur (K S A) r) g 0
        ((K S A).params.latency cap i) := by
  intro cap g hcap hg idx r hv ⟨hs, hp⟩
  have hg' : g = Out.confirmed := by
    rcases hcap with rfl | rfl <;> exact Option.some.inj hg.symm
  subst g
  by_cases hc : r.2.HashCollision
  · exact Or.inr hc
  left
  intro t ht hb hr
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨hr.choose⟩
  let Q : ConfirmedQueryAt S A V := ⟨r, hn, cap, hcap, idx, 0, t, hv, hc,
    Or.inl ⟨hs, hp, ht⟩, hb, hr⟩
  obtain ⟨P, service⟩ := sleepy_serviced_proposal_supply_at S A V Q hs hp ht
  exact confirmed_payload_projection_at S A V Q ht P
    (sleepy_serviced_proposal_coverage_at S A V Q P service)

end Consensus.Goldilocks.Obligations.Growing

end

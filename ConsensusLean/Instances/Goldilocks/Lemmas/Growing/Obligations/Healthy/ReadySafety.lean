module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.CutTips
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.NoColl
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ContractDefs
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Healed safety under growing faults

`healthy_ready_safety_at`: the confirmed reads of nodes ready from the heal point are safe. Each
ready engine reader is read at the trace cut after its last own event, at its stored clock
(`engine_read_point`); the comparability and temporal ancestry of those read tips
(`healthy_cut_tips_comparable_at`, `healthy_cut_tips_ancestor_at`) are prefixes of the confirmed
chains inside the coherent blocks held while honest (`read_prefix`). -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- The catch-up duration of a healed-safety query is at least one. -/
private theorem one_le_cDur (Q : HealthyPreparationQueryAt S A V) :
    1 ≤ (Sys (goldilocks S) V).cDur (K S A) Q.run := by
  have hc : (19 : Time) ≤ (contract_catchUp S A : Nat) := by
    exact_mod_cast contract_catchUp_ge_sleepy S A
  have hd : (1 : Time) ≤ Q.run.1.ΔAC := Q.run.1.ΔAC_pos
  simp only [System.cDur, Params.standard, contract_coefficients_catchUp]
  change 1 ≤ (contract_catchUp S A : Nat) * Q.run.1.ΔAC
  linarith [mul_le_mul hc hd zero_le_one (by linarith)]

/-- **Healed safety under growing faults**: on a query healthy through the horizon, with progress
on `[ready, heal]` and the heal point within the horizon, the confirmed reads of nodes ready from
the heal point are safe. -/
theorem healthy_ready_safety_at (Q : HealthyPreparationQueryAt S A V)
    (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.bound) (hB : Q.run.2.horizon ≤ Q.bound)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run) :
    (chainTrace Q.run.2).ReadySafe ((Sys (goldilocks S) V).cDur (K S A) Q.run)
      .confirmed Q.heal := by
  have hc0 : 0 ≤ (Sys (goldilocks S) V).cDur (K S A) Q.run - 1 := by
    linarith [one_le_cDur S A V Q]
  have hnc := noCollRun_simTraceAt S Q.run.2 Q.hn Q.valid Q.noCollision
  have hr : ∀ {v i}, Q.run.2.point.Ready ((Sys (goldilocks S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime i) →
      Q.run.2.point.Ready (((Sys (goldilocks S) V).cDur (K S A) Q.run - 1) + 1) v
        (Q.run.2.cutTime i) := fun h => by simpa only [sub_add_cancel, chainTrace] using h
  constructor
  · intro u v i j hi hj hu hv
    obtain ⟨hrp, h0', hh, hra, hread⟩ := engine_read_point S Q.run.2 Q.hn Q.valid hc0 hi.1 (hr hu)
    obtain ⟨hrp', h0'', hh', hra', hread'⟩ :=
      engine_read_point S Q.run.2 Q.hn Q.valid hc0 hj.1 (hr hv)
    rw [hread, hread']
    rcases healthy_cut_tips_comparable_at S A V Q h0 hb hp u v i j hi hj hu hv (hh.trans hB)
      (hh'.trans hB) with hc | hc
    · exact Or.inl (read_prefix S Q.run.2 Q.hn Q.valid hnc h0' hrp.1 hra.1 h0'' hrp'.1 hra'.1 hc)
    · exact Or.inr (read_prefix S Q.run.2 Q.hn Q.valid hnc h0'' hrp'.1 hra'.1 h0' hrp.1 hra.1 hc)
  · intro v i j hi hij hj hvi hvj
    obtain ⟨hrp, h0', -, hra, hread⟩ :=
      engine_read_point S Q.run.2 Q.hn Q.valid hc0 hi.1 (hr hvi)
    obtain ⟨hrp', h0'', hh', hra', hread'⟩ :=
      engine_read_point S Q.run.2 Q.hn Q.valid hc0 hj.1 (hr hvj)
    rw [hread, hread']
    exact read_prefix S Q.run.2 Q.hn Q.valid hnc h0' hrp.1 hra.1 h0'' hrp'.1 hra'.1
      (healthy_cut_tips_ancestor_at S A V Q h0 hb hp v i j hi hij hj hvi hvj (hh'.trans hB))

end Consensus.Goldilocks.Obligations.Growing

end

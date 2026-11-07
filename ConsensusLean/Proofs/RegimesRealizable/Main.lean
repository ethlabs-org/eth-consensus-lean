module
public import ConsensusLean.Proofs.RegimesRealizable.Basic
import ConsensusLean.Lemmas.Tactic.Linarith

public section

namespace Consensus.Shape
open Blocks
open Consensus.Model (pubOf)

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]

/-- Generic realizability, with active progress windows and fault growth. -/
theorem regimes_realizable (F : ChainShapeFamily O Info) (K : Contract ProgressReq)
    (ha : K.params.Admissible) (hf : ProgressFits K F) (ht : ProgressTolerant O K)
    (V : Type) [Fintype V] [DecidableEq V]
    (hn : 5 ≤ Fintype.card V) : RealizableActive F K V := by
  let key : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  refine ⟨fun cap i Δ ΔF hΔ1 hΔF1 => ?_, fun cap i Δ ΔF g hΔ1 hΔF1 hr hg => ?_,
    fun cap hc ho => ?_, fun Δ ΔF k hΔ1 hΔF1 => ?_,
    fun cap ho Δ ΔF g hΔ1 hΔF1 hr hg => ?_, ?_, ?_, ?_⟩
  · obtain ⟨rho, -, -, hw, hs, hp, hpa, ht⟩ := sleepy_witness key hn (zero_lt_one.trans hΔ1)
      (zero_lt_one.trans hΔF1) _ ha hΔ1 hΔF1 hf cap i le_rfl
    exact ⟨⟨_, rho⟩, ⟨hw, rfl, rfl⟩, ⟨hs, hp, ht⟩, hpa⟩
  · have hΔ : 0 < Δ := zero_lt_one.trans hΔ1
    have hΔF : 0 < ΔF := zero_lt_one.trans hΔF1
    have hL := progLen_nonneg F K cap i (⟨Δ, hΔ, ΔF, hΔF, allAwake⟩ : Env V)
    have hlat : 0 ≤ (K.params.latency cap i : Time) * Δ := mul_nonneg (by positivity) hΔ.le
    have hheal : 0 ≤ (max g 0 + (K.params.heal cap i : Time) * Δ) :=
      add_nonneg (le_max_right _ _) (mul_nonneg (by positivity) hΔ.le)
    have hrdy : 0 ≤ (max g 0 + (K.params.catchUp : Time) * Δ + 1) := by
      have hg := le_max_right g 0
      have : (0 : Time) ≤ (K.params.catchUp : Time) * Δ := mul_nonneg (by positivity) hΔ.le
      linarith only [hg, this]
    obtain ⟨rho, -, -, hw, he, hs, hp, hpa, ht, hsa⟩ := healthy_witness key hn hΔ hΔF
      ((max g 0 + (K.params.heal cap i : Time) * Δ) +
        (max g 0 + (K.params.catchUp : Time) * Δ + 1) + (K.params.latency cap i : Time) * Δ +
        progLen F K cap i (⟨Δ, hΔ, ΔF, hΔF, allAwake⟩ : Env V) + Δ + 2) ha hΔ1 hΔF1 hf cap i g hr
      (by linarith only [hheal, hrdy, hlat, hL, hΔ]) (by linarith only [hheal, hrdy, hlat, hL, hΔ])
      (by linarith only [hheal, hrdy, hlat, hL, hΔ])
    exact ⟨⟨_, rho⟩, ⟨hw, rfl, rfl⟩, ⟨he, hs, hp, ht⟩, hsa, hpa⟩
  · obtain ⟨i, hi⟩ := ht cap ho (Fintype.card V)
    refine ⟨i, fun Δ ΔF hΔ1 hΔF1 => ?_⟩
    obtain ⟨rho, -, -, hw, hs, hp, hpa, hl, hb⟩ :=
      sleepyStress_witness key hn (zero_lt_one.trans hΔ1) (zero_lt_one.trans hΔF1) _ ha hΔ1 hΔF1
        hf cap i hi le_rfl
    exact ⟨⟨_, rho⟩, ⟨hw, rfl, rfl⟩, ⟨hs, hp, hl⟩, hb, hpa⟩
  · have hΔ : 0 < Δ := zero_lt_one.trans hΔ1
    have hΔF : 0 < ΔF := zero_lt_one.trans hΔF1
    have hl : (0 : Time) ≤ (K.params.lag : Time) * Δ := mul_nonneg (by positivity) hΔ.le
    have hk : (0 : Time) ≤ (k : Time) * Δ := mul_nonneg (by positivity) hΔ.le
    have hbud : (1 : Time) ≤ (K.params.budget : Time) := by exact_mod_cast ha.budget_pos
    have hT : OutageTimes K.params Δ ((k : Time) * Δ)
        ((k : Time) * Δ + (K.params.lag : Time) * Δ + Δ)
        ((k : Time) * Δ + (K.params.lag : Time) * Δ + Δ + Δ) :=
      ⟨hk, by linarith only [hΔ], by linarith only [hΔ],
        by linarith only [hk, hl, hΔ, le_mul_of_one_le_left hΔ.le hbud]⟩
    obtain ⟨rho, -, -, hw, ho, hoa⟩ := outage_witness (F := F) key hn hΔ hΔF _ ha hΔ1 hΔF1 hT
      (by linarith only [hl, hΔ]) le_rfl le_rfl
    exact ⟨⟨_, rho⟩, _, _, _, ⟨hw, rfl, rfl⟩, ho, hoa, le_rfl⟩
  · have hΔ : 0 < Δ := zero_lt_one.trans hΔ1
    have hΔF : 0 < ΔF := zero_lt_one.trans hΔF1
    obtain ⟨i, hi⟩ := ht cap ho (Fintype.card V)
    have hL := progLen_nonneg F K cap i (⟨Δ, hΔ, ΔF, hΔF, allAwake⟩ : Env V)
    have hlat : 0 ≤ (K.params.latency cap i : Time) * Δ := mul_nonneg (by positivity) hΔ.le
    have hheal : 0 ≤ (max g 0 + (K.params.heal cap i : Time) * Δ) :=
      add_nonneg (le_max_right _ _) (mul_nonneg (by positivity) hΔ.le)
    have hrdy : 0 ≤ (max g 0 + (K.params.catchUp : Time) * Δ + 1) := by
      have hg := le_max_right g 0
      have : (0 : Time) ≤ (K.params.catchUp : Time) * Δ := mul_nonneg (by positivity) hΔ.le
      linarith only [hg, this]
    obtain ⟨sel, hsel, hprog, hbad⟩ := bad_selection key hn hΔ hΔF
      ((max g 0 + (K.params.heal cap i : Time) * Δ) +
        (max g 0 + (K.params.catchUp : Time) * Δ + 1) + (K.params.latency cap i : Time) * Δ +
        progLen F K cap i (⟨Δ, hΔ, ΔF, hΔF, allAwake⟩ : Env V) + Δ + 2) allAwake (fun _ => rfl)
        hf cap i hi
    obtain ⟨rho, hpt, hk, hs, hw, he, hs', hp, hpa, ht', -⟩ :=
      healthy_witness_sel key hn hΔ hΔF _ ha hΔ1 hΔF1 cap i g sel hsel hprog hr
        (by linarith only [hheal, hrdy, hlat, hL, hΔ])
        (by linarith only [hheal, hrdy, hlat, hL, hΔ])
        (by linarith only [hheal, hrdy, hlat, hL, hΔ])
    exact ⟨i, ⟨_, rho⟩, ⟨hw, rfl, rfl⟩, ⟨he, hs', hp, ht'⟩, hpa,
      hbad rho hs hk (congrArg EnvPoint.faultyAt hpt)⟩

end Consensus.Shape
end

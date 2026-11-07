module
public import ConsensusLean.Proofs.RegimesRealizable.Growth
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
    exact ⟨⟨_, rho⟩, ⟨hw, by change rho.point.env.ΔAC = Δ; rw [Model.Run.point, realPoint_env],
      by change rho.point.env.ΔFG = ΔF; rw [Model.Run.point, realPoint_env]⟩, ⟨hs, hp, ht⟩, hpa⟩
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
    exact ⟨⟨_, rho⟩, ⟨hw, by change rho.point.env.ΔAC = Δ; rw [Model.Run.point, realPoint_env],
      by change rho.point.env.ΔFG = ΔF; rw [Model.Run.point, realPoint_env]⟩,
      ⟨he, hs, hp, ht⟩, hsa, hpa⟩
  · obtain ⟨i, hi⟩ := ht cap ho (Fintype.card V)
    refine ⟨i, fun Δ ΔF hΔ1 hΔF1 => ?_⟩
    obtain ⟨rho, -, -, hw, hs, hp, hpa, hl, hb⟩ :=
      sleepyStress_witness key hn (zero_lt_one.trans hΔ1) (zero_lt_one.trans hΔF1) _ ha hΔ1 hΔF1
        hf cap i hi le_rfl
    exact ⟨⟨_, rho⟩, ⟨hw, by change rho.point.env.ΔAC = Δ; rw [Model.Run.point, realPoint_env],
      by change rho.point.env.ΔFG = ΔF; rw [Model.Run.point, realPoint_env]⟩, ⟨hs, hp, hl⟩, hb, hpa⟩
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
    exact ⟨⟨_, rho⟩, _, _, _,
      ⟨hw, by change rho.point.env.ΔAC = Δ; rw [Model.Run.point, realPoint_env],
        by change rho.point.env.ΔFG = ΔF; rw [Model.Run.point, realPoint_env]⟩, ho, hoa, le_rfl⟩
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
        progLen F K cap i (⟨Δ, hΔ, ΔF, hΔF, allAwake⟩ : Env V) + Δ + 2) allAwake
        (fun _ => allAwake_apply _ _)
        hf cap i hi
    obtain ⟨rho, hpt, hk, hs, hw, he, hs', hp, hpa, ht', -⟩ :=
      healthy_witness_sel key hn hΔ hΔF _ ha hΔ1 hΔF1 cap i g sel hsel hprog hr
        (by linarith only [hheal, hrdy, hlat, hL, hΔ])
        (by linarith only [hheal, hrdy, hlat, hL, hΔ])
        (by linarith only [hheal, hrdy, hlat, hL, hΔ])
    exact ⟨i, ⟨_, rho⟩,
      ⟨hw, by change rho.point.env.ΔAC = Δ; rw [Model.Run.point, realPoint_env],
        by change rho.point.env.ΔFG = ΔF; rw [Model.Run.point, realPoint_env]⟩,
      ⟨he, hs', hp, ht'⟩, hpa,
      hbad rho hs hk (congrArg EnvPoint.faultyAt hpt)⟩
  · intro cap i Δ ΔF hΔ hΔF
    obtain ⟨r, hv, hnexc, hAC, hFG, he, hs, -, hp, hl, hgrowth, hpa⟩ :=
      growing_live_witness F K key hn ha hf cap i Δ ΔF 0 0 0 hΔ hΔF
    exact ⟨r, hv, hnexc, hAC, hFG,
      ⟨⟨he.psync le_rfl (by rwa [hAC]) (by rwa [hFG]), hs⟩, hp, hl⟩, hgrowth, hpa⟩
  · intro cap i Δ ΔF g hΔ hΔF hr hg
    obtain ⟨r, hv, hnexc, hAC, hFG, he, -, hh, hp, hl, hgrowth, hpa⟩ :=
      growing_live_witness F K key hn ha hf cap i Δ ΔF g
        (max g 0 + (K.params.heal cap i : Time) * Δ)
        (max g 0 + (K.params.catchUp : Time) * Δ + 1) hΔ hΔF
    rw [← hAC] at hr
    exact ⟨r, hv, hnexc, hAC, hFG,
      ⟨he, ⟨he.psync le_rfl (by rwa [hAC]) (by rwa [hFG]), hh, by rwa [hFG]⟩,
        by simpa only [System.ready, System.cDur, hAC] using hp,
        by simpa only [System.heal, hAC] using hl⟩,
      by simpa only [System.heal, hAC] using hgrowth,
      by simpa only [System.ready, System.cDur, hAC] using hpa⟩
  · exact growing_outage_witness F K key hn ha

end Consensus.Shape
end

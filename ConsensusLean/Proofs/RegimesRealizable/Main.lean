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
    (hn : K.params.Room (Fintype.card V)) : RealizableActive F K V := by
  have hn3 : 3 ≤ Fintype.card V := by
    have hnonneg := mul_nonneg ha.θ_range.1 (Nat.cast_nonneg (α := ℚ) (Fintype.card V))
    have htwo : (2 : ℚ) < Fintype.card V := by linarith only [hn.1, hnonneg]
    have : 2 < Fintype.card V := by exact_mod_cast htwo
    omega
  let key : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  refine ⟨fun cap i Δ ΔF hΔ1 hΔF1 => ?_, fun cap i Δ ΔF g hΔ1 hΔF1 hr hg => ?_,
    fun cap hc ho k hk hθk => ?_, fun Δ ΔF k hΔ1 hΔF1 => ?_,
    fun cap ho Δ ΔF g hΔ1 hΔF1 hr hg => ?_, ?_, ?_, ?_⟩
  · obtain ⟨rho, -, hw, hs, hp, hpa, ht⟩ := sleepy_witness key hn3 (zero_lt_one.trans hΔ1)
      (zero_lt_one.trans hΔF1) _ ha hn hΔ1 hΔF1 hf cap i le_rfl
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
    obtain ⟨rho, -, hw, he, hs, hp, hpa, ht, hsa⟩ := healthy_witness key hn3 hΔ hΔF
      ((max g 0 + (K.params.heal cap i : Time) * Δ) +
        (max g 0 + (K.params.catchUp : Time) * Δ + 1) + (K.params.latency cap i : Time) * Δ +
        progLen F K cap i (⟨Δ, hΔ, ΔF, hΔF, allAwake⟩ : Env V) + Δ + 2) ha hn hΔ1 hΔF1 hf cap i g hr
      (by linarith only [hheal, hrdy, hlat, hL, hΔ]) (by linarith only [hheal, hrdy, hlat, hL, hΔ])
      (by linarith only [hheal, hrdy, hlat, hL, hΔ])
    exact ⟨⟨_, rho⟩, ⟨hw, by change rho.point.env.ΔAC = Δ; rw [Model.Run.point, realPoint_env],
      by change rho.point.env.ΔFG = ΔF; rw [Model.Run.point, realPoint_env]⟩,
      ⟨he, hs, hp, ht⟩, hsa, hpa⟩
  · obtain ⟨i, hi⟩ := ht cap ho (Fintype.card V)
    let m := min k (Fintype.card V - 1)
    have hm : 2 ≤ m := by dsimp [m]; omega
    have hmn : m < Fintype.card V := by dsimp [m]; omega
    have hmk : m ≤ k := min_le_left _ _
    have hmargin : K.params.θ * ((m : ℚ) + 1) < m := by
      by_cases h : k ≤ Fintype.card V - 1
      · simpa only [m, min_eq_left h] using hθk
      · have he : m + 1 = Fintype.card V := by dsimp [m]; omega
        have heq : (m : ℚ) + 1 = Fintype.card V := by exact_mod_cast he
        rw [heq]
        linarith only [hn.1, heq]
    refine ⟨i, fun Δ ΔF hΔ1 hΔF1 => ?_⟩
    obtain ⟨rho, -, hw, hs, hp, hpa, hl, hb⟩ :=
      sleepyStress_witness key hn3 (zero_lt_one.trans hΔ1) (zero_lt_one.trans hΔF1) _ ha
        m hm hmn hmargin hΔ1 hΔF1
        hf cap i hi le_rfl
    exact ⟨⟨_, rho⟩, ⟨hw, by change rho.point.env.ΔAC = Δ; rw [Model.Run.point, realPoint_env],
      by change rho.point.env.ΔFG = ΔF; rw [Model.Run.point, realPoint_env]⟩, ⟨hs, hp, hl⟩,
      fun t ht hH => (hb t ht hH).trans hmk, hpa⟩
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
    obtain ⟨rho, -, hw, ho, hoa⟩ := outage_witness (F := F) key hn3 hΔ hΔF _ ha hn hΔ1 hΔF1 hT
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
    obtain ⟨key', z, hz, hk1, hgood⟩ :=
      exists_witness_key key hn3 (extremalCommittee F (⟨Δ, hΔ, ΔF, hΔF, allAwake⟩ : Env V))
    obtain ⟨sel, hsel, hduty, hprog, hbad⟩ := bad_selection key hn3 hΔ hΔF
      ((max g 0 + (K.params.heal cap i : Time) * Δ) +
        (max g 0 + (K.params.catchUp : Time) * Δ + 1) + (K.params.latency cap i : Time) * Δ +
        progLen F K cap i (⟨Δ, hΔ, ΔF, hΔF, allAwake⟩ : Env V) + Δ + 2) allAwake
        (fun _ => allAwake_apply _ _) key' z hz hk1
        hf cap i hi
    obtain ⟨rho, hpt, hk, hs, hw, he, hs', hp, hpa, ht', -⟩ :=
      healthy_witness_sel key hn3 hΔ hΔF _ ha hn hΔ1 hΔF1 cap i g key' sel hsel hduty
        (by rw [realPoint_env]; exact hgood) hprog hr
        (by linarith only [hheal, hrdy, hlat, hL, hΔ])
        (by linarith only [hheal, hrdy, hlat, hL, hΔ])
        (by linarith only [hheal, hrdy, hlat, hL, hΔ])
    exact ⟨i, ⟨_, rho⟩,
      ⟨hw, by change rho.point.env.ΔAC = Δ; rw [Model.Run.point, realPoint_env],
        by change rho.point.env.ΔFG = ΔF; rw [Model.Run.point, realPoint_env]⟩,
      ⟨he, hs', hp, ht'⟩, hpa,
      hbad rho hs hk (congrArg EnvPoint.faultyAt hpt)⟩
  · intro cap i Δ ΔF hΔ hΔF
    obtain ⟨r, hv, hnexc, hAC, hFG, he, hs, hcs, -, -, hp, hl, hgrowth, hpa⟩ :=
      growing_live_witness F K key hn3 ha hn hf cap i Δ ΔF 0 0 0 hΔ hΔF
    exact ⟨r, hv, hnexc, hAC, hFG,
      ⟨⟨he.psync le_rfl (by rwa [hAC]) (by rwa [hFG]), hs, hcs⟩, hp, hl⟩, hgrowth, hpa⟩
  · intro cap i Δ ΔF g hΔ hΔF hr hg
    obtain ⟨r, hv, hnexc, hAC, hFG, he, -, -, hh, hch, hp, hl, hgrowth, hpa⟩ :=
      growing_live_witness F K key hn3 ha hn hf cap i Δ ΔF g
        (max g 0 + (K.params.heal cap i : Time) * Δ)
        (max g 0 + (K.params.catchUp : Time) * Δ + 1) hΔ hΔF
    rw [← hAC] at hr
    exact ⟨r, hv, hnexc, hAC, hFG,
      ⟨he, ⟨he.psync le_rfl (by rwa [hAC]) (by rwa [hFG]), hh, by rwa [hFG], hch⟩,
        by simpa only [System.ready, System.cDur, hAC] using hp,
        by simpa only [System.heal, hAC] using hl⟩,
      by simpa only [System.heal, hAC] using hgrowth,
      by simpa only [System.ready, System.cDur, hAC] using hpa⟩
  · exact growing_outage_witness F K key hn3 ha hn

end Consensus.Shape
end

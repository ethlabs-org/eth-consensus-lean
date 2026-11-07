module
public import ConsensusLean.Proofs.RegimesRealizable.Basic
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Growing-fault realizability witnesses

The transaction source is initially honest and is compromised strictly after
its submission and protected read. The selected proposer and the later reader
are different validators and stay honest throughout.
-/

namespace Consensus.Shape
open Blocks
open Consensus.Model (pubOf)

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]
variable {V : Type} [Fintype V] [DecidableEq V]

/-- A single compromise at `κ`, with the only transaction submitted to its source at zero. -/
def growthPoint (key : Fin (Fintype.card V) ≃ V) (hn : 5 ≤ Fintype.card V)
    (Δ : Time) (hΔ : 0 < Δ) (ΔF : Time) (hΔF : 0 < ΔF)
    (awake : V → Time → Bool) (H κ : Time) : EnvPoint V :=
  ⟨⟨Δ, hΔ, ΔF, hΔF, awake⟩, fun t => if κ ≤ t then {key ⟨0, by omega⟩} else ∅,
    by
      intro a b hab
      dsimp only
      split_ifs with ha hb
      · exact Finset.Subset.refl _
      · exact False.elim (hb (ha.trans hab))
      · exact Finset.empty_subset _
      · exact Finset.Subset.refl _,
    H, fun v t => if v = key ⟨0, by omega⟩ ∧ t = 0 then [42] else []⟩

theorem growthPoint_eq (key : Fin (Fintype.card V) ≃ V) (hn : 5 ≤ Fintype.card V)
    (Δ : Time) (hΔ : 0 < Δ) (ΔF : Time) (hΔF : 0 < ΔF)
    (awake : V → Time → Bool) (H κ : Time) :
    growthPoint key hn Δ hΔ ΔF hΔF awake H κ =
      { (realPoint key hn Δ hΔ ΔF hΔF awake H) with
        faultyAt := fun t => if κ ≤ t then {key ⟨0, by omega⟩} else ∅
        faultyAt_mono := by
          intro a b hab
          dsimp only
          split_ifs with ha hb
          · exact Finset.Subset.refl _
          · exact False.elim (hb (ha.trans hab))
          · exact Finset.empty_subset _
          · exact Finset.Subset.refl _
        submit := fun v t => if v = key ⟨0, by omega⟩ ∧ t = 0 then [42] else [] } := by
  rw [realPoint_eq]
  rfl

section Point
variable (key : Fin (Fintype.card V) ≃ V) (hn : 5 ≤ Fintype.card V)
  {Δ : Time} (hΔ : 0 < Δ) {ΔF : Time} (hΔF : 0 < ΔF)
  (awake : V → Time → Bool) (H κ : Time)

theorem growthPoint_faulty (t : Time) :
    (growthPoint key hn Δ hΔ ΔF hΔF awake H κ).faultyAt t =
      if κ ≤ t then {kv key hn 0 (by decide)} else ∅ := by rfl

theorem growthPoint_honest {j : Nat} (hj : j < 5) (h0 : j ≠ 0) (t : Time) :
    (growthPoint key hn Δ hΔ ΔF hΔF awake H κ).HonestAt (kv key hn j hj) t := by
  simp only [EnvPoint.HonestAt, growthPoint_faulty]
  split_ifs
  · simpa only [Finset.mem_singleton] using (kv_ne key hn (hj' := by decide) h0)
  · exact Finset.notMem_empty _

/-- Every validator ready in the fully charged static view is ready in every retained view. -/
theorem growthPoint_ready_subset (c t d : Time) :
    (realPoint key hn Δ hΔ ΔF hΔF awake H).readyAt c t ⊆
      ((growthPoint key hn Δ hΔ ΔF hΔF awake H κ).retain d).readyAt c t := by
  intro v hv
  simp only [EnvPoint.readyAt, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  rw [realPoint_eq] at hv
  refine ⟨?_, hv.2⟩
  change v ∉ (if κ ≤ d then {kv key hn 0 (by decide)} else ∅)
  split_ifs
  · exact hv.1
  · exact Finset.notMem_empty _

theorem growthPoint_eta {θ : ℚ} (hθ : 0 ≤ θ ∧ θ ≤ 1 / 2)
    (hready : ∀ c t, Fintype.card V ≤
      ((realPoint key hn Δ hΔ ΔF hΔF awake H).readyAt c t).card + 2)
    (η c W a b : Time) :
    (growthPoint key hn Δ hΔ ΔF hΔF awake H κ).EtaSleepyOn θ η c W a b := by
  intro t _ _
  apply etaReadyAbove_of_card hn hθ
  exact (hready c t).trans (Nat.add_le_add_right
    (Finset.card_le_card (growthPoint_ready_subset key hn hΔ hΔF awake H κ c t _)) 2)

end Point

section Activity
variable (key : Fin (Fintype.card V) ≃ V) (hn : 5 ≤ Fintype.card V)
  {Δ : Time} (hΔ : 0 < Δ) {ΔF : Time} (hΔF : 0 < ΔF) (H κ : Time)

/-- The permanently honest selected proposer satisfies every fitting recurrence, including hold. -/
theorem growthPoint_holds (F : ChainShapeFamily O Info) (K : Contract ProgressReq)
    (hf : ProgressFits K F) (cap : Capability) (i : K.Idx) (c s e : Time) :
    shapeHolds F (K.progress cap i) c s e
      (growthPoint key hn Δ hΔ ΔF hΔF allAwake H κ)
      (key, extremalSel F (growthPoint key hn Δ hΔ ΔF hΔF allAwake H κ).env) := by
  have hfit := hf cap i (pubOf (growthPoint key hn Δ hΔ ΔF hΔF allAwake H κ).env)
  cases hreq : K.progress cap i with
  | recur ρ =>
    rw [hreq] at hfit
    change ∀ s, (F _).skel.proposerSel s = .sized 1 at hfit
    apply patternRecurrence_of_all
    intro sl j _
    have hmem := extremalSel_proposer_mem F hfit (by omega) (sl + j)
    refine ⟨⟨⟨1, by omega⟩, (hmem _).mpr rfl⟩, fun k hk => ?_⟩
    have hk1 : k = ⟨1, by omega⟩ := Fin.ext ((hmem k).mp hk)
    subst hk1
    exact ⟨⟨growthPoint_honest key hn hΔ hΔF allAwake H κ (by decide) (by decide) _,
      fun _ _ _ => allAwake_apply _ _⟩,
      growthPoint_honest key hn hΔ hΔF allAwake H κ (by decide) (by decide) _⟩
  | notReadyAtMost m =>
    intro t _ _ _
    have hr := growthPoint_ready_subset key hn hΔ hΔF allAwake H κ c t t
    have hc := Finset.card_le_card hr
    have he : ((growthPoint key hn Δ hΔ ΔF hΔF allAwake H κ).retain t).readyAt c t =
        (growthPoint key hn Δ hΔ ΔF hΔF allAwake H κ).readyAt c t := by rfl
    rw [he] at hc
    have hm := m.pos
    exact (allAwake_readyAt key hn hΔ hΔF H c t).trans
      (by omega)

/-- The source's pre-compromise read and its sole submission remain active at a later reader. -/
theorem growthPoint_active (c start D : Time) (hκ : 0 < κ) (hκH : κ ≤ H)
    (hH : max 0 start + Δ + D ≤ H) :
    GrowthActive c start D (growthPoint key hn Δ hΔ ΔF hΔF allAwake H κ) := by
  refine ⟨kv key hn 0 (by decide), kv key hn 1 (by decide), 42, 0, 0, κ, H,
    kv_ne key hn (by decide), le_rfl, le_rfl, hκ, hκH, le_rfl, hH,
    ⟨?_, fun _ _ _ => allAwake_apply _ _⟩, allAwake_apply _ _, ?_, ?_, ?_, ?_,
    ⟨growthPoint_honest key hn hΔ hΔF allAwake H κ (by decide) (by decide) _,
      fun _ _ _ => allAwake_apply _ _⟩,
    ⟨growthPoint_honest key hn hΔ hΔF allAwake H κ (by decide) (by decide) _,
      fun _ _ _ => allAwake_apply _ _⟩⟩
  · simp only [EnvPoint.HonestAt, growthPoint_faulty, not_le.mpr hκ, ↓reduceIte,
      Finset.notMem_empty, not_false_eq_true]
  · simp only [growthPoint_eq, and_self, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false]
  · intro v t hx
    simp only [growthPoint_eq] at hx
    split_ifs at hx with h
    · exact h.1
    · exact False.elim (List.not_mem_nil hx)
  · simp only [growthPoint_faulty, not_le.mpr hκ, ↓reduceIte, Finset.notMem_empty,
      not_false_eq_true]
  · simp only [growthPoint_faulty, le_rfl, ↓reduceIte, Finset.mem_singleton]

/-- The same sole submission is an active liveness query. -/
theorem growthPoint_txLiveActive (c start D : Time) (hκ : 0 < κ)
    (hH : max 0 start + Δ + D ≤ H) :
    (growthPoint key hn Δ hΔ ΔF hΔF allAwake H κ).TxLiveActive c start D := by
  refine ⟨42, 0, H, kv key hn 0 (by decide), kv key hn 1 (by decide), le_rfl,
    ?_, allAwake_apply _ _, ?_, kv_ne key hn (by decide), ?_, hH, le_rfl,
    growthPoint_honest key hn hΔ hΔF allAwake H κ (by decide) (by decide) _,
    fun _ _ _ => allAwake_apply _ _⟩
  · simp only [EnvPoint.HonestAt, growthPoint_faulty, not_le.mpr hκ, ↓reduceIte,
      Finset.notMem_empty, not_false_eq_true]
  · simp only [growthPoint_eq, and_self, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false]
  · intro t
    have hne : kv key hn 1 (by decide) ≠ key ⟨0, by omega⟩ := kv_ne key hn (by decide)
    simp only [growthPoint_eq, hne, false_and,
      ↓reduceIte, List.not_mem_nil, not_false_eq_true]

end Activity
end Consensus.Shape
end

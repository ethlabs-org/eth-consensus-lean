module
public import AvailableChainFGSAClaims.Statements.Healed

public section

/-! F0.5: same-time compatibility and restriction to a later healing start. -/

namespace AvailableChain.FGSA.Run

variable (p : Params) {In : Type} (c : AppCodec In)
    {V : Type} [DecidableEq V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

omit [DecidableEq V] in
private theorem healed_start_le {t u : Time} (htu : t ≤ u) :
    healStart p c rho t ≤ healStart p c rho u := by
  rcases htu.lt_or_eq with hlt | rfl
  · rw [healStart_def, healStart_def]
    split <;> split
    all_goals
      change (rho.events.filter _).length ≤ (rho.events.filter _).length
      rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
      apply List.countP_mono_left
      intro e _ he
    · have het : e.time ≤ t := by
        rcases Prod.Lex.toLex_le_toLex.mp (of_decide_eq_true he) with h | ⟨h, _⟩
        · exact h.le
        · exact h.le
      exact decide_eq_true (Prod.Lex.toLex_le_toLex.mpr (Or.inl (het.trans_lt hlt)))
    · have het : e.time ≤ t := by
        rcases Prod.Lex.toLex_le_toLex.mp (of_decide_eq_true he) with h | ⟨h, _⟩
        · exact h.le
        · exact h.le
      exact decide_eq_true (het.trans htu)
    · exact decide_eq_true (Prod.Lex.toLex_le_toLex.mpr
        (Or.inl ((of_decide_eq_true he).trans_lt hlt)))
    · exact decide_eq_true ((of_decide_eq_true he).trans htu)
  · exact le_rfl

/-- Same-time compatibility (21 H.22:2996–2997; 22 §1:178–179),
by taking equal event indices in the Gen cross-time property. -/
theorem healed_same_time {t : Time} (h : Healed p c E rho t) :
    ∀ i x y, HealSuffix p c rho t i → confirmedReaderIdx p c E rho x i →
      confirmedReaderIdx p c E rho y i →
      Block.Compatible (S_at p c E rho i x) (S_at p c E rho i y) := by
  intro i x y hi hx hy
  exact h.1 i i x y hi hi hx hy

/-- Healed.mono, J17: a later start restricts the suffix and the proposal slots
(21 H.22:2985–2999; 22 §1:167–181; P3 §4.6 and S3 §8 row 14). -/
theorem healed_mono_start {t u : Time} (htu : t ≤ u) (h : Healed p c E rho t) :
    Healed p c E rho u := by
  have hs : ∀ i, HealSuffix p c rho u i → HealSuffix p c rho t i :=
    fun _ hi => ⟨(healed_start_le p c rho htu).trans hi.1, hi.2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j x y hi hj hx hy
    exact h.1 i j x y (hs i hi) (hs j hj) hx hy
  · intro i j x hi hj hij hx
    exact h.2.1 i j x (hs i hi) (hs j hj) hij hx
  · intro i x y hi hx hy
    exact h.2.2.1 i x y (hs i hi) hx hy
  · intro s B hu hh hp
    exact h.2.2.2 s B (htu.trans hu) hh hp

end AvailableChain.FGSA.Run
end

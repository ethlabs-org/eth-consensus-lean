module
public import ConsensusProblem.Properties
public import Mathlib.Tactic

@[expose] public section

/-! # Environment atoms: monotonicity and counting (layer 0)

Facts about the participation and fault-bound vocabulary of `Basic`: each
threshold is monotone in its parameter, and a counting step from "more than
half of all validators ready" to a bound on the faulty validators together
with an honest set that avoids the ready ones. -/

namespace Consensus

namespace EnvPoint

variable {V : Type} [Fintype V] [DecidableEq V] (p : EnvPoint V)

/-- A smaller ready fraction is weaker. -/
theorem ReadyAbove.mono {θ θ' : ℚ} {c t : Time} (h : p.ReadyAbove θ' c t)
    (hle : θ ≤ θ') : p.ReadyAbove θ c t :=
  lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle (by positivity)) h

/-- A larger absolute fault bound is weaker. -/
theorem FaultsAtMost.mono {m m' : Nat} (h : p.FaultsAtMost m') (hle : m' ≤ m) : p.FaultsAtMost m :=
  le_trans h hle

/-- A larger fault bound is weaker. -/
theorem FaultsBelow.mono {β β' : ℚ} (h : p.FaultsBelow β') (hle : β' ≤ β) : p.FaultsBelow β :=
  lt_of_lt_of_le h (mul_le_mul_of_nonneg_right hle (by positivity))

omit [DecidableEq V] in
/-- A smaller fraction of all validators is weaker. -/
theorem ReadyOfAll.mono {φ φ' : ℚ} {c t : Time} (h : p.ReadyOfAll φ' c t)
    (hle : φ ≤ φ') : p.ReadyOfAll φ c t :=
  lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle (by positivity)) h

omit [DecidableEq V] in
/-- A smaller fraction of all validators honest and awake is weaker. -/
theorem AwakeOfAll.mono {φ φ' : ℚ} {t : Time} (h : p.AwakeOfAll φ' t) (hle : φ ≤ φ') :
    p.AwakeOfAll φ t :=
  lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle (by positivity)) h

/-- If every validator ready at `t` is in an honest set `C`, and `W` avoids
`C`, then more than half of all validators ready gives `2·|faulty ∪ W| < n`
(the outage regime's cover at `b₀` with `cover = ½`). -/
theorem two_mul_card_faulty_union_lt {c t : Time} {C W : Finset V}
    (hR : p.readyAt c t ⊆ C) (hC : C ⊆ p.honest) (hW : Disjoint W C)
    (h : p.ReadyOfAll (1 / 2) c t) : 2 * (p.faulty ∪ W).card < Fintype.card V := by
  have hdis : Disjoint (p.faulty ∪ W) C := by
    refine Finset.disjoint_union_left.mpr ⟨?_, hW⟩
    refine Finset.disjoint_left.mpr fun v hv hvC => ?_
    exact (Finset.mem_sdiff.mp hv).2 (hC hvC)
  have hsum : (p.faulty ∪ W).card + C.card ≤ Fintype.card V := by
    rw [← Finset.card_union_of_disjoint hdis]
    exact Finset.card_le_univ _
  have hRC : (p.readyAt c t).card ≤ C.card := Finset.card_le_card hR
  have h' : (Fintype.card V : ℚ) < 2 * (p.readyAt c t).card := by
    unfold ReadyOfAll at h; linarith
  have h'' : Fintype.card V < 2 * (p.readyAt c t).card := by exact_mod_cast h'
  omega

end EnvPoint

end Consensus

end

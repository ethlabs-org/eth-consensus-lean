module
public import ConsensusLean.Spec.Problem.Regimes

public section

/-! # Constant-fault environment points

Static fixtures and reductions of the growing-fault participation vocabulary. -/

namespace Consensus.EnvPoint

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A static environment point with the given honest validators. -/
def ofHonest (E : Env V) (H : Finset V) (horizon : Time)
    (submit : V → Time → List Tx) : EnvPoint V :=
  ⟨E, fun _ => Finset.univ \ H, monotone_const, horizon, submit⟩

@[simp] theorem ofHonest_constantFaults (E : Env V) (H : Finset V) (horizon : Time)
    (submit : V → Time → List Tx) : (ofHonest E H horizon submit).ConstantFaults :=
  fun _ => rfl

@[simp] theorem ofHonest_honestAt (E : Env V) (H : Finset V) (horizon : Time)
    (submit : V → Time → List Tx) (v : V) (t : Time) :
    (ofHonest E H horizon submit).HonestAt v t ↔ v ∈ H := by
  simp [ofHonest, HonestAt]

omit [Fintype V] [DecidableEq V] in
/-- Retaining a constant-fault point does not change it. -/
theorem retain_eq {p : EnvPoint V} (h : p.ConstantFaults) (d : Time) : p.retain d = p := by
  cases p
  simp only [retain, EnvPoint.mk.injEq, true_and, and_true]
  funext t
  exact (h d).trans (h t).symm

omit [Fintype V] [DecidableEq V] in
/-- Honesty is independent of time for a constant fault profile. -/
theorem honestAt_iff_zero {p : EnvPoint V} (h : p.ConstantFaults) (v : V) (t : Time) :
    p.HonestAt v t ↔ p.HonestAt v 0 := by
  simp only [HonestAt, h t]

theorem honestAt_eq {p : EnvPoint V} (h : p.ConstantFaults) (t : Time) :
    p.honestAt t = p.honestAt 0 := by
  simp only [honestAt, h t]

omit [Fintype V] [DecidableEq V] in
theorem ready_iff {p : EnvPoint V} (h : p.ConstantFaults) (c : Time) (v : V) (t : Time) :
    p.Ready c v t ↔ p.HonestAt v 0 ∧ p.AwakeOnClosed v (max 0 (t - c - 1)) t := by
  simp only [Ready, honestAt_iff_zero h]

omit [Fintype V] [DecidableEq V] in
theorem submittedToSome_iff {p : EnvPoint V} (h : p.ConstantFaults) (x : Tx) (t : Time) :
    p.SubmittedToSome x t ↔ ∃ v τ, 0 ≤ τ ∧ τ ≤ t ∧ p.HonestAt v 0 ∧
      p.env.awake v τ = true ∧ x ∈ p.submit v τ := by
  simp only [SubmittedToSome, honestAt_iff_zero h]

omit [DecidableEq V] in
/-- Under constant faults, every look-ahead has the original pointwise sleepy meaning. -/
theorem sleepyOn_iff {p : EnvPoint V} (h : p.ConstantFaults) (θ : ℚ) (c W a b : Time) :
    p.SleepyOn θ c W a b ↔ ∀ t, a ≤ t → t ≤ b → p.ReadyAbove θ c t := by
  simp only [SleepyOn, retain_eq h]

/-- The same reduction for the identity-sensitive sleepy budget. -/
theorem etaSleepyOn_iff {p : EnvPoint V} (h : p.ConstantFaults) (θ : ℚ) (η c W a b : Time) :
    p.EtaSleepyOn θ η c W a b ↔ ∀ t, a ≤ t → t ≤ b → p.EtaReadyAbove θ η c t := by
  simp only [EtaSleepyOn, retain_eq h]

end Consensus.EnvPoint

end

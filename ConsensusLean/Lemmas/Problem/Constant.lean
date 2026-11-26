module
public import ConsensusLean.Spec.Problem.Regimes
public import ConsensusLean.Spec.Problem.CorrectProtocol

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

namespace Consensus.CommLog

variable {V M : Type} {p : EnvPoint V} (L : CommLog V M)

/-- The three static delivery clauses, with honesty fixed at zero. -/
theorem delivers_constant_iff (h : p.ConstantFaults) (dl dlF : Time → Time) (cut : Time) :
    L.Delivers p dl dlF cut ↔
      (∀ v m t, L.sent v m t → p.HonestAt v 0 → ¬ L.fgAtt m → ∀ w a, t ≤ a →
        dl a ≤ cut → dl a ≤ p.horizon → p.HonestAt w 0 → p.AwakeOnClosed w a (dl a) →
        L.Held p w m (dl a)) ∧
      (∀ v m t, L.sent v m t → p.HonestAt v 0 → L.fgAtt m → ∀ w a, t ≤ a →
        dlF a ≤ cut → dlF a ≤ p.horizon → p.HonestAt w 0 → p.AwakeOnClosed w a (dlF a) →
        L.Held p w m (dlF a)) ∧
      (∀ u x τ, 0 ≤ τ → p.HonestAt u 0 → p.env.awake u τ = true → x ∈ p.submit u τ →
        ∀ w a, τ ≤ a → dl a ≤ cut → dl a ≤ p.horizon → p.HonestAt w 0 →
          p.AwakeOnClosed w a (dl a) → L.TxHeld w x (dl a)) := by
  constructor
  · intro hd
    exact ⟨by simpa only [EnvPoint.honestAt_iff_zero h] using hd.msgs,
      by simpa only [EnvPoint.honestAt_iff_zero h] using hd.fgAtts,
      by simpa only [EnvPoint.honestAt_iff_zero h] using hd.txs⟩
  · rintro ⟨hm, hf, ht⟩
    exact ⟨by simpa only [EnvPoint.honestAt_iff_zero h] using hm,
      by simpa only [EnvPoint.honestAt_iff_zero h] using hf,
      by simpa only [EnvPoint.honestAt_iff_zero h] using ht⟩

end Consensus.CommLog

namespace Consensus.System

variable {V : Type} {S : System V} {r : S.Run}

/-- At the horizon, constant-fault historical evidence is exactly the old terminal honest view. -/
theorem honestEvidenceBy_eq (hS : S.Laws) (hr : S.Valid r)
    (hc : (S.trace r).point.ConstantFaults) {d : Time}
    (hd : (S.trace r).point.horizon ≤ d) :
    S.honestEvidenceBy r d =
      {o | ∃ v, (S.trace r).point.HonestAt v 0 ∧ o ∈ S.view r v (S.trace r).cuts} := by
  ext o
  constructor
  · rintro ⟨v, i, hi, _, hv, ho⟩
    exact ⟨v, (EnvPoint.honestAt_iff_zero hc _ _).mp hv, hS.view_mono r v i _ hi ho⟩
  · rintro ⟨v, hv, ho⟩
    exact ⟨v, (S.trace r).cuts, le_rfl,
      ((hS.trace r hr).cutTime_le_horizon _ le_rfl).trans hd,
      (EnvPoint.honestAt_iff_zero hc _ _).mpr hv, ho⟩

end Consensus.System

end

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

theorem awakeAt_constant_eq {p : EnvPoint V} (h : p.ConstantFaults) (t : Time) :
    p.awakeAt t = (p.honestAt 0).filter (fun v => p.env.awake v t = true) := by
  simp only [awakeAt, honestAt_eq h]

theorem readyAt_constant_eq {p : EnvPoint V} (h : p.ConstantFaults) (c t : Time) :
    p.readyAt c t = (by
      classical
      exact (p.honestAt 0).filter (fun v => p.Ready c v t)) := by
  classical
  ext v
  change (v ∈ Finset.univ.filter (fun w => p.Ready c w t)) ↔ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hv
    refine ⟨?_, hv⟩
    simpa only [honestAt, Finset.mem_sdiff, Finset.mem_univ, true_and, HonestAt] using
      (honestAt_iff_zero h v t).mp hv.1
  · exact And.right

theorem awakeIn_constant_eq {p : EnvPoint V} (h : p.ConstantFaults) (a b : Time) :
    p.awakeIn a b = (by
      classical
      exact (p.honestAt 0).filter
        (fun v => ∃ u, a ≤ u ∧ u ≤ b ∧ p.env.awake v u = true)) := by
  classical
  ext v
  change v ∈ Finset.univ.filter (fun w =>
    ∃ u, a ≤ u ∧ u ≤ b ∧ p.HonestAt w u ∧ p.env.awake w u = true) ↔ _
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, honestAt_iff_zero h]
  rw [Finset.mem_filter]
  simp only [honestAt, Finset.mem_sdiff, Finset.mem_univ, true_and]
  change (∃ u, a ≤ u ∧ u ≤ b ∧ p.HonestAt v 0 ∧ p.env.awake v u = true) ↔
    p.HonestAt v 0 ∧ ∃ u, a ≤ u ∧ u ≤ b ∧ p.env.awake v u = true
  constructor
  · rintro ⟨u, ha, hb, hv, hw⟩
    exact ⟨hv, u, ha, hb, hw⟩
  · rintro ⟨hv, u, ha, hb, hw⟩
    exact ⟨u, ha, hb, hv, hw⟩

omit [DecidableEq V] in
theorem readyAbove_constant_iff {p : EnvPoint V} (h : p.ConstantFaults) (θ : ℚ)
    (c t : Time) : p.ReadyAbove θ c t ↔
      θ * ((p.readyAt c t).card + (p.faultyAt 0).card : ℚ) < (p.readyAt c t).card := by
  simp only [ReadyAbove, faultCount, h t]

theorem etaReadyAbove_constant_iff {p : EnvPoint V} (h : p.ConstantFaults) (θ : ℚ)
    (η c t : Time) : p.EtaReadyAbove θ η c t ↔
      if η ≤ 0 then p.ReadyAbove θ c t else
        θ * ((p.readyAt c t ∪ p.awakeIn (max 0 (t - η)) t ∪ p.faultyAt 0).card : ℚ) <
          (p.readyAt c t).card := by
  simp only [EtaReadyAbove, h t]

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

theorem healthyOn_constant_iff {p : EnvPoint V} (h : p.ConstantFaults) (β : ℚ) (g b : Time) :
    p.HealthyOn β g b ↔ ((p.faultyAt 0).card : ℚ) < β * Fintype.card V ∧
      ∀ v ∈ p.honestAt 0, p.AwakeOnClosed v (max g 0) b := by
  simp only [HealthyOn, faultCount, h b, AwakeOnClosed, honestAt, Finset.mem_sdiff,
    Finset.mem_univ, true_and, honestAt_iff_zero h]
  constructor
  · exact fun ⟨hb, ha⟩ => ⟨hb, fun v hv t ht htb => ha v t ht htb hv⟩
  · exact fun ⟨hb, ha⟩ => ⟨hb, fun v t ht htb hv => ha v hv t ht htb⟩

theorem noSleepOn_constant_iff {p : EnvPoint V} (h : p.ConstantFaults) (a b : Time) :
    p.NoSleepOn a b ↔ ∀ v ∈ p.honestAt 0, ∀ t, a ≤ t → t ≤ b →
      p.env.awake v t = true → p.AwakeOnClosed v t b := by
  simp only [NoSleepOn, HonestAt, h b, honestAt, Finset.mem_sdiff,
    Finset.mem_univ, true_and]

theorem cohortOn_constant_iff {p : EnvPoint V} (h : p.ConstantFaults) (a b : Time) :
    p.CohortOn a b ↔ (p.faultyAt 0 ∪ p.lateWakers a b).card < (p.awakeAt a).card := by
  simp only [CohortOn, h b]

omit [Fintype V] [DecidableEq V] in
theorem txLiveActive_constant_iff {p : EnvPoint V} (h : p.ConstantFaults) (c start D : Time) :
    p.TxLiveActive c start D ↔ ∃ (x : Tx) (t t' : Time) (u w : V),
      0 ≤ t ∧ p.HonestAt u 0 ∧ p.env.awake u t = true ∧ x ∈ p.submit u t ∧ w ≠ u ∧
      (∀ τ, x ∉ p.submit w τ) ∧ max t start + p.env.ΔAC + D ≤ t' ∧
      t' ≤ p.horizon ∧ p.Ready c w t' := by
  simp only [TxLiveActive, honestAt_iff_zero h]

end Consensus.EnvPoint

namespace Consensus

theorem outageActive_constant_iff {V : Type}
    {p : EnvPoint V} (h : p.ConstantFaults) (c D T b₀ b₁ : Time) :
    OutageActive c D T b₀ b₁ p ↔
      0 ≤ T ∧ T < b₀ ∧ b₀ + p.env.ΔAC ≤ b₁ ∧ (∃ u, p.Ready c u T) ∧
      (∃ v t, b₀ ≤ t ∧ t < b₁ ∧ p.HonestAt v 0 ∧ p.env.awake v t = false) ∧
      ∃ w t, b₁ + D ≤ t ∧ t ≤ p.horizon ∧ p.Ready c w t := by
  simp only [OutageActive, EnvPoint.honestAt_iff_zero h]

end Consensus

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

theorem eagerFrom_constant_iff (h : p.ConstantFaults) (g : Time) :
    L.EagerFrom p g ↔
      (∀ v m t, L.sent v m t → p.HonestAt v 0 → ∀ w a, max t g < a →
        a ≤ p.horizon → p.HonestAt w 0 → p.env.awake w a = true → L.recv w m a) ∧
      (∀ w m t, L.recv w m t → g ≤ t) ∧
      (∀ u x τ, 0 ≤ τ → p.HonestAt u 0 → p.env.awake u τ = true → x ∈ p.submit u τ →
        ∀ w a, τ ≤ a → p.HonestAt w 0 → p.env.awake w a = true → x ∈ L.inbox w a) := by
  constructor
  · intro hd
    exact ⟨by simpa only [EnvPoint.honestAt_iff_zero h] using hd.recv, hd.quiet,
      by simpa only [EnvPoint.honestAt_iff_zero h] using hd.txs⟩
  · rintro ⟨hr, hq, ht⟩
    exact ⟨by simpa only [EnvPoint.honestAt_iff_zero h] using hr, hq,
      by simpa only [EnvPoint.honestAt_iff_zero h] using ht⟩

theorem pSync_constant_iff (h : p.ConstantFaults) (g : Time) :
    L.PSync p g ↔
      (∀ v m t, L.sent v m t → p.HonestAt v 0 → ¬ L.fgAtt m → ∀ w a, t ≤ a →
        max a g + p.env.ΔAC - 1 ≤ p.horizon →
        max a g + p.env.ΔAC - 1 ≤ p.horizon → p.HonestAt w 0 →
        p.AwakeOnClosed w a (max a g + p.env.ΔAC - 1) →
        L.Held p w m (max a g + p.env.ΔAC - 1)) ∧
      (∀ v m t, L.sent v m t → p.HonestAt v 0 → L.fgAtt m → ∀ w a, t ≤ a →
        max a g + p.env.ΔFG - 1 ≤ p.horizon →
        max a g + p.env.ΔFG - 1 ≤ p.horizon → p.HonestAt w 0 →
        p.AwakeOnClosed w a (max a g + p.env.ΔFG - 1) →
        L.Held p w m (max a g + p.env.ΔFG - 1)) ∧
      (∀ u x τ, 0 ≤ τ → p.HonestAt u 0 → p.env.awake u τ = true → x ∈ p.submit u τ →
        ∀ w a, τ ≤ a → max a g + p.env.ΔAC - 1 ≤ p.horizon →
        max a g + p.env.ΔAC - 1 ≤ p.horizon → p.HonestAt w 0 →
        p.AwakeOnClosed w a (max a g + p.env.ΔAC - 1) →
        L.TxHeld w x (max a g + p.env.ΔAC - 1)) :=
  L.delivers_constant_iff h _ _ _

theorem syncUntil_constant_iff (h : p.ConstantFaults) (b : Time) :
    L.SyncUntil p b ↔
      (∀ v m t, L.sent v m t → p.HonestAt v 0 → ¬ L.fgAtt m → ∀ w a, t ≤ a →
        a + p.env.ΔAC - 1 ≤ b → a + p.env.ΔAC - 1 ≤ p.horizon → p.HonestAt w 0 →
        p.AwakeOnClosed w a (a + p.env.ΔAC - 1) → L.Held p w m (a + p.env.ΔAC - 1)) ∧
      (∀ v m t, L.sent v m t → p.HonestAt v 0 → L.fgAtt m → ∀ w a, t ≤ a →
        a + p.env.ΔFG - 1 ≤ b → a + p.env.ΔFG - 1 ≤ p.horizon → p.HonestAt w 0 →
        p.AwakeOnClosed w a (a + p.env.ΔFG - 1) → L.Held p w m (a + p.env.ΔFG - 1)) ∧
      (∀ u x τ, 0 ≤ τ → p.HonestAt u 0 → p.env.awake u τ = true → x ∈ p.submit u τ →
        ∀ w a, τ ≤ a → a + p.env.ΔAC - 1 ≤ b → a + p.env.ΔAC - 1 ≤ p.horizon →
        p.HonestAt w 0 → p.AwakeOnClosed w a (a + p.env.ΔAC - 1) →
        L.TxHeld w x (a + p.env.ΔAC - 1)) :=
  L.delivers_constant_iff h _ _ _

end Consensus.CommLog

namespace Consensus.Trace

variable {V α Id : Type} (tr : Trace V α Id)

theorem monotone_constant_iff (hc : tr.point.ConstantFaults) (g : Id) (t : Time) :
    tr.Monotone g t ↔ tr.MonotoneAmong (fun v _ => tr.point.HonestAt v 0) g t := by
  simp only [Monotone, MonotoneAmong, EnvPoint.honestAt_iff_zero hc]

theorem nested_constant_iff (hc : tr.point.ConstantFaults) (g₁ g₂ : Id) :
    tr.Nested g₁ g₂ ↔ ∀ v, tr.point.HonestAt v 0 → ∀ i, i ≤ tr.cuts →
      tr.read g₁ v i <+: tr.read g₂ v i := by
  simp only [Nested, EnvPoint.honestAt_iff_zero hc]
  constructor
  · exact fun h v hv i hi => h v i hi hv
  · exact fun h v i hi hv => h v hv i hi

theorem accountablySafe_constant_iff [Fintype V] {O : Type}
    (hc : tr.point.ConstantFaults)
    (view : V → Nat → Set O) (convicts : Set O → V → Prop) (a : ℚ) (g : Id) (t : Time) :
    tr.AccountablySafe view convicts a g t ↔
      ∀ u, tr.point.HonestAt u 0 → ∀ v, tr.point.HonestAt v 0 → ∀ i j,
        tr.InCuts t i → tr.InCuts t j → Compatible (tr.read g u i) (tr.read g v j) ∨
          (Fintype.card V : ℚ) * a ≤ (Consensus.convicted convicts (view u i ∪ view v j)).card := by
  simp only [AccountablySafe, EnvPoint.honestAt_iff_zero hc]
  constructor
  · exact fun h u hu v hv i j hi hj => h u v i j hi hj hu hv
  · exact fun h u v i j hi hj hu hv => h u hu v hv i j hi hj

end Consensus.Trace

namespace Consensus.System

variable {V : Type} {S : System V} {r : S.Run}

theorem witness_constant_iff [Fintype V] [DecidableEq V]
    (hc : (S.pt r).ConstantFaults) :
    S.Witness r ↔ S.Valid r ∧ ¬ S.Excuse r ∧ ((S.pt r).faultyAt 0).Nonempty ∧
      ((S.pt r).honestAt 0).Nonempty := by
  simp only [Witness, hc, true_and]

theorem outage_constant_iff [Fintype V] [DecidableEq V] {Prog : Type}
    (hc : (S.pt r).ConstantFaults) (K : Contract Prog) (T b₀ b₁ : Time) :
    S.Outage K T b₀ b₁ r ↔
      OutageTimes K.params (S.pt r).env.ΔAC T b₀ b₁ ∧
      (S.log r).OutageNet (S.pt r) b₀ b₁ ∧
      (∀ t, 0 ≤ t → t ≤ (S.pt r).horizon →
        (S.pt r).EtaReadyAbove K.params.θ ((K.params.η : Time) * (S.pt r).env.ΔAC)
          (S.cDur K r) t) ∧
      (S.pt r).NoSleepOn (S.outageStart K b₀ r) (S.outageEnd K b₁ r) ∧
      (S.pt r).CohortOn (S.outageStart K b₀ r) (S.outageEnd K b₁ r) := by
  simp only [Outage, EnvPoint.retain_eq hc, EnvPoint.etaSleepyOn_iff hc]

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

/-- Constant-fault non-framing is the original whole-run honest-evidence statement. -/
theorem nonFraming_constant_iff
    (hS : S.Laws) (hr : S.Valid r) (hc : (S.trace r).point.ConstantFaults) :
    S.NonFraming r ↔ ∀ v, (S.trace r).point.HonestAt v 0 →
      ¬ S.convicts r
        {o | ∃ w, (S.trace r).point.HonestAt w 0 ∧ o ∈ S.view r w (S.trace r).cuts} v := by
  constructor
  · intro h v hv
    have hh := h v (S.trace r).point.horizon ((EnvPoint.honestAt_iff_zero hc _ _).mpr hv)
    rwa [honestEvidenceBy_eq hS hr hc le_rfl] at hh
  · intro h v d hv hconv
    apply h v ((EnvPoint.honestAt_iff_zero hc _ _).mp hv)
    apply hS.convicts_mono r _ _ v _ hconv
    rintro o ⟨w, i, hi, _, hw, ho⟩
    exact ⟨w, (EnvPoint.honestAt_iff_zero hc _ _).mp hw, hS.view_mono r w i _ hi ho⟩

end Consensus.System

end

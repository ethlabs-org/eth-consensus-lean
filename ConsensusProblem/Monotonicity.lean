module
public import ConsensusProblem.Claims
@[expose] public section
namespace Consensus

/-- `A` admits at least the environments admitted by `A'`. Accountability
fractions run in the opposite direction: a larger fraction is a stronger
conclusion. Catch-up is equal because it also selects the readers. -/
structure Assumptions.Weaker (A A' : Assumptions) : Prop where
  catchUp : A.catchUp = A'.catchUp
  sleepy : A.sleepyReadyAbove ≤ A'.sleepyReadyAbove
  stable : A.stableEtaAbove ≤ A'.stableEtaAbove
  eta : A.eta ≤ A'.eta
  fast : A'.fastFaultsBelow ≤ A.fastFaultsBelow
  lag : A.armingLag ≤ A'.armingLag
  fastLag : A.fastArmingLag ≤ A'.fastArmingLag
  budget : A'.outageBudget ≤ A.outageBudget
  outage : A.fastOutageReadyAtLeast ≤ A'.fastOutageReadyAtLeast
  recovery : A.recovery.readyAbove ≤ A'.recovery.readyAbove
  full : A.recovery.requireFull = true → A'.recovery.requireFull = true
  noWake : A.recovery.noWakeAfterGST = true → A'.recovery.noWakeAfterGST = true
  finality : A.finalityReadyOfAll ≤ A'.finalityReadyOfAll
  accountable : A'.accFrac ≤ A.accFrac

namespace EnvPoint
variable {V : Type} [Fintype V] [DecidableEq V] (p : EnvPoint V)

theorem ReadyAbove.mono {θ θ' : ℚ} {c t : Time} (h : p.ReadyAbove θ' c t)
    (hle : θ ≤ θ') : p.ReadyAbove θ c t :=
  lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle (by positivity)) h

theorem FaultsBelow.mono {β β' : ℚ} (h : p.FaultsBelow β') (hle : β' ≤ β) : p.FaultsBelow β :=
  lt_of_lt_of_le h (mul_le_mul_of_nonneg_right hle (by positivity))

theorem ReadyOfAll.mono {φ φ' : ℚ} {c t : Time} (h : p.ReadyOfAll φ' c t)
    (hle : φ ≤ φ') : p.ReadyOfAll φ c t :=
  lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle (by positivity)) h

theorem ReadyOfAllAtLeast.mono {φ φ' : ℚ} {c t : Time} (h : p.ReadyOfAllAtLeast φ' c t)
    (hle : φ ≤ φ') : p.ReadyOfAllAtLeast φ c t :=
  le_trans (mul_le_mul_of_nonneg_right hle (by positivity)) h

theorem EtaSleepy.mono {θ θ' : ℚ} {η η' c t : Time} (h : p.EtaSleepy θ' η' c t)
    (h0 : 0 ≤ θ) (hθ : θ ≤ θ') (hη : η ≤ η') : p.EtaSleepy θ η c t := by
  classical
  have hsub : p.awakeIn (t - η) t ∪ p.faulty ⊆ p.awakeIn (t - η') t ∪ p.faulty := by
    apply Finset.union_subset_union _ (Finset.Subset.refl _)
    intro v hv
    obtain ⟨hv, u, ha, hb, hw⟩ := Finset.mem_filter.mp hv
    apply Finset.mem_filter.mpr
    exact ⟨hv, u, by dsimp only [Time] at *; omega, hb, hw⟩
  have hc : ((p.awakeIn (t - η) t ∪ p.faulty).card : ℚ) ≤
      (p.awakeIn (t - η') t ∪ p.faulty).card := by exact_mod_cast Finset.card_le_card hsub
  exact lt_of_le_of_lt
    ((mul_le_mul_of_nonneg_left hc h0).trans
      (mul_le_mul_of_nonneg_right hθ (by positivity))) h
end EnvPoint

namespace System
variable {V : Type} [Fintype V] [DecidableEq V]

theorem EnvAssumption.mono {A A' : Assumptions} (hA : A.WellFormed)
    (h : A.Weaker A') (B : Bounds) (q : ClaimKey) (p : EnvPoint V)
    (he : EnvAssumption A' B q p) : EnvAssumption A B q p := by
  have heta := mul_le_mul_of_nonneg_right (Int.ofNat_le.mpr h.eta) p.env.Δ_pos.le
  have sleepy (hg : p.env.gst = 0)
      (hp : EnvPoint.Throughout 0 p.horizon (p.ReadyAbove A'.sleepyReadyAbove
        ((A'.catchUp : Time) * p.env.Δ))) :
      EnvAssumption A B .sleepy p := by
    refine ⟨hg, ?_⟩
    intro t ht hh
    rw [h.catchUp]
    exact (hp t ht hh).mono p h.sleepy
  have eta (t : Time) (he : p.EtaSleepy A'.stableEtaAbove ((A'.eta : Time) * p.env.Δ) ((A'.catchUp : Time) * p.env.Δ) t) :
      p.EtaSleepy A.stableEtaAbove ((A.eta : Time) * p.env.Δ) ((A.catchUp : Time) * p.env.Δ) t := by
    rw [h.catchUp]
    exact he.mono p hA.stable_lower h.stable heta
  have recovery (k : Nat) (he : EnvAssumption A' B (.recovery k) p) :
      EnvAssumption A B (.recovery k) p := by
    refine ⟨?_, fun hf => he.2.1 (h.full hf), fun hn => he.2.2.1 (h.noWake hn), he.2.2.2⟩
    intro t ht hh
    rw [h.catchUp]
    exact (he.1 t ht hh).mono p h.recovery
  have outage (l l' : Nat) (hl : l ≤ l') (T b₀ b₁ : Time)
      (he : (0 ≤ T ∧ T ≤ b₀ ∧ b₀ ≤ b₁ ∧ b₁ ≤ p.horizon) ∧
        T + (l' : Time) * p.env.Δ ≤ b₀ ∧
        b₁ - b₀ ≤ (A'.outageBudget : Time) * p.env.Δ ∧
        (∀ t, 0 ≤ t → t < b₀ → p.ReadyAbove A'.sleepyReadyAbove ((A'.catchUp : Time) * p.env.Δ) t) ∧
        (∀ t, 0 ≤ t → t < b₀ → p.EtaSleepy A'.stableEtaAbove ((A'.eta : Time) * p.env.Δ) ((A'.catchUp : Time) * p.env.Δ) t)) :
      (0 ≤ T ∧ T ≤ b₀ ∧ b₀ ≤ b₁ ∧ b₁ ≤ p.horizon) ∧
        T + (l : Time) * p.env.Δ ≤ b₀ ∧
        b₁ - b₀ ≤ (A.outageBudget : Time) * p.env.Δ ∧
        (∀ t, 0 ≤ t → t < b₀ → p.ReadyAbove A.sleepyReadyAbove ((A.catchUp : Time) * p.env.Δ) t) ∧
        (∀ t, 0 ≤ t → t < b₀ → p.EtaSleepy A.stableEtaAbove ((A.eta : Time) * p.env.Δ) ((A.catchUp : Time) * p.env.Δ) t) := by
    refine ⟨he.1, ?_, ?_, ?_, fun t ht hh => eta t (he.2.2.2.2 t ht hh)⟩
    · exact (add_le_add_right
        (mul_le_mul_of_nonneg_right (Int.ofNat_le.mpr hl) p.env.Δ_pos.le) T).trans he.2.1
    · exact he.2.2.1.trans
        (mul_le_mul_of_nonneg_right (Int.ofNat_le.mpr h.budget) p.env.Δ_pos.le)
    · intro t ht hh
      rw [h.catchUp]
      exact (he.2.2.2.1 t ht hh).mono p h.sleepy
  cases q with
  | sleepy | live k => exact sleepy he.1 he.2
  | stableInclusion => exact ⟨sleepy he.1.1 he.1.2, fun t ht hh => eta t (he.2 t ht hh)⟩
  | fastInclusion => exact ⟨sleepy he.1.1 he.1.2, he.2.1, he.2.2.mono p h.fast⟩
  | outage T b₀ b₁ => exact outage _ _ h.lag T b₀ b₁ he
  | fastOutage T b₀ b₁ =>
    refine ⟨outage _ _ h.fastLag T b₀ b₁ he.1, ?_⟩
    intro t ht hh
    rw [h.catchUp]
    exact (he.2 t ht hh).mono p h.outage
  | recovery k => exact recovery k he
  | finality k =>
    refine ⟨recovery k he.1, ?_⟩
    intro t ht hh
    rw [h.catchUp]
    exact (he.2 t ht hh).mono p h.finality

/-- Restricting the admitted environments preserves all claims. The
interpretation of recurrence changes only with catch-up, which is equal. -/
theorem ProblemClaims.mono {S : System V} {A A' : Assumptions} {B : Bounds}
    {X : ExecProfile S} (hc : ProblemClaims S A B X) (hA : A.WellFormed)
    (h : A.Weaker A') : ProblemClaims S A' B X := by
  have premise (q : ClaimKey) (r : S.Run) (hp : S.Premise A' B X q r) :
      S.Premise A B X q r := ⟨EnvAssumption.mono hA h B q _ hp.1, hp.2⟩
  have slashed (r : S.Run) (hs : S.Slashed A.accFrac r) : S.Slashed A'.accFrac r :=
    le_trans (mul_le_mul_of_nonneg_left h.accountable (by positivity)) hs
  have acc (r : S.Run) (ha : S.AccountablySafe r A.accFrac .finalized 0) :
      S.AccountablySafe r A'.accFrac .finalized 0 := by
    intro u hu v hv i j hi hj
    exact (ha u hu v hv i j hi hj).imp id
      (le_trans (mul_le_mul_of_nonneg_left h.accountable (by positivity)))
  refine ⟨hc.laws, hc.nested, hc.finalizedMonotone, hc.nonFraming, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hv ht
    exact (hc.finalizedAccountable r hv ht).imp (acc r) (Or.imp id (slashed r))
  · intro r hv hp; exact hc.confirmedSafe r hv (premise _ _ hp)
  · intro r hv hp; exact hc.stableSafe r hv (premise _ _ hp)
  · intro k r hv hp
    simpa only [h.catchUp] using hc.confirmedLive k r hv (premise _ _ hp)
  · intro k r hv hp
    simpa only [h.catchUp] using hc.stableLive k r hv (premise _ _ hp)
  · intro T b₀ b₁ r hv hp
    simpa only [h.catchUp] using hc.stablePersists T b₀ b₁ r hv (premise _ _ hp)
  · intro T b₀ b₁ r hv hp
    simpa only [h.catchUp] using hc.stablePersistsFast T b₀ b₁ r hv (premise _ _ hp)
  · intro k r hv hp
    have hh := (hc.recovered k r hv (premise _ _ hp)).imp id (Or.imp id (slashed r))
    simpa only [h.catchUp] using hh
  · intro k r hv hp
    simpa only [h.catchUp] using hc.finalizedLive k r hv (premise _ _ hp)
end System
end Consensus
end

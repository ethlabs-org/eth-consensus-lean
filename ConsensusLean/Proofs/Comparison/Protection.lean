module
public import ConsensusLean.Comparison.Protection
public import ConsensusLean.Lemmas.Problem.Facts.Outage
import Mathlib.Tactic.Linarith

public section

/-! # Comparison, Slice 2: the order lemma and the protection default (proofs)

* `protClass_mono` (`ProtClassMono`): the order of `ProtQ` implies inclusion of the protection
  classes. The budget and the fault cap are immediate; the η-sleepy premise weakens at a smaller
  threshold, look-back, catch-up and look-ahead (`EnvPoint.EtaSleepyOn.weaken`, with the smaller
  threshold nonnegative); the cohort point depends only on `noSleep + cohortAhead`
  (`protCohortAt_eq`), which the order fixes, so `NoSleepOn` and `CohortOn` pass from the wider
  no-sleep window to the narrower one on the same retained view, and the cohort only grows
  (`EnvPoint.NoSleepOn.awakeAt_sub`).
* `persistsPoint_of_le`, `protLagDefault_mono`, `protRecDefault_mono`: the default region is
  downward closed in the order, so the defaults are monotone.
* `outage_of_protClass`: at a `PersistsPoint`, the class with the arming premise
  `T + lag·ΔAC ≤ b₀` is in the contract's `Outage K T b₀ b₁` (the same window argument, at the
  contract's numbers; the threshold is nonnegative by `Params.Admissible`).
* `protectionDefault` (`ProtectionDefault`): `Behaviour.persists` at that outage, with the readers
  of the point's catch-up among the contract's (`Trace.ProtectedReadyUpTo.catchUp_mono`). -/

namespace Consensus.Comparison

variable {V : Type} [Fintype V] [DecidableEq V] (S : System V)

/-- The no-sleep windows of a wider margin `u ≥ u' ≥ 0` contain those of the narrower one, and the
narrower window's start is the wider one's or lies within the wider window. -/
theorem window_sub {b₀ b₁ h u u' : Time} (hb : b₀ ≤ b₁) (hu' : 0 ≤ u') (hu : u' ≤ u) :
    min (max 0 (b₀ - u)) h ≤ min (max 0 (b₀ - u')) h ∧ min (b₁ + u') h ≤ min (b₁ + u) h ∧
      (min (max 0 (b₀ - u)) h = min (max 0 (b₀ - u')) h ∨
        min (max 0 (b₀ - u')) h ≤ min (b₁ + u) h) := by
  dsimp only [Time] at *
  omega

omit [Fintype V] [DecidableEq V] in
/-- The cohort point depends only on the retention offset `noSleep + cohortAhead`. -/
theorem protCohortAt_eq (q : ProtQ) (b₁ : Time) (r : S.Run) :
    protCohortAt S q b₁ r =
      min (b₁ + ((q.noSleep + q.cohortAhead : ℕ) : Time) * (S.pt r).env.ΔAC) (S.pt r).horizon := by
  unfold protCohortAt protEnd
  have h0 : 0 ≤ (q.cohortAhead : Time) * (S.pt r).env.ΔAC :=
    mul_nonneg (by positivity) (S.pt r).env.ΔAC_pos.le
  push_cast
  rw [add_mul]
  generalize (S.pt r).env.ΔAC = Δ at *
  dsimp only [Time] at *
  omega

omit [Fintype V] [DecidableEq V] in
/-- The contract's cohort point, in the same form. -/
theorem cohortAt_eq {Prog : Type} (K : Contract Prog) (b₁ : Time) (r : S.Run) :
    S.cohortAt K b₁ r = min (b₁ + ((K.params.noSleep + K.params.cohortAhead : ℕ) : Time) *
      (S.pt r).env.ΔAC) (S.pt r).horizon := by
  unfold System.cohortAt System.outageEnd
  have h0 : 0 ≤ (K.params.cohortAhead : Time) * (S.pt r).env.ΔAC :=
    mul_nonneg (by positivity) (S.pt r).env.ΔAC_pos.le
  push_cast
  rw [add_mul]
  generalize (S.pt r).env.ΔAC = Δ at *
  dsimp only [Time] at *
  omega

private theorem natMul_le {m m' : ℕ} (h : m' ≤ m) (Δ : Time) (hΔ : 0 ≤ Δ) :
    (m' : Time) * Δ ≤ (m : Time) * Δ :=
  mul_le_mul_of_nonneg_right (by exact_mod_cast h) hΔ

private theorem natMul_nonneg (m : ℕ) {Δ : Time} (hΔ : 0 ≤ Δ) : 0 ≤ (m : Time) * Δ :=
  mul_nonneg (by positivity) hΔ

theorem protClass_mono : ProtClassMono := by
  intro V _ _ S q q' T b₀ b₁ r hle hθ0 hcl
  obtain ⟨hT, hb, hβ, hnet, hsl, hns, hco, hA, hfc⟩ := hcl
  obtain ⟨hβle, hAle, hfle, -, hηle, hahle, hnsle, hsum, hθle, hcule⟩ := hle
  have hΔ := (S.pt r).env.ΔAC_pos.le
  have hd : protCohortAt S q' b₁ r = protCohortAt S q b₁ r := by
    rw [protCohortAt_eq, protCohortAt_eq, hsum]
  obtain ⟨ha, hz, haz⟩ := window_sub (h := (S.pt r).horizon) hb (natMul_nonneg q'.noSleep hΔ)
    (natMul_le hnsle _ hΔ)
  have hsub := EnvPoint.NoSleepOn.awakeAt_sub _ hns ha haz
  refine ⟨hT, hb, hβ.trans (by linarith [natMul_le hβle _ hΔ]), hnet,
    hsl.weaken _ le_rfl hθle hθ0 (natMul_le hηle _ hΔ) (natMul_le hcule _ hΔ)
      (natMul_nonneg _ hΔ) (natMul_le hahle _ hΔ), ?_, ?_, ?_, hfc.trans hfle⟩
  · rw [hd]
    exact EnvPoint.NoSleepOn.retain_sub _ hns ha hz
  · rw [hd]
    exact EnvPoint.CohortOn.retain_sub _ hns hco ha hz haz
  · unfold cohort
    rw [hd]
    exact hAle.trans (hA.trans (Finset.card_le_card hsub))

variable {Prog : Type}

/-- The default region is downward closed in the order. -/
theorem persistsPoint_of_le {K : Contract Prog} {q q' : ProtQ} (h : q ≤ q')
    (hp : PersistsPoint K q') : PersistsPoint K q := by
  obtain ⟨hβ, -, -, hsrc, hη, ha, hns, hsum, hθ, hc⟩ := h
  obtain ⟨hs', hβ', hη', ha', hns', hsum', hθ', hc'⟩ := hp
  exact ⟨hsrc.trans hs', by omega, by omega, by omega, by omega, by omega, hθ'.trans hθ,
    by omega⟩

private theorem ite_mono_top {p p' : Prop} [Decidable p] [Decidable p'] (h : p' → p)
    (x : WithTop ℕ) : (if p then x else ⊤) ≤ (if p' then x else ⊤) := by
  by_cases h' : p'
  · simp [h', h h']
  · simp [h']

theorem protLagDefault_mono (K : Contract Prog) : AdverseMonotone (protLagDefault K) :=
  fun _ _ h => ite_mono_top (persistsPoint_of_le h) _

theorem protRecDefault_mono (K : Contract Prog) : AdverseMonotone (protRecDefault K) :=
  fun _ _ h => ite_mono_top (persistsPoint_of_le h) _

private theorem eq_of_ite_coe {p : Prop} [Decidable p] {a c : ℕ}
    (h : (if p then (a : WithTop ℕ) else ⊤) = c) : p ∧ c = a := by
  by_cases hp : p
  · simp only [hp, ite_true] at h; exact ⟨hp, (WithTop.coe_injective h).symm⟩
  · simp only [hp, ite_false] at h; exact absurd h WithTop.top_ne_coe

/-- At a `PersistsPoint` of an admissible contract, the class armed with the contract's lag is in
the contract's outage regime. -/
theorem outage_of_protClass (K : Contract Prog) (hK : K.params.Admissible) {q : ProtQ}
    (hp : PersistsPoint K q) {T b₀ b₁ : Time} {r : S.Run} (hcl : ProtClass S q T b₀ b₁ r)
    (harm : T + (K.params.lag : Time) * (S.pt r).env.ΔAC ≤ b₀) : S.Outage K T b₀ b₁ r := by
  obtain ⟨-, hβle, hηle, hahle, hnsle, hsum, hθle, hcule⟩ := hp
  obtain ⟨hT, hb, hβ, hnet, hsl, hns, hco, -, -⟩ := hcl
  have hΔ := (S.pt r).env.ΔAC_pos.le
  have hd : S.cohortAt K b₁ r = protCohortAt S q b₁ r := by
    rw [cohortAt_eq, protCohortAt_eq, hsum]
  obtain ⟨ha, hz, haz⟩ := window_sub (h := (S.pt r).horizon) hb
    (natMul_nonneg K.params.noSleep hΔ) (natMul_le hnsle _ hΔ)
  refine ⟨⟨hT, harm, hb, hβ.trans (by linarith [natMul_le hβle _ hΔ])⟩, hnet,
    hsl.weaken _ le_rfl hθle hK.θ_range.1 (natMul_le hηle _ hΔ) (natMul_le hcule _ hΔ)
      (natMul_nonneg _ hΔ) (natMul_le hahle _ hΔ), ?_, ?_⟩
  · rw [hd]
    exact EnvPoint.NoSleepOn.retain_sub _ hns ha hz
  · rw [hd]
    exact EnvPoint.CohortOn.retain_sub _ hns hco ha hz haz

theorem protectionDefault : ProtectionDefault := by
  intro V _ _ Prog S X K hB
  refine ⟨⟨protLagDefault_mono K, protRecDefault_mono K⟩, ?_⟩
  intro q c d hc hd g hg T b₀ b₁ r hv ⟨hcl, harm⟩
  obtain ⟨hp, rfl⟩ := eq_of_ite_coe hc
  obtain ⟨-, rfl⟩ := eq_of_ite_coe hd
  have hsrc : q.src.cap = .stable := by rw [hp.1]; rfl
  rw [hsrc] at hg
  rcases hB.persists g hg T b₀ b₁ r hv (outage_of_protClass S K hB.admissible hp hcl harm) with
    h | h
  · exact Or.inl (Trace.ProtectedReadyUpTo.catchUp_mono _ h
      (natMul_le hp.2.2.2.2.2.2.2 _ (S.pt r).env.ΔAC_pos.le))
  · exact Or.inr h

end Consensus.Comparison

end

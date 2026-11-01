module
public import AvailableChainFramework.Claim

@[expose] public section

namespace AvailableChain.Framework

variable {K : ClaimDomain}

namespace ClaimSpec

/-- `k` is strictly stronger than `k'`. -/
def stronger (c : ClaimSpec K) (k k' : c.Const) : Bool :=
  c.le k k' && !c.le k' k

/-- The constants that no constant in the list beats (the strongest ones). -/
def pareto (c : ClaimSpec K) (ks : List c.Const) : List c.Const :=
  ks.filter (fun k => !ks.any (fun k' => c.stronger k' k))

theorem pareto_sub (c : ClaimSpec K) (ks : List c.Const) :
    ∀ k ∈ c.pareto ks, k ∈ ks := fun _ hk => (List.mem_filter.mp hk).1

/-- No constant is strictly stronger than itself. -/
theorem stronger_irrefl (c : ClaimSpec K) (k : c.Const) : c.stronger k k = false := by
  simp [stronger, c.le_refl]

/-- Strictly stronger is transitive. -/
theorem stronger_trans (c : ClaimSpec K) {a b d : c.Const}
    (hab : c.stronger a b = true) (hbd : c.stronger b d = true) :
    c.stronger a d = true := by
  simp only [stronger, Bool.and_eq_true, Bool.not_eq_true'] at hab hbd ⊢
  refine ⟨c.le_trans _ _ _ hab.1 hbd.1, ?_⟩
  cases h : c.le d a
  · rfl
  · have := c.le_trans _ _ _ h hab.1
    rw [hbd.2] at this
    exact absurd this (by decide)

/-- A strictly stronger constant in the list has fewer constants in the list
that are strictly stronger than it. -/
theorem stronger_count_lt (c : ClaimSpec K) (ks : List c.Const) {k k₁ : c.Const}
    (hk₁ : k₁ ∈ ks) (h : c.stronger k₁ k = true) :
    (ks.filter (fun k' => c.stronger k' k₁)).length <
      (ks.filter (fun k' => c.stronger k' k)).length := by
  have hsub : ks.filter (fun k' => c.stronger k' k₁) =
      (ks.filter (fun k' => c.stronger k' k)).filter (fun k' => c.stronger k' k₁) := by
    rw [List.filter_filter]
    refine List.filter_congr (fun x _ => ?_)
    cases hx : c.stronger x k₁
    · rfl
    · simp [stronger_trans c hx h]
  rw [hsub, List.length_filter_lt_length_iff_exists]
  exact ⟨k₁, List.mem_filter.mpr ⟨hk₁, h⟩, by simp [stronger_irrefl]⟩

/-- Every listed constant is at least as weak as some Pareto constant. -/
theorem pareto_covers (c : ClaimSpec K) (ks : List c.Const) :
    ∀ k ∈ ks, ∃ k' ∈ c.pareto ks, c.le k' k = true := by
  suffices hn : ∀ n, ∀ k ∈ ks, (ks.filter (fun k' => c.stronger k' k)).length = n →
      ∃ k' ∈ c.pareto ks, c.le k' k = true from
    fun k hk => hn _ k hk rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k hk hn
    cases hany : ks.any (fun k' => c.stronger k' k)
    · exact ⟨k, List.mem_filter.mpr ⟨hk, by simp [hany]⟩, c.le_refl k⟩
    · obtain ⟨k₁, hk₁, h₁⟩ := List.any_eq_true.mp hany
      have hlt := stronger_count_lt c ks hk₁ h₁
      obtain ⟨k', hk', hle⟩ := ih _ (hn ▸ hlt) k₁ hk₁ rfl
      have hle₁ : c.le k₁ k = true := by
        simp only [stronger, Bool.and_eq_true] at h₁
        exact h₁.1
      exact ⟨k', hk', c.le_trans _ _ _ hle hle₁⟩

end ClaimSpec

end AvailableChain.Framework

end

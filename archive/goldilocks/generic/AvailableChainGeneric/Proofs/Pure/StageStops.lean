module
public import AvailableChainGeneric.Statements.Pure.StageStops
public import AvailableChainGeneric.Proofs.Pure.Stages
public import Mathlib.Data.List.FinRange -- shake: keep (re-export)

public section

namespace AvailableChain.Gen.Pure

/-- Ordered stage suppliers give a bounded tagged stop or terminal state.
Consumers: F5.H.10, HG.3, HG.5, HG.8a, H.11 and H.11-Q.
Sources: S1b:389–437; 21:1324–1328,1474–1523,2253–2256,2429–2439.
DC: additive (no DC counterpart); reason: ordered stages and tagged stop suppliers are inputs. -/
theorem stage_or_stop : StageOrStopStatement := by
  rw [StageOrStopStatement_def]
  intro α _ n timeOf clock f stage stop htime _hclock hmono hext
    _hpersist hstep e₀ x₀ hs ht
  have hsuffix : ∀ (k : Nat), k ≤ n → ∀ (e : Nat) (x : α),
      stage k e x → timeOf e ≤ clock x →
      ∃ e' y, e ≤ e' ∧ timeOf e' ≤ clock y ∧
        y ≤ ((List.finRange n).drop k).foldl (fun y i => f i y) x ∧
        ((∃ c : Fin 3, stop c e') ∨ stage n e' y) := by
    intro k hk e x hs ht
    induction hrem : n - k using Nat.strong_induction_on generalizing k e x with
    | h m ih =>
      by_cases hkn : k = n
      · subst k
        refine ⟨e, x, le_refl e, ht, ?_, Or.inr hs⟩
        have hnil : (List.finRange n).drop n = [] :=
          List.drop_eq_nil_of_le (by simp only [List.length_finRange, le_refl])
        rw [hnil, List.foldl_nil]
      · have hlt : k < n := by omega
        let i : Fin n := ⟨k, hlt⟩
        have hdrop : (List.finRange n).drop k =
            i :: (List.finRange n).drop (k + 1) := by
          have hlen : k < (List.finRange n).length := by
            simpa only [List.length_finRange] using hlt
          have hget : (List.finRange n)[k]'hlen = i :=
            (List.getElem_finRange hlen).trans (by rfl)
          rw [List.drop_eq_getElem_cons hlen, hget]
        obtain ⟨e', y, he, hty, hy, hnext⟩ := hstep i e x hs ht
        rcases hnext with hstop | ⟨j, hjk, hjn, hstage⟩
        · refine ⟨e', y, he, hty, ?_, Or.inl hstop⟩
          rw [hdrop, List.foldl_cons]
          exact foldl_le_of_sublist f hmono hext []
            ((List.finRange n).drop (k + 1)) (List.nil_sublist _) y (f i x) hy
        · obtain ⟨e'', z, he', htz, hz, hend⟩ :=
            ih (n - j) (by dsimp [i] at hjk; omega) j hjn e' y hstage hty rfl
          refine ⟨e'', z, he.trans he', htz, ?_, hend⟩
          rw [hdrop, List.foldl_cons]
          exact hz.trans (foldl_le_of_sublist f hmono hext
            ((List.finRange n).drop j) ((List.finRange n).drop (k + 1))
            (List.drop_sublist_drop_left _ (by dsimp [i] at hjk; omega)) y (f i x) hy)
  obtain ⟨e, x, he, htx, hx, hend⟩ :=
    hsuffix 0
      (Nat.zero_le n) e₀ x₀ hs ht
  exact ⟨e, x, he, htime he, htx, by simpa using hx, hend⟩

end AvailableChain.Gen.Pure

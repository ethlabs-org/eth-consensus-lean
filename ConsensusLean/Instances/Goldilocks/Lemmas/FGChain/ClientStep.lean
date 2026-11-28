module
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Client

/-! # One validator client step

The compact record tracks distinct signed entries. Timeouts at a height follow a target
at that height and never name that target. -/

namespace Consensus.Goldilocks.FG.Record

public section

/-- A timeout at a height follows a target and names a different entry. -/
def TimeoutAfterTarget (Λ : Record) : Prop :=
  ∀ h, Λ.timeout h ≠ ∅ → ∃ T, Λ.target h = some T ∧ T ∉ Λ.timeout h

theorem timeoutAfterTarget_iff {Λ : Record} : TimeoutAfterTarget Λ ↔
    ∀ h, Λ.timeout h ≠ ∅ → ∃ T, Λ.target h = some T ∧ T ∉ Λ.timeout h := by rfl

theorem timeoutAfterTarget_empty : TimeoutAfterTarget empty :=
  timeoutAfterTarget_iff.2 (by simp [empty])

/-- The height pair names its input, is not locked elsewhere, and does not repeat an entry. -/
theorem heightPair_some {Λ : Record} {h T j R : Nat} {τ : Bool}
    (hp : Λ.heightPair h T = some (j, R, τ)) :
    j = h ∧ R = T ∧ (Λ.lock h = none ∨ Λ.lock h = some T) ∧
    Λ.target h ≠ some T ∧ T ∉ Λ.timeout h ∧ (τ = false ↔ Λ.target h = none) := by
  unfold heightPair at hp
  split_ifs at hp <;> cases hp <;> simp_all <;> tauto

/-- A refusal is either a conflicting lock or a repeated entry. -/
theorem createAtt_eq_none {n : Nat} {Λ : Record} {v : Fin n} {σ : ChainState n} :
    Λ.createAtt v σ = none ↔ (Λ.lock σ.h ≠ none ∧ Λ.lock σ.h ≠ some σ.Th) ∨
      Λ.target σ.h = some σ.Th ∨ σ.Th ∈ Λ.timeout σ.h := by
  unfold createAtt heightPair
  split_ifs <;> simp_all

/-- A successful signing names the input's entry and updates the record exactly once. -/
theorem createAtt_some {n : Nat} {Λ Λ' : Record} {v : Fin n} {σ : ChainState n} {a : Att n}
    (ha : Λ.createAtt v σ = some (a, Λ')) :
    a.val = v ∧ Λ' = Λ.recordAtt a ∧ a.h = σ.h ∧ a.T = σ.Th ∧
    a.fin = Λ.finalityPair σ ∧ (Λ.lock a.h = none ∨ Λ.lock a.h = some a.T) ∧
    Λ.target a.h ≠ some a.T ∧ a.T ∉ Λ.timeout a.h ∧
    (a.timeout = false ↔ Λ.target a.h = none) := by
  unfold createAtt at ha
  rcases hp : Λ.heightPair σ.h σ.Th with _ | ⟨j, R, τ⟩ <;> rw [hp] at ha
  · cases ha
  cases ha
  obtain ⟨rfl, rfl, hl, ht, hm, hf⟩ := heightPair_some hp
  exact ⟨rfl, rfl, rfl, rfl, rfl, hl, ht, hm, hf⟩

/-- An entry is recorded after writing iff it was already recorded or is being written now. -/
theorem recordAtt_entry_iff {n : Nat} {Λ : Record} {a : Att n} {h T : Nat}
    (ht : a.timeout = false → Λ.target a.h = none) :
    ((Λ.recordAtt a).target h = some T ∨ T ∈ (Λ.recordAtt a).timeout h) ↔
      (Λ.target h = some T ∨ T ∈ Λ.timeout h) ∨ (a.h = h ∧ a.T = T) := by
  by_cases hh : h = a.h
  · subst h
    cases hτ : a.timeout
    · have hnone := ht hτ
      simp [recordAtt, hτ, hnone, eq_comm, or_comm]
    · simp [recordAtt, hτ, eq_comm]
      tauto
  · simp only [recordAtt, ite_apply, Function.update_of_ne hh, ite_self, Ne.symm hh,
      false_and, or_false]

theorem timeoutAfterTarget_createAtt {n : Nat} {Λ Λ' : Record} {v : Fin n} {σ : ChainState n}
    {a : Att n} (hinv : Λ.TimeoutAfterTarget) (ha : Λ.createAtt v σ = some (a, Λ')) :
    Λ'.TimeoutAfterTarget := by
  obtain ⟨-, rfl, -, -, -, -, hne, -, ht⟩ := createAtt_some ha
  apply timeoutAfterTarget_iff.2
  intro h
  by_cases hh : h = a.h
  · subst h
    cases hτ : a.timeout
    · have hnone := ht.mp hτ
      have he : Λ.timeout a.h = ∅ := by
        by_contra h
        obtain ⟨T, hT, -⟩ := timeoutAfterTarget_iff.1 hinv _ h
        simp [hnone] at hT
      simp [recordAtt, hτ, he]
    · have hn : Λ.target a.h ≠ none := by
        intro h
        simp [hτ] at ht
        exact ht h
      obtain ⟨T, hT⟩ := Option.ne_none_iff_exists'.1 hn
      have hTa : T ≠ a.T := fun e => hne (e ▸ hT)
      have hm : T ∉ Λ.timeout a.h := by
        intro h
        obtain ⟨R, hR, hnR⟩ := timeoutAfterTarget_iff.1 hinv _ (Finset.ne_empty_of_mem h)
        exact hnR (Option.some.inj (hT.symm.trans hR) ▸ h)
      simp [recordAtt, hτ, hT, hTa, hm]
  · simpa only [recordAtt, ite_apply, Function.update_of_ne hh, ite_self] using
      timeoutAfterTarget_iff.1 hinv h

end

end Consensus.Goldilocks.FG.Record

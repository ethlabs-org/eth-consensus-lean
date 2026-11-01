module
public import AvailableChainFGCompose.Statements.Promotion
public import AvailableChainFGCompose.Statements.Phase
public import AvailableChainKitFG.Ancestry

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {Prot : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads Prot n Base Proposal Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V Prot)
variable (H : FGHeightView (Fin n)) (T : FGTiming)
variable (Ef : Electorate (Fin n)) (laws : FGHeightLaws Ef H)

include laws in
/-- SAME: a prefix at equal height fixes the entry root of every selected source. -/
theorem common_entry_of_plateau (r m : Nat) (Qfg : FGBlock (Fin n)) (hh : (H Qfg).h = m)
    (hsources : ∀ x K, x ∈ rho.honest → actionSourceFG R E rho T x r = some (some K) →
      FGBlock.Preceq Qfg K ∧ (H K).h ≤ m) : OpeningEntry R E rho H T r m := by
  refine ⟨(H Qfg).T_h.root, ?_⟩
  intro x K hx hK
  obtain ⟨hQK, hcap⟩ := hsources x K hx hK
  have he : (H K).h = m := le_antisymm hcap (hh ▸ laws.h_mono hQK)
  exact ⟨he, by rw [laws.entry_plateau hQK (hh.trans he.symm)]⟩

include laws in
/-- SAME: the low branch or an actual honest source at the cap. -/
theorem common_low_or_high (r m : Nat) (Qfg : FGBlock (Fin n))
    (hh : (H Qfg).h = m - 1)
    (hsources : ∀ x K, x ∈ rho.honest → actionSourceFG R E rho T x r = some (some K) →
      FGBlock.Preceq Qfg K ∧ (H K).h ≤ m) :
    OpeningEntry R E rho H T r (m - 1) ∨
      ∃ x K, x ∈ rho.honest ∧ actionSourceFG R E rho T x r = some (some K) ∧
        (H K).h = m := by
  classical
  by_cases hhigh : ∃ x K, x ∈ rho.honest ∧
      actionSourceFG R E rho T x r = some (some K) ∧ (H K).h = m
  · exact Or.inr hhigh
  · apply Or.inl
    apply common_entry_of_plateau R E rho H T Ef laws r (m - 1) Qfg hh
    intro x K hx hK
    obtain ⟨hQK, hcap⟩ := hsources x K hx hK
    have hne : (H K).h ≠ m := fun he => hhigh ⟨x, K, hx, hK, he⟩
    refine ⟨hQK, ?_⟩
    simp only [Height] at hcap hne ⊢
    omega

/-- SAME: identify the serviced source at the actual read, then apply the phase cap.
Only prefix service is needed. Exact opening service remains in FGSourceService. -/
theorem common_sources_extend_and_cap {r m : Nat} {Qfg : FGBlock (Fin n)}
    (transfer : ∀ x nd, x ∈ rho.honest → postClock E rho x (T.action r) = some nd →
      ∃ L, R.source nd = some L ∧ FGBlock.Preceq Qfg L)
    (cap : ∀ x K, x ∈ rho.honest → actionSourceFG R E rho T x r = some (some K) →
      (H K).h ≤ m) :
    ∀ x K, x ∈ rho.honest → actionSourceFG R E rho T x r = some (some K) →
      FGBlock.Preceq Qfg K ∧ (H K).h ≤ m := by
  intro x K hx hK
  obtain ⟨nd, hnd, hsrc⟩ := Option.map_eq_some_iff.mp hK
  obtain ⟨L, hL, hQL⟩ := transfer x nd hx hnd
  have he : L = K := Option.some.inj (hL.symm.trans hsrc)
  exact ⟨he ▸ hQL, cap x K hx hK⟩

include laws in
/-- SAME: the first-opening source result supplies the plateau consumer. -/
theorem common_entry_at_high {r m : Nat} {Qfg : FGBlock (Fin n)}
    (hsources : ∀ x K, x ∈ rho.honest → actionSourceFG R E rho T x r = some (some K) →
      FGBlock.Preceq Qfg K ∧ (H K).h ≤ m) (hh : (H Qfg).h = m) :
    OpeningEntry R E rho H T r m := by
  exact common_entry_of_plateau R E rho H T Ef laws r m Qfg hh hsources

/-- SAME: transfer through the serviced body, without requiring an honest opening. -/
theorem common_next_sources_extend_and_cap {r m : Nat} {K : FGBlock (Fin n)}
    (transfer : ∀ x nd, x ∈ rho.honest → postClock E rho x (T.action (r + 1)) = some nd →
      ∃ D L, R.source nd = some L ∧ FGBlock.Preceq K D ∧ FGBlock.Preceq D L)
    (cap : ∀ x L, x ∈ rho.honest →
      actionSourceFG R E rho T x (r + 1) = some (some L) → (H L).h ≤ m) :
    ∀ x L, x ∈ rho.honest → actionSourceFG R E rho T x (r + 1) = some (some L) →
      FGBlock.Preceq K L ∧ (H L).h ≤ m := by
  apply common_sources_extend_and_cap R E rho H T (cap := cap)
  intro x nd hx hnd
  obtain ⟨D, L, hL, hKD, hDL⟩ := transfer x nd hx hnd
  exact ⟨L, hL, KitFG.preceq_trans hKD hDL⟩

include laws in
/-- SAME: an actual high source fixes the next entry under its own phase cap. -/
theorem common_next_entry {r m : Nat} {K : FGBlock (Fin n)} (hh : (H K).h = m)
    (hsources : ∀ x L, x ∈ rho.honest →
      actionSourceFG R E rho T x (r + 1) = some (some L) →
      FGBlock.Preceq K L ∧ (H L).h ≤ m) : OpeningEntry R E rho H T (r + 1) m := by
  exact common_entry_of_plateau R E rho H T Ef laws (r + 1) m K hh hsources

include laws in
/-- SAME: the high witness is chosen before applying the next-phase service leaf. -/
theorem common_entry_at_low (O : FGObservationReads R) {u : Time}
    {J : Option (FGBlock (Fin n))} {contested : Bool} {r m : Nat} {Qfg : FGBlock (Fin n)}
    (hh : (H Qfg).h = m - 1)
    (hsources : ∀ x K, x ∈ rho.honest → actionSourceFG R E rho T x r = some (some K) →
      FGBlock.Preceq Qfg K ∧ (H K).h ≤ m)
    (nextSources : ∀ y K, y ∈ rho.honest →
      actionSourceFG R E rho T y r = some (some K) →
      PhaseInterval R E rho O u (T.action (r + 1)) m J contested →
      ∀ x L, x ∈ rho.honest → actionSourceFG R E rho T x (r + 1) = some (some L) →
        FGBlock.Preceq K L ∧ (H L).h ≤ m) :
    OpeningEntry R E rho H T r (m - 1) ∨
      ((∃ x K, x ∈ rho.honest ∧ actionSourceFG R E rho T x r = some (some K) ∧
          (H K).h = m) ∧
        (PhaseInterval R E rho O u (T.action (r + 1)) m J contested →
          OpeningEntry R E rho H T (r + 1) m)) := by
  rcases common_low_or_high R E rho H T Ef laws r m Qfg hh hsources with hlow | hhigh
  · exact Or.inl hlow
  · obtain ⟨x, K, hx, hK, hhK⟩ := hhigh
    refine Or.inr ⟨⟨x, K, hx, hK, hhK⟩, ?_⟩
    intro hphase
    exact common_next_entry R E rho H T Ef laws hhK (nextSources x K hx hK hphase)

end AvailableChain.FGCompose
end

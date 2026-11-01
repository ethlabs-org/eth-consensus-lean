module
public import AvailableChainFGSARun.Model.TestSupport.EmissionFreshness
public import AvailableChainFGSARun.Proofs.Emission -- shake: keep (re-export)
public import AvailableChainFGSARun.Proofs.NamedHistory

public section

namespace AvailableChain.FGSA.Run.EmissionFreshnessTests

open AvailableChain.SimplexFG

private theorem sleep_valid : V2.D.SleepWellFormed env run := by
  refine ⟨by intros; rfl, by intros; rfl, by intros; rfl, ?_⟩
  intro v hv t ht hh hw
  have hf := hw.2
  change true = false at hf
  cases hf

/-- The collision trace satisfies every engine validity condition. -/
theorem valid : V2.D.ExecutionValid env run := by
  refine { toScheduleWellFormed := ?_, toSleepWellFormed := sleep_valid,
           toDeliveryWellFormed := ?_, toUnforgeableSignatures := ?_ }
  · refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩
    · intro e he
      simp at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
    · intro e he
      simp at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
    · intro v t he
      simp at he
      refine ⟨(t / 2).toNat, ?_⟩
      simp; dsimp [Time] at *; omega
    · intro v hv t ⟨k, hk⟩ ht hh ha
      have hv0 : v = 0 := Finset.mem_singleton.mp hv
      subst v
      change t = (k : Time) * 2 at hk
      change t ≤ 18 at hh
      have hkbound : k ≤ 9 := by dsimp [Time] at *; omega
      interval_cases k <;> simp <;> dsimp [Time] at * <;> omega
  · refine ⟨?_, ?_, ?_⟩
    all_goals intro i v o t hi
    all_goals have he := List.mem_of_getElem? hi
    all_goals simp at he
    all_goals obtain ⟨rfl, rfl, rfl⟩ := he
    all_goals have hib := (List.getElem?_eq_some_iff.mp hi).1
    all_goals simp at hib
    all_goals interval_cases i <;> first
      | decide +kernel
      | exact False.elim ((by decide +kernel : ¬ (type_of% hi)) hi)
  · refine ⟨?_, ?_⟩
    · intro v o t hp u hu hh
      obtain ⟨i, hi⟩ := hp
      have he := List.mem_of_getElem? hi
      simp at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      have hu0 : u = 0 := Finset.mem_singleton.mp hu
      subst u
      change some (1 : Fin 2) = some 0 at hh
      cases hh
    · intro v o t hp o' hc u hu hh
      obtain ⟨i, hi⟩ := hp
      have he := List.mem_of_getElem? hi
      simp at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      change o' ∈ [] ∨ o' ∈ [] ∨ o' ∈ [] at hc
      simp at hc

private theorem scope_cases {N : NamedProposal p.n}
    (hN : NamedProposalInRun p unitCodec env run N) :
    N = .genesis ∨ N = namedProposal p .genesis 1 0 [] [] [] := by
  have hparents : ∀ x o t M, V2.Event.deliver x o t ∈ run.events →
      o.payload = .proposal M →
      ∃ i y, M.parent ∈ (run.stateBefore env i y).st.namedBodies := by
    intro x o t M hd ho
    simp at hd
    obtain ⟨rfl, rfl, rfl⟩ := hd
    change Msg.proposal (namedProposal p .genesis 1 0 [] [] []) = Msg.proposal M at ho
    cases Msg.proposal.inj ho
    exact ⟨0, 0, by decide⟩
  rcases namedProposalInRun_genesis_or_delivered env run hparents hN with hg |
    ⟨x, o, t, hd, ho⟩
  · exact Or.inl hg
  · simp at hd
    obtain ⟨rfl, rfl, rfl⟩ := hd
    change Msg.proposal (namedProposal p .genesis 1 0 [] [] []) = Msg.proposal N at ho
    exact Or.inr (Msg.proposal.inj ho).symm

/-- Scoped root injectivity also holds; it does not cover the new emitted body. -/
theorem roots : NamedRootCollisionFree p unitCodec env run := by
  constructor
  intro B C hB hC A D hAB hDC he
  have hA : NamedProposalInRun p unitCodec env run A :=
    hAB.elim (namedScope_ancestor env run hB) (namedScope_ancestor env run hC)
  have hD : NamedProposalInRun p unitCodec env run D :=
    hDC.elim (namedScope_ancestor env run hB) (namedScope_ancestor env run hC)
  rcases scope_cases hA with rfl | rfl
  all_goals rcases scope_cases hD with rfl | rfl
  all_goals first
    | rfl
    | exact False.elim ((by decide : ¬ (type_of% he)) he)

/-- An honest proposal can already be processed before its first emission:
processedS tests only its root, and the older held block has the same root. -/
theorem emitted_proposal_already_processed :
    second ∈ V2.D.Run.emitsAt env run 9 ∧
      P.processed (V2.D.Run.stateBefore env run 9 0) second = true := by
  constructor
  · change second ∈ [second]
    exact List.mem_cons_self
  · decide +kernel

end AvailableChain.FGSA.Run.EmissionFreshnessTests
end

module
public import AvailableChainFGSARun.Proofs.TestSupport.EmissionFreshness -- shake: keep (axioms)
public import AvailableChainFGSARun.Proofs.ReceiptCoverageReady
public import AvailableChainFGSARun.Proofs.Hooks

@[expose] public section

namespace AvailableChain.FGSA.Run.ReceiptReadyTests

open AvailableChain.SimplexFG

abbrev p := EmissionFreshnessTests.p
abbrev P := fgsa p unitCodec
abbrev first := EmissionFreshnessTests.first
abbrev env := EmissionFreshnessTests.env

/-- Stop before the colliding slot-2 emission. The slot-1 delivery is retained. -/
def run : V2.D.Run (Fin 2) P where
  honest := {0}
  horizon := 10
  events := [.tick 0 0, .tick 0 2, .tick 0 4, .tick 0 6, .tick 0 8,
    .deliver 0 first 8, .tick 0 10]
  seatOf := EmissionFreshnessTests.run.seatOf
  input := fun _ _ => ()

abbrev body : NamedProposal p.n := namedProposal p .genesis 1 0 [] [] []
abbrev B := body.erase
abbrev dl (t : Time) := t + 1

def required (o : Obj p) (t : Time) : Prop := o = first ∧ t = 8
def paths (K : Block) (d : Time) : Prop := K = B ∧ d = 9

private theorem no_emission {v : Fin 2} {o : Obj p} {t : Time}
    (h : V2.D.Run.emits env run v o t) : False := by
  obtain ⟨i, hi, ho⟩ := h
  have hb := (List.getElem?_eq_some_iff.mp hi).1
  change i < 7 at hb
  interval_cases i <;> simp [run] at hi
  all_goals obtain ⟨rfl, rfl⟩ := hi
  all_goals change o ∈ [] at ho
  all_goals exact (List.not_mem_nil ho).elim

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
      simp [run] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
    · intro e he
      simp [run] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
    · intro v t he
      simp [run] at he
      refine ⟨(t / 2).toNat, ?_⟩
      simp; dsimp [Time] at *; omega
    · intro v hv t ⟨k, hk⟩ ht hh ha
      have hv0 : v = 0 := Finset.mem_singleton.mp hv
      subst v
      change t = (k : Time) * 2 at hk
      change t ≤ 10 at hh
      have hkbound : k ≤ 5 := by dsimp [Time] at *; omega
      interval_cases k <;> simp [run] <;> dsimp [Time] at * <;> omega
  · refine ⟨?_, ?_, ?_⟩
    all_goals intro i v o t hi
    all_goals have he := List.mem_of_getElem? hi
    all_goals simp [run] at he
    all_goals obtain ⟨rfl, rfl, rfl⟩ := he
    all_goals have hib := (List.getElem?_eq_some_iff.mp hi).1
    all_goals simp [run] at hib
    all_goals interval_cases i <;> first
      | decide +kernel
      | exact False.elim ((by decide +kernel : ¬ (type_of% hi)) hi)
  · refine ⟨?_, ?_⟩
    · intro v o t hp u hu hh
      obtain ⟨i, hi⟩ := hp
      have he := List.mem_of_getElem? hi
      simp [run] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      have hu0 : u = 0 := Finset.mem_singleton.mp hu
      subst u
      change some (1 : Fin 2) = some 0 at hh
      cases hh
    · intro v o t hp o' hc u hu hh
      obtain ⟨i, hi⟩ := hp
      have he := List.mem_of_getElem? hi
      simp [run] at he
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
    simp [run] at hd
    obtain ⟨rfl, rfl, rfl⟩ := hd
    change Msg.proposal (namedProposal p .genesis 1 0 [] [] []) = Msg.proposal M at ho
    cases Msg.proposal.inj ho
    exact ⟨0, 0, by decide⟩
  rcases namedProposalInRun_genesis_or_delivered env run hparents hN with hg |
    ⟨x, o, t, hd, ho⟩
  · exact Or.inl hg
  · simp [run] at hd
    obtain ⟨rfl, rfl, rfl⟩ := hd
    change Msg.proposal (namedProposal p .genesis 1 0 [] [] []) = Msg.proposal N at ho
    exact Or.inr (Msg.proposal.inj ho).symm

/-- The old scope covers only genesis and the delivered proposal. -/
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

private theorem accepted_cases {i : Nat} {v : Fin 2} {o : Obj p} {t : Time}
    (h : V2.D.Run.acceptsAt env run i v o t) : v = 0 ∧ o = first ∧ t = 8 := by
  obtain ⟨parent, he, hc⟩ := h.1
  have hm := List.mem_of_getElem? he
  simp [run] at hm
  obtain ⟨rfl, rfl, rfl⟩ := hm
  rcases (fgsaHooks p unitCodec).handles_carries _ _ _ hc with h | h
  · exact ⟨rfl, h.symm, rfl⟩
  · change o ∈ [] ∨ o ∈ [] ∨ o ∈ [] at h
    simp at h

private theorem demand_first : V2.D.DeliveryDemand env run 0 0 first 8 dl 10 := by
  intro a ha _ _ hc _ _ _
  change a + 1 ≤ 10 at hc
  have hb : a ≤ 9 := by dsimp [Time] at *; omega
  interval_cases a
  all_goals first
    | (right; exact ⟨8, by decide, by decide, 5, first, rfl, Or.inl rfl⟩)
    | (left; exact ⟨6, by decide, by decide +kernel⟩)

/-- The revised per-anchor delivery law permits the root-based history exemption. -/
theorem within : Gen.V2.Duty.DeliveryWithinOn env run (fun o => ¬ isRowObject o) dl 10 := by
  constructor
  · intro v hv o ho t he w hw
    exact (no_emission he).elim
  · intro v hv i o ho t he w hw
    obtain ⟨rfl, rfl, rfl⟩ := accepted_cases he
    have hw0 : w = 0 := Finset.mem_singleton.mp hw
    subst w
    exact demand_first

private theorem prefix_cases (b : Block) (hb : Block.Preceq b B) :
    b = B ∨ b = .genesis := by
  cases b with
  | genesis => exact Or.inr rfl
  | node parent s root inner =>
    left
    change (decide (Block.node parent s root inner = B) ||
      Block.preceq (Block.node parent s root inner) .genesis) = true at hb
    simpa only [Block.preceq, reduceCtorEq, decide_false, Bool.or_false,
      decide_eq_true_eq] using hb

/-- K8 requires the accepted slot-1 proposal and its path at the strict deadline. -/
theorem premises : ReceiptCoveragePremises env run dl 10 9 0 0 B required paths := by
  refine ⟨within, ?_, ?_, ?_⟩
  · intro o t hr
    obtain ⟨rfl, rfl⟩ := hr
    refine ⟨Or.inr ⟨0, by decide, 5, ⟨first, rfl, Or.inl rfl⟩, by decide +kernel⟩,
      by decide, ?_⟩
    intro s a K h
    cases h
  · intro i _ hi
    change i ≤ 6 at hi
    interval_cases i <;> change Block.compatible B _ = true
    all_goals decide +kernel
  · refine ⟨?_, by decide, by decide, by decide, ?_, ?_, ?_⟩
    · intro a b h
      change (a : Time) + 1 ≤ (b : Time) + 1
      dsimp [Time] at *
      omega
    · intro o t hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨by decide, by decide, by decide, by decide⟩
    · intro K d hp
      obtain ⟨rfl, rfl⟩ := hp
      refine ⟨Gen.Pure.block_preceq_refl _, le_refl _, ?_⟩
      intro b hb hg
      rcases prefix_cases b hb with rfl | rfl
      · exact ⟨first, 8, 1, body, rfl, ⟨rfl, rfl⟩, rfl, le_refl _⟩
      · exact (hg rfl).elim
    · intro o t s N hr hd
      obtain ⟨rfl, rfl⟩ := hr
      change some (Input.block 1 body) = some (Input.block s N) at hd
      obtain ⟨rfl, rfl⟩ := Input.block.inj (Option.some.inj hd)
      exact ⟨B, 9, ⟨rfl, rfl⟩, Gen.Pure.block_preceq_refl _⟩

/-- The receiver is awake on every required receipt window. -/
theorem ready : ∀ o t, required o t → ∀ u, t ≤ u → u < dl t → env.awake 0 u = true := by
  intros
  rfl

/-- Receipt collision freedom holds on this valid nonempty trace. -/
theorem receipt_roots : NamedReceiptRootCollisionFree p unitCodec env run := by
  have old (N) (h : NamedProposalReceiptScope p unitCodec env run N) :
      NamedProposalInRun p unitCodec env run N := by
    rcases h with h | ⟨_, _, _, _, _, he, _⟩
    · exact h
    · exact (no_emission he).elim
  intro A C hA hC he
  exact namedProposal_eq env run roots (old A hA) (old C hC) he

/-- The new core supplies the required exact proposal receipt at its deadline. -/
theorem coverage_ready :
    ∃ Y ∈ (V2.D.Run.stateBeforeTime env run 9 0).st.fg.TF, eraseFG Y = B := by
  have hNR : V2.D.NoRestart run := by
    intro i v t hi
    have hm := List.mem_of_getElem? hi
    simp [run] at hm
  have hc := fgsa_receiptCoverage_ready env run dl 10 9 0 0 B required paths
    receipt_roots rfl valid hNR (by decide) ready premises
  rcases hc.1 with hleft | hright
  · exact (by decide +kernel : ¬ Block.Preceq B
      (eraseFG (V2.D.Run.stateBeforeTime env run 9 0).st.fg.F)) hleft.1 |>.elim
  · exact hright.2.1 first 8 1 body ⟨rfl, rfl⟩ rfl

end AvailableChain.FGSA.Run.ReceiptReadyTests
end

#print axioms AvailableChain.FGSA.Run.ReceiptReadyTests.valid
#print axioms AvailableChain.FGSA.Run.ReceiptReadyTests.receipt_roots
#print axioms AvailableChain.FGSA.Run.ReceiptReadyTests.premises
#print axioms AvailableChain.FGSA.Run.ReceiptReadyTests.coverage_ready

#print axioms AvailableChain.FGSA.Run.ReceiptReadyTests.roots
#print axioms AvailableChain.FGSA.Run.ReceiptReadyTests.within
#print axioms AvailableChain.FGSA.Run.ReceiptReadyTests.ready

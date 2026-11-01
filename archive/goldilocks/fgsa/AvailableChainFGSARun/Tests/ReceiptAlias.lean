module
public import AvailableChainFGSARun.Proofs.TestSupport.EmissionFreshness
public import AvailableChainFGSARun.Statements.ReceiptCoverage
public import AvailableChainFGSARun.Proofs.Hooks
public import AvailableChainFGSARun.Proofs.ReadFacts -- shake: keep (axioms)

@[expose] public section

namespace AvailableChain.FGSA.Run.ReceiptAliasTests

open AvailableChain.SimplexFG EmissionFreshnessTests

abbrev body : NamedProposal p.n := namedProposal p .genesis 2 0 [] [] []
abbrev B := body.erase
abbrev dl (t : Time) := t + 1

def required (o : Obj p) (t : Time) : Prop := o = second ∧ t = 16
def paths (K : Block) (d : Time) : Prop := K = B ∧ d = 17

private theorem emitted_cases {v : Fin 2} {o : Obj p} {t : Time}
    (h : V2.D.Run.emits env run v o t) : v = 0 ∧ o = second ∧ t = 16 := by
  obtain ⟨i, hi, ho⟩ := h
  have hb := (List.getElem?_eq_some_iff.mp hi).1
  change i < 11 at hb
  interval_cases i <;> simp at hi
  all_goals obtain ⟨rfl, rfl⟩ := hi
  all_goals first
    | (change o ∈ [] at ho; exact (List.not_mem_nil ho).elim)
    | (change o ∈ [second] at ho; exact ⟨rfl, List.mem_singleton.mp ho, rfl⟩)

private theorem accepted_cases {i : Nat} {v : Fin 2} {o : Obj p} {t : Time}
    (h : V2.D.Run.acceptsAt env run i v o t) : v = 0 ∧ o = first ∧ t = 8 := by
  obtain ⟨parent, he, hc⟩ := h.1
  have hm := List.mem_of_getElem? he
  simp at hm
  obtain ⟨rfl, rfl, rfl⟩ := hm
  rcases (fgsaHooks p unitCodec).handles_carries _ _ _ hc with h | h
  · exact ⟨rfl, h.symm, rfl⟩
  · change o ∈ [] ∨ o ∈ [] ∨ o ∈ [] at h
    simp at h

private theorem demand_second : V2.D.DeliveryDemand env run 0 0 second 16 dl 18 := by
  intro a ha _ _ hc _ _ _
  change a + 1 ≤ 18 at hc
  have he : a = 16 ∨ a = 17 := by dsimp [Time] at *; omega
  rcases he with rfl | rfl
  all_goals left; exact ⟨6, by decide, by decide +kernel⟩

private theorem demand_first : V2.D.DeliveryDemand env run 0 0 first 8 dl 18 := by
  intro a ha _ _ hc _ _ _
  change a + 1 ≤ 18 at hc
  have hb : a ≤ 17 := by dsimp [Time] at *; omega
  interval_cases a
  all_goals first
    | (right; exact ⟨8, by decide, by decide, 5, first, rfl, Or.inl rfl⟩)
    | (left; exact ⟨6, by decide, by decide +kernel⟩)

/-- The revised per-anchor delivery law permits the root-based history exemption. -/
theorem within : Gen.V2.Duty.DeliveryWithinOn env run (fun o => ¬ isRowObject o) dl 18 := by
  constructor
  · intro v hv o ho t he w hw
    obtain ⟨rfl, rfl, rfl⟩ := emitted_cases he
    have hw0 : w = 0 := Finset.mem_singleton.mp hw
    subst w
    exact demand_second
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

/-- All K8 premises hold, including awake readiness, without receipt of the new body. -/
theorem premises : ReceiptCoveragePremises env run dl 18 17 0 0 B required paths := by
  refine ⟨within, ?_, ?_, ?_⟩
  · intro o t hr
    obtain ⟨rfl, rfl⟩ := hr
    refine ⟨Or.inl ⟨0, by decide, 9, rfl, emitted_proposal_already_processed.1⟩,
      by decide, ?_⟩
    intro s a K h
    cases h
  · intro i _ hi
    change i ≤ 10 at hi
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
      · exact ⟨second, 16, 2, body, rfl, ⟨rfl, rfl⟩, rfl, le_refl _⟩
      · exact (hg rfl).elim
    · intro o t s N hr hd
      obtain ⟨rfl, rfl⟩ := hr
      change some (Input.block 2 body) = some (Input.block s N) at hd
      obtain ⟨rfl, rfl⟩ := Input.block.inj (Option.some.inj hd)
      exact ⟨B, 17, ⟨rfl, rfl⟩, Gen.Pure.block_preceq_refl _⟩

/-- The receiver is awake on every required receipt window. -/
theorem ready : ∀ o t, required o t → ∀ u, t ≤ u → u < dl t → env.awake 0 u = true := by
  intros
  rfl

/-- The proposed body is absent at the required deadline despite its processed root. -/
theorem missing : ¬ ∃ Y ∈ (V2.D.Run.stateBeforeTime env run 17 0).st.fg.TF,
    eraseFG Y = B := by
  have hTF : (V2.D.Run.stateBeforeTime env run 17 0).st.fg.TF =
      {.genesis, fgBlock .genesis (namedProposal p .genesis 1 0 [] [] []).erase []} := by
    decide +kernel
  rintro ⟨Y, hY, he⟩
  rw [hTF] at hY
  simp only [Finset.mem_insert, Finset.mem_singleton] at hY
  rcases hY with rfl | rfl
  all_goals exact False.elim ((by decide : ¬ (type_of% he)) he)

/-- DECISION P23-A: keep the retired contract in the negative-test namespace. -/
def legacyReceiptCoverageStatement : Prop :=
  ∀ {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (dl : Time → Time) (cut D : Time) (first : Nat) (x : V) (B : Block)
    (required : Obj p → Time → Prop) (paths : Block → Time → Prop),
    NamedRootCollisionFree p c E rho → E.Δ = p.Δ → V2.D.ExecutionValid E rho → V2.D.NoRestart rho
      → x ∈ rho.honest →
    ReceiptCoveragePremises E rho dl cut D first x B required paths →
    let st := (V2.D.Run.stateBeforeTime E rho D x).st
    ((Block.Preceq B (eraseFG st.fg.F) ∧
      Block.Preceq B st.base.stableRecord ∧
      (∀ s, 0 < s → Block.Preceq B (headVote p st s)) ∧
      (∀ raw sup, Block.Preceq B (getHead p st raw sup)) ∧
      Block.Preceq B (fgHead p st) ∧
      (∀ lease ∈ st.base.obligations, Block.Compatible B lease.1)) ∨
     (Block.Preceq (eraseFG st.fg.F) B ∧
      (∀ o t s N, required o t →
        (toWire p o).decode = some (.block s N) →
        ∃ Y ∈ (V2.D.Run.stateBeforeTime E rho (dl t) x).st.fg.TF, eraseFG Y = N.erase) ∧
      (∀ K d, paths K d → ∀ b, Block.Preceq b K →
        ∃ Y ∈ (V2.D.Run.stateBeforeTime E rho d x).st.fg.TF, eraseFG Y = b))) ∧
    (∀ o t s a K, required o t → (toWire p o).decode = some (.vote s a K) →
      let v := baseVote (⟨.seat (.head s) a, K⟩ : HeadWire p.n)
      (v ∈ st.base.votes ∧ GridCO.stampVote st.base v < dl t) ∨
      ∃ v₁ ∈ st.base.votes, ∃ v₂ ∈ st.base.votes,
        v₁ ≠ v₂ ∧ GridCO.headLabel? v₁ = some s ∧ GridCO.headLabel? v₂ = some s ∧
        GridCO.headSeat? v₁ = some a ∧ GridCO.headSeat? v₂ = some a ∧
        GridCO.stampVote st.base v₁ < dl t ∧ GridCO.stampVote st.base v₂ < dl t)


/-- The legacy conclusion fails even with the approved receiver readiness. -/
theorem coverage_false : ¬ legacyReceiptCoverageStatement := by
  intro h
  have hNR : V2.D.NoRestart run := by
    intro i v t hi
    have hm := List.mem_of_getElem? hi
    simp at hm
  have hc := h env run dl 18 17 0 0 B required paths roots rfl valid hNR (by decide) premises
  rcases hc.1 with hleft | hright
  · exact (by decide +kernel : ¬ Block.Preceq B
      (eraseFG (V2.D.Run.stateBeforeTime env run 17 0).st.fg.F)) hleft.1
  · exact missing (hright.2.1 second 16 2 body ⟨rfl, rfl⟩ rfl)

end AvailableChain.FGSA.Run.ReceiptAliasTests
end

#print axioms AvailableChain.FGSA.Run.ReceiptAliasTests.within
#print axioms AvailableChain.FGSA.Run.ReceiptAliasTests.premises
#print axioms AvailableChain.FGSA.Run.ReceiptAliasTests.ready
#print axioms AvailableChain.FGSA.Run.ReceiptAliasTests.missing
#print axioms AvailableChain.FGSA.Run.ReceiptAliasTests.coverage_false

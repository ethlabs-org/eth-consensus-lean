module
public import AvailableChainFGSARun.Statements.Roots
public import AvailableChainFGSA.Proofs.NamedStore

public section

namespace AvailableChain.FGSA.Run

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]

/-- [ROOT-DIGEST-2 W1; DC NamedRootCollisionFree] Full scoped identity from the single field. -/
theorem namedProposal_eq (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hr : NamedRootCollisionFree p c E rho) {N N' : NamedProposal p.n}
    (hN : NamedProposalInRun p c E rho N) (hN' : NamedProposalInRun p c E rho N')
    (he : N.root = N'.root) : N = N' := by
  exact hr.root_injective N N' hN hN' N N'
    (Or.inl (named_preceq_refl N)) (Or.inr (named_preceq_refl N')) he

/-- [ROOT-DIGEST-2 W1; DC NamedRun.blockInRun] Named scope is ancestor closed. -/
theorem namedScope_ancestor (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {A B : NamedProposal p.n} (hB : NamedProposalInRun p c E rho B)
    (hAB : NamedProposal.Preceq A B) : NamedProposalInRun p c E rho A := by
  obtain ⟨C, hC, hBC⟩ := hB
  exact ⟨C, hC, named_preceq_trans hAB hBC⟩

/-- [P23-A] Old named scope is included in receipt scope. -/
theorem namedReceiptScope_of_namedScope (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {N : NamedProposal p.n}
    (hN : NamedProposalInRun p c E rho N) : NamedProposalReceiptScope p c E rho N :=
  Or.inl hN

/-- [P23-A] An honest emission scopes its exact body and every named ancestor. -/
theorem namedReceiptScope_emitted (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {v : V} {o : Obj p} {t : Time} {A N : NamedProposal p.n}
    (hv : v ∈ rho.honest) (hem : V2.D.Run.emits E rho v o t)
    (ho : o.payload = .proposal N) (hAN : NamedProposal.Preceq A N) :
    NamedProposalReceiptScope p c E rho A := Or.inr ⟨v, hv, o, t, N, hem, ho, hAN⟩

/-- [P23-A] Receipt scope is closed under named ancestry. -/
theorem namedReceiptScope_ancestor (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {A B : NamedProposal p.n} (hB : NamedProposalReceiptScope p c E rho B)
    (hAB : NamedProposal.Preceq A B) : NamedProposalReceiptScope p c E rho A := by
  rcases hB with hB | ⟨v, hv, o, t, N, hem, ho, hBN⟩
  · exact Or.inl (namedScope_ancestor E rho hB hAB)
  · exact Or.inr ⟨v, hv, o, t, N, hem, ho, named_preceq_trans hAB hBN⟩

/-- [P23-A] Receipt collision freedom supplies the old two-tip ancestor clause. -/
theorem NamedReceiptRootCollisionFree.toNamedRootCollisionFree (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hr : NamedReceiptRootCollisionFree p c E rho) :
    NamedRootCollisionFree p c E rho := by
  refine ⟨?_⟩
  intro B C hB hC A D hA hD he
  have hA' := hA.elim (namedScope_ancestor E rho hB) (namedScope_ancestor E rho hC)
  have hD' := hD.elim (namedScope_ancestor E rho hB) (namedScope_ancestor E rho hC)
  exact hr A D (Or.inl hA') (Or.inl hD') he

/-- [ROOT-DIGEST-2 W1; DC NamedRootCollisionFree] Equal named ancestor occurrences are full
    values. -/
theorem namedAncestor_eq (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hr : NamedRootCollisionFree p c E rho) {A B C D : NamedProposal p.n}
    (hB : NamedProposalInRun p c E rho B) (hC : NamedProposalInRun p c E rho C)
    (hA : NamedProposal.Preceq A B ∨ NamedProposal.Preceq A C)
    (hD : NamedProposal.Preceq D B ∨ NamedProposal.Preceq D C)
    (he : A.root = D.root) : A = D := hr.root_injective B C hB hC A D hA hD he

/-- [ROOT-DIGEST-2 W1; DC NamedRootCollisionFree] Scoped erasure is injective. -/
theorem namedScope_erase_injective (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hr : NamedRootCollisionFree p c E rho) {N M : NamedProposal p.n}
    (hN : NamedProposalInRun p c E rho N) (hM : NamedProposalInRun p c E rho M)
    (he : N.erase = M.erase) : N = M :=
  namedProposal_eq E rho hr hN hM (by simpa using congrArg Block.root he)

/-- [ROOT-DIGEST-2 W1; DC NamedRun.blockInRun] Projected scope is ancestor closed. -/
theorem rootBlockInRun_ancestor (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {A B : Block} (hB : RootBlockInRun p c E rho B) (hAB : Block.Preceq A B) :
    RootBlockInRun p c E rho A := by
  obtain ⟨N, hN, rfl⟩ := hB
  obtain ⟨M, hM, he⟩ := named_erase_ancestor hAB
  exact ⟨M, namedScope_ancestor E rho hN hM, he⟩

/-- [ROOT-DIGEST-2 W1; DC NamedRootCollisionFree] Project full identity to geometry. -/
theorem rootBlockInRun_eq (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hr : NamedRootCollisionFree p c E rho) {A B : Block}
    (hA : RootBlockInRun p c E rho A) (hB : RootBlockInRun p c E rho B)
    (he : A.root = B.root) : A = B := by
  obtain ⟨N, hN, rfl⟩ := hA
  obtain ⟨M, hM, rfl⟩ := hB
  exact congrArg NamedProposal.erase (namedProposal_eq E rho hr hN hM (by simpa using he))

/-- [ROOT-DIGEST-2 W1; DC NamedRootCollisionFree] Project covered FG chains. -/
theorem rootInjectiveOn_run (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hr : NamedRootCollisionFree p c E rho) {K W : SimplexFG.FGBlock (Fin p.n)}
    (hK : RootBlockInRun p c E rho (eraseFG K))
    (hW : RootBlockInRun p c E rho (eraseFG W)) : KitFG.RootInjectiveOn K W := by
  intro A B hA hB he
  apply eraseFG_injective
  apply rootBlockInRun_eq E rho hr
  · rcases hA with hA | hA
    · exact rootBlockInRun_ancestor E rho hK (eraseFG_preceq hA)
    · exact rootBlockInRun_ancestor E rho hW (eraseFG_preceq hA)
  · rcases hB with hB | hB
    · exact rootBlockInRun_ancestor E rho hK (eraseFG_preceq hB)
    · exact rootBlockInRun_ancestor E rho hW (eraseFG_preceq hB)
  · simpa only [eraseFG_root] using he

/-- [ROOT-DIGEST-2 W1; DC NamedRootCollisionFree] Full equality gives every ContentAgree field. -/
theorem contentAgree_of_namedScope (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hr : NamedRootCollisionFree p c E rho) {st st' : State p.n}
    (hs : ∀ N ∈ st.namedBodies, NamedProposalInRun p c E rho N)
    (hs' : ∀ N ∈ st'.namedBodies, NamedProposalInRun p c E rho N) : ContentAgree st st' := by
  intro s N hN s' N' hN' he
  have hn := hs N ((mem_namedBodies st N).mpr (Or.inr ⟨s, hN⟩))
  have hn' := hs' N' ((mem_namedBodies st' N').mpr (Or.inr ⟨s', hN'⟩))
  cases namedProposal_eq E rho hr hn hn' he
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- [ROOT-DIGEST-2 W1; DC NamedBlocks.erase] Scoped erasure reflects named ancestry. -/
theorem namedScope_preceq_iff (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hr : NamedRootCollisionFree p c E rho) {N M : NamedProposal p.n}
    (hN : NamedProposalInRun p c E rho N) (hM : NamedProposalInRun p c E rho M) :
    Block.Preceq N.erase M.erase ↔ NamedProposal.Preceq N M := by
  constructor
  · intro he
    obtain ⟨A, hAM, hA⟩ := named_erase_ancestor he
    have hnA := namedScope_erase_injective E rho hr hN
      (namedScope_ancestor E rho hM hAM) hA.symm
    simpa only [hnA] using hAM
  · exact named_preceq_erase

/-- [ROOT-DIGEST-2 W1; DC NamedBlocks.erase] Scoped erasure reflects compatibility. -/
theorem namedScope_compatible_iff (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hr : NamedRootCollisionFree p c E rho) {N M : NamedProposal p.n}
    (hN : NamedProposalInRun p c E rho N) (hM : NamedProposalInRun p c E rho M) :
    Block.Compatible N.erase M.erase ↔
      NamedProposal.Preceq N M ∨ NamedProposal.Preceq M N := by
  change (Block.preceq N.erase M.erase || Block.preceq M.erase N.erase) = true ↔ _
  rw [Bool.or_eq_true_iff]
  exact or_congr (namedScope_preceq_iff E rho hr hN hM)
    (namedScope_preceq_iff E rho hr hM hN)

/-- [ROOT-DIGEST-2 W1; DC NamedRun.blockInRun] Every literal delivery is scoped, even if
    rejected. -/
theorem namedScope_delivered (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {x : V} {o : Obj p} {t : Time} {N : NamedProposal p.n}
    (hd : V2.Event.deliver x o t ∈ rho.events) (ho : o.payload = .proposal N) :
    NamedProposalInRun p c E rho N :=
  ⟨N, Or.inl ⟨x, o, t, hd, ho⟩, named_preceq_refl N⟩

/-- [ROOT-DIGEST-2 W1; DC NamedRun.blockInRun] Honest named storage gives a scope seed. -/
theorem namedScope_held (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {x : V} (hx : x ∈ rho.honest) (i : Nat) {N : NamedProposal p.n}
    (hN : N ∈ (rho.stateBefore E i x).st.namedBodies) : NamedProposalInRun p c E rho N :=
  ⟨N, Or.inr ⟨x, hx, i, hN⟩, named_preceq_refl N⟩

/-- [ROOT-DIGEST-2 W1; DC NamedRootCollisionFree] Distinct scoped list variants refute the
    premise. -/
theorem namedScope_collision (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {N M : NamedProposal p.n} (hN : NamedProposalInRun p c E rho N)
    (hM : NamedProposalInRun p c E rho M) (he : N.root = M.root) (hne : N ≠ M) :
    ¬ NamedRootCollisionFree p c E rho := fun hr => hne (namedProposal_eq E rho hr hN hM he)

end AvailableChain.FGSA.Run
end

module
public import AvailableChainFGSARun.Proofs.NamedOrigins -- shake: keep (re-export)
public import AvailableChainFGSARun.Proofs.Reachable

public section

namespace AvailableChain.FGSA.Run

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]

/-- [ROOT-DIGEST-2 W2; DC NamedRun] A stored wire has an exact named delivery origin. -/
theorem namedScope_stored_proposal (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (x : V) {s : Slot} {N : NamedProposal p.n}
    (hw : (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈
      (rho.stateBefore E i x).st.proposals) : NamedProposalInRun p c E rho N := by
  obtain ⟨_, o, _, _, hd, ho, _, _⟩ := stored_proposal_delivered E rho i x _ hw
  have he : o = ofWire p ⟨.proposer s, .proposal N⟩ := by
    apply toWire_injective
    rwa [toWire_ofWire]
  exact namedScope_delivered E rho (List.mem_of_getElem? hd) (by rw [he]; rfl)

/-- [ROOT-DIGEST-2 W2; DC NamedRun] A stored non-genesis named body was delivered locally. -/
theorem stored_named_body_delivery (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (x : V) {N : NamedProposal p.n}
    (hN : N ∈ (rho.stateBefore E i x).st.namedBodies) (hne : N ≠ .genesis) :
    ∃ j o t, j < i ∧ rho.events[j]? = some (.deliver x o t) ∧
      o.payload = .proposal N := by
  obtain ⟨s, hs⟩ := ((mem_namedBodies _ N).mp hN).resolve_left hne
  obtain ⟨j, o, t, hj, hd, ho, _, _⟩ := stored_proposal_delivered E rho i x _ hs
  have he : o = ofWire p ⟨.proposer s, .proposal N⟩ := by
    apply toWire_injective
    rwa [toWire_ofWire]
  exact ⟨j, o, t, hj, hd, by rw [he]; rfl⟩

/-- [ROOT-DIGEST-2 W2; DC NamedStore] Exact named ancestry stays in the local store. -/
theorem stored_named_body_ancestor (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (x : V) {A B : NamedProposal p.n}
    (hB : B ∈ (rho.stateBefore E i x).st.namedBodies)
    (hAB : NamedProposal.Preceq A B) : A ∈ (rho.stateBefore E i x).st.namedBodies := by
  induction B with
  | genesis =>
    have he : A = .genesis := by simpa [NamedProposal.Preceq, NamedProposal.preceq] using hAB
    exact he ▸ hB
  | node P s r body raw sup rows ih =>
    rcases Bool.or_eq_true_iff.mp hAB with he | hp
    · have he' : A = .node P s r body raw sup rows := of_decide_eq_true he
      exact he' ▸ hB
    · exact ih (namedBodies_parent p _ (metaInv_stateBefore E rho i x) hB) hp

/-- [ROOT-DIGEST-2 W2; DC NamedRun] Delivery-parent origin covers the full named scope.
This helper uses no collision premise, Base₂, or ContentAgree. -/
theorem namedProposalInRun_genesis_or_delivered (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c))
    (hparents : ∀ x o t N, V2.Event.deliver x o t ∈ rho.events →
      o.payload = .proposal N → ∃ i y, N.parent ∈ (rho.stateBefore E i y).st.namedBodies)
    {A : NamedProposal p.n} (hA : NamedProposalInRun p c E rho A) :
    A = .genesis ∨ ∃ x o t, V2.Event.deliver x o t ∈ rho.events ∧
      o.payload = .proposal A := by
  by_cases hg : A = .genesis
  · exact Or.inl hg
  apply Or.inr
  have held (i : Nat) (x : V) (hm : A ∈ (rho.stateBefore E i x).st.namedBodies) :
      ∃ x o t, V2.Event.deliver x o t ∈ rho.events ∧ o.payload = .proposal A := by
    obtain ⟨_, o, t, _, hd, ho⟩ := stored_named_body_delivery E rho i x hm hg
    exact ⟨x, o, t, List.mem_of_getElem? hd, ho⟩
  obtain ⟨B, hd | ⟨x, _, i, hm⟩, hAB⟩ := hA
  · obtain ⟨x, o, t, hd, ho⟩ := hd
    by_cases he : A = B
    · exact ⟨x, o, t, hd, he ▸ ho⟩
    obtain ⟨i, y, hm⟩ := hparents x o t B hd ho
    apply held i y
    apply stored_named_body_ancestor E rho i y hm
    cases B with
    | genesis =>
      have he : A = .genesis := by
        simpa [NamedProposal.Preceq, NamedProposal.preceq] using hAB
      exact (hg he).elim
    | node P s r body raw sup rows =>
      exact (Bool.or_eq_true_iff.mp hAB).resolve_left (by simpa using he)
  · exact held i x (stored_named_body_ancestor E rho i x hm hAB)

/-- [ROOT-DIGEST-2 W2; DC NamedRun] A predicate on genesis and deliveries covers named scope. -/
theorem namedProposalInRun_origin (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hparents : ∀ x o t N, V2.Event.deliver x o t ∈ rho.events →
      o.payload = .proposal N → ∃ i y, N.parent ∈ (rho.stateBefore E i y).st.namedBodies)
    (Q : NamedProposal p.n → Prop) (hgen : Q .genesis)
    (hdel : ∀ x o t N, V2.Event.deliver x o t ∈ rho.events →
      o.payload = .proposal N → Q N)
    {A : NamedProposal p.n} (hA : NamedProposalInRun p c E rho A) : Q A := by
  rcases namedProposalInRun_genesis_or_delivered E rho hparents hA with rfl | hd
  · exact hgen
  · obtain ⟨x, o, t, hd, ho⟩ := hd
    exact hdel x o t A hd ho

/-- [ROOT-DIGEST-2 W2; DC NamedRootCollisionFree; S2] Cross-store identity uses delivery
scope for non-genesis bodies and local uniqueness for genesis. -/
theorem namedStored_eq (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hr : NamedRootCollisionFree p c E rho) (i j : Nat) (x y : V)
    {N M : NamedProposal p.n} (hN : N ∈ (rho.stateBefore E i x).st.namedBodies)
    (hM : M ∈ (rho.stateBefore E j y).st.namedBodies) (he : N.root = M.root) : N = M := by
  rcases (mem_namedBodies _ N).mp hN with rfl | ⟨s, hs⟩
  · exact namedBodies_root_injective p _ (cstoreInv_stateBefore E rho j y)
      (metaInv_stateBefore E rho j y) ((mem_namedBodies _ _).mpr (Or.inl rfl)) hM he
  rcases (mem_namedBodies _ M).mp hM with rfl | ⟨t, ht⟩
  · exact namedBodies_root_injective p _ (cstoreInv_stateBefore E rho i x)
      (metaInv_stateBefore E rho i x) hN ((mem_namedBodies _ _).mpr (Or.inl rfl)) he
  exact namedProposal_eq E rho hr (namedScope_stored_proposal E rho i x hs)
    (namedScope_stored_proposal E rho j y ht) he


end AvailableChain.FGSA.Run
end

module
public import AvailableChainFGSA.Proofs.Metadata
public import AvailableChainFGSA.Proofs.Head
public import AvailableChainFGSA.Proofs.HeadDomain

public section

namespace AvailableChain.FGSA

/-- [ROOT-DIGEST-2 W1; DC NamedStore.bodies] Local reachability supplies all named-store laws.
No run collision premise is used in this induction or its local consequences. -/
theorem reachable_named_store (p : Params) {st : State p.n} (hr : Reachable p st) :
    (∀ N ∈ st.namedBodies, N.parent ∈ st.namedBodies) ∧
    (∀ b, b ∈ st.base.blocks ↔ ∃ N ∈ st.namedBodies, N.erase = b) ∧
    (∀ N ∈ st.namedBodies, ∀ M ∈ st.namedBodies, N.erase = M.erase → N = M) ∧
    (∀ N ∈ st.namedBodies, ∀ M ∈ st.namedBodies, N.root = M.root → N = M) ∧
    st.base.headDomain = none := by
  have h := storeInvariant p st hr
  have m := metadataInvariant p st hr
  exact ⟨fun _ hN => namedBodies_parent p st m hN,
    namedBodies_erase_domain p st h m,
    fun _ hN _ hM => namedBodies_erase_injective p st m hN hM,
    fun _ hN _ hM => namedBodies_root_injective p st h m hN hM,
    base_headDomain_none p hr⟩

/-- [ROOT-DIGEST-2 W1; DC NamedBlocks] The unchanged geometric head has one held named parent. -/
theorem propose_parent_lookup (p : Params) {st : State p.n} (hr : Reachable p st) (s : Slot) :
    ∃ N, namedByErase? st (getHead p st (proposerVotes st s) (proposerSupport st s)) = some N ∧
      N ∈ st.namedBodies ∧ N.erase = getHead p st (proposerVotes st s) (proposerSupport st s) :=
  namedByErase?_stored p st (storeInvariant p st hr) (metadataInvariant p st hr) _
    (getHead_stored p st (storeInvariant p st hr) _ _)

/-- [ROOT-DIGEST-2 W1; DC NamedBlocks] Honest construction succeeds on reachable stores. -/
theorem propose_isSome_of_reachable (p : Params) {st : State p.n} (hr : Reachable p st)
    (s : Slot) (hs : s ≠ 0) : (propose p st s).isSome := by
  obtain ⟨N, hN, _, _⟩ := propose_parent_lookup p hr s
  simp only [propose, hs, ↓reduceIte, hN, Option.map_some, Option.isSome_some]

end AvailableChain.FGSA
end

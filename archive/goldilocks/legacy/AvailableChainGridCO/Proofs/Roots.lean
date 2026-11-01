module
public import AvailableChainGridCO.Model.StoreKeys -- shake: keep (re-export)
public import AvailableChainGridCO.Proofs.Paths
public import AvailableChainGridCO.Proofs.Proposals

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- The common run scope is closed under ancestry. -/
theorem blockInRun_of_prefix {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (A B : Block)
    (hB : BlockInRun E (gridInterface p) rho B) (hAB : Block.Preceq A B) :
    BlockInRun E (gridInterface p) rho A := by
  rcases hB with rfl | ⟨v, o, t, tip, hs, hb, hp⟩
  · exact Or.inl (by simpa [Block.Preceq, Block.preceq] using hAB)
  · exact Or.inr ⟨v, o, t, tip, hs, hb, prefix_trans A B tip hAB hp⟩

/-- Every stored block is in the contract's root scope, at any reader. -/
theorem stored_block_in_run {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (index : Nat) (reader : V) (B : Block)
    (hm : B ∈ (Run.stateBefore (gridCO p) rho index reader).blocks) :
    BlockInRun E (gridInterface p) rho B := by
  by_cases hg : B = .genesis
  · exact Or.inl hg
  · obtain ⟨j, _, t, o, raw, support, hi, hp, _⟩ :=
      stored_block_accepted p rho index reader B hg hm
    exact Or.inr ⟨reader, o, t, B, Or.inl ⟨j, hi⟩,
      by simp [gridInterface, block, hp], block_preceq_self B⟩

/-- Root uniqueness applies across different readers and different times. -/
theorem stored_ancestors_root_injective {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (hroot : RootInjective E (gridInterface p) rho)
    (i j : Nat) (u v : V) (A B C D : Block)
    (hB : B ∈ (Run.stateBefore (gridCO p) rho i u).blocks)
    (hD : D ∈ (Run.stateBefore (gridCO p) rho j v).blocks)
    (hAB : Block.Preceq A B) (hCD : Block.Preceq C D) (he : A.root = C.root) : A = C :=
  hroot A C (blockInRun_of_prefix p E rho A B (stored_block_in_run p E rho i u B hB) hAB)
    (blockInRun_of_prefix p E rho C D (stored_block_in_run p E rho j v D hD) hCD) he

/-- A local GHOST tree and all its ancestors meet the reference premise. -/
theorem stateBefore_rootInjectiveBelow {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (hroot : RootInjective E (gridInterface p) rho) (index : Nat) (reader : V) :
    RootInjectiveBelow (Run.stateBefore (gridCO p) rho index reader).blocks := by
  intro A C hA hC he
  obtain ⟨B, hB, hAB⟩ := hA
  obtain ⟨D, hD, hCD⟩ := hC
  exact stored_ancestors_root_injective p E rho hroot index index reader reader
    A B C D hB hD hAB hCD he

/-- The same root premise holds in every strict time input. -/
theorem time_input_rootInjectiveBelow {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (hs : ScheduleWellFormed E rho) (hroot : RootInjective E (gridInterface p) rho)
    (t : Time) (reader : V) :
    RootInjectiveBelow (Run.stateBeforeTime (gridCO p) rho t reader).blocks := by
  rw [time_input_eq_event_prefix p E rho hs]
  exact stateBefore_rootInjectiveBelow p E rho hroot _ reader

/-- The proposer's clock keeps its block tree and thus root uniqueness. -/
theorem proposalState_rootInjectiveBelow {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (hs : ScheduleWellFormed E rho) (hroot : RootInjective E (gridInterface p) rho)
    (s : Slot) : RootInjectiveBelow (proposalState p rho s).blocks := by
  have he := congrArg Prod.fst (clock_receiptData p
    (Run.stateBeforeTime (gridCO p) rho (proposalTime p s) (rho.proposerOf s))
    (proposalTime p s))
  change (proposalState p rho s).blocks =
    (Run.stateBeforeTime (gridCO p) rho (proposalTime p s) (rho.proposerOf s)).blocks at he
  rw [he]
  exact time_input_rootInjectiveBelow p E rho hs hroot _ _

end AvailableChain.GridCO
end

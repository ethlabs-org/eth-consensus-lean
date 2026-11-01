module
public import AvailableChainFGSA.Proofs.LeaseOutput
public import AvailableChainFGSA.Proofs.Metadata

public section

namespace AvailableChain.FGSA

open AvailableChain.Generic AvailableChain.SimplexFG

/-- [GLY E-11; D14; Statements/Store.lean:30]
One induction keeps the bundle and the bound on all stored targets. -/
theorem storeBundleInvariant (p : Params) : StoreBundleInvariant p := by
  have strengthened : ∀ st, Reachable p st →
      StoreBundle p st ∧ StoredTargetsBelowOutput p st := by
    intro st hst
    induction hst with
    | init =>
      have hL := storedTargetsBelowOutput_init p
      exact ⟨⟨cstoreInv_init p, metaInv_init p, block_preceq_refl _,
        leaseBelowOutputStore_of_storedTargetsBelowOutput p _ hL⟩, hL⟩
    | @restart st w _ ih =>
      rcases ih with ⟨hB, hL⟩
      have hL' := storedTargetsBelowOutput_wipe p st w hL
      exact ⟨⟨cstoreInv_wipe p st w hB.cstore, metaInv_wipe p st w hB.«meta», hB.nest,
        leaseBelowOutputStore_of_storedTargetsBelowOutput p _ hL'⟩, hL'⟩
    | @tick st t _ ih =>
      rcases ih with ⟨hB, hL⟩
      have hL' := storedTargetsBelowOutput_clock p st t hB.cstore hB.nest hL
      exact ⟨⟨cstoreInv_clock p st hB.cstore t, metaInv_clock p st hB.«meta» t,
        clock_nest p st t hB.nest,
        leaseBelowOutputStore_of_storedTargetsBelowOutput p _ hL'⟩, hL'⟩
    | @deliver st o _ ih =>
      rcases ih with ⟨hB, hL⟩
      have hL' := storedTargetsBelowOutput_process p st o hB.cstore hL
      exact ⟨⟨cstoreInv_process p st hB.cstore o, metaInv_process p st hB.cstore hB.«meta» o,
        process_nest p st o hB.nest,
        leaseBelowOutputStore_of_storedTargetsBelowOutput p _ hL'⟩, hL'⟩
  exact fun st hst => (strengthened st hst).1

/-- [GLY E-11; D14; Statements/Store.lean:22–30] The reachable-state bundle. -/
theorem storeBundle_of_reachable (p : Params) :
    ∀ st, Reachable p st → StoreBundle p st :=
  storeBundleInvariant p

/-- [Proofs/Admission.lean:15] The bundle gives the admission invariant. -/
theorem inv0_of_reachable (p : Params) (st : State p.n) (hst : Reachable p st) :
    Inv0 p st :=
  (storeBundle_of_reachable p st hst).cstore.toInv0

/-- [GLY E-11; D14; Statements/Invariants.lean:40]
Every live lease target is below the stored output. -/
theorem leaseBelowOutputStore_of_reachable
    (p : Params) (st : State p.n) (hst : Reachable p st) :
    ∀ ℓ ∈ st.base.obligations, st.base.now < ℓ.2.2 →
      Block.Preceq ℓ.1 st.base.stableRecord :=
  (storeBundle_of_reachable p st hst).lease

end AvailableChain.FGSA
end

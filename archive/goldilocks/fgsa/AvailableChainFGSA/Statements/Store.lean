module
public import AvailableChainFGSA.Statements.Invariants

@[expose] public section

namespace AvailableChain.FGSA

open AvailableChain.Generic AvailableChain.SimplexFG

/-- [bp comp.outputNesting.v2; K2] At every reachable state, `F ⪯ S`, and both
available accessors return S; for every `a`, without synchrony, including
empty and vetoed gates (spec 563–568). Conjuncts 2 and 3 are definitional
(`rfl`, DQ7): they are a regression check on the accessor bodies, not proved
content (G8 m1). -/
def OutputNestingStored (p : Params) : Prop :=
  ∀ st, Reachable p st → NestOK st ∧ confirmed st = st.base.stableRecord ∧ stable st = confirmed st

/-- [bp bp.store.v1; K4 core] Every reachable state satisfies the composite invariant. -/
def StoreInvariant (p : Params) : Prop := ∀ st, Reachable p st → CStoreInv p st

/-- [GLY E-11, §C.3; D14] The store, metadata, nesting, and live lease invariants. -/
structure StoreBundle (p : Params) (st : State p.n) : Prop where
  cstore : CStoreInv p st
  «meta» : MetaInv p st
  nest : NestOK st
  lease : LeaseBelowOutputStore p st

/-- [GLY E-11; D14] Every reachable state satisfies the store bundle.
The proof is in step 3. -/
def StoreBundleInvariant (p : Params) : Prop := ∀ st, Reachable p st → StoreBundle p st

theorem StoreBundleInvariant_def (p : Params) :
    StoreBundleInvariant p = (∀ st, Reachable p st → StoreBundle p st) := by
  rw [StoreBundleInvariant]

/-- [bp bp.store.v1] Local F moves only to a descendant, at every step. -/
def FMonotone (p : Params) : Prop :=
  ∀ st : State p.n, (∀ o, FGBlock.Preceq st.fg.F (process p st o).fg.F) ∧
    (∀ t, (clock p st t).fg.F = st.fg.F)

/-- [bp bp.store.v1; K4 metadata] -/
def MetadataInvariant (p : Params) : Prop := ∀ st, Reachable p st → MetaInv p st

end AvailableChain.FGSA
end

module
public import AvailableChainPCSA.Statements.Invariants

@[expose] public section

namespace AvailableChain.PCSA

open AvailableChain.Generic AvailableChain.SimplexFG

/-- [PC-SA M1; FG-SA Statements/Store.lean; pcsa34-r3 3.2; bp
comp.outputNesting.v2; K2] At every reachable state, `F ⪯ available` and
`strong ⪯ available`, and `get_stable` returns `get_confirmed`; for every
`a`, without synchrony, including empty and vetoed gates. The last conjunct
is definitional (`rfl`, DQ7): a regression check on the accessor body. -/
def OutputNestingStored (p : Params) : Prop :=
  ∀ st, Reachable p st → NestOK st ∧ stable st = confirmed st

/-- [PC-SA M1] [bp bp.store.v1; K4 core] Every reachable state satisfies the composite
invariant. -/
def StoreInvariant (p : Params) : Prop := ∀ st, Reachable p st → CStoreInv p st

/-- [PC-SA M1] [GLY E-11, §C.3; D14] The store, metadata and nesting
invariants. The FG-SA `lease` field (live leases below `S`) is not a PC-SA
store invariant: a lease can turn non-effective under a conflicting PC, `S`
can advance past it, and a later PC can make it effective again while it is
live (second review, fix 3). It is the lane claim
`LeaseBelowRecordClaim` (Claims/PC.lean). -/
structure StoreBundle (p : Params) (st : State p.n) : Prop where
  cstore : CStoreInv p st
  «meta» : MetaInv p st
  nest : NestOK st

/-- [PC-SA M1] [GLY E-11; D14] Every reachable state satisfies the store bundle. -/
def pcsa_StoreBundleInvariant (p : Params) : Prop := ∀ st, Reachable p st → StoreBundle p st

theorem pcsa_StoreBundleInvariant_def (p : Params) :
    pcsa_StoreBundleInvariant p = (∀ st, Reachable p st → StoreBundle p st) := by
  rw [pcsa_StoreBundleInvariant]

/-- [PC-SA M1] [bp bp.store.v1] Local F moves only to a descendant, at every step. -/
def FMonotone (p : Params) : Prop :=
  ∀ st : State p.n, (∀ o, FGBlock.Preceq st.fg.F (process p st o).fg.F) ∧
    (∀ t, (clock p st t).fg.F = st.fg.F)

/-- [PC-SA M1] [bp bp.store.v1; K4 metadata] -/
def MetadataInvariant (p : Params) : Prop := ∀ st, Reachable p st → MetaInv p st

end AvailableChain.PCSA
end

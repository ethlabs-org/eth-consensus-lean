module
public import AvailableChainFGSA.Model.Restart
public import AvailableChainKitFG.StoreSafetyDef
public import AvailableChainFGSA.Statements.FinalityView

@[expose] public section

namespace AvailableChain.FGSA

open AvailableChain.Generic AvailableChain.SimplexFG

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The states that the local steps reach from the initial state: ticks at any
times and deliveries of any wire objects, in any order. No engine, no run.
This is an OVER-approximation (audit M1, N3): it allows unchecked inputs
(`process` does not run `wellFormed`, DQ14) and repeated or backward clocks.
Every store fact of this plan holds on it. Exact spec simulation needs the
scheduled event order and checked inputs of T7; in particular no statement of
this plan claims that the GridCO release test equals the spec's release on an
arbitrary store (the equivocation set of `GridCO.releaseCount` reads all stored
label-r votes; the spec reads the votes stamped before `q_r`; the two agree at
the first scheduled release tick). -/
inductive Reachable (p : Params) : State p.n → Prop
  | init : Reachable p (initial p.n)
  | restart {st : State p.n} (w : Time) :
      Reachable p st → Reachable p (wipe p st w)
  | tick {st : State p.n} (t : Time) : Reachable p st → Reachable p (clock p st t)
  | deliver {st : State p.n} (o : Wire p.n) : Reachable p st → Reachable p (process p st o)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[bp comp.outputNesting.v2; K2] `F ⪯ S` (erased). -/
def NestOK {n : Nat} (st : State n) : Prop :=
  Block.Preceq (eraseFG st.fg.F) st.base.stableRecord

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[bp bp.activeView.v1, bp.reconcile.v1] Every live lease target, saved
nonempty result and fastWrite member is compatible with F. -/
def SACompat {n : Nat} (st : State n) : Prop :=
  (∀ row ∈ st.base.obligations, Block.Compatible row.1 (eraseFG st.fg.F)) ∧
  (∀ r C, (r, some C) ∈ st.base.genuine → Block.Compatible C (eraseFG st.fg.F)) ∧
  (∀ row ∈ st.fastWrite, ∀ b ∈ row.2, Block.Compatible b (eraseFG st.fg.F))

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[GLY E-11, §C.3; D14] Every live lease target is below the stored output.
For a GridCO obligation, `ℓ.1` is the target and `ℓ.2.2` is the deadline.
There is no honest premise. -/
def LeaseBelowOutputStore (p : Params) (st : State p.n) : Prop :=
  ∀ ℓ ∈ st.base.obligations, st.base.now < ℓ.2.2 → Block.Preceq ℓ.1 st.base.stableRecord

theorem LeaseBelowOutputStore_def (p : Params) (st : State p.n) :
    LeaseBelowOutputStore p st =
      (∀ ℓ ∈ st.base.obligations, st.base.now < ℓ.2.2 → Block.Preceq ℓ.1 st.base.stableRecord) := by
  rw [LeaseBelowOutputStore]

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[bp bp.leaseOrigins.v1 (fastWrite clause), bp.reconcile.v1 §6.3; K1; Opus M3]
The local fast-write origin invariant, relative to a block `Fb` (the erased F):
each member `B` of `fastWrite[r]` is below the saved body `C` of label `r`, or
below `Fb`. It needs no run: a gate writes a fresh label whose members are
prefixes of the saved result; reconcile keeps it (Task 9); no other step writes
`fastWrite` or `genuine`. -/
def FastOrigin {n : Nat} (Fb : Block) (st : State n) : Prop :=
  ∀ row ∈ st.fastWrite, ∀ B ∈ row.2,
    (∃ C, GridCO.savedGenuine st.base row.1 = some (some C) ∧ Block.Preceq B C) ∨
      Block.Preceq B Fb

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[ROOT-DIGEST W1; DC NamedBlocks and RootInjectiveOnAncestors]
[bp bp.store.v1; K4 core; K1] The composite store invariant. `fg`: the FG
module's invariant (K4). `rootInj`: Σ.T is root-injective (DQ2). `baseTree`: the
base list is Σ.T erased. `Smem`: S is stored. `fastOrigin`, `fastDom`: the
fast-write origins (M3). `rootInj` follows from local fresh-root admission; the field stays (D6).
`genuineKeys`, `leaseKeys`: one saved result per label
and one lease row per target, at the SA level (audit M4; used by `fastWriteAt`,
`leaseOf`). -/
structure CStoreInv (p : Params) (st : State p.n) : Prop where
  fg : KitFG.FGStoreInvariant (heightView p) (finalityView p) st.fg
  rootInj : ∀ X ∈ st.fg.TF, ∀ Y ∈ st.fg.TF, X.root = Y.root → X = Y
  baseTree : ∀ b, b ∈ st.base.blocks ↔ ∃ B ∈ st.fg.TF, eraseFG B = b
  saCompat : SACompat st
  Smem : st.base.stableRecord ∈ st.base.blocks
  fastOrigin : FastOrigin (eraseFG st.fg.F) st
  fastDom : (st.fastWrite.map Prod.fst).Nodup ∧
    ∀ r ∈ st.fastWrite.map Prod.fst, (GridCO.savedGenuine st.base r).isSome
  genuineKeys : (st.base.genuine.map Prod.fst).Nodup
  leaseKeys : (st.base.obligations.map Prod.fst).Nodup ∧
    ∀ row ∈ st.base.obligations, row.2.1 = SA.releaseThreshold p.toParams

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[helper] The first three fields of `CStoreInv`: the FG invariant, root
injectivity of Σ.T, and the base list as Σ.T erased (Task 10). -/
def Inv0 (p : Params) (st : State p.n) : Prop :=
  KitFG.FGStoreInvariant (heightView p) (finalityView p) st.fg ∧
    (∀ X ∈ st.fg.TF, ∀ Y ∈ st.fg.TF, X.root = Y.root → X = Y) ∧
    (∀ b, b ∈ st.base.blocks ↔ ∃ B ∈ st.fg.TF, eraseFG B = b)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[bp bp.store.v1, bp.frame.v1; K4 metadata; audit M4] The local metadata
invariant. `wireTree`: every stored wire retains its exact named proposal, passes
`namedContentOk`, and has its exact named parent in the store. Its rows decode and its FG
projection is in Σ.T with the same ordered decoded rows (`filterMap toRow?`).
`treeWire`: every non-genesis block of Σ.T has exactly one stored wire.
`stampKeys`: the block stamps are keyed by the base list, once each.
`pool*`: the row pool holds decoded rows without duplicates. `noGenesisWire`: no stored wire
carries genesis (G12 m1; with `treeWire` it gives `contentAgree_self`). -/
structure MetaInv (p : Params) (st : State p.n) : Prop where
  wireTree : ∀ o ∈ st.proposals, ∃ (s : Slot) (N : NamedProposal p.n),
    o = ⟨.proposer s, .proposal N⟩ ∧ namedContentOk p N = true ∧
    N.parent ∈ st.namedBodies ∧
    (∀ a ∈ N.rows, (RowWire.decode? a).isSome) ∧
    ∃ B ∈ st.fg.TF, eraseFG B = N.erase ∧ B.rows = N.rows.filterMap RowWire.toRow?
  treeWire : ∀ B ∈ st.fg.TF, B ≠ .genesis →
    ∃! o, o ∈ st.proposals ∧ Wire.block? o = some (eraseFG B)
  proposalsNodup : st.proposals.Nodup
  stampKeys : st.base.blockStamp.map Prod.fst = st.base.blocks
  blocksNodup : st.base.blocks.Nodup
  poolDecodes : ∀ a ∈ st.rowPool, (RowWire.decode? a).isSome
  poolNodup : st.rowPool.Nodup
  noGenesisWire : ∀ o ∈ st.proposals, Wire.block? o ≠ some .genesis

/-- [ROOT-DIGEST-2 W1; DC NamedRootCollisionFree] Full recursive content agreement.
Equal roots identify every ancestor and all its signed lists in the two stores. -/
def ContentAgree {n : Nat} (st st' : State n) : Prop :=
  ∀ s (N : NamedProposal n),
    (⟨.proposer s, .proposal N⟩ : Wire n) ∈ st.proposals →
  ∀ s' (N' : NamedProposal n),
    (⟨.proposer s', .proposal N'⟩ : Wire n) ∈ st'.proposals →
    N.root = N'.root →
      N = N' ∧ N.erase = N'.erase ∧ N.raw = N'.raw ∧
      N.support = N'.support ∧ N.rows = N'.rows

end AvailableChain.FGSA
end

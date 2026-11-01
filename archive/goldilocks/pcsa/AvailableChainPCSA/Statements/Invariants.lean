module
public import AvailableChainPCSA.Model.Frame
public import AvailableChainKitFG.StoreSafetyDef
public import AvailableChainPCSA.Statements.FinalityView

@[expose] public section

namespace AvailableChain.PCSA

open AvailableChain.Generic AvailableChain.SimplexFG

/-- [PC-SA M1; FG-SA Statements/Invariants.lean Reachable]
The states that the local steps reach from the initial state: ticks at any
times and deliveries of any wire objects, in any order. No engine, no run.
This is an OVER-approximation (audit M1, N3): it allows unchecked inputs
(`process` does not run `wellFormed`, DQ14) and repeated or backward clocks.
Every store fact holds on it. -/
inductive Reachable (p : Params) : State p.n → Prop
  | init : Reachable p (initial p.n)
  | tick {st : State p.n} (t : Time) : Reachable p st → Reachable p (clock p st t)
  | deliver {st : State p.n} (o : Wire p.n) : Reachable p st → Reachable p (process p st o)

/-- [PC-SA M1; pcsa34-r3 3.2; bp comp.outputNesting.v2; K2] Nesting by
construction: `F ⪯ available` and `strong ⪯ available` (erased). -/
def NestOK {n : Nat} (st : State n) : Prop :=
  Block.Preceq (eraseFG st.fg.F) (confirmed st) ∧ Block.Preceq (strong st) (confirmed st)

/-- [PC-SA M1; pcsa34-r3 R9; bp bp.activeView.v1, bp.reconcile.v1] Every live
lease target, saved nonempty result, held PC target and frozen PC target is
compatible with F. -/
def SACompat {n : Nat} (st : State n) : Prop :=
  (∀ row ∈ st.base.obligations, Block.Compatible row.1 (eraseFG st.fg.F)) ∧
  (∀ r C, (r, some C) ∈ st.base.genuine → Block.Compatible C (eraseFG st.fg.F)) ∧
  (∀ c ∈ st.pcs, Block.Compatible c.target (eraseFG st.fg.F)) ∧
  (∀ row ∈ st.pcSnapshot, ∀ c ∈ row.2, Block.Compatible c.target (eraseFG st.fg.F))

/-- [PC-SA M1; pcsa34-r3 2.3, 2.6, 3.6] The PC domain: every held PC is valid
(well formed, usable, F-compatible), one PC per slot and target, the ack pool
holds decodable acks once each, and the snapshot has one row per freeze
label. -/
def PCDom {n : Nat} (st : State n) : Prop :=
  (∀ c ∈ st.pcs, pcValid st c = true) ∧
  (st.pcs.map (fun c => (c.slot, c.target))).Nodup ∧
  (∀ a ∈ st.ackPool, (AckWire.decode? a).isSome) ∧ st.ackPool.Nodup ∧
  (st.pcSnapshot.map Prod.fst).Nodup

/-- [PC-SA M1; FG-SA CStoreInv; pcsa34-r3 3.1]
[bp bp.store.v1; K4 core; K1] The composite store invariant. `fg`: the FG
module's invariant (K4). `rootInj`: Σ.T is root-injective (DQ2). `baseTree`: the
base list is Σ.T erased. `Smem`: S is stored. `pcDom`: the PC domain (in place
of the fast-write origins). `genuineKeys`, `leaseKeys`: one saved result per
label and one lease row per target, at the SA level. -/
structure CStoreInv (p : Params) (st : State p.n) : Prop where
  fg : KitFG.FGStoreInvariant (FGSA.heightView p) (pcsa_finalityView p) st.fg
  rootInj : ∀ X ∈ st.fg.TF, ∀ Y ∈ st.fg.TF, X.root = Y.root → X = Y
  baseTree : ∀ b, b ∈ st.base.blocks ↔ ∃ B ∈ st.fg.TF, eraseFG B = b
  saCompat : SACompat st
  Smem : st.base.stableRecord ∈ st.base.blocks
  pcDom : PCDom st
  genuineKeys : (st.base.genuine.map Prod.fst).Nodup
  leaseKeys : (st.base.obligations.map Prod.fst).Nodup ∧
    ∀ row ∈ st.base.obligations, row.2.1 = SA.releaseThreshold p.toParams

/-- [PC-SA M1] [helper] The first three fields of `CStoreInv`: the FG invariant, root
injectivity of Σ.T, and the base list as Σ.T erased. -/
def Inv0 (p : Params) (st : State p.n) : Prop :=
  KitFG.FGStoreInvariant (FGSA.heightView p) (pcsa_finalityView p) st.fg ∧
    (∀ X ∈ st.fg.TF, ∀ Y ∈ st.fg.TF, X.root = Y.root → X = Y) ∧
    (∀ b, b ∈ st.base.blocks ↔ ∃ B ∈ st.fg.TF, eraseFG B = b)

/-- [PC-SA M1; FG-SA MetaInv; pcsa34-r3 2.4]
[bp bp.store.v1, bp.frame.v1; K4 metadata; audit M4] The local metadata
invariant. `wireTree`: every stored wire retains its exact named proposal, passes
`namedContentOk`, has its exact named parent in the store and a well-formed
carried PC if any. Its rows decode and its FG projection is in Σ.T with the
same ordered decoded rows (`filterMap toRow?`). `treeWire`: every non-genesis
block of Σ.T has exactly one stored wire. `stampKeys`: the block stamps are
keyed by the base list, once each. `pool*`: the row pool holds decoded rows
without duplicates. `noGenesisWire`: no stored wire carries genesis. -/
structure MetaInv (p : Params) (st : State p.n) : Prop where
  wireTree : ∀ o ∈ st.proposals, ∃ (s : Slot) (N : NamedProposal p.n),
    o = ⟨.proposer s, .proposal N⟩ ∧ namedContentOk p N = true ∧
    N.parent ∈ st.namedBodies ∧
    (∀ a ∈ N.rows, (RowWire.decode? a).isSome) ∧
    (∀ c, N.pc = some c → c.wellFormed = true) ∧
    ∃ B ∈ st.fg.TF, eraseFG B = N.erase ∧ B.rows = N.rows.filterMap RowWire.toRow?
  treeWire : ∀ B ∈ st.fg.TF, B ≠ .genesis →
    ∃! o, o ∈ st.proposals ∧ Wire.block? o = some (eraseFG B)
  proposalsNodup : st.proposals.Nodup
  stampKeys : st.base.blockStamp.map Prod.fst = st.base.blocks
  blocksNodup : st.base.blocks.Nodup
  poolDecodes : ∀ a ∈ st.rowPool, (RowWire.decode? a).isSome
  poolNodup : st.rowPool.Nodup
  noGenesisWire : ∀ o ∈ st.proposals, Wire.block? o ≠ some .genesis

/-- [PC-SA M1; DC NamedRootCollisionFree] Full recursive content agreement.
Equal roots identify every ancestor, all its signed lists and its carried PC
in the two stores. -/
def ContentAgree {n : Nat} (st st' : State n) : Prop :=
  ∀ s (N : NamedProposal n),
    (⟨.proposer s, .proposal N⟩ : Wire n) ∈ st.proposals →
  ∀ s' (N' : NamedProposal n),
    (⟨.proposer s', .proposal N'⟩ : Wire n) ∈ st'.proposals →
    N.root = N'.root →
      N = N' ∧ N.erase = N'.erase ∧ N.raw = N'.raw ∧
      N.support = N'.support ∧ N.rows = N'.rows ∧ N.pc = N'.pc

end AvailableChain.PCSA
end

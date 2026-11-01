module
public import AvailableChainFGSA.Model.RowCore
public import AvailableChainFGSA.Model.WindowStore

@[expose] public section

namespace AvailableChain.FGSA

open AvailableChain.Generic AvailableChain.SimplexFG

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 831–842] `on_goldfish_vote`: SA's vote pool, unchanged. -/
def admitHead (p : Params) (st : State p.n) (s : Slot) (i : Fin p.n) (b : BlockId) : State p.n :=
  { st with base := GridCO.admitVote p.toParams.engine st.base ⟨.seat s i, .head b⟩ }

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[R5] Store one copy of a decoded full wire. `wellFormed` checks the
payload at the delivery boundary. There is no row window or count limit. -/
def admitRow (p : Params) (st : State p.n) (a : RowWire p.n) : State p.n :=
  match a.decode? with
  | some _ =>
      if a ∈ st.rowPool then st else { st with rowPool := st.rowPool ++ [a] }
  | none => st

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 519–522; M3] The stored FG parent of an erased block. `pickPair`
returns `none` on two candidates; Task 10 shows there is at most one. -/
def parentFG {n : Nat} (st : State n) (b : Block) : Option (FGBlock (Fin n)) :=
  pickPair st.fg.TF (fun P => decide (eraseFG P = b.parent))

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 818–819, 902–912; M3; D9] The FG block of an admitted proposal: the
stored parent, the slot of the wire block, the inner packed value of its
application value and signed rows, and the decoded rows. Under `rowsOk` its
erasure is the wire block (`eraseFG_fgBlock`). -/
def fgBlock {n : Nat} (P : FGBlock (Fin n)) (b : Block) (rows : List (RowWire n)) :
    FGBlock (Fin n) :=
  .node P b.slot b.root (packInner (appOf b.body) rows) (rows.filterMap RowWire.toRow?)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 530–536, 806–817; M5, DQ2, DQ12, DQ14; D9] The acceptance tests of
`on_block`, all before any write: not genesis; `b.slot ≤ Σ.s`; no stored block
has the root of `b` (the duplicate test); `F ⪯ B`; `b.parent.slot < b.slot`;
the slot-`b.slot` proposer signs it; every row passes R6 against the parent
state; the body packs the carried rows (`rowsOk`, the same check as
in `wellFormed`). The dependencies are the exact named parent and `parentFG st N.erase = some P`. -/
def blockAccepted (p : Params) (st : State p.n) (s : Slot) (N : NamedProposal p.n)
    (P : FGBlock (Fin p.n)) : Bool :=
  let b := N.erase
  b != .genesis && decide (b.slot ≤ st.slot p) &&
    !decide (∃ Y ∈ st.fg.TF, Y.root = b.root) &&
    FGBlock.preceq st.fg.F (fgBlock P b N.rows) &&
    decide (b.parent.slot < b.slot) && s == b.slot &&
    rowsValidForParent p P b.slot N.rows && namedContentOk p N

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 804–829; M6] `on_block`. On refusal the state does not change. On
acceptance: the SA block admission and the carried votes (SA code on the
cumulative base, with the erased block); the FG admission (`on_block` of the FG
module: insert, then `update_finality`); the proposal wire is stored; if F
moved, `reconcile`; then the carried rows pass `admitRow`. The FG acceptance
decides; if the base admission then refused the block, the state would diverge
(a block in Σ.T but not in the base list); `base_admitProposal_accepts`
(Task 10) excludes this under the store invariant. -/
def admitBlock (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) : State p.n :=
  if !namedParentHeld st N then st else
  match parentFG st N.erase with
  | none => st
  | some P =>
      if blockAccepted p st s N P then
        let st1 : State p.n := { st with
          base := GridCO.admitProposal p.toParams.engine st.base
            (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead)
          fg := Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)
          proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
        let st2 := if st1.fg.F = st.fg.F then st1 else reconcile st1
        N.rows.foldl (admitRow p) st2
      else st

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 804–857] The delivery handler. It reads the wire only through
`Wire.decode` (J1). It does not run the input check (DQ14). -/
def process (p : Params) (st : State p.n) (o : Wire p.n) : State p.n :=
  match o.decode with
  | some (.vote s i b) => admitHead p st s i b
  | some (.row _ body) => admitRow p st ⟨o.auth, body⟩
  | some (.block s N) => admitBlock p st s N
  | none => st

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 247–255, 505–518; M12, DQ9, DQ14] The input check, as a pure function
(T7 binds it). A vote: a HEAD seat. A row: an FG seat and a valid body. A block:
not genesis; the proposer key of its slot; every carried vote a HEAD seat of
slot `b.slot − 1`; support ⊆ votes; every carried row passes the SAME row check
(`RowWire.valid`). The parent slot must be smaller than the block slot.
R6 is state-dependent and belongs to `blockAccepted`. The body packs the carried
rows (`rowsOk`, D9): a content check, the same one as in `blockAccepted`. -/
def wellFormed (p : Params) (o : Wire p.n) : Bool :=
  match o.decode with
  | some (.vote _ _ _) => true
  | some (.row _ body) => body.valid
  | some (.block s N) =>
      let b := N.erase
      let raw := N.raw
      let support := N.support
      let rows := N.rows
      b != .genesis && s == b.slot && decide (b.parent.slot < b.slot) &&
        raw.all (fun v => match v.decode? with
          | some (r, _, _) => r + 1 == b.slot
          | none => false) &&
        support.all (fun v => decide (v ∈ raw)) &&
        rows.all RowWire.valid &&
        contentOk p b raw support rows
  | none => false

end AvailableChain.FGSA
end

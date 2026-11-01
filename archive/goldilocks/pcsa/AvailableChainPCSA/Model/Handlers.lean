module
public import AvailableChainPCSA.Model.RowCore
public import AvailableChainPCSA.Model.PC
public import AvailableChainFGSA.Model.WindowStore

@[expose] public section

namespace AvailableChain.PCSA

open AvailableChain.Generic AvailableChain.SimplexFG

/-- [PC-SA M1] [spec 831–842] `on_goldfish_vote`: SA's vote pool, unchanged. -/
def admitHead (p : Params) (st : State p.n) (s : Slot) (i : Fin p.n) (b : BlockId) : State p.n :=
  { st with base := GridCO.admitVote p.toParams.engine st.base ⟨.seat s i, .head b⟩ }

/-- [PC-SA M1] [R5] Store one copy of a decoded full wire. `wellFormed` checks the
payload at the delivery boundary. There is no row window or count limit. -/
def admitRow (p : Params) (st : State p.n) (a : RowWire p.n) : State p.n :=
  match a.decode? with
  | some _ =>
      if a ∈ st.rowPool then st else { st with rowPool := st.rowPool ++ [a] }
  | none => st

/-- [PC-SA M1; pcsa-decisions 3n/4] `on_ack`: pool the ack, then assemble the
PCs the pool supports. -/
def admitAck (p : Params) (st : State p.n) (a : AckWire p.n) : State p.n :=
  collectPCs (poolAck p st a)

/-- [PC-SA M1; pcsa-decisions 3n/4; review fix 1 (D4)] `on_pc`: a well-formed
PC contributes its acks whole (no acceptance limit), then the PCs are
assembled; a malformed PC is ignored. A PC enters the store only by
assembly, with the node's own first-per-seat acks. `installPC` records the
stamp and deletes conflicting leases (pcsa34-r4.3 §3.7 (iii)). -/
def admitPC {n : Nat} (st : State n) (c : PC n) : State n :=
  if c.wellFormed then collectPCs (c.acks.foldl poolAckRaw st) else st

/-- [PC-SA M1] [spec 519–522; M3] The stored FG parent of an erased block. -/
def parentFG {n : Nat} (st : State n) (b : Block) : Option (FGBlock (Fin n)) :=
  pickPair st.fg.TF (fun P => decide (eraseFG P = b.parent))

/-- [PC-SA M1] [spec 818–819, 902–912; M3; D9] The FG block of an admitted proposal: the
stored parent, the slot of the wire block, the inner packed value of its
application value and signed rows, and the decoded rows. -/
def fgBlock {n : Nat} (P : FGBlock (Fin n)) (b : Block) (rows : List (RowWire n)) :
    FGBlock (Fin n) :=
  .node P b.slot b.root (packInner (appOf b.body) rows) (rows.filterMap RowWire.toRow?)

/-- [PC-SA M1; FG-SA Handlers.lean blockAccepted]
[spec 530–536, 806–817; M5, DQ2, DQ12, DQ14; D9] The acceptance tests of
`on_block`, all before any write: not genesis; `b.slot ≤ Σ.s`; no stored block
has the root of `b` (the duplicate test); `F ⪯ B`; `b.parent.slot < b.slot`;
the slot-`b.slot` proposer signs it; every row passes R6 against the parent
state; a carried PC is well formed (review fix 5: an invalid carried PC is a
malformed block); the body packs the carried rows and the digest covers the
carried PC (`namedContentOk`). -/
def blockAccepted (p : Params) (st : State p.n) (s : Slot) (N : NamedProposal p.n)
    (P : FGBlock (Fin p.n)) : Bool :=
  let b := N.erase
  b != .genesis && decide (b.slot ≤ st.slot p) &&
    !decide (∃ Y ∈ st.fg.TF, Y.root = b.root) &&
    FGBlock.preceq st.fg.F (fgBlock P b N.rows) &&
    decide (b.parent.slot < b.slot) && s == b.slot &&
    rowsValidForParent p P b.slot N.rows && (N.pc.map PC.wellFormed).getD true &&
    namedContentOk p N

/-- [PC-SA M1; FG-SA Handlers.lean admitBlock; pcsa-decisions R-e]
[pcsa34-r4.3 §3.6 on_block; M6] On refusal the state does not change.
Lines 587–588 (`add B to Σ.T`, `for vote ∈ B.votes`) use SA admission on
the cumulative base. Line 589 (`if B.pc ≠ ⊥: on_pc`) deletes conflicting
locks with `deleteConflictingLeases`, under lines 576–578's admission
tests with the old F (deletion: lines 580–581).
FG has no separate insert handler: `FGSA.Window.on_block` inserts the FG
block and implements line 590 (`update_finality`). Store the proposal wire
and, if F moved, implement lines 595–600 with `reconcile`. Keep PC
assembly from the carried acks after this step (the block may complete a
path). Line 591 (`for a ∈ B.atts`) uses `admitRow`. -/
def admitBlock (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) : State p.n :=
  if !namedParentHeld st N then st else
  match parentFG st N.erase with
  | none => st
  | some P =>
      if blockAccepted p st s N P then
        let st1 : State p.n := { st with
          base := GridCO.admitProposal p.toParams.engine st.base
            (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead) }
        let st1 := match N.pc with
          | none => st1
          | some c =>
              if pcValid st1 c &&
                  !st1.pcs.any (fun o => o.slot == c.slot && o.target == c.target)
              then deleteConflictingLeases st1 c else st1
        let st1 := { st1 with
          fg := FGSA.Window.on_block p p.K_W st1.fg (fgBlock P N.erase N.rows)
          proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
        let st2 := if st1.fg.F = st.fg.F then st1 else reconcile st1
        let st3 := collectPCs (N.pcAcks.foldl poolAckRaw st2)
        N.rows.foldl (admitRow p) st3
      else st

/-- [PC-SA M1] [spec 804–857] The delivery handler. It reads the wire only through
`Wire.decode` (J1). It does not run the input check (DQ14). -/
def process (p : Params) (st : State p.n) (o : Wire p.n) : State p.n :=
  match o.decode with
  | some (.vote s i b) => admitHead p st s i b
  | some (.row _ body) => admitRow p st ⟨o.auth, body⟩
  | some (.block s N) => admitBlock p st s N
  | some (.ack _ _ b) => admitAck p st ⟨o.auth, b⟩
  | some (.pc c) => admitPC st c
  | none => st

/-- [PC-SA M1; FG-SA Handlers.lean wellFormed; pcsa-decisions 3n/4]
[spec 247–255, 505–518; M12, DQ9, DQ14] The input check, as a pure function
(T7 binds it). A vote: a HEAD seat. A row: an FG seat and a valid body. An
ack: an ack seat (the identifier may be unresolved). A PC: well formed. A
block: not genesis; the proposer key of its slot; every carried vote a HEAD
seat of slot `b.slot − 1`; support ⊆ votes; every carried row
passes the SAME row check (`RowWire.valid`); a carried PC is well formed. The
parent slot must be smaller than the block slot. R6 is state-dependent and
belongs to `blockAccepted`. The body packs the carried rows and the digest
covers the PC (`contentOk`, D9). -/
def wellFormed (p : Params) (o : Wire p.n) : Bool :=
  match o.decode with
  | some (.vote _ _ _) => true
  | some (.row _ body) => body.valid
  | some (.ack _ _ _) => true
  | some (.pc c) => c.wellFormed
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
        (N.pc.map PC.wellFormed).getD true &&
        contentOk p b raw support rows N.pc
  | none => false

end AvailableChain.PCSA
end

module
public import AvailableChainFGSA.Model.Handlers
public import AvailableChainFGSA.Model.Frame
public import AvailableChainFGSA.Model.Legacy.Frame -- shake: keep (axioms)
public import AvailableChainFGSA.Tests.Support
public import AvailableChainFGSA.Proofs.RowSelection

@[expose] public section

namespace AvailableChain.FGSA.Tests

open AvailableChain.SimplexFG hiding B1 B2 B3 B1' B1a B1b childA X Y stF

/-- A signed row by identity `i`; the legacy round input has no effect. -/
def rw (_r : Nat) (i : Fin 4) (a : Row (Fin 4)) : RowWire 4 :=
  ⟨.seat .fg i,  .vote (RowBody.ofRow a)⟩

/-! ### Packed fixtures (D9)

A proposal block carries its signed rows in its body (`packBody`). The FG-SA
fixtures are therefore packed here, in FG-SA: `pk P s app rw` is the FG block of
a wire block with parent `eraseFG P`, slot `s`, application value `app` and
signed rows `rw` (`fgBlock`), and `pb` is a wire block with a packed body. The
blocks `B1`, `B2`, `B3`, `B1'`, `B1a`, `childA`, `B1b`, `X`, `Y` have the
parents, slots and decoded rows of the FG module's blocks of the same name
(`AvailableChainSimplexFG`), with row targets that name the packed roots; the
FG module's own blocks are hidden. Every block has application value `0`,
except `B1b` (value `1`, so that it differs from `B1a`). ROOT-DIGEST W3 uses small roots. -/

/-- Fixed-FG signatures for the rows `rs`; the legacy round input has no effect. -/
def signRows (_r : Nat) (rs : List (Row (Fin 4))) : List (RowWire 4) :=
  rs.map (fun a => ⟨.seat .fg a.signer,  .vote (RowBody.ofRow a)⟩)

/-- ROOT-DIGEST W3: the literal root is independent of the digest table. -/
def literalFG (P : FGBlock (Fin 4)) (s : Slot) (r : BlockId) (app : Nat)
    (rows : List (RowWire 4)) : FGBlock (Fin 4) :=
  .node P s r (packInner app rows) (rows.filterMap RowWire.toRow?)

def B1 : FGBlock (Fin 4) := literalFG .genesis 1 ⟨1⟩ 0 (signRows 0 [rowT 0, rowT 1, rowT 2])
def B2 : FGBlock (Fin 4) :=
  literalFG B1 2 ⟨4⟩ 0 (signRows 1 [rowAt 2 B1.root false 0, rowAt 2 B1.root false 1,
    rowAt 2 B1.root false 2])
/-- [helper] A timeout row for `(3, B2)` with the finality pair `(2, B1)`. -/
def rowB3' (i : Fin 4) : Row (Fin 4) := ⟨i, .vote 3 B2.root true, some ⟨2, B1.root⟩⟩
def B3 : FGBlock (Fin 4) := literalFG B2 3 ⟨9⟩ 0 (signRows 1 [rowB3' 0, rowB3' 1, rowB3' 2])
def B1' : FGBlock (Fin 4) := literalFG .genesis 2 ⟨3⟩ 0 (signRows 0 [rowT 0, rowT 1, rowT 2])
def B1a : FGBlock (Fin 4) := B1
def childA : FGBlock (Fin 4) :=
  literalFG B1a 2 ⟨4⟩ 0 (signRows 1 [rowAt 2 B1a.root false 0, rowAt 2 B1a.root false 1,
    rowAt 2 B1a.root false 2])
def B1b : FGBlock (Fin 4) := literalFG .genesis 1 ⟨2⟩ 1 (signRows 0 [rowT 0, rowT 1, rowT 2])
def Y : FGBlock (Fin 4) :=
  literalFG B1b 2 ⟨7⟩ 0 (signRows 1 [rowAt 2 B1b.root false 0, rowAt 2 B1b.root false 1,
    rowAt 2 B1b.root true 2])
/-- ROOT-DIGEST W3: X uses root 8, above childA root 4, to keep the stK tie. -/
def X : FGBlock (Fin 4) := literalFG B1a 3 ⟨8⟩ 0 []

def v2 : HeadWire 4 := ⟨.seat (.head 2) 0, B2.root⟩
def rF : RowWire 4 := ⟨.seat .fg 3, .vote ⟨.vote 1 ⟨77⟩ true, none⟩⟩
def r0 : RowWire 4 := ⟨.seat .fg 2, .vote ⟨.vote 0 genesisRoot false, none⟩⟩
def r1 : RowWire 4 := ⟨.seat .fg 2, .vote ⟨.vote 1 genesisRoot false, none⟩⟩
def vX : HeadWire 4 := ⟨.seat (.head 2) 1, B1'.root⟩
def q (h : Nat) : RowWire 4 :=
  ⟨.seat .fg 3, .vote ⟨.vote 3 B2.root false, some ⟨h - 1, genesisRoot⟩⟩⟩
def r0z : RowWire 4 := rw 0 3 (rowAt 3 B2.root true 3)

namespace M05
def a0 : RowWire 4 := ⟨.seat .fg 0, .vote ⟨.vote 1 genesisRoot false, none⟩⟩
def a1 : RowWire 4 := ⟨.seat .fg 0, .vote ⟨.vote 1 genesisRoot true, none⟩⟩
def a2 : RowWire 4 :=
  ⟨.seat .fg 0, .vote ⟨.vote 1 genesisRoot false, some ⟨0, genesisRoot⟩⟩⟩
def qW (i : Fin 4) : RowWire 4 := ⟨.seat .fg i, .vote ⟨.vote 1 genesisRoot false, none⟩⟩
end M05

/-- ROOT-DIGEST W3: every table key has all six signed-content fields. -/
def digestTable : List (DigestInput 4 × BlockId) :=
  [
  (⟨genesisRoot, 1, 0, signRows 0 [rowT 0, rowT 1, rowT 2], [], []⟩, ⟨1⟩),
  (⟨B1.root, 2, 0, signRows 1 [rowAt 2 B1.root false 0, rowAt 2 B1.root false 1, rowAt 2 B1.root
      false 2], [], []⟩, ⟨4⟩),
  (⟨B2.root, 3, 0, signRows 1 [rowB3' 0, rowB3' 1, rowB3' 2], [], []⟩, ⟨9⟩),
  (⟨genesisRoot, 2, 0, signRows 0 [rowT 0, rowT 1, rowT 2], [], []⟩, ⟨3⟩),
  (⟨genesisRoot, 1, 1, signRows 0 [rowT 0, rowT 1, rowT 2], [], []⟩, ⟨2⟩),
  (⟨B1b.root, 2, 0, signRows 1 [rowAt 2 B1b.root false 0, rowAt 2 B1b.root false 1, rowAt 2 B1b.root
      true 2], [], []⟩, ⟨7⟩),
  (⟨B1.root, 3, 0, [], [], []⟩, ⟨8⟩),
  (⟨genesisRoot, 3, 99, [rF], [v2], []⟩, ⟨20⟩),
  (⟨genesisRoot, 1, 98, [rw 1 2 (rowT 2)], [], []⟩, ⟨21⟩),
  (⟨genesisRoot, 3, 97, [r0], [], []⟩, ⟨22⟩),
  (⟨genesisRoot, 3, 97, [r1], [], []⟩, ⟨23⟩),
  (⟨B1.root, 4, 96, [], [], []⟩, ⟨24⟩),
  (⟨B1.root, 3, 95, [], [], []⟩, ⟨25⟩),
  (⟨B2.root, 3, 96, [], [v2], []⟩, ⟨26⟩),
  (⟨B2.root, 3, 96, [], [], []⟩, ⟨27⟩),
  (⟨B1'.root, 3, 96, [], [vX], []⟩, ⟨28⟩),
  (⟨B1'.root, 3, 96, [], [vX], [vX]⟩, ⟨29⟩),
  (⟨B2.root, 3, 95, [q 3], [], []⟩, ⟨30⟩),
  (⟨B2.root, 4, 0, signRows 1 B3.rows, [], []⟩, ⟨31⟩),
  (⟨B2.root, 3, 95, [q 1], [], []⟩, ⟨32⟩),
  (⟨B2.root, 3, 94, [q 3, r0z], [], []⟩, ⟨33⟩),
  (⟨genesisRoot, 1, 31, [M05.a0], [], []⟩, ⟨34⟩),
  (⟨genesisRoot, 2, 32, [M05.a2], [], []⟩, ⟨35⟩),
  (⟨genesisRoot, 1, 41, [M05.qW 0, M05.qW 1, M05.qW 2], [], []⟩, ⟨36⟩),
  (⟨genesisRoot, 4, 33, [], [], []⟩, ⟨37⟩),
  (⟨genesisRoot, 100, 9, [M05.a0, M05.a1, M05.a2], [], []⟩, ⟨38⟩),
  (⟨genesisRoot, 100, 9, [M05.a1, M05.a0, M05.a2], [], []⟩, ⟨39⟩),
  (⟨B1.root, 2, 0, [⟨.seat .fg 0, .vote ⟨.vote 2 B1.root false, some ⟨1, genesisRoot⟩⟩⟩], [], []⟩,
      ⟨40⟩) ]

/-- ROOT-DIGEST W3: positive IDs; 4095 is outside the finite table. -/
def fixtureDigest (d : DigestInput 4) : BlockId :=
  ((digestTable.find? (fun e => e.1 == d)).map Prod.snd).getD ⟨4095⟩

/-- ROOT-DIGEST W3: the table has distinct roots for distinct full inputs. -/
theorem digestTable_distinct :
    ∀ e ∈ digestTable, ∀ f ∈ digestTable, e.2 = f.2 → e.1 = f.1 := by
  decide +kernel

/-- The test parameters: Δ = 1, n = 4, k = 2, R = 2, δ_t = 1.
`pT.cfg` is the FG module's `cfg1` and `pT.E` is its `E4`.
`pT.n` reduces to `4`, so `State 4` and `State pT.n` are one type. -/
abbrev pT : Params :=
  { Δ := 1, n := 4, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide, digest := fixtureDigest }

/-- ROOT-DIGEST W3: construct an FG fixture with its full digest input. -/
def pk (P : FGBlock (Fin 4)) (s : Slot) (app : Nat) (rows : List (RowWire 4))
    (raw support : List (HeadWire 4) := []) : FGBlock (Fin 4) :=
  .node P s (fixtureDigest ⟨P.root, s, app, rows, raw, support⟩)
    (packInner app rows) (rows.filterMap RowWire.toRow?)

/-- ROOT-DIGEST W3: the wire fixture uses the model smart constructor. -/
def pb (P : Block) (s : Slot) (app : Nat) (rows : List (RowWire 4))
    (raw support : List (HeadWire 4) := []) : Block :=
  proposalBlock pT P s app raw support rows

/-- The literal row-only family has empty ancestor HEAD lists. -/
def namedFixture : FGBlock (Fin 4) → NamedProposal 4
  | .genesis => .genesis
  | .node P slot root app rows =>
      .node (namedFixture P) slot root (eraseFG (.node P slot root app rows)).body
        [] [] (rows.map (fun a => ⟨.seat .fg a.signer, .vote (RowBody.ofRow a)⟩))

/-- Fixture list edits keep the exact previously constructed named parent. -/
def namedLists (N : NamedProposal 4) (raw support : List (HeadWire 4))
    (rows : List (RowWire 4)) : NamedProposal 4 :=
  match N with
  | .genesis => .genesis
  | .node P slot root body _ _ _ => .node P slot root body raw support rows

/-- A new fixture node takes its parent from the explicit named fixture family. -/
def namedBody (P : NamedProposal 4) (b : Block) (raw support : List (HeadWire 4))
    (rows : List (RowWire 4)) : NamedProposal 4 :=
  .node P b.slot b.root b.body raw support rows

theorem namedFixture_erase (B : FGBlock (Fin 4)) : (namedFixture B).erase = eraseFG B := by
  induction B with
  | genesis => rfl
  | node P slot root app rows ih =>
    simpa only [namedFixture, NamedProposal.erase, eraseFG, Block.body] using
      congrArg (fun b => Block.node b slot root (encFGBody app rows)) ih

theorem namedLists_erase (N : NamedProposal 4) (raw support : List (HeadWire 4))
    (rows : List (RowWire 4)) : (namedLists N raw support rows).erase = N.erase := by
  cases N <;> rfl

/-- ROOT-DIGEST W3: the smart constructors reproduce the literal fixtures. -/
theorem literal_constructors :
    pk .genesis 1 0 (signRows 0 [rowT 0, rowT 1, rowT 2]) = B1 ∧
    pk B1 2 0 (signRows 1 B2.rows) = B2 ∧
    pk B2 3 0 (signRows 1 B3.rows) = B3 ∧
    pk B1 3 0 [] = X := by decide +kernel

/-- ROOT-DIGEST W3: the literal fixture table is closed under parents. -/
def smokeRootScope : Finset (FGBlock (Fin 4)) := {.genesis, B1, B2, B3, B1', B1b, Y, X}

/-- ROOT-DIGEST W3b. Each table member has its parent in the same table. -/
theorem smoke_scope_parent_mem : ∀ B ∈ smokeRootScope, B.parent ∈ smokeRootScope := by
  decide +kernel

/-- ROOT-DIGEST W3: structural ancestor inclusion precedes the finite root check. -/
theorem smoke_ancestor_scope : ∀ B ∈ smokeRootScope,
    ∀ A, FGBlock.Preceq A B → A ∈ smokeRootScope :=
  KitFG.ancestor_closed_of_parent_closed smokeRootScope smoke_scope_parent_mem

theorem smoke_scope_roots : ∀ A ∈ smokeRootScope, ∀ B ∈ smokeRootScope,
    A.root = B.root → A = B := by decide +kernel

#print axioms digestTable_distinct
#print axioms literal_constructors
#print axioms smoke_ancestor_scope
#print axioms smoke_scope_roots

/-- [helper] The FG module's store after the packed blocks `B1`, `B2`, `B3`. -/
def stF : Store (Fin 4) := [B1, B2, B3].foldl (on_block E4 cfg1) Store.init
/-- The G02 chain, packed: `B3` finalizes `B1`. -/
example : stF.TF = {.genesis, B1, B2, B3} ∧ stF.F = B1 ∧ stF.J = B1 ∧ stF.h_j = 2 ∧
    stF.h_max = 4 := by decide +kernel
/-- The erasure of a packed block is its wire block, and the wire block passes
the content check with its signed rows. -/
example : eraseFG B1 = pb .genesis 1 0 (signRows 0 [rowT 0, rowT 1, rowT 2]) ∧
    rowsOk (eraseFG B1) (signRows 0 [rowT 0, rowT 1, rowT 2]) = true := by decide +kernel
/-- The FG content of the packed blocks: the decoded rows are the FG module's
rows, and the application values decode. -/
example : B1.rows = [rowT 0, rowT 1, rowT 2] ∧ B1b.rows = B1.rows ∧ B1 ≠ B1b ∧
    appOf (eraseFG B1).body = 0 ∧ appOf (eraseFG B1b).body = 1 := by decide +kernel
example : (rw 0 2 (rowT 2)).decode? = some (2, .vote (RowBody.ofRow (rowT 2))) := by decide
example : (rw 0 2 (rowT 2)).toRow? = some (rowT 2) := by decide
/-- `a_r = d_{rR}` (spec 217–220): with R = 2, `a_1 = d_2 = 4·2 + 6 = 14`. -/
example : pT.actionTime 1 = 14 := by decide
/-- At `a_1 = 14` the store slot is `rR + 1 = 3`, still round 1 (spec 1306, 1317). -/
example : pT.slotOf 14 = 3 ∧ pT.round 3 = 1 := by decide
/-- The base form of a carried vote: a HEAD seat of slot `s` is a seat of base
label `s`; an FG seat is not a base signature. -/
example : baseHead (n := 4) ⟨.seat (.head 3) 1, genesisRoot⟩ = ⟨.seat 3 1, genesisRoot⟩ ∧
    baseHead (n := 4) ⟨.seat .fg 1, genesisRoot⟩ = ⟨.none, genesisRoot⟩ := by decide
/-- One row check (M12; spec 234–237): height 0 fails; height 1 passes and the empty
pair fails; a row with a HEAD signature fails. -/
example : (RowBody.mk (.vote 0 genesisRoot false) none).valid = false ∧
    (RowBody.mk (.vote 1 genesisRoot false) none).valid = true ∧
    (RowBody.mk .empty none).valid = false ∧
    RowWire.valid (n := 4) ⟨.seat (.head 0) 2, .vote (RowBody.mk .empty none)⟩ = false := by decide
example : Wire.decode (n := 4) ⟨.seat .fg 2, .row (.vote (RowBody.ofRow (rowT 2)))⟩ =
    some (.row 2 (.vote (RowBody.ofRow (rowT 2)))) ∧
    Wire.decode (n := 4) ⟨.seat (.head 1) 2, .row (.vote (RowBody.ofRow (rowT 2)))⟩ = none := by
  decide

/-- G1: the positive row checks. An FG row at height 1 passes; an FG row at
height 0 fails. -/
example : (rw 0 2 (rowT 2)).valid = true ∧
    RowWire.valid (n := 4) ⟨.seat .fg 2, .vote (RowBody.mk (.vote 0 genesisRoot false) none)⟩ =
      false := by decide

/-- A carried HEAD vote of slot 3 by seat 1 for `B1`, and an FG signature on a
HEAD payload. -/
def hv : HeadWire 4 := ⟨.seat (.head 3) 1, B1.root⟩
def hf : HeadWire 4 := ⟨.seat .fg 1, B1.root⟩

/-- G1: the decoders of a vote and a proposal; a wrong auth gives `none`. -/
example : hv.decode? = some (3, 1, B1.root) ∧ hf.decode? = none := by decide +kernel
example : Wire.decode (n := 4) ⟨.seat (.head 3) 1, .head B1.root⟩ =
      some (.vote 3 1 B1.root) ∧
    Wire.decode (n := 4) ⟨.proposer 2,
    .proposal (namedLists (namedFixture B1) [hv] [hv] [rw 0 2 (rowT 2)])⟩ =
      some (.block 2 (namedLists (namedFixture B1) [hv] [hv] [rw 0 2 (rowT 2)])) ∧
    Wire.decode (n := 4) ⟨.proposer 2, .head B1.root⟩ = none ∧
    Wire.decode (n := 4) ⟨.seat (.head 2) 1,
    .proposal (namedLists (namedFixture B1) [] [] [])⟩ = none ∧
    Wire.decode (n := 4) ⟨.seat .fg 2, .head B1.root⟩ = none := by decide +kernel
/-- G1: `Wire.block?` gives the block of a proposal and `none` for a vote. -/
example : Wire.block? (n := 4) ⟨.proposer 2, .proposal (namedLists (namedFixture B1) [] [] [])⟩ =
      some (eraseFG B1) ∧
    Wire.block? (n := 4) ⟨.seat (.head 3) 1, .head B1.root⟩ = none := by decide +kernel
/-- G1: `liftHead?` inverts `baseVote` on a HEAD vote; it gives `none` for a
base proposal. -/
example : liftHead? (baseVote hv) = some hv ∧
    liftHead? (n := 4) ⟨.proposer 2, .proposal (eraseFG B1) [] []⟩ = none := by decide +kernel
/-- G1: `baseProposal` maps each carried vote by `baseHead`: a HEAD seat keeps its
slot and seat; an FG seat becomes `.none`. -/
example : baseProposal 2 (eraseFG B1) [hv, hf] [hv] =
    ⟨.proposer 2, .proposal (eraseFG B1) [⟨.seat 3 1, B1.root⟩, ⟨.none, B1.root⟩]
      [⟨.seat 3 1, B1.root⟩]⟩ := by decide +kernel

/-! Task 3: store, active view, reconcile, outputs. -/

def b1 : Block := eraseFG B1
def b1' : Block := eraseFG B1'
/-- F = B1 (the FG store of the FG module's G02 test), with a lease, a saved
result and a fast write on the conflicting `b1'`, and S = b1'. A hand-set,
NOT reachable fixture: `b1'` is in `base.blocks` but `B1'` is not in `fg.TF`,
so the correspondence "base list = Σ.T erased" (CStoreInv `baseTree`) does not
hold. Use it only for the Task 3 read and reconcile tests, never with an
invariant. -/
def stR0 : State 4 :=
  { fg := stF, base := { GridCO.initial 4 .root with
      blocks := [.genesis, b1, eraseFG B2, eraseFG B3, b1'],
      genuine := [(1, some b1'), (2, some .genesis)],
      obligations := [(b1', 2, 100)], stableRecord := b1' },
    fastWrite := [(1, [b1'])] }

/-- Reconcile deletes the lease, empties the conflicting result but keeps its
label, keeps the compatible result, filters fastWrite, and sets S := F (spec 874–894). -/
example : (reconcile stR0).base.obligations = [] ∧
    (reconcile stR0).base.genuine = [(1, none), (2, some .genesis)] ∧
    (reconcile stR0).fastWrite = [(1, [])] ∧
    (reconcile stR0).base.stableRecord = b1 ∧
    (reconcile stR0).base.blocks = stR0.base.blocks := by decide +kernel
/-- act(Σ) keeps the cumulative list but drops `b1'` (spec 360–361). -/
example : b1' ∈ stR0.base.blocks ∧ b1' ∉ (actView stR0).blocks ∧
    b1 ∈ (actView stR0).blocks := by decide +kernel
/-- A compatible S ahead of F stays (spec 565). -/
example : (normalizeS
      { stR0 with base := { stR0.base with stableRecord := eraseFG B3 } }).base.stableRecord =
    eraseFG B3 := by decide +kernel
example : blockExcluded stR0 b1' = true ∧ blockExcluded stR0 .genesis = false := by decide +kernel
/-- G3: `Σ.s = ⌊t / 4Δ⌋` (spec 711); with Δ = 1, times 0, 13 and 16 give slots 0, 3, 4. -/
example : State.slot pT (initial 4) = 0 ∧
    State.slot pT { base := { GridCO.initial 4 .root with now := 13 } } = 3 ∧
    State.slot pT { base := { GridCO.initial 4 .root with now := 16 } } = 4 := by decide

/-- G3 coverage: the initial store (spec 486–503) and the outputs (spec 558–561). -/
example : (initial 4).fg = Store.init ∧ (initial 4).base.stableRecord = .genesis ∧
    (initial 4).fastWrite = [] ∧ (initial 4).rowPool = [] := by decide
example : finalized stR0 = B1 ∧ confirmed stR0 = b1' ∧ stable stR0 = b1' := by decide +kernel
/-- G3 coverage: the lease and fastWrite reads (spec 293–298). -/
example : leaseOf stR0 b1' = some 100 ∧ leaseOf stR0 b1 = none ∧
    fastWriteAt stR0 1 = some [b1'] ∧ fastWriteAt stR0 2 = none := by decide +kernel
/-- G3 coverage: reconcile keeps a compatible lease, also on F and below F, and
writes no FG, proposal, row-pool or G field (spec 474–484). -/
example : (reconcile { stR0 with base := { stR0.base with
      obligations := [(b1', 2, 100), (.genesis, 2, 50), (b1, 2, 60)] } }).base.obligations =
    [(.genesis, 2, 50), (b1, 2, 60)] := by decide +kernel
example : (reconcile stR0).fg = stR0.fg ∧ (reconcile stR0).proposals = stR0.proposals ∧
    (reconcile stR0).rowPool = stR0.rowPool ∧
    (reconcile stR0).base.goldfishRecord = stR0.base.goldfishRecord := by decide +kernel
/-- G3 coverage: `onView` runs the step on `act(Σ)` (its last active block is
`B3`, not `b1'`) and then restores the cumulative list (M2). -/
example : (onView (fun v => { v with goldfishRecord := v.blocks.getLastD .genesis })
      stR0).base.goldfishRecord = eraseFG B3 ∧
    (onView (fun v => { v with goldfishRecord := v.blocks.getLastD .genesis })
      stR0).base.blocks = stR0.base.blocks := by decide +kernel

/-! Task 4: handlers. -/

def rowsOf (_r : Nat) (B : FGBlock (Fin 4)) : List (RowWire 4) :=
  B.rows.map (fun a => ⟨.seat .fg a.signer,  .vote (RowBody.ofRow a)⟩)
def wProp (B : FGBlock (Fin 4)) (r : Nat) (raw : List (HeadWire 4) := []) : Wire 4 :=
  ⟨.proposer B.slot, .proposal (namedLists (namedFixture B) raw [] (rowsOf r B))⟩
/-- Now = 12: slot 3, round 1. -/
def st0 : State pT.n := { base := { GridCO.initial 4 .root with now := 12 } }
def stA : State pT.n := [wProp B1 0, wProp B2 1, wProp B3 1].foldl (process pT) st0

/-- [test helper] `admitWith` for the wire `wProp B r` with FG parent `P`. -/
def aw (st : State pT.n) (B P : FGBlock (Fin 4)) (r : Nat) : State pT.n :=
  admitWith pT st B.slot (namedLists (namedFixture B) [] [] (rowsOf r B)) P B

/-- [test helper] The delivery of `wProp B r`, with FG parent `P`. -/
theorem process_wProp_eq (st : State pT.n) (B P : FGBlock (Fin 4)) (r : Nat)
    (hP : parentFG st (eraseFG B) = some P) (hB : fgBlock P (eraseFG B) (rowsOf r B) = B) :
    process pT st (wProp B r) = aw st B P r :=
  process_eq_admitWith pT st B.slot (namedLists (namedFixture B) [] [] (rowsOf r B)) P B
    (by simpa only [namedLists_erase, namedFixture_erase] using hP) (by
      have hrows : (namedLists (namedFixture B) [] [] (rowsOf r B)).rows = rowsOf r B := by
        cases B <;> rfl
      simpa only [namedLists_erase, namedFixture_erase, hrows] using hB)


/-- The FG part is the FG module's store after the same blocks (K4). -/
example : stA.fg.TF = stF.TF ∧ stA.fg.F = B1 ∧ stA.fg.J = stF.J ∧
    stA.fg.h_j = stF.h_j ∧ stA.fg.h_max = stF.h_max := by decide +kernel
/-- The base holds the erased tree (spec 355–358). -/
example : stA.base.blocks = [.genesis, b1, eraseFG B2, eraseFG B3] := by decide +kernel
/-- F moved to B1: S := F (spec 890–892). -/
example : stA.base.stableRecord = b1 := by decide +kernel

/-- Review Focus 2 (audit N1). A label-2 vote and a fresh round-1 row: separate
calls admit both at stA (slot 3, round 1). -/
example : (process pT stA ⟨v2.auth, .head v2.payload⟩).base.votes ≠ stA.base.votes ∧
    (admitRow pT stA rF).rowPool = stA.rowPool ++ [rF] := by decide +kernel
/-- A checked slot-3 block on genesis conflicts with F = B1. It carries `v2` and
`rF`. Refusal of `F ⋠ B` before unpacking (spec 808, 535–536): no block, no
stamp, no carried vote, no row, no FG change, no stored wire. -/
def wX : Wire 4 := ⟨.proposer 3,
    .proposal (namedBody .genesis (pb .genesis 3 99 [rF] [v2]) [v2] [] [rF])⟩
example : wellFormed pT wX = true := by decide +kernel
example : (process pT stA wX).base.blocks = stA.base.blocks ∧
    (process pT stA wX).base.votes = stA.base.votes ∧
    (process pT stA wX).base.blockStamp = stA.base.blockStamp ∧
    (process pT stA wX).rowPool = stA.rowPool ∧
    (process pT stA wX).fg.TF = stA.fg.TF ∧
    (process pT stA wX).proposals = stA.proposals := by decide +kernel
/-- A duplicate block changes nothing (spec 806–807). -/
example : (process pT stA (wProp B2 1)).base.blocks = stA.base.blocks ∧
    (process pT stA (wProp B2 1)).proposals = stA.proposals ∧
    (process pT stA (wProp B2 1)).rowPool = stA.rowPool := by decide +kernel
/-- The old round input is absent from the wire. This parent-valid row passes
the input check and the block handler. -/
def wFut : Wire 4 :=
  ⟨.proposer 1,
    .proposal (namedBody .genesis (pb .genesis 1 98 [rw 1 2 (rowT 2)]) [] [] [rw 1 2 (rowT 2)])⟩
example : rowsOk (pb .genesis 1 98 [rw 1 2 (rowT 2)]) [rw 1 2 (rowT 2)] = true ∧
    wellFormed pT wFut = true ∧ wFut ∈ (process pT st0 wFut).proposals := by decide +kernel
/-- Review Focus 9 (M12): the same height-0 row fails alone and in a block; the
height-1 row passes in both forms. -/
example : wellFormed pT ⟨r0.auth, .row r0.payload⟩ = false ∧
    rowsOk (pb .genesis 3 97 [r0]) [r0] = true ∧
    wellFormed pT ⟨.proposer 3,
    .proposal (namedBody .genesis (pb .genesis 3 97 [r0]) [] [] [r0])⟩ = false ∧
    wellFormed pT ⟨r1.auth, .row r1.payload⟩ = true ∧
    wellFormed pT ⟨.proposer 3,
    .proposal (namedBody .genesis (pb .genesis 3 97 [r1]) [] [] [r1])⟩ = true := by
  decide +kernel

/-- A handler-integration fixture (NOT a reachable state: the lease, the saved
result and the fast write on `b1'` are set by hand). `B1'` enters while
F = genesis; then `B1`, `B2`, `B3` move F to `B1`, and reconcile runs inside the
handler. -/
def stR1 : State pT.n :=
  let st := process pT st0 (wProp B1' 0)
  { st with
      base := { st.base with
        genuine := [(1, some b1')], obligations := [(b1', 2, 100)], stableRecord := b1' }
      fastWrite := [(1, [b1'])] }
def stR2 : State pT.n := [wProp B1 0, wProp B2 1, wProp B3 1].foldl (process pT) stR1
example : stR2.fg.F = B1 ∧ stR2.base.obligations = [] ∧
    GridCO.savedGenuine stR2.base 1 = some none ∧ stR2.fastWrite = [(1, [])] ∧
    stR2.base.stableRecord = b1 ∧ b1' ∈ stR2.base.blocks ∧
    b1' ∉ (actView stR2).blocks := by decide +kernel

/-- DQ2, the duplicate test: a new wire whose block is already stored (the
slot-3 block of `B3` with its rows, and the carried label-2 vote `v2`) is
refused by the root test. Distinct blocks have distinct roots, so the root test
is the block test. ROOT-DIGEST W3 rejects the changed raw list with the old digest. Direct delivery
    admits `v2`
at `stA`, but the duplicate does not admit it. -/
def wDup : Wire 4 := wProp B3 1 [v2]
example : wellFormed pT wDup = false ∧ wDup ∉ stA.proposals ∧
    baseVote v2 ∉ stA.base.votes ∧
    baseVote v2 ∈ (process pT stA ⟨v2.auth, .head v2.payload⟩).base.votes ∧
    (process pT stA wDup).fg.TF = stA.fg.TF ∧
    (process pT stA wDup).proposals = stA.proposals ∧
    (process pT stA wDup).base.votes = stA.base.votes := by decide +kernel
/-- Full-wire admission has no per-seat cap and removes exact duplicates. -/
def rA (h : Nat) : RowWire 4 := ⟨.seat .fg 0, .vote ⟨.vote h genesisRoot false, none⟩⟩
example : ([rA 1, rA 2, rA 3].foldl (admitRow pT) st0).rowPool = [rA 1, rA 2, rA 3] := by decide
example : wellFormed pT ⟨.seat .fg 0, .row (.vote ⟨.empty, none⟩)⟩ = false := by decide
example : ([rA 1, rA 2, rA 3, rA 1].foldl (admitRow pT) st0).rowPool =
    [rA 1, rA 2, rA 3] := by decide

/-- G4 coverage: temporary refusals (spec 806–807). A block whose parent is not
stored, and a block from a future slot (`4 > Σ.s = 3`), change nothing. -/
example : (process pT st0 (wProp B2 1)).fg.TF = st0.fg.TF ∧
    (process pT st0 (wProp B2 1)).base.blocks = st0.base.blocks ∧
    rowsOk (pb b1 4 96 []) ([] : List (RowWire 4)) = true ∧
    (process pT stA ⟨.proposer 4,
    .proposal (namedBody (namedFixture B1) (pb b1 4 96 []) [] [] [])⟩).fg.TF = stA.fg.TF := by
  decide +kernel
/-- G4 coverage: the slot-3 block signed by the slot-2 proposer key fails the
input check and the handler refuses it (spec 511–512, 810–812). -/
example : rowsOk (pb b1 3 95 []) ([] : List (RowWire 4)) = true ∧
    wellFormed pT ⟨.proposer 2,
    .proposal (namedBody (namedFixture B1) (pb b1 3 95 []) [] [] [])⟩ = false ∧
    (process pT stA ⟨.proposer 2,
    .proposal (namedBody (namedFixture B1) (pb b1 3 95 []) [] [] [])⟩).fg.TF = stA.fg.TF := by
  decide +kernel
/-- G4 coverage: a slot-1 vote at slot 3 is outside the vote window (spec 834–835);
a wire that does not decode changes nothing and fails the input check. -/
example : (process pT stA ⟨.seat (.head 1) 0, .head b1.root⟩).base.votes = stA.base.votes ∧
    (process pT stA ⟨.proposer 3, .head b1.root⟩).base.votes = stA.base.votes ∧
    (process pT stA ⟨.proposer 3, .head b1.root⟩).fg.TF = stA.fg.TF ∧
    wellFormed pT ⟨.proposer 3, .head b1.root⟩ = false := by decide +kernel
/-- G4 coverage: an accepted slot-3 block on `B2` passes its carried vote `v2`
to the vote pool (spec 820–821) and stores its wire. -/
def wY : Wire 4 := ⟨.proposer 3,
    .proposal (namedBody (namedFixture B2) (pb (eraseFG B2) 3 96 [] [v2]) [v2] [] [])⟩
example : baseVote v2 ∈ (process pT stA wY).base.votes ∧ baseVote v2 ∉ stA.base.votes ∧
    (process pT stA wY).proposals = stA.proposals ++ [wY] ∧
    pb (eraseFG B2) 3 96 [] [v2] ∈ (process pT stA wY).base.blocks := by
  rw [show process pT stA wY = _
    from process_eq_admitWith pT stA 3
      (namedBody (namedFixture B2) (pb (eraseFG B2) 3 96 [] [v2]) [v2] [] [])
    B2 (pk B2 3 96 [] [v2])
    (by decide +kernel) (by decide +kernel)]
  decide +kernel
/-- G4 coverage: the pool refuses the rows of `B1` in `stR2` (they duplicate the
rows of `B1'`), but the FG block `B1` keeps them (spec 540–541). The pool holds
the three round-0 rows of `B1'` and the six round-1 rows of `B2`, `B3`. -/
example : B1 ∈ stR2.fg.TF ∧ B1.rows.length = 3 ∧ stR2.rowPool.length = 9 := by decide +kernel

/-! Task 5: clock and composite gate. -/

/-- An empty gate at d_2 = 14 (no votes): the result is saved as empty, the fast
set of label 2 is created empty, and S := F runs after the gate (spec 756–781). -/
def stG : State pT.n :=
  { stA with base := { stA.base with now := 14, stableRecord := .genesis } }
example : GridCO.savedGenuine (gateStep pT stG 2).base 2 = some none ∧
    fastWriteAt (gateStep pT stG 2) 2 = some [] ∧
    (gateStep pT stG 2).base.stableRecord = b1 := by decide +kernel
/-- Evaluate once: a second gate of label 2 writes nothing new (spec 756). -/
example : (gateStep pT (gateStep pT stG 2) 2).fastWrite = (gateStep pT stG 2).fastWrite := by
  decide +kernel
/-- The clock at 14 runs the gate of slot 2 and keeps the FG part (spec 718–720). -/
example : fastWriteAt (clock pT stA 14) 2 = some [] ∧ (clock pT stA 14).fg.F = stA.fg.F := by
  decide +kernel

/-- [helper] A state at a new time (no clock step runs). -/
def atTime (st : State pT.n) (t : Time) : State pT.n :=
  { st with base := { st.base with now := t } }
/-- A label-2 HEAD vote of seat `i` for `B2`. -/
def hv2 (i : Fin 4) : Wire 4 := ⟨.seat (.head 2) i, .head B2.root⟩
/-- `B1`, `B2` admitted at now = 8 (stamps 8 < e_2 = 10); F stays genesis
(`B2` justifies `B1`; nothing finalizes it). -/
def stS0 : State pT.n := [wProp B1 0, wProp B2 1].foldl (process pT) (atTime {} 8)
/-- Two label-2 votes for `B2` at now = 9 (stamps 9 < e_2), then now = 14 = d_2. -/
def stS : State pT.n := atTime ([hv2 0, hv2 1].foldl (process pT) (atTime stS0 9)) 14

/-- Successful fast gate (spec 756–777, 457–461). By hand: both votes resolve
before e_2 = 10 and are late participants (stamps < d_2 = 14), so the scores are
b1: 2, b2: 2, and 2·2 > 2; the GHOST walk from F = genesis gives b2. The admission
level is τ = ⌈4/2⌉ = 2 ≤ p(2, B) = 2 for b1 and b2. The deadline is
d_2 + L = 14 + (4k − 1)Δ = 14 + 7 = 21. No lease exists, so there is no veto;
S := advance(genesis, b2) = b2. -/
example : GridCO.savedGenuine (gateStep pT stS 2).base 2 = some (some (eraseFG B2)) ∧
    fastWriteAt (gateStep pT stS 2) 2 = some [b1, eraseFG B2] ∧
    leaseOf (gateStep pT stS 2) b1 = some 21 ∧
    leaseOf (gateStep pT stS 2) (eraseFG B2) = some 21 ∧
    (gateStep pT stS 2).base.stableRecord = eraseFG B2 := by decide +kernel

/-- `B1'` is admitted too at now = 8, and a lease on `b1'` is set by hand. -/
def stV : State pT.n :=
  let st := atTime ([hv2 0, hv2 1].foldl (process pT)
    (atTime ([wProp B1 0, wProp B2 1, wProp B1' 0].foldl (process pT) (atTime {} 8)) 9)) 14
  { st with base := { st.base with obligations := [(b1', 2, 100)] } }
/-- Vetoed gate (spec 759–762). By hand: `b1'` has no support, so the result is
still b2 and it is saved; the live lease on `b1'` conflicts with b2, so the gate
writes no lease and `fastWrite[2] = ∅`. F is genesis, so `S := F` leaves S
(genesis) unchanged. -/
example : stV.fg.F = .genesis ∧
    GridCO.savedGenuine (gateStep pT stV 2).base 2 = some (some (eraseFG B2)) ∧
    fastWriteAt (gateStep pT stV 2) 2 = some [] ∧
    (gateStep pT stV 2).base.obligations = [(b1', 2, 100)] ∧
    (gateStep pT stV 2).base.stableRecord = .genesis := by decide +kernel

/-- Fast renewal with an unchanged deadline (spec 457–461). By hand: the gate
renews b1 with `max(100, 21) = 100`, and b1 still enters `fastWrite[2]`. -/
def stN : State pT.n := { stS with base := { stS.base with obligations := [(b1, 2, 100)] } }
example : leaseOf (gateStep pT stN 2) b1 = some 100 ∧
    fastWriteAt (gateStep pT stN 2) 2 = some [b1, eraseFG B2] := by decide +kernel

/-- Slow-only renewal (spec 457–461; SA slow arming). One label-2 vote (seat 0)
and a saved label-1 result b2. By hand: score 1 and one late voter give
2·1 > 1, so the result is b2; `p(2, b1) = 1 < τ = 2`, but `slowEligible` holds
(k = 2 ≤ 3; the label-1 result covers b1 and b2). So b1 gets a lease with
deadline 21, and `fastWrite[2] = ∅`. -/
def stW : State pT.n :=
  let st := atTime ([hv2 0].foldl (process pT) (atTime stS0 9)) 14
  { st with base := { st.base with genuine := [(1, some (eraseFG B2))] } }
example : leaseOf (gateStep pT stW 2) b1 = some 21 ∧
    fastWriteAt (gateStep pT stW 2) 2 = some [] := by decide +kernel

/-! The walk from F (spec 4e85ff34: 1280–1297, 502–505). In `stA`, F = B1 ≠
genesis. Two label-3 HEADs for block `b` enter at now = 13 (stamps 13 < e_3 = 14,
and the blocks have stamp 12), and the gate of label 3 runs at d_3 = 18. -/

/-- A label-3 HEAD vote of seat `i` for block `b`. -/
def hv3 (i : Fin 4) (b : Block) : Wire 4 := ⟨.seat (.head 3) i, .head b.root⟩
/-- `stA` (F = B1) with the label-3 HEADs of seats 0 and 1 for `b`, at d_3 = 18. -/
def stFw (b : Block) : State pT.n :=
  atTime ([hv3 0 b, hv3 1 b].foldl (process pT) (atTime stA 13)) 18

/-- T1: HEADs only for genesis. By hand: genesis has score 2 and 2·2 > 2, and
`b1` has score 0. The walk from genesis gives genesis (shown for contrast), but
the walk from F = B1 stops at `b1`, and `b1` fails the final strict-majority
test. So the saved result is empty, `fastWrite[3] = ∅`, no lease is written,
and S = F. This is the empty case of the transfer lemma (spec 2096–2103). Only
the `savedGenuine` conjunct tells the two walks apart. Label 3 is unsaved
before the gate, so the gate runs. -/
example : (stFw .genesis).fg.F = B1 ∧ b1 ≠ .genesis ∧
    GridCO.savedGenuine (stFw .genesis).base 3 = none ∧
    SA.Root.confirmation pT.toParams (actView (stFw .genesis)) 3 = some .genesis ∧
    GridCO.savedGenuine (gateStep pT (stFw .genesis) 3).base 3 = some none ∧
    fastWriteAt (gateStep pT (stFw .genesis) 3) 3 = some [] ∧
    (gateStep pT (stFw .genesis) 3).base.obligations = [] ∧
    (gateStep pT (stFw .genesis) 3).base.stableRecord = b1 := by decide +kernel

/-- T2: HEADs for `b2 ⪰ b1`. By hand: b1 and b2 have score 2, and b3 has score
0. The walk from F = B1 goes to b2 and stops there; b2 passes the final test.
The saved result is b2, the same as the walk from genesis, and the fast set is
`[b1, b2]` (τ = 2 ≤ p(3, B) = 2). -/
example : (stFw (eraseFG B2)).fg.F = B1 ∧
    GridCO.savedGenuine (stFw (eraseFG B2)).base 3 = none ∧
    GridCO.savedGenuine (gateStep pT (stFw (eraseFG B2)) 3).base 3 =
      some (some (eraseFG B2)) ∧
    SA.Root.confirmation pT.toParams (actView (stFw (eraseFG B2))) 3 = some (eraseFG B2) ∧
    fastWriteAt (gateStep pT (stFw (eraseFG B2)) 3) 3 = some [b1, eraseFG B2] := by
  decide +kernel

/-- T3: HEADs for F itself (spec 4e85ff34: 503–504, the final test applies also
when the block is Σ.F). By hand: b1 has score 2 and 2·2 > 2; its child b2 has
score 0, so no child of F is eligible. The walk stays at F = B1, and F passes
the final test: the saved result is `b1`. With T1, this fixes the rule "the walk
tests eligibility at F". -/
example : (stFw b1).fg.F = B1 ∧ GridCO.savedGenuine (stFw b1).base 3 = none ∧
    GridCO.savedGenuine (gateStep pT (stFw b1) 3).base 3 = some (some b1) ∧
    fastWriteAt (gateStep pT (stFw b1) 3) 3 = some [b1] := by decide +kernel

/-- G5 coverage: expiry (spec 713, 736–742). After the gate, both leases have the
deadline 21. At t = 20 no step runs (f_4 = 19, e_4 = 18, q_3 = 17, d_3 = 18),
and both leases stay; at t = 21 they expire (a lease expires at the first tick
at or after its deadline). No tick at 20 or 21 is a gate, so fastWrite stays.
At t = 21 = q_4 the release step of label 4 also runs; it has no effect (the
leases have already expired, and there are no label-4 votes). -/
example : (clock pT (gateStep pT stS 2) 20).base.obligations.length = 2 ∧
    (clock pT (gateStep pT stS 2) 21).base.obligations = [] ∧
    (clock pT (gateStep pT stS 2) 21).fastWrite = (gateStep pT stS 2).fastWrite := by decide +kernel
/-- G5 coverage: release at q_2 = 13 (spec 714–716, 744–752). The two label-2 votes for
b2 resolve before 13 and conflict with `b1'`, so 2 ≥ τ seats release the lease on
`b1'`; the lease on b1 is compatible with b2 and stays. A hand-set, NOT
reachable fixture: the lease names `b1'`, which is not in the store (release
counts do not read the target's membership). -/
def stQ : State pT.n :=
  { stS with base := { stS.base with now := 12, obligations := [(b1', 2, 100), (b1, 2, 100)] } }
example : (clock pT stQ 13).base.obligations = [(b1, 2, 100)] := by decide +kernel
/-- G5 coverage: the model-only freeze and early caches (DQ8) run at f_2 = 11
and e_2 = 10 for label 2. These ticks set the time of `stS` back from 14 to 11
and 10 (a pure test of the step, not a run). At t = 10 = d_1 the clock also runs
the gate of label 1 (no label-1 votes: an empty result). -/
example : ((clock pT stS 11).base.frozen.map Prod.fst) = [2] ∧
    ((clock pT stS 10).base.early.map Prod.fst) = [2] := by decide +kernel

/-- [R5] Admission has no clock window. The same valid content enters at
an early time and at a later time. -/
example : (admitRow pT (atTime {} 0) (rA 1)).rowPool = [rA 1] ∧
    (admitRow pT (atTime {} 4000) (rA 1)).rowPool = [rA 1] := by decide
/-- G4: a vote of a label above Σ.s = 3 is refused (spec 834–835); a label-3 vote
is admitted. -/
example : (process pT st0 ⟨.seat (.head 4) 0, .head b1.root⟩).base.votes = st0.base.votes ∧
    (process pT st0 ⟨.seat (.head 3) 0, .head b1.root⟩).base.votes =
      [⟨.seat 3 0, .head b1.root⟩] := by
  decide +kernel

/-! Task 6: frame reads and duties. -/

/-- The FG action of round 1 at a_1 = 14, after the empty gate of slot 2:
fastWrite[2] is empty, so C_fg is none and the height pair is empty; there is
no fallback to S, the root, a slow lease or an older set (spec 669–677). -/
def stC0 : State pT.n := clock pT stA 14
example : fastWriteAt stC0 2 = some [] ∧ (fgInputs pT stC0).1 = none ∧
    (attest pT stC0 RecordOnce.initial 0).1 = none := by decide +kernel
/-- With a live fast write on B2 (set by hand), C_fg = B2 (the deepest member
of fastWrite[2] in the full filtered tree with a lease after a_1). -/
def stC1 : State pT.n :=
  { stC0 with
      fastWrite := [(2, [eraseFG B2])]
      base := { stC0.base with obligations := [(eraseFG B2, 2, 21)] } }
example : (fgInputs pT stC1).1 = some B2 := by decide +kernel
/-- An expired lease does not count (spec 1329: `lease[B] > Σ.t`). -/
example : (fgInputs pT
      { stC1 with base := { stC1.base with obligations := [(eraseFG B2, 2, 14)] } }).1 =
    none := by decide +kernel
/-- Band eligibility (spec 1068): at v_4 = 17 with no votes, the HEAD walks from
Z = F = B1 (no lease). B2 is eligible because σ[B1].h = 2 < lo = 3; B3 is not
(σ[B2].h = 3, no majority, not current). -/
example : headVote pT { stA with base := { stA.base with now := 17 } } 4 = eraseFG B2 := by
  decide +kernel
/-- DQ13: `deepest` breaks a depth tie by the greater root (spec 260–262). The
two blocks have depth 1; the slot-2 block has the greater root. -/
example : (FGBlock.node .genesis 1 ⟨50⟩ 5 [] : FGBlock (Fin 4)).root <
      (FGBlock.node .genesis 2 ⟨51⟩ 9 [] : FGBlock (Fin 4)).root ∧
    deepest ({.node .genesis 1 ⟨50⟩ 5 [], .node .genesis 2 ⟨51⟩ 9 []} : Finset (FGBlock (Fin 4)))
      = some (.node .genesis 2 ⟨51⟩ 9 []) := by decide +kernel

/-- (a) Review Focus 7 (spec 423–430): resolution at read time. `B1'` enters at
now = 8, and a label-2 vote of seat 0 for `b1'` at now = 9 (before
z_2 = f_2 = 11). While F = genesis, the HEAD of slot 3 has the vote in both
merges. After `B1`, `B2`, `B3` at now = 12 move F to `B1`, `b1'` leaves `act(Σ)`:
the vote stays in the raw merge (stamp 9 < 11), but the frozen support tests the
CURRENT `act(Σ)` and drops it; no slot-3 proposal declares support. -/
def vH : GridCO.Wire 4 .root := ⟨.seat 2 0, .head b1'.root⟩
def stH0 : State pT.n :=
  atTime (process pT (atTime ([wProp B1' 0].foldl (process pT) (atTime {} 8)) 9)
    ⟨.seat (.head 2) 0, .head b1'.root⟩) 12
def stH : State pT.n := [wProp B1 0, wProp B2 1, wProp B3 1].foldl (process pT) stH0
example : vH ∈ headVotes pT stH0 3 ∧ vH ∈ headSupport pT stH0 3 ∧
    stH.fg.F = B1 ∧ vH ∈ headVotes pT stH 3 ∧ headSupport pT stH 3 = [] := by decide +kernel

/-- (b) spec 190–193 (audit N1): a slot-3 proposal `X` on `b1'` carries a label-2
vote of seat 1 for `b1'`. `X` is admitted at now = 12 while F = genesis (its vote
enters the pool with stamp 12 ≥ z_2 = 11, so the frozen arm does not hold it).
Then `B1`, `B2`, `B3` move F to `B1`: `X` leaves `act(Σ)`. Its carried vote
stays in the Legacy raw merge; the canonical HEAD omits the off-F proposal. -/
def xB : Block := pb b1' 3 96 [] [vX]
def stX : State pT.n :=
  [wProp B1 0, wProp B2 1, wProp B3 1].foldl (process pT)
    (process pT (atTime ([wProp B1' 0].foldl (process pT) (atTime {} 8)) 12)
      ⟨.proposer 3, .proposal (namedBody (namedFixture B1') xB [vX] [] [])⟩)
example : stX.fg.F = B1 ∧ xB ∈ stX.base.blocks ∧ xB ∉ (actView stX).blocks ∧
    baseVote vX ∈ Legacy.headVotes pT stX 3 ∧ headVotes pT stX 3 = [] := by decide +kernel

/-- [R7] Three distinct fixed-seat rows are valid for B2. All are held and
selected when they are absent from the parent chain. -/
def yB3 : Block := pb (eraseFG B2) 3 95 [q 3]
/-- `stA` with the pool rows `q 1`, `q 2`. -/
def stAq : State pT.n := [q 1, q 2].foldl (admitRow pT) stA
def stP : State pT.n := process pT stAq ⟨.proposer 3,
    .proposal (namedBody (namedFixture B2) yB3 [] [] [q 3])⟩
/-- [test helper] `stP` with its FG block explicit (`process_eq_admitWith`). -/
theorem stP_eq : stP = admitWith pT stAq 3 (namedBody (namedFixture B2) yB3 [] [] [q 3])
    B2 (pk B2 3 95 [q 3]) :=
  process_eq_admitWith pT stAq 3 (namedBody (namedFixture B2) yB3 [] [] [q 3]) B2 _
    (by decide +kernel) (by decide +kernel)
/-- Fallback (plan Global Constraints, R1): plain `decide` and the `Bool` form
both reach the elaborator's recursion limit on `stP`; the kernel check works. -/
example : yB3 ∈ stP.base.blocks ∧ q 3 ∈ stP.rowPool ∧
    proposalRows pT stP (eraseFG B2) = rowsOf 1 B3 ++ [q 1, q 2, q 3] := by
  rw [stP_eq]; decide +kernel

/-- G6 coverage: `live_root` (spec 648–655, 1086–1098). In `stA` (Z = F = B1,
now 12) a live lease on b2 makes b2 the live root (deeper than b1); an expired
lease (deadline 12) and a lease on a block outside the full filtered tree
(`b1'`) do not count, so the live root is Z = b1. -/
example : liveRoot pT { stA with base := { stA.base with obligations := [(eraseFG B2, 2, 100)] } } =
      eraseFG B2 ∧
    liveRoot pT { stA with base := { stA.base with obligations := [(eraseFG B2, 2, 12)] } } = b1 ∧
    liveRoot pT { stA with base := { stA.base with obligations := [(b1', 2, 100)] } } = b1 := by
  decide +kernel
/-- G6 coverage: `propose_block` at t_4 = 16 (spec 1236–1253). No slot-3 votes.
The head walk from Z = b1 takes b2 (band: σ[B1].h = 2 < lo = 3) and stops (b3:
σ[B2].h = 3, no majority, slot 3 ≠ Σ.s = 4). The
rows (I = {1, 2}): the rows of B1 (round 0) and B2 (on the chain of b2) drop;
the pool rows of B3 stay; the block rows add nothing new. The block packs
application value `0` with these rows (D5, D9). -/
example : propose pT (atTime stA 16) 4 =
    some (
    .proposal (namedBody (namedFixture B2)
      (pb (eraseFG B2) 4 0 (rowsOf 1 B3)) [] [] (rowsOf 1 B3))) := by decide +kernel
/-- G6 coverage: the finality head (spec 1318–1323) at `stA` (slot 3): the walk
reaches b3 (current slot), and the head fields are those of `B3`. -/
example : fgHead pT stA = eraseFG B3 ∧
    (fgInputs pT stA).2 = HeadFields.ofBlock pT.E pT.cfg B3 := by decide +kernel
/-- G6 coverage: `attest` with a source (spec 1304–1313, 1379–1387). In `stC1`
the source is B2 and the finality head is b3. σ[B3] has h_j = h_F = 2, so there
is no finality pair; with the initial record the height pair is the target
vote `(σ[B2].h, σ[B2].T_h.root) = (3, …)`. -/
example : (attest pT stC1 RecordOnce.initial 0).1 =
    some (.vote ⟨.vote 3 (derive pT.E pT.cfg B2).T_h.root false, none⟩) := by decide +kernel

/-- G5: the evaluate-once guard skips the lease and S writes (spec 756). After a
successful gate of label 2 on `stS` (leases on b1, b2; S = b2), clear the leases
and S by hand. A second gate of label 2 is skipped, so no lease comes back and S
stays genesis (F = genesis). Without the guard, `SA.gateFrom` (here equal to
`SA.gate`, because F = genesis) would write the leases again and set S = b2. -/
def g' : State pT.n :=
  let g := gateStep pT stS 2
  { g with base := { g.base with obligations := [], stableRecord := .genesis } }
example : (gateStep pT g' 2).base.obligations = [] ∧
    (gateStep pT g' 2).base.stableRecord = .genesis := by decide +kernel

/-! G6 fold (MAJOR 1 = Astra N1): tests that pin the HEAD view `voterBlocks`
and the merges in `headVote` (spec 598–606, 616–646, 1219–1233, 1276–1302). -/

/-- (Opus i) [the late block b2 is outside the slot-3 view] `B1` at now 8
(stamp 8), two equivocating label-2 seats at now 9, `B2` at now 12 (stamp
12 ≥ z_2 = 11), HEAD at v_3 = 13. The view is {genesis, B1}; the controls are
J = B1, h_j = 2, H = 3, no contest, so Z = B1, lo = 2; the filtered view tree is
{B1}, and the head is b1. With the full filtered tree, the two equivocating
seats make b2 eligible (2 < 2·2), and the head would be b2. -/
def eqv (i : Fin 4) (b : Block) : Wire 4 := ⟨.seat (.head 2) i, .head b.root⟩
def stE : State pT.n :=
  atTime (process pT (atTime ([eqv 0 .genesis, eqv 0 b1, eqv 1 .genesis, eqv 1 b1].foldl
    (process pT) (atTime (process pT (atTime {} 8) (wProp B1 0)) 9)) 12) (wProp B2 1)) 13
example : headVote pT stE 3 = b1 := by decide +kernel

/-- (Opus ii) [the merges reach the walk] In `stS` at v_3 = 13, the two label-2
votes for b2 (stamps 9 < 11) resolve before 11; b2 is eligible (2 < 2·2) and is
the head. With empty merges the head would be b1. -/
example : headVote pT (atTime stS 13) 3 = eraseFG B2 := by decide +kernel

/-- (Proposal arm of `voterBlocks`, spec 1224–1226) `stE` plus a slot-3 child
`x3` of B2 admitted at now 12. B2 (stamp 12 ≥ 11) is now in the view as an
ancestor of the slot-3 proposal. The view tree is {B1, B2, x3} (no contest,
Z = B1, lo = 2); the equivocating seats make b2 and x3 eligible, and the head is
x3. Without the proposal arm the view is {genesis, B1} and the head is b1. -/
def x3 : Block := pb (eraseFG B2) 3 96 []
def stE3 : State pT.n :=
  atTime (process pT (atTime stE 12) ⟨.proposer 3,
    .proposal (namedBody (namedFixture B2) x3 [] [] [])⟩) 13
example : B2 ∉ voterBlocks pT stE 3 ∧ B2 ∈ voterBlocks pT stE3 3 ∧
    headVote pT stE3 3 = x3 := by decide +kernel

/-- (Astra N1) [restricted witnesses and full-store controls together] The
contest blocks of the FG module: `B1a` (= B1), `childA` (justifies B1a at
height 2), `B1b`, `X` (child of B1a, no rows, height 2) at now 12 (stamps
12 < z_3 = 15), and `Y` (child of B1b, height 3, does not extend J = B1a) at now
16 (outside the slot-4 view). HEAD at v_4 = 17. By hand: the live controls read
the full Σ.T, so `Y` makes the store contested: Z = F = genesis, lo = H = 3.
The view tree (witnesses in the view only) is {genesis, B1a, childA}; the walk
from genesis takes b1a and then childA (band: heights 1, 2 < 3); the head is
childA. With controls from the view (no `Y`: Z = J = B1a, lo = 2) the tree also
has `X`, which wins the tie by root (`childA.root < X.root`, proved below): head
X. With witnesses from the full store, `Y` makes `B1b` viable, `B1b` wins the tie
at genesis (`B1a.root < B1b.root`, proved below), and the head is Y. -/
def stK : State pT.n :=
  atTime (process pT
    (atTime ([wProp B1a 0, wProp childA 1, wProp B1b 0, wProp X 1].foldl (process pT)
      (atTime {} 12)) 16) (wProp Y 1)) 17
/-- [test helper] `stK` with its FG blocks explicit (`process_wProp_eq`). -/
theorem stK_eq : stK = atTime (aw (atTime (aw (aw (aw (aw (atTime {} 12) B1a .genesis 0)
    childA B1a 1) B1b .genesis 0) X B1a 1) 16) Y B1b 1) 17 := by
  unfold stK
  rw [List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_nil,
    process_wProp_eq _ B1a .genesis 0 ?_ ?_, process_wProp_eq _ childA B1a 1 ?_ ?_,
    process_wProp_eq _ B1b .genesis 0 ?_ ?_, process_wProp_eq _ X B1a 1 ?_ ?_,
    process_wProp_eq _ Y B1b 1 ?_ ?_]
  all_goals decide +kernel
/-- The root orders that make the alternative winners `X` and `Y` differ from
the head `childA`. -/
example : childA.root < X.root ∧ B1a.root < B1b.root := by decide +kernel
example : (controls pT stK).contest = true ∧ (controls pT stK).Z = .genesis ∧
    (controls pT stK).lo = 3 ∧ Y ∈ stK.fg.TF ∧ Y ∉ voterBlocks pT stK 4 ∧
    headVote pT stK 4 = eraseFG childA := by
  rw [stK_eq]; decide +kernel

/-! G6 fold (Astra N2): the carried support arm and the two row arms. In this
and the next G6 sections, a test uses `decide +kernel` where plain `decide`
reaches the elaborator's recursion limit (plan Global Constraints, R1). -/

/-- (Carried support, spec 1286–1293) As `stX`, but the slot-3 proposal `xB`
also declares `vX` as support. By hand: after F moves to B1, `xB` and `b1'` are
outside `act(Σ)` but `b1'` is in Σ.T. The frozen arm is empty (the pool stamp of
`vX` is 12 ≥ z_2 = 11). The carried arm now excludes `vX`: its proposal and head
are not retained above F (port r2, change j). -/
-- ROOT-DIGEST W3: carried support has its own digest, root 29.
def xBs : Block := pb b1' 3 96 [] [vX] [vX]
def stXs : State pT.n :=
  [wProp B1 0, wProp B2 1, wProp B3 1].foldl (process pT)
    (process pT (atTime ([wProp B1' 0].foldl (process pT) (atTime {} 8)) 12)
      ⟨.proposer 3, .proposal (namedBody (namedFixture B1') xBs [vX] [vX] [])⟩)
example : stXs.fg.F = B1 ∧ xBs ∉ (actView stXs).blocks ∧ b1' ∉ (actView stXs).blocks ∧
    b1' ∈ stXs.base.blocks ∧ headSupport pT stXs 3 = [] := by decide +kernel

/-- [R7] Two sibling proposals carry distinct parent-valid rows. All rows
enter the pool; exact parent-chain exclusion removes only prior contents. -/
def yB : Block := pb (eraseFG B2) 3 95 [q 1]
def zB : Block := pb (eraseFG B2) 3 94 [q 3, r0z]
def stB : State pT.n :=
  [⟨.proposer 3,
    .proposal (namedBody (namedFixture B2) yB [] [] [q 1])⟩,
    ⟨.proposer 3, .proposal (namedBody (namedFixture B2) zB [] [] [q 3, r0z])⟩].foldl
    (process pT) stAq
/-- [test helper] `stB` with its FG blocks explicit (`process_eq_admitWith`). -/
theorem stB_eq : stB = admitWith pT
    (admitWith pT stAq 3 (namedBody (namedFixture B2) yB [] [] [q 1]) B2 (pk B2 3 95 [q 1]))
    3 (namedBody (namedFixture B2) zB [] [] [q 3, r0z]) B2 (pk B2 3 94 [q 3, r0z]) := by
  unfold stB
  rw [List.foldl_cons, List.foldl_cons, List.foldl_nil,
    process_eq_admitWith pT stAq 3 (namedBody (namedFixture B2) yB [] [] [q 1])
    B2 (pk B2 3 95 [q 1]) (by decide +kernel)
      (by decide +kernel)]
  exact process_eq_admitWith pT _ 3 (namedBody (namedFixture B2) zB [] [] [q 3, r0z]) B2 _
    (by decide +kernel)
    (by decide +kernel)
example : yB ∈ stB.base.blocks ∧ zB ∈ stB.base.blocks ∧ q 3 ∈ stB.rowPool ∧
    r0z ∈ stB.rowPool := by
  rw [stB_eq]; decide +kernel
/-- [R7] Exact removal keeps the other contents in their first-held order. -/
example : proposalRows pT stB yB = rowsOf 1 B3 ++ [q 2, q 3, r0z] := by
  rw [stB_eq]; decide +kernel
/-- [R7] A later clock does not expire any selected row. -/
example : proposalRows pT (atTime stB 16) yB = rowsOf 1 B3 ++ [q 2, q 3, r0z] := by
  rw [stB_eq]; decide +kernel

/-! G6 fold (Astra N3, Opus O-m1): no fallback in `C_fg`; `deepest`; the FJ
filter of `live_root`; a live root outside the HEAD view. -/

/-- (No fallback, spec 666–677, 1327–1335) A hand-set, NOT reachable fixture:
`stR2` (B1' in Σ.T, F = B1) at a_1 = 14 with an older nonempty set
`fastWrite[0] = [b1]`, `fastWrite[2] = [b1']`, and live leases on b1, b1' and b2
(b2 is in no fast set: a slow-only lease). By hand: rR = 2, and `b1'` is the only
member of `fastWrite[2]`, but `B1'` conflicts with F, so it is outside the full
filtered tree: C_fg = none. A fallback to the older set gives B1; a fallback to
any live lease gives B2; a read of Σ.T without the filter gives B1'. -/
def stF3 : State pT.n :=
  { stR2 with
      fastWrite := [(0, [b1]), (2, [b1'])]
      base := { stR2.base with
        now := 14, obligations := [(b1, 2, 100), (b1', 2, 100), (eraseFG B2, 2, 100)] } }
example : B1' ∈ stF3.fg.TF ∧ (fgInputs pT stF3).1 = none := by decide +kernel
/-- (Two fast targets) `fastWrite[2] = [b1, b2]`, both with a live lease. By hand:
C_fg = B2 (depth 2 > 1). The first member of the set is b1. -/
def stF4 : State pT.n := { stF3 with fastWrite := [(2, [b1, eraseFG B2])] }
example : (fgInputs pT stF4).1 = some B2 := by decide +kernel
/-- (FJ filter of `live_root`, spec 648–655) In `stR2`, a live lease on `b1'`:
`B1'` is in Σ.T but not in the full filtered tree, so the live root is Z = b1.
Over Σ.T, `b1'` would win (depth 1 = 1, `b1.root < b1'.root`, proved here). -/
example : b1.root < b1'.root ∧
    liveRoot pT { stR2 with base := { stR2.base with obligations := [(b1', 2, 100)] } } =
    b1 := by decide +kernel
/-- (A live root outside the HEAD view, spec 1086–1107) `stE` plus a live lease
on b2. By hand: B2 is in the full filtered tree, so the live root is b2 (deeper
than Z = b1); B2 is not in the slot-3 view (stamp 12 ≥ 11). The walk starts at
b2, which has no child in the view tree: the head is b2. A live root from the
view gives b1. -/
def stEL : State pT.n :=
  { stE with base := { stE.base with obligations := [(eraseFG B2, 2, 100)] } }
example : liveRoot pT stEL = eraseFG B2 ∧ B2 ∉ voterBlocks pT stEL 3 ∧
    headVote pT stEL 3 = eraseFG B2 := by decide +kernel

/-! G6 fold (Astra N5, Opus O-m2): the head fields and the returned record. -/

/-- (Head fields, spec 1312, 1318–1326) In `stK` at slot 4 the finality head is
`Y` (full filtered tree: contest, Z = genesis, lo = 3; `B1b` wins the tie at
genesis by root, `B1a.root < B1b.root` (proved at `stK`), and `Y` is its only
child). σ[Y] has h_j = 1, J = genesis,
h_F = 0; the live cache has J = B1a, h_j = 2. The head fields are σ[Y]'s. From
the cache they would be (2, B1a.root, 1). -/
example : fgHead pT stK = eraseFG Y ∧ stK.fg.J = B1a ∧ stK.fg.h_j = 2 ∧
    (fgInputs pT stK).2 = ⟨1, genesisRoot, 0⟩ := by
  rw [stK_eq]; decide +kernel
/-- [R2/R3] With no height source, no row is emitted and no finality lock
is written. There is no finality-only vote. -/
example : (fgInputs pT stK).1 = none ∧
    (attest pT stK RecordOnce.initial 0).1 = none ∧
    (attest pT stK RecordOnce.initial 0).2.lock 1 = none ∧
    (attest pT stK RecordOnce.initial 0).2.target 1 = none := by
  rw [stK_eq]; decide +kernel
/-- (The returned record, spec 1391–1399) In `stC1` the height pair is the target
vote at height 3 and there is no finality pair: the record gets `target[3]`, no
timeout at 3, and no lock at 2. -/
example : (attest pT stC1 RecordOnce.initial 0).2.target 3 =
      some (derive pT.E pT.cfg B2).T_h.root ∧
    (attest pT stC1 RecordOnce.initial 0).2.timeout 3 = false ∧
    (attest pT stC1 RecordOnce.initial 0).2.lock 2 = none := by decide +kernel

/-! G13 (Astra N3; r195 N3): an ACTIVE stored target that only the FJ filter
excludes. The tests above use `B1'`, which conflicts with F, so the active
filter and the full FJ filter both reject it. -/

/-- `stK` (F = genesis, so every stored block is active; contested store:
Z = genesis, lo = 3) with a live lease on `X` (deadline 100 > now 17) and
`fastWrite[4] = [eraseFG X]` (now 17: slot 4, round 2, rR = 4). `X` (height 2, no
descendant) is not in the full filtered tree. Hand-set, not reachable. -/
def stL : State pT.n :=
  { stK with
      fastWrite := [(4, [eraseFG X])]
      base := { stK.base with obligations := [(eraseFG X, 2, 100)] } }
/-- By hand: `X` is in Σ.T and in `act(Σ)`, but not in the full filtered tree. -/
example : X ∈ stL.fg.TF ∧ eraseFG X ∈ (actView stL).blocks ∧ X ∉ fullTree pT stL := by
  unfold stL; rw [stK_eq]; decide +kernel
/-- (spec 648–655, 1327–1335) By hand: no live target is in the full filtered
tree, so the live root is Z = genesis, and C_fg = none. With the active tree in
place of the full filtered tree, the live root is `eraseFG X` and C_fg = X (a scratch
check of that wrong rule gives these values). -/
example : liveRoot pT stL = .genesis ∧ (fgInputs pT stL).1 = none := by
  unfold stL; rw [stK_eq]; decide +kernel

/-! Migration 05: R6/R7 helpers before activation. These small hand-set stores
isolate selection from the old admission rule. -/

namespace M05

/-- One on-chain row and a sibling's row. Both carriers stay at height 1. -/
def C : FGBlock (Fin 4) := pk .genesis 1 31 [a0]
def D : FGBlock (Fin 4) := pk .genesis 2 32 [a2]
def held : State 4 :=
  { fg := { Store.init with TF := {.genesis, C, D} }
    proposals := [⟨.proposer 1, .proposal (namedLists (namedFixture C) [] [] [a0])⟩,
      ⟨.proposer 2, .proposal (namedLists (namedFixture D) [] [] [a2])⟩]
    rowPool := [a0, a1, a0] }

/-- Plan: mismatched height refusal. -/
theorem wrong_height : Window.rowValidW (parentFoldState pT 3 .genesis)
    ⟨.seat .fg 0, .vote ⟨.vote 2 genesisRoot false, none⟩⟩ = false := by decide

/-- Plan: mismatched target refusal. -/
theorem wrong_target : Window.rowValidW (parentFoldState pT 3 .genesis)
    ⟨.seat .fg 0, .vote ⟨.vote 1 C.root false, none⟩⟩ = false := by decide +kernel

/-- Plan R6: empty height and incorrect auth cannot pass. -/
theorem empty_and_auth : Window.rowValidW (parentFoldState pT 3 .genesis)
    ⟨.seat .fg 0, .vote ⟨.empty, none⟩⟩ = false ∧
    Window.rowValidW (parentFoldState pT 3 .genesis)
      ⟨.seat (.head 0) 0, a0.payload⟩ = false := by decide

/-- Plan: reset the slot before the fold. It changes timeout maturity. -/
theorem slot_before_fold : (parentFoldState pT 1 .genesis).s = 1 ∧
    (Window.process_height_events pT.E pT.cfg pT.K_W
      (([rowX 0, rowX 1, rowX 2]).foldl Window.process_row
        (parentFoldState pT 1 .genesis))).h = 2 ∧
    (process_height_events pT.E pT.cfg
      (([rowX 0, rowX 1, rowX 2]).foldl process_row
        (derive pT.E pT.cfg .genesis))).h = 1 := by decide

/-- Plan: one pre-fold parent state. A quorum changes the child's height only
when the height events run, after all three rows pass R6. -/
theorem common_parent :
    rowsValidForParent pT .genesis 1 (signRows 0 [rowT 0, rowT 1, rowT 2]) = true ∧
    (derive pT.E pT.cfg (pk .genesis 1 0 (signRows 0 [rowT 0, rowT 1, rowT 2]))).h = 2 := by
  decide +kernel

/-- A parent whose window is not empty (J5 Opus N3). -/
def winParent : FGBlock (Fin 4) := pk .genesis 1 41 [qW 0, qW 1, qW 2]

/-- Plan: no finality-state match requirement. On a parent with a non-empty
window, a foreign finality pair (entry height 1, another root) passes R6W and
sets progress, but it sets no finality bit: the window is unchanged. -/
theorem foreign_finality :
    (parentFoldState pT 3 winParent).W ≠ [] ∧
    Window.rowValidW (parentFoldState pT 3 winParent)
      ⟨.seat .fg 3, .vote ⟨.vote 2 (parentFoldState pT 3 winParent).T_h.root false,
        some ⟨1, C.root⟩⟩⟩ = true ∧
    (Window.process_row (parentFoldState pT 3 winParent)
      ⟨3, .vote 2 (parentFoldState pT 3 winParent).T_h.root false, some ⟨1, C.root⟩⟩).W =
      (parentFoldState pT 3 winParent).W ∧
    3 ∈ (Window.process_row (parentFoldState pT 3 winParent)
      ⟨3, .vote 2 (parentFoldState pT 3 winParent).T_h.root false,
        some ⟨1, C.root⟩⟩).progress := by
  decide +kernel

/-- Plan: full-content dedup, stable order, and more than two rows per seat.
The third row comes only from an admitted block. -/
theorem three_same_seat : proposalRowsFor pT held 100 .genesis = [a0, a1, a2] := by
  decide +kernel

/-- Plan: exact-row exclusion keeps the other two contents from that seat. -/
theorem exact_removal : proposalRowsFor pT held 100 (eraseFG C) = [a1, a2] := by
  decide +kernel

/-- Plan: old held rows have no expiry, including rows from old blocks. -/
theorem old_held : proposalRowsFor pT (atTime held 4000) 1000 .genesis = [a0, a1, a2] := by
  decide +kernel

/-- Plan R7: an absent parent yields no rows. -/
theorem absent_parent : proposalRowsFor pT held 3 (pb .genesis 4 33 []) = [] := by
  decide +kernel

/-- Plan: permutation law. Pool order changes selector order, not membership. -/
theorem reordered_pool :
    proposalRowsFor pT { held with rowPool := [a1, a0, a0] } 100 .genesis = [a1, a0, a2] ∧
    (proposalRowsFor pT held 100 .genesis).Perm
      (proposalRowsFor pT { held with rowPool := [a1, a0, a0] } 100 .genesis) := by
  constructor
  · decide +kernel
  · exact proposalRowsFor_perm pT (st := held) (st' := { held with rowPool := [a1, a0, a0] })
      rfl (List.Perm.swap _ _ _) (List.Perm.refl _) _ _

/-- Plan: packed-content laws. The selected signed list is the carried list. -/
theorem packed_content : rowsOk
    (pb .genesis 100 9 (proposalRowsFor pT held 100 .genesis))
    (proposalRowsFor pT held 100 .genesis) = true :=
  rowsOk_node_packBody _ _ _ _ _

/-- Plan: roots retain the ordered signed contents. A permutation need not
keep the block root; erasure does keep it. -/
theorem ordered_roots :
    (pk .genesis 100 9 [a0, a1, a2]).root ≠ (pk .genesis 100 9 [a1, a0, a2]).root ∧
    (eraseFG (pk .genesis 100 9 [a0, a1, a2])).root =
      (pk .genesis 100 9 [a0, a1, a2]).root := by
  constructor
  · decide +kernel
  · exact eraseFG_root _

/-- Plan: the payload has total accessors and a tagged, injective codec. -/
theorem payload_accessors :
    a2.payload.height_pair = a2.payload.height_pair ∧
    a2.payload.finality_pair = a2.payload.finality_pair ∧
    a2.payload.valid = a2.payload.valid ∧
    a2.payload.toRow (0 : Fin 4) =
      ⟨0, a2.payload.height_pair, a2.payload.finality_pair⟩ ∧
    encRowPayload a0.payload ≠ encRowPayload a2.payload := by decide

/-- Plan: bits persist while the height and entry stay fixed. -/
theorem progress_persists : 0 ∈ (derive pT.E pT.cfg (.node C 3 ⟨52⟩ 0 [])).progress := by
  decide +kernel

/-- Plan: the additive stored-row obligation holds for this R6-valid fixture. -/
theorem valid_stored : RowsValidStored pT held := by
  intro o ho s N hd
  change o ∈ [⟨.proposer 1, .proposal (namedLists (namedFixture C) [] [] [a0])⟩,
    ⟨.proposer 2, .proposal (namedLists (namedFixture D) [] [] [a2])⟩] at ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  all_goals
    simp only [Wire.decode, Option.some.injEq, Input.block.injEq] at hd
    obtain ⟨rfl, rfl⟩ := hd
    exact ⟨.genesis, by decide +kernel, by decide +kernel⟩

/-- Plan: all three bits retain their own tests. A timeout sets progress and
a matching finality bit, but it does not set target participation. -/
theorem timeout_bits :
    let σ : ChainState (Fin 4) := { ChainState.initial with h := 3, h_j := 2, h_F := 1 }
    let b := process_row σ ⟨0, .vote 3 genesisRoot true, some ⟨2, genesisRoot⟩⟩
    b.target_participation = ∅ ∧ b.progress = {0} ∧ b.finalize = {0} := by decide

/-- Plan: finality persists after a valid first inclusion below the row height.
This uses the R3/R6 specialization with a later matching finality pair. -/
theorem finality_persists :
    let a : RowWire 4 :=
      ⟨.seat .fg 0, .vote ⟨.vote 2 B1.root false, some ⟨1, genesisRoot⟩⟩⟩
    let C' := pk B1 2 0 [a]
    0 ∈ (derive pT.E pT.cfg (.node C' 3 ⟨53⟩ 0 [])).finalize := by
  decide +kernel

end M05

end AvailableChain.FGSA.Tests
end

-- ROOT-DIGEST: public fixture dependency audit.
#print axioms AvailableChain.FGSA.Tests.digestTable
#print axioms AvailableChain.FGSA.Tests.fixtureDigest
#print axioms AvailableChain.FGSA.Tests.literalFG
#print axioms AvailableChain.FGSA.Tests.smokeRootScope
#print axioms AvailableChain.FGSA.Tests.smoke_scope_parent_mem
#print axioms AvailableChain.FGSA.Tests.xBs

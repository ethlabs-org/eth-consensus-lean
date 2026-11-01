module
public import AvailableChainFGSA.Proofs.Port.VoteMerge -- shake: keep (examples)
public import AvailableChainFGSA.Model.Handlers -- shake: keep (examples)

public section

namespace AvailableChain.FGSA.Next.MergeTests

open AvailableChain.SimplexFG hiding B1 B2 B3 B1' B1a B1b childA X Y

/-! Local copies of the Smoke fixtures and their helpers. The complete digest
table preserves the admission behavior of stXs and stK. -/

namespace Fixtures

private def rw (_r : Nat) (i : Fin 4) (a : Row (Fin 4)) : RowWire 4 :=
  ⟨.seat .fg i,  .vote (RowBody.ofRow a)⟩

private def signRows (_r : Nat) (rs : List (Row (Fin 4))) : List (RowWire 4) :=
  rs.map (fun a => ⟨.seat .fg a.signer,  .vote (RowBody.ofRow a)⟩)

private def literalFG (P : FGBlock (Fin 4)) (s : Slot) (r : BlockId) (app : Nat)
    (rows : List (RowWire 4)) : FGBlock (Fin 4) :=
  .node P s r (packInner app rows) (rows.filterMap RowWire.toRow?)

private def B1 : FGBlock (Fin 4) := literalFG .genesis 1 ⟨1⟩ 0 (signRows 0 [rowT 0, rowT 1, rowT 2])

private def B2 : FGBlock (Fin 4) :=
  literalFG B1 2 ⟨4⟩ 0 (signRows 1 [rowAt 2 B1.root false 0, rowAt 2 B1.root false 1,
    rowAt 2 B1.root false 2])

private def rowB3' (i : Fin 4) : Row (Fin 4) := ⟨i, .vote 3 B2.root true, some ⟨2, B1.root⟩⟩

private def B3 : FGBlock (Fin 4) := literalFG B2 3 ⟨9⟩ 0 (signRows 1 [rowB3' 0, rowB3' 1, rowB3' 2])

private def B1' : FGBlock (Fin 4) :=
  literalFG .genesis 2 ⟨3⟩ 0 (signRows 0 [rowT 0, rowT 1, rowT 2])

private def B1a : FGBlock (Fin 4) := B1

private def childA : FGBlock (Fin 4) :=
  literalFG B1a 2 ⟨4⟩ 0 (signRows 1 [rowAt 2 B1a.root false 0, rowAt 2 B1a.root false 1,
    rowAt 2 B1a.root false 2])

private def B1b : FGBlock (Fin 4) :=
  literalFG .genesis 1 ⟨2⟩ 1 (signRows 0 [rowT 0, rowT 1, rowT 2])

private def Y : FGBlock (Fin 4) :=
  literalFG B1b 2 ⟨7⟩ 0 (signRows 1 [rowAt 2 B1b.root false 0, rowAt 2 B1b.root false 1,
    rowAt 2 B1b.root true 2])

private def X : FGBlock (Fin 4) := literalFG B1a 3 ⟨8⟩ 0 []

private def v2 : HeadWire 4 := ⟨.seat (.head 2) 0, B2.root⟩

private def rF : RowWire 4 := ⟨.seat .fg 3, .vote ⟨.vote 1 ⟨77⟩ true, none⟩⟩

private def r0 : RowWire 4 := ⟨.seat .fg 2, .vote ⟨.vote 0 genesisRoot false, none⟩⟩

private def r1 : RowWire 4 := ⟨.seat .fg 2, .vote ⟨.vote 1 genesisRoot false, none⟩⟩

private def vX : HeadWire 4 := ⟨.seat (.head 2) 1, B1'.root⟩

private def q (h : Nat) : RowWire 4 :=
  ⟨.seat .fg 3, .vote ⟨.vote 3 B2.root false, some ⟨h - 1, genesisRoot⟩⟩⟩

private def r0z : RowWire 4 := rw 0 3 (rowAt 3 B2.root true 3)

namespace M05

private def a0 : RowWire 4 := ⟨.seat .fg 0, .vote ⟨.vote 1 genesisRoot false, none⟩⟩

private def a1 : RowWire 4 := ⟨.seat .fg 0, .vote ⟨.vote 1 genesisRoot true, none⟩⟩

private def a2 : RowWire 4 :=
  ⟨.seat .fg 0, .vote ⟨.vote 1 genesisRoot false, some ⟨0, genesisRoot⟩⟩⟩

private def qW (i : Fin 4) : RowWire 4 := ⟨.seat .fg i, .vote ⟨.vote 1 genesisRoot false, none⟩⟩

end M05

private def digestTable : List (DigestInput 4 × BlockId) :=
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

private def fixtureDigest (d : DigestInput 4) : BlockId :=
  ((digestTable.find? (fun e => e.1 == d)).map Prod.snd).getD ⟨4095⟩

private abbrev pT : Params :=
  { Δ := 1, n := 4, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide, digest := fixtureDigest }

private def pb (P : Block) (s : Slot) (app : Nat) (rows : List (RowWire 4))
    (raw support : List (HeadWire 4) := []) : Block :=
  proposalBlock pT P s app raw support rows

private def namedFixture : FGBlock (Fin 4) → NamedProposal 4
  | .genesis => .genesis
  | .node P slot root app rows =>
      .node (namedFixture P) slot root (eraseFG (.node P slot root app rows)).body
        [] [] (rows.map (fun a => ⟨.seat .fg a.signer, .vote (RowBody.ofRow a)⟩))

private def namedLists (N : NamedProposal 4) (raw support : List (HeadWire 4))
    (rows : List (RowWire 4)) : NamedProposal 4 :=
  match N with
  | .genesis => .genesis
  | .node P slot root body _ _ _ => .node P slot root body raw support rows

private def namedBody (P : NamedProposal 4) (b : Block) (raw support : List (HeadWire 4))
    (rows : List (RowWire 4)) : NamedProposal 4 :=
  .node P b.slot b.root b.body raw support rows

private def b1' : Block := eraseFG B1'

private def rowsOf (_r : Nat) (B : FGBlock (Fin 4)) : List (RowWire 4) :=
  B.rows.map (fun a => ⟨.seat .fg a.signer,  .vote (RowBody.ofRow a)⟩)

private def wProp (B : FGBlock (Fin 4)) (r : Nat) (raw : List (HeadWire 4) := []) : Wire 4 :=
  ⟨.proposer B.slot, .proposal (namedLists (namedFixture B) raw [] (rowsOf r B))⟩

private def atTime (st : State pT.n) (t : Time) : State pT.n :=
  { st with base := { st.base with now := t } }

private def stK : State pT.n :=
  atTime (process pT
    (atTime ([wProp B1a 0, wProp childA 1, wProp B1b 0, wProp X 1].foldl (process pT)
      (atTime {} 12)) 16) (wProp Y 1)) 17

private def xBs : Block := pb b1' 3 96 [] [vX] [vX]

private def stXs : State pT.n :=
  [wProp B1 0, wProp B2 1, wProp B3 1].foldl (process pT)
    (process pT (atTime ([wProp B1' 0].foldl (process pT) (atTime {} 8)) 12)
      ⟨.proposer 3, .proposal (namedBody (namedFixture B1') xBs [vX] [vX] [])⟩)

end Fixtures

/-- Slot zero has the same genesis head for every parameter set. -/
theorem initial_head (p : Params) : headVoteNext p (initial p.n) 0 = .genesis := rfl

private abbrev p := Fixtures.pT
private def first : FGBlock (Fin 4) := .node .genesis 1 ⟨100⟩ 0 []
private def final : FGBlock (Fin 4) := .node first 2 ⟨101⟩ 0 []
private def above : FGBlock (Fin 4) := .node final 3 ⟨102⟩ 0 []
private def fork : FGBlock (Fin 4) := .node .genesis 3 ⟨103⟩ 0 []
private def proposal : FGBlock (Fin 4) := .node above 4 ⟨104⟩ 0 []
private def offProposal : FGBlock (Fin 4) := .node fork 4 ⟨105⟩ 0 []
private def future : FGBlock (Fin 4) := .node final 4 ⟨106⟩ 0 []
private def vote (i : Fin 4) (s : Slot) (r : BlockId) : HeadWire 4 :=
  ⟨.seat (.head s) i, r⟩
private def a := vote 0 3 above.root
private def b := vote 1 3 first.root
private def c := vote 0 3 fork.root
private def d := vote 2 3 ⟨999⟩
private def e := vote 3 3 future.root
private def wrong := vote 3 2 above.root
private def raw := [a, b, c, a, d, e, wrong]
private def support := [b, a, c, d, e, a, wrong]
private def carried (B : FGBlock (Fin 4)) (rs ss : List (HeadWire 4)) : Wire 4 :=
  ⟨.proposer B.slot,
    .proposal (Fixtures.namedBody (Fixtures.namedFixture B.parent) (eraseFG B) rs ss [])⟩

/-- Pure reader fixtures. These stores need no admission or execution premise. -/
private def st : State 4 :=
  { base := { GridCO.initial 4 .root with
      now := 17
      blocks := [.genesis, eraseFG first, eraseFG final, eraseFG above, eraseFG fork,
        eraseFG proposal, eraseFG offProposal, eraseFG future]
      votes := [baseVote d, baseVote a]
      voteStamp := [(baseVote d, 14), (baseVote a, 14)]
      blockStamp := [(eraseFG above, 15), (eraseFG fork, 15),
        (eraseFG proposal, 15), (eraseFG offProposal, 15), (eraseFG future, 15)] }
    fg := { Store.init with
      TF := {.genesis, first, final, above, fork, proposal, offProposal, future}, F := final }
    proposals := [carried offProposal [b] [b], carried proposal raw support,
      carried proposal [c, b] [a], carried above [e] [e]] }

/-- Only slot-4 proposals in the accepted tree supply lists; order is unchanged. -/
example : proposalsAtNext p st 4 = [(raw, support), ([c, b], [a])] ∧
    proposalsAt st 4 = [(raw, support), ([c, b], [a])] := by decide +kernel

/-- Raw participation includes unresolved, off-F, ancestor, and future heads.
Frozen votes precede carried votes; the first occurrence wins deduplication. -/
example : headVotesNext p st 4 = [baseVote d, baseVote a, baseVote b, baseVote c, baseVote e] ∧
    GridCO.voterCount (headVotesNext p st 4) = 4 ∧
    GridCO.equivocates (headVotesNext p st 4) 0 = true := by decide +kernel

/-- Carried support excludes ancestor, conflicting, unresolved, and future heads.
The retained head passes through its proposal even at the strict freeze boundary. -/
example : GridCO.resolvedHead? st.base (baseVote b) = some (eraseFG first) ∧
    GridCO.resolvedHead? st.base (baseVote c) = some (eraseFG fork) ∧
    headSupportNext p st 4 = [baseVote a] ∧
    GridCO.goldfishScore st.base.blocks (headVotesNext p st 4)
      (headSupportNext p st 4) (eraseFG fork) = 1 := by decide +kernel

/-- Only retained proposal ancestors enter the late voter arm. Off-F blocks
stay out even with a current-slot proposal. Early ancestors below F stay out too. -/
example : above ∈ voterBlocksNext p st 4 ∧ proposal ∈ voterBlocksNext p st 4 ∧
    first ∉ voterBlocksNext p st 4 ∧ fork ∉ voterBlocksNext p st 4 ∧
    offProposal ∉ voterBlocksNext p st 4 ∧ fork ∉ voterBlocks p st 4 := by decide +kernel

private def ordered : State 4 :=
  { st with
    base := { st.base with votes := [] }
    proposals := [carried proposal [vote 1 3 final.root, a, vote 1 3 final.root, a]
      [vote 1 3 final.root, a, vote 1 3 final.root, a]] }

/-- Distinct retained support heads keep their first-occurrence order too. -/
example : headVotesNext p ordered 4 = [baseVote (vote 1 3 final.root), baseVote a] ∧
    headSupportNext p ordered 4 = [baseVote (vote 1 3 final.root), baseVote a] := by
  decide +kernel

private def frozen : State 4 :=
  { st with proposals := [], base := { st.base with
      votes := [baseVote b, baseVote a]
      voteStamp := [(baseVote b, 14), (baseVote a, 15)]
      blockStamp := [(eraseFG first, 14), (eraseFG above, 14)] } }

/-- The minimal change keeps frozen ancestor support. A vote stamped exactly
at the freeze is absent from both frozen arms. -/
example : headVotesNext p frozen 4 = [baseVote b] ∧
    headSupportNext p frozen 4 = [baseVote b] ∧
    headSupportNext p frozen 4 = Legacy.headSupport p frozen 4 := by decide +kernel

private def collision : FGBlock (Fin 4) := .node final 3 first.root 0 []
private def ambiguous : State 4 :=
  { st with
    base := { st.base with blocks := st.base.blocks ++ [eraseFG collision], votes := [] }
    fg := { st.fg with TF := insert collision st.fg.TF }
    proposals := [carried proposal [b] [b]] }

/-- The retained collision cannot repair an ambiguous cumulative root. -/
example : GridCO.resolvedHead? ambiguous.base (baseVote b) = none ∧
    headVotesNext p ambiguous 4 = [baseVote b] ∧
    headSupportNext p ambiguous 4 = [] ∧
    Block.findByRoot? (erasedList ambiguous (tree p ambiguous)) first.root =
      some (eraseFG collision) := by decide +kernel

/-- Preserve the old admitted-state regression through the complete legacy chain. -/
example : Legacy.headSupport p Fixtures.stXs 3 = [baseVote Fixtures.vX] ∧
    headSupportNext p Fixtures.stXs 3 = [] ∧ headVotesNext p Fixtures.stXs 3 = [] := by
  decide +kernel

private def contest : State 4 :=
  { Fixtures.stK with
    fg := { Fixtures.stK.fg with F := Fixtures.B1a }
    base := { Fixtures.stK.base with
      votes := [baseVote (vote 0 3 Fixtures.B1a.root), baseVote (vote 0 3 Fixtures.Y.root)]
      voteStamp := [(baseVote (vote 0 3 Fixtures.B1a.root), 14),
        (baseVote (vote 0 3 Fixtures.Y.root), 14)] } }

/-- The late off-F top block contests only the legacy frame. The guarded
controls also reach the voter walk, which can now select the lower-band X. -/
example : (Legacy.controls p contest).contest = true ∧
    (controls p contest).contest = false ∧
    (controls p contest).H = (Legacy.controls p contest).H ∧
    (controls p contest).J = (Legacy.controls p contest).J ∧
    headVoteNext p contest 4 = eraseFG Fixtures.X ∧
    Legacy.headVote p contest 4 = eraseFG Fixtures.childA := by decide +kernel

/-- The slot-zero guard is preserved. -/
example : headVoteNext p st 0 = .genesis ∧ proposeNext p st 0 = none := by decide

end AvailableChain.FGSA.Next.MergeTests
end

module
public import AvailableChainFGSA.Proofs.CrossNode

@[expose] public section

namespace AvailableChain.FGSA.Tests.RootCollision

open AvailableChain.SimplexFG

/-! ROOT-DIGEST W3: finite full-content roots and collision controls. -/

/-- ROOT-DIGEST W3: action rounds do not change the fixed FG signature. -/
def rw (_r : Nat) (i : Fin 4) (a : Row (Fin 4)) : RowWire 4 :=
  ⟨.seat .fg i, .vote (RowBody.ofRow a)⟩

/-- ROOT-DIGEST W3: literal bodies precede the digest table. -/
def ba : Block := .node .genesis 4 ⟨1⟩ (packBody 0 ([] : List (RowWire 4)))
def c1 : Block := .node .genesis 1 ⟨2⟩ (packBody 0 ([] : List (RowWire 4)))
def bb : Block := .node c1 2 ⟨3⟩ (packBody 0 ([] : List (RowWire 4)))
def ra : RowWire 4 := rw 0 0 (rowT 0)
def rb : RowWire 4 := rw 0 1 (rowT 1)
def ha : HeadWire 4 := ⟨.seat (.head 0) 0, genesisRoot⟩
def hb : HeadWire 4 := ⟨.seat (.head 0) 1, genesisRoot⟩

/-- Full fixture parents keep their exact signed content. -/
def na : NamedProposal 4 := .node .genesis 4 ⟨1⟩ (packBody (n := 4) 0 []) [] [] []
def n1 : NamedProposal 4 := .node .genesis 1 ⟨2⟩ (packBody (n := 4) 0 []) [] [] []
def nb : NamedProposal 4 := .node n1 2 ⟨3⟩ (packBody (n := 4) 0 []) [] [] []

/-- ROOT-DIGEST W3: valid old/new inputs change one content field or one list. -/
def inputPairs : List (DigestInput 4 × DigestInput 4) :=
  [(⟨genesisRoot, 2, 0, [], [], []⟩, ⟨c1.root, 2, 0, [], [], []⟩),
   (⟨genesisRoot, 1, 0, [], [], []⟩, ⟨genesisRoot, 2, 0, [], [], []⟩),
   (⟨genesisRoot, 1, 0, [], [], []⟩, ⟨genesisRoot, 1, 1, [], [], []⟩),
   (⟨genesisRoot, 1, 0, [ra], [], []⟩, ⟨genesisRoot, 1, 0, [rb], [], []⟩),
   (⟨genesisRoot, 1, 0, [ra, rb], [], []⟩, ⟨genesisRoot, 1, 0, [rb, ra], [], []⟩),
   (⟨genesisRoot, 1, 0, [ra, rb], [], []⟩, ⟨genesisRoot, 1, 0, [ra, rb, ra], [], []⟩),
   (⟨genesisRoot, 1, 0, [], [ha, hb], []⟩,
      ⟨genesisRoot, 1, 0, [], [hb, ha], []⟩),
   (⟨genesisRoot, 1, 0, [], [ha, hb], []⟩,
      ⟨genesisRoot, 1, 0, [], [ha, hb, ha], []⟩),
   (⟨genesisRoot, 1, 0, [], [], []⟩, ⟨genesisRoot, 1, 0, [], [ha], []⟩),
   (⟨genesisRoot, 1, 0, [], [ha, hb], [ha, hb]⟩,
      ⟨genesisRoot, 1, 0, [], [ha, hb], [hb, ha]⟩),
   (⟨genesisRoot, 1, 0, [], [ha, hb], [ha, hb]⟩,
      ⟨genesisRoot, 1, 0, [], [ha, hb], [ha, hb, ha]⟩),
   (⟨genesisRoot, 1, 0, [], [ha, hb], []⟩,
      ⟨genesisRoot, 1, 0, [], [ha, hb], [ha]⟩)]

/-- ROOT-DIGEST W3: distinct full inputs have distinct positive table positions. -/
def digestInputs : List (DigestInput 4) :=
  [⟨genesisRoot, 4, 0, [], [], []⟩,
   ⟨genesisRoot, 1, 0, [], [], []⟩,
   ⟨c1.root, 2, 0, [], [], []⟩,
   ⟨genesisRoot, 1, 0, [ra], [], []⟩,
   ⟨genesisRoot, 0, 0, [], [], []⟩,
   ⟨genesisRoot, 2, 0, [], [], []⟩,
   ⟨genesisRoot, 1, 1, [], [], []⟩,
   ⟨genesisRoot, 1, 0, [rb], [], []⟩,
   ⟨genesisRoot, 1, 0, [ra, rb], [], []⟩,
   ⟨genesisRoot, 1, 0, [rb, ra], [], []⟩,
   ⟨genesisRoot, 1, 0, [ra, rb, ra], [], []⟩,
   ⟨genesisRoot, 1, 0, [], [ha, hb], []⟩,
   ⟨genesisRoot, 1, 0, [], [hb, ha], []⟩,
   ⟨genesisRoot, 1, 0, [], [ha, hb, ha], []⟩,
   ⟨genesisRoot, 1, 0, [], [ha], []⟩,
   ⟨genesisRoot, 1, 0, [], [ha, hb], [ha, hb]⟩,
   ⟨genesisRoot, 1, 0, [], [ha, hb], [hb, ha]⟩,
   ⟨genesisRoot, 1, 0, [], [ha, hb], [ha, hb, ha]⟩,
   ⟨genesisRoot, 1, 0, [], [ha, hb], [ha]⟩]

def fixtureDigest (d : DigestInput 4) : BlockId :=
  ⟨digestInputs.findIdx (fun e => e == d) + 1⟩

abbrev pT : Params :=
  { Δ := 1, n := 4, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide, digest := fixtureDigest }

def pb (P : Block) (s : Slot) (app : Nat) (rows : List (RowWire 4)) : Block :=
  proposalBlock pT P s app [] [] rows

def pk (P : FGBlock (Fin 4)) (s : Slot) (app : Nat) (rows : List (RowWire 4)) :
    FGBlock (Fin 4) := fgBlock P (pb (eraseFG P) s app rows) rows

/-- ROOT-DIGEST W3: smart constructors reproduce all three literal bodies. -/
theorem literal_bodies :
    pb .genesis 4 0 [] = ba ∧ pb .genesis 1 0 [] = c1 ∧ pb c1 2 0 [] = bb := by
  decide +kernel

/-- ROOT-DIGEST W3: the explicit table needs no runtime deduplication. -/
theorem digestInputs_nodup : digestInputs.Nodup := by decide +kernel

/-- ROOT-DIGEST W3: injectivity is restricted to this finite table. -/
theorem finite_digest_injective : ∀ d ∈ digestInputs, ∀ e ∈ digestInputs,
    fixtureDigest d = fixtureDigest e → d = e := by decide +kernel

/-- ROOT-DIGEST W3: The store at time 20, with no block. -/
def stT : State pT.n := clock pT (initial 4) 20
/- Honest slot-4 block on genesis: application value `0`, no rows. -/
/- Honest slot-1 block on genesis. -/
/-- ROOT-DIGEST W3: Honest slot-2 block on `c1`. -/
def wa : Wire 4 := ⟨.proposer 4, .proposal na⟩
def w1 : Wire 4 := ⟨.proposer 1, .proposal n1⟩
def wb : Wire 4 := ⟨.proposer 2, .proposal nb⟩
/-- ROOT-DIGEST W3: A node that received only `ba`. -/
def stX : State pT.n := process pT stT wa
/-- ROOT-DIGEST W3: A node that received `c1` and `bb`. -/
def stY : State pT.n := process pT (process pT stT w1) wb

/-- ROOT-DIGEST W3: The honest proposer's blocks pass the content check with their (empty) rows. -/
example : rowsOk ba ([] : List (RowWire 4)) = true ∧ rowsOk c1 ([] : List (RowWire 4)) = true ∧
    rowsOk bb ([] : List (RowWire 4)) = true := by decide +kernel

theorem reachable_stX : Reachable pT stX := .deliver _ (.tick _ .init)
theorem reachable_stY : Reachable pT stY := .deliver _ (.deliver _ (.tick _ .init))

theorem wa_mem : wa ∈ stX.proposals := by decide +kernel
theorem wb_mem : wb ∈ stY.proposals := by decide +kernel
theorem fg_ba : ∃ X ∈ stX.fg.TF, eraseFG X = ba := by decide +kernel
theorem fg_bb : ∃ Y ∈ stY.fg.TF, eraseFG Y = bb := by decide +kernel
/-- ROOT-DIGEST W3: (1) Both blocks are admitted: the stores are not trivial. -/
example : ba ∈ stX.base.blocks ∧ bb ∈ stY.base.blocks ∧ c1 ∈ stY.base.blocks := by
  decide +kernel

/-- ROOT-DIGEST W3: (1) The local invariants hold at both stores. -/
example : CStoreInv pT stX ∧ MetaInv pT stX ∧ CStoreInv pT stY ∧ MetaInv pT stY :=
  ⟨storeInvariant pT _ reachable_stX, metadataInvariant pT _ reachable_stX,
    storeInvariant pT _ reachable_stY, metadataInvariant pT _ reachable_stY⟩

/-- ROOT-DIGEST W3: (2) The two blocks have different parents, so they are different blocks, and
ROOT-DIGEST W3 assigns roots 1 and 3 to these two bodies. -/
theorem ba_root_ne_bb_root : ba.root ≠ bb.root := by decide +kernel

/-- ROOT-DIGEST W3: (2) `ContentAgree` holds on this pair: ROOT-DIGEST W3 checks roots on the two
    finite stores. -/
theorem contentAgree_stX_stY : ContentAgree stX stY :=
  contentAgree pT (metadataInvariant pT _ reachable_stX)
    (metadataInvariant pT _ reachable_stY) (by decide +kernel)

/-- ROOT-DIGEST W3: (2) The conclusion of `rootInjectiveOn_across` holds for this pair. -/
example : ∀ {B₁ B₂ : FGBlock (Fin 4)}, B₁ ∈ stX.fg.TF → B₂ ∈ stY.fg.TF →
    KitFG.RootInjectiveOn B₁ B₂ :=
  fun h₁ h₂ => rootInjectiveOn_across pT stX stY (storeInvariant pT _ reachable_stX)
    (storeInvariant pT _ reachable_stY) (metadataInvariant pT _ reachable_stX)
    (metadataInvariant pT _ reachable_stY) contentAgree_stX_stY h₁ h₂

/-- ROOT-DIGEST W3: The store of a node that holds `ba` and then receives `c1` and `bb`. -/
def stXY : State pT.n := process pT (process pT stX w1) wb

/-- ROOT-DIGEST W3: (3) A node that holds `ba` accepts `c1` and then `bb`. -/
example : ba ∈ stXY.base.blocks ∧ c1 ∈ stXY.base.blocks ∧ bb ∈ stXY.base.blocks ∧
    wb ∈ stXY.proposals := by decide +kernel

/-- ROOT-DIGEST W3: (3) A repeated `bb` is refused as a duplicate: nothing changes. -/
example : (process pT stXY wb).base.blocks = stXY.base.blocks ∧
    (process pT stXY wb).fg.TF = stXY.fg.TF ∧
    (process pT stXY wb).proposals = stXY.proposals := by decide +kernel

/-! ### Derived-root checks (r203 §8; Review Focus 2, 3, 5)

Each refusal has a companion that passes every other check, so the refusal
comes from the check that it names. -/

/-- ROOT-DIGEST W3: Genesis versus a slot-0 node: a node root is never the genesis root, also at
slot 0 and in the FG view. -/
example : (pb .genesis 0 0 []).root ≠ Block.genesis.root ∧
    (pk .genesis 0 0 []).root ≠ (FGBlock.genesis : FGBlock (Fin 4)).root :=
  by decide +kernel

/-- ROOT-DIGEST W3: The same parent and slot with different bodies give different roots. -/
example : (pb .genesis 1 0 []).root ≠ (pb .genesis 1 1 []).root :=
  by decide +kernel

/- A round-0 row of identity 0. -/
/-- ROOT-DIGEST W3: A slot-1 block that packs the row `ra`. -/
def bR : Block := pb .genesis 1 0 [ra]

def nR (rows : List (RowWire 4)) : NamedProposal 4 :=
  .node .genesis 1 bR.root bR.body [] [] rows

/-- ROOT-DIGEST W3: A wrong row list is refused, and both the base store and the FG store stay
unchanged: the wire carries the block `bR` (which packs `[ra]`) with no rows. The
companion wire with the right rows is accepted. -/
example : rowsOk bR ([] : List (RowWire 4)) = false ∧
    wellFormed pT ⟨.proposer 1, .proposal (nR [])⟩ = false ∧
    (process pT stT ⟨.proposer 1, .proposal (nR [])⟩).base.blocks = stT.base.blocks ∧
    (process pT stT ⟨.proposer 1, .proposal (nR [])⟩).fg.TF = stT.fg.TF ∧
    (process pT stT ⟨.proposer 1, .proposal (nR [])⟩).proposals = stT.proposals ∧
    rowsOk bR [ra] = true ∧ wellFormed pT ⟨.proposer 1, .proposal (nR [ra])⟩ = true ∧
    bR ∈ (process pT stT ⟨.proposer 1, .proposal (nR [ra])⟩).base.blocks := by
  decide +kernel

/-- ROOT-DIGEST W3: A body with the right signed-row code and a wrong outer decoded-row list:
`encFGBody (packInner 0 [ra]) []`. The content check refuses it, and both stores
and the stored wires stay unchanged. (The companion with the right decoded rows
is `bR`, above.) -/
def bW : Block := .node .genesis 1 ⟨4⟩ (encFGBody (packInner 0 [ra]) ([] : List (Row (Fin 4))))
def nW : NamedProposal 4 := .node .genesis 1 bW.root bW.body [] [] [ra]
example : appOf bW.body = 0 ∧ rowsOk bW [ra] = false ∧
    wellFormed pT ⟨.proposer 1, .proposal nW⟩ = false ∧
    (process pT stT ⟨.proposer 1, .proposal nW⟩).base.blocks = stT.base.blocks ∧
    (process pT stT ⟨.proposer 1, .proposal nW⟩).fg.TF = stT.fg.TF ∧
    (process pT stT ⟨.proposer 1, .proposal nW⟩).proposals = stT.proposals := by
  decide +kernel

/-- ROOT-DIGEST W3: The action round is absent from signed content and packed roots. -/
example : rw 0 0 (rowT 0) = rw 1 0 (rowT 0) ∧
    (pb .genesis 1 0 [rw 0 0 (rowT 0)]).root = (pb .genesis 1 0 [rw 1 0 (rowT 0)]).root := by
  exact ⟨rfl, rfl⟩

/-- ROOT-DIGEST W3: reconstruct the parent used by the finite input table. -/
def inputBody (d : DigestInput 4) (r : BlockId) : NamedProposal 4 :=
  .node (if d.parent = c1.root then n1 else .genesis) d.slot r (packBody d.app d.rows)
    d.raw d.support d.rows

/-- Reuse the failed content check instead of evaluating the digest a second time. -/
private theorem rejected_content (N : NamedProposal 4) (s : Slot)
    (h : contentOk pT N.erase N.raw N.support N.rows = false) :
    wellFormed pT ⟨.proposer s, .proposal N⟩ = false := by
  simp only [wellFormed, Wire.decode, h, Bool.and_false]

private theorem content_facts : ∀ e ∈ inputPairs,
    let stale := inputBody e.2 (fixtureDigest e.1)
    let fresh := inputBody e.2 (fixtureDigest e.2)
    rowsOk stale.erase e.2.rows = true ∧
    contentOk pT stale.erase e.2.raw e.2.support e.2.rows = false ∧
    contentOk pT fresh.erase e.2.raw e.2.support e.2.rows = true ∧
    wellFormed pT ⟨.proposer e.2.slot, .proposal fresh⟩ = true := by
  decide +kernel

/-- ROOT-DIGEST W3: every stale digest fails; each recomputed companion is valid. -/
theorem full_content_controls : ∀ e ∈ inputPairs,
    let stale := inputBody e.2 (fixtureDigest e.1)
    let fresh := inputBody e.2 (fixtureDigest e.2)
    rowsOk stale.erase e.2.rows = true ∧
    contentOk pT stale.erase e.2.raw e.2.support e.2.rows = false ∧
    wellFormed pT ⟨.proposer e.2.slot, .proposal stale⟩ = false ∧
    contentOk pT fresh.erase e.2.raw e.2.support e.2.rows = true ∧
    wellFormed pT ⟨.proposer e.2.slot, .proposal fresh⟩ = true := by
  intro e he
  obtain ⟨hrows, hstale, hfresh, hwf⟩ := content_facts e he
  exact ⟨hrows, hstale, rejected_content _ _ hstale, hfresh, hwf⟩


/-- ROOT-DIGEST W3: the recomputed companions pass actual block admission. -/
theorem full_content_admission : ∀ e ∈ inputPairs,
    let st := process pT stT w1
    let fresh := inputBody e.2 (fixtureDigest e.2)
    fresh.erase ∈ (process pT st
      ⟨.proposer e.2.slot, .proposal fresh⟩).base.blocks := by
  decide +kernel

abbrev aliasParams : Params := { pT with digest := fun d => ⟨d.slot + 1⟩ }
def parentA : NamedProposal 4 := namedProposal aliasParams .genesis 1 0 [ha] [] []
def parentB : NamedProposal 4 := namedProposal aliasParams .genesis 1 0 [hb] [] []
def parentStore : State 4 := process aliasParams (clock aliasParams (initial 4) 8)
  ⟨.proposer 1, .proposal parentA⟩
def aliasChild : NamedProposal 4 := namedProposal aliasParams parentB 2 0 [] [] []

/-- An equal erased parent cannot install a different named ancestor list. -/
theorem exact_parent_dependency : parentA.erase = parentB.erase ∧ parentA ≠ parentB ∧
    parentA ∈ parentStore.namedBodies ∧ parentB ∉ parentStore.namedBodies ∧
    namedParentHeld parentStore aliasChild = false ∧
    wellFormed aliasParams ⟨.proposer 2, .proposal aliasChild⟩ = true ∧
    (process aliasParams parentStore ⟨.proposer 2, .proposal aliasChild⟩).proposals =
      parentStore.proposals := by decide +kernel

#print axioms exact_parent_dependency


#print axioms full_content_admission

#print axioms digestInputs_nodup
#print axioms finite_digest_injective
#print axioms full_content_controls
#print axioms contentAgree_stX_stY

end AvailableChain.FGSA.Tests.RootCollision
end

-- ROOT-DIGEST: public fixture dependency audit.
#print axioms AvailableChain.FGSA.Tests.RootCollision.digestInputs
#print axioms AvailableChain.FGSA.Tests.RootCollision.fixtureDigest
#print axioms AvailableChain.FGSA.Tests.RootCollision.ha
#print axioms AvailableChain.FGSA.Tests.RootCollision.hb
#print axioms AvailableChain.FGSA.Tests.RootCollision.inputBody
#print axioms AvailableChain.FGSA.Tests.RootCollision.inputPairs
#print axioms AvailableChain.FGSA.Tests.RootCollision.literal_bodies
#print axioms AvailableChain.FGSA.Tests.RootCollision.pT
#print axioms AvailableChain.FGSA.Tests.RootCollision.pb
#print axioms AvailableChain.FGSA.Tests.RootCollision.pk
#print axioms AvailableChain.FGSA.Tests.RootCollision.rb
#print axioms AvailableChain.FGSA.Tests.RootCollision.rw

module
public import AvailableChainSA.Model.Protocol
public import AvailableChainPCSA.Model.ProposalContent
public import AvailableChainFGSA.Model.Objects
public import AvailableChainSimplexFG.Store
public import AvailableChainSimplexFG.Client

@[expose] public section

namespace AvailableChain.PCSA

open AvailableChain.Generic AvailableChain.SimplexFG

/-- [PC-SA M1; pcsa-v2-plan M0] The PC-SA parameters are the FG-SA
parameters (`Δ`, `n`, `k`, `η`, `R`, `δ_t`, `K_W`, the digest). The digest
reads the FG-SA digest input; `digestOf` embeds the PC-SA input
(`DigestInput.toFGSA`). -/
abbrev Params := FGSA.Params

/-- [PC-SA M1] The digest of a PC-SA digest input through the FG-SA digest. -/
def digestOf (p : Params) (d : DigestInput p.n) : BlockId := p.digest d.toFGSA

/-- [PC-SA M1; FG-SA Objects.lean Msg; pcsa-decisions 3n/4]
[spec 225–263; comp §4.2] A proposal carries its full named parent and signed
content. A HEAD and an ack carry only a root identifier; a PC carries its
acks and its resolved target. The geometric readers use named erasure. -/
inductive Msg (n : Nat) where
  | head (target : BlockId)
  | proposal (N : NamedProposal n)
  | row (body : RowPayload)
  | ack (target : BlockId)
  | pc (c : PC n)
  deriving DecidableEq, Repr

/-- [PC-SA M1] [spec 225–263; comp §4.2] A wire object: an auth and a payload. -/
abbrev Wire (n : Nat) := Signed Label n (Msg n)

/-- [PC-SA M1; FG-SA Objects.lean Input] [spec 505–518, 804–857; J1] A decoded
wire. A PC is unsigned (`.none`); its acks carry the signatures. -/
inductive Input (n : Nat) where
  | vote (s : Slot) (i : Fin n) (target : BlockId)
  | row (i : Fin n) (body : RowPayload)
  | block (s : Slot) (N : NamedProposal n)
  | ack (s : Slot) (i : Fin n) (target : BlockId)
  | pc (c : PC n)
  deriving DecidableEq, Repr

/-- [PC-SA M1; FG-SA Objects.lean Wire.decode]
[spec 505–518; J1] The one auth decoder of a wire. Every handler and the input check read
a wire only through `Wire.decode`, `HeadWire.decode?`, `RowWire.decode?` and
`AckWire.decode?`. -/
def Wire.decode {n : Nat} (o : Wire n) : Option (Input n) :=
  match o.auth, o.payload with
  | .seat (.head s) i, .head b => some (.vote s i b)
  | .seat .fg i, .row body => some (.row i body)
  | .proposer s, .proposal N => some (.block s N)
  | .seat ℓ i, .ack b => ℓ.ackSlot?.map (fun s => .ack s i b)
  | .none, .pc c => some (.pc c)
  | _, _ => none

/-- [PC-SA M1] [spec 248–255; helper] The block of a proposal wire. -/
def Wire.block? {n : Nat} (o : Wire n) : Option Block :=
  match o.decode with
  | some (.block _ N) => some N.erase
  | _ => none

/-- [PC-SA M1; FG-SA Objects.lean eraseFG]
[spec 248–263, 381–403; bp bp.carrier.v1] The geometric erasure of an FG block
(bp01 §2.1 `eraseFG`). The base body is the FG body code `encFGBody x rs`, so
the erasure copies the stored digest. -/
def eraseFG {V : Type} [RowCodec V] : FGBlock V → Block
  | .genesis => .genesis
  | .node p s r x rs => .node (eraseFG p) s r (encFGBody x rs)

/-! ### Signed content in the base body (D9)

A named proposal keeps its parent, body, ordered signed lists and carried PC.
The geometric body packs an application value and the ordered signed rows. It
does not encode the HEAD lists or the PC; the digest covers them. The FG view
of the block reads the same content: its body is the inner packed value and
its rows are the decoded rows. Every code is built from `epair` and `encList`
(`Objects/Codec.lean`); a sum is a pair of a constructor tag and its fields.
`encLabel` and `encAuth` are in `ProposalContent` (the digest embedding reads
them). -/

/-- [PC-SA M1] The row-body code: the height pair and the optional finality pair. -/
def encRowBody (a : RowBody) : Nat :=
  epair (encHeightPair a.height_pair) (encOption encFinalityPair a.finality_pair)

/-- [PC-SA M1] The vote tag and its complete body code. -/
def encRowPayload : RowPayload → Nat
  | .vote body => epair 0 (encRowBody body)

/-- [PC-SA M1] The signed-row code: the complete auth (fixed label and seat) and the
body. -/
def encRowWire {n : Nat} (a : RowWire n) : Nat := epair (encAuth a.auth) (encRowPayload a.payload)

/-- [PC-SA M1] The inner packed value: the application value and the ordered signed rows. -/
def packInner {n : Nat} (app : Nat) (rw : List (RowWire n)) : Nat :=
  epair app (encList encRowWire rw)

/-- [PC-SA M1] The packed base body: the FG body code of the inner packed value and the
decoded rows. -/
def packBody {n : Nat} (app : Nat) (rw : List (RowWire n)) : Nat :=
  encFGBody (packInner app rw) (rw.filterMap RowWire.toRow?)

/-- [PC-SA M1] The application value of a packed body (`appOf_packBody`). On a body that
is not packed the value has no meaning; `rowsOk` checks the full packing. -/
def appOf (x : Nat) : Nat := efst (efst (esnd x))

/-- [PC-SA M1; FG-SA Objects.lean rowsOk]
[D9] The content check of a proposal: the base body is the packing of its
own application value with the carried signed rows. It is a full
reconstruction check of the body, not a root check. `contentOk` adds the digest check for both
  admission paths. -/
def rowsOk {n : Nat} (b : Block) (rw : List (RowWire n)) : Bool :=
  b.body == packBody (appOf b.body) rw

/-- [PC-SA M1; pcsa-decisions R-e] Recover the full digest input, with the
carried PC. -/
def proposalInput {n : Nat} (b : Block) (raw support : List (HeadWire n))
    (rows : List (RowWire n)) (pc : Option (PC n)) : DigestInput n :=
  ⟨b.parent.root, b.slot, appOf b.body, rows, raw, support, pc⟩

/-- [PC-SA M1] Check the BODY codec and the supplied digest. -/
def contentOk (p : Params) (b : Block) (raw support : List (HeadWire p.n))
    (rows : List (RowWire p.n)) (pc : Option (PC p.n)) : Bool :=
  rowsOk b rows && b.root == digestOf p (proposalInput b raw support rows pc)

/-- [PC-SA M1] Construct a proposal with its full digest. -/
def proposalBlock (p : Params) (H : Block) (s : Slot) (app : Nat)
    (raw support : List (HeadWire p.n)) (rows : List (RowWire p.n)) (pc : Option (PC p.n)) :
    Block :=
  .node H s (digestOf p ⟨H.root, s, app, rows, raw, support, pc⟩) (packBody app rows)

/-- [PC-SA M1] Read the exact named payload. -/
def Wire.proposal? {n : Nat} (o : Wire n) : Option (NamedProposal n) :=
  match o.decode with
  | some (.block _ N) => some N
  | _ => none

/-- [PC-SA M1] Read the seven digest fields. -/
def NamedProposal.digestInput {n : Nat} (N : NamedProposal n) : DigestInput n :=
  ⟨N.parent.root, N.slot, appOf N.body, N.rows, N.raw, N.support, N.pc⟩

/-- [PC-SA M1] Check the supplied body and signed content. -/
def namedContentOk (p : Params) (N : NamedProposal p.n) : Bool :=
  contentOk p N.erase N.raw N.support N.rows N.pc

/-- [PC-SA M1] Keep the full parent in an honest proposal. -/
def namedProposal (p : Params) (P : NamedProposal p.n) (s : Slot) (app : Nat)
    (raw support : List (HeadWire p.n)) (rows : List (RowWire p.n)) (pc : Option (PC p.n)) :
    NamedProposal p.n :=
  .node P s (digestOf p ⟨P.root, s, app, rows, raw, support, pc⟩)
    (packBody app rows) raw support rows pc

/-- [PC-SA M1; FG-SA Objects.lean baseHead]
[spec 225–228; model representation of a carried vote in the SA base] The base
form of a carried vote: a HEAD seat of slot `s` becomes a
seat of base label `s`; any other auth becomes `.none`. -/
def baseHead {n : Nat} (o : HeadWire n) : GridCO.HeadWire n .root :=
  match o.decode? with
  | some (s, i, b) => ⟨.seat s i, b⟩
  | none => ⟨.none, o.payload⟩
/-- [PC-SA M1] [spec 225–228, 821–823] The base form of a carried vote as a GridCO vote wire. -/
def baseVote {n : Nat} (o : HeadWire n) : GridCO.Wire n .root := GridCO.fromHead (baseHead o)
/-- [PC-SA M1] [spec 1240–1249; helper] A base vote as a composite carried vote (for the
proposer's lists). It reads the GridCO accessors; it matches no auth. -/
def liftHead? {n : Nat} (o : GridCO.Wire n .root) : Option (HeadWire n) := do
  let s ← GridCO.headLabel? o
  let i ← GridCO.headSeat? o
  let b ← GridCO.headTarget? o
  pure ⟨.seat (.head s) i, b⟩
/-- [PC-SA M1] [spec 248–255, 820–823] The base proposal of a decoded composite proposal. -/
def baseProposal {n : Nat} (s : Slot) (b : Block) (raw support : List (HeadWire n)) :
    GridCO.Wire n .root :=
  ⟨.proposer s, .proposal b (raw.map baseHead) (support.map baseHead)⟩

-- ROOT-DIGEST-2 option 3: generate equations in their home module (BUILD B3a).
private theorem pcsa_Wire_block_eq_1_export :
    type_of% (@Wire.block?.eq_1) := @Wire.block?.eq_1
private theorem pcsa_Wire_decode_eq_1_export :
    type_of% (@Wire.decode.eq_1) := @Wire.decode.eq_1
private theorem pcsa_Wire_proposal_eq_1_export :
    type_of% (@Wire.proposal?.eq_1) := @Wire.proposal?.eq_1
private theorem pcsa_namedContentOk_eq_1_export :
    type_of% (@namedContentOk.eq_1) := @namedContentOk.eq_1
private theorem pcsa_namedProposal_eq_1_export :
    type_of% (@namedProposal.eq_1) := @namedProposal.eq_1
private theorem pcsa_proposalBlock_eq_1_export :
    type_of% (@proposalBlock.eq_1) := @proposalBlock.eq_1

end AvailableChain.PCSA
end

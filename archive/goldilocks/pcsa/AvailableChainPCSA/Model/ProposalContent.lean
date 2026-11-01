module
public import AvailableChainModel.Objects.Seats
public import AvailableChainSimplexFG.Objects
public import AvailableChainFGSA.Model.ProposalContent

@[expose] public section

namespace AvailableChain.PCSA

open AvailableChain.SimplexFG

/-- [PC-SA M1; FG-SA ProposalContent.lean:12]
[spec 197–220; pcsa-decisions 3n/4] Duty labels: the HEAD of slot `s`, the
fixed FG identity, and the exact ack of slot `s` (`ack s`). -/
inductive Label where
  | head (s : Slot)
  | fg
  | ack (s : Slot)
  deriving DecidableEq, Repr

/-- [PC-SA M1; pcsa34-v2-delta (4)] The slot of an ack label; `none` for the
other labels. Every definition that classifies acks reads this hook, so a
later second ack label extends it without a change of their text. -/
def Label.ackSlot? : Label → Option Slot
  | .ack s => some s
  | _ => none

/-- [PC-SA M1; FG-SA ProposalContent.lean:19]
[spec 230–237] An FG row without its identity: the height pair and
the finality pair. The identity is the seat index of the fixed FG signature. -/
structure RowBody where
  height_pair : NamedHeightPair
  finality_pair : Option FinalityPair
  deriving DecidableEq, Repr

/-- [PC-SA M1; FG-SA ProposalContent.lean:27] The body of an FG row: the row
without its signer. -/
def RowBody.ofRow {V : Type} (a : Row V) : RowBody := ⟨a.height_pair, a.finality_pair⟩

/-- [PC-SA M1; FG-SA ProposalContent.lean:32]
[R2/R3] A row needs a positive height. A present finality pair must
have a smaller height. An empty height pair is not a valid sent row. -/
def RowBody.valid (a : RowBody) : Bool :=
  match a.height_pair with
  | .empty => false
  | .vote h _ _ => decide (1 ≤ h) &&
      (a.finality_pair.map (fun fp => decide (fp.height < h))).getD true

/-- [PC-SA M1; FG-SA ProposalContent.lean:41]
[R3] The signed row payload. Finality rides on a vote at a greater height. -/
inductive RowPayload where
  | vote (body : RowBody)
  deriving DecidableEq, Repr

/-- [PC-SA M1] The height pair of the vote payload. -/
def RowPayload.height_pair : RowPayload → NamedHeightPair
  | .vote body => body.height_pair

/-- [PC-SA M1] The finality pair of the vote payload. -/
def RowPayload.finality_pair : RowPayload → Option FinalityPair
  | .vote body => body.finality_pair

/-- [PC-SA M1] The input check for the vote payload. -/
def RowPayload.valid : RowPayload → Bool
  | .vote body => body.valid

/-- [PC-SA M1] Decode the payload with the supplied signing identity. -/
def RowPayload.toRow {V : Type} (a : RowPayload) (i : V) : Row V :=
  ⟨i, a.height_pair, a.finality_pair⟩

/-- [PC-SA M1; FG-SA ProposalContent.lean:66]
[spec 225–228] A signed Goldfish vote, as a block carries it. -/
abbrev HeadWire (n : Nat) := Signed Label n BlockId
/-- [PC-SA M1; FG-SA ProposalContent.lean:69]
[spec 230–237] A signed FG row. Its auth is `.seat .fg i`. -/
abbrev RowWire (n : Nat) := Signed Label n RowPayload
/-- [PC-SA M1; pcsa34-r3 2.2] A signed exact ack: seat `i` of label `ack s`
signs the root identifier of the acked block. It may be unresolved. -/
abbrev AckWire (n : Nat) := Signed Label n BlockId

namespace HeadWire
variable {n : Nat}
/-- [PC-SA M1; FG-SA ProposalContent.lean:74]
[spec 225–228, 510–511; J1] The one auth decoder of a carried vote: label `s`,
seat `i`, head. -/
def decode? (o : HeadWire n) : Option (Slot × Fin n × BlockId) :=
  match o.auth with
  | .seat (.head s) i => some (s, i, o.payload)
  | _ => none
end HeadWire

namespace RowWire
variable {n : Nat}
/-- [PC-SA M1; FG-SA ProposalContent.lean:84]
[R1/R9] Decode the fixed FG seat and the full payload. -/
def decode? (a : RowWire n) : Option (Fin n × RowPayload) :=
  match a.auth with
  | .seat .fg i => some (i, a.payload)
  | _ => none
/-- [PC-SA M1] [spec 230–237; M4] The FG row: the signer is the seat index of the fg-label
signature. The round is not a field of the FG row. -/
def toRow? (a : RowWire n) : Option (Row (Fin n)) :=
  a.decode?.map (fun x => x.2.toRow x.1)
/-- [PC-SA M1] [spec 505–518; M12] The row input check: an FG signature and a valid body. -/
def valid (a : RowWire n) : Bool := (a.decode?.map (fun x => x.2.valid)).getD false
end RowWire

namespace AckWire
variable {n : Nat}
/-- [PC-SA M1; pcsa-decisions 3n/4] The one auth decoder of an ack: label
`s`, seat `i`, the acked block. -/
def decode? (a : AckWire n) : Option (Slot × Fin n × BlockId) :=
  match a.auth with
  | .seat ℓ i => ℓ.ackSlot?.map (fun s => (s, i, a.payload))
  | _ => none
/-- [PC-SA M1] The seat of an ack, if it has an ack auth. -/
def seat? (a : AckWire n) : Option (Fin n) := a.decode?.map (fun x => x.2.1)
end AckWire

/-- [PC-SA M1; pcsa-decisions 3n/4] `q_A = ⌈n/2⌉`: the PC quorum (the SA
release threshold). -/
def pcQuorum (n : Nat) : Nat := (n + 1) / 2

/-- [PC-SA M1; pcsa-decisions 3n/4] `q_N = ⌈3n/4⌉`: the ack trigger count. -/
def nQuorum (n : Nat) : Nat := (3 * n + 3) / 4

/-- [PC-SA M1; pcsa34-r3 2.3; SAPC Objects.lean PC] A PC: at least `q_A`
exact acks of slot `slot` with distinct seats on the root of `target`. A
node assembles it from its ack pool; it is never revoked. -/
structure PC (n : Nat) where
  slot : Slot
  target : Block
  acks : List (AckWire n)
  deriving DecidableEq, Repr

namespace PC
variable {n : Nat}
/-- [PC-SA M1] The distinct ack seats. -/
def seats (c : PC n) : List (Fin n) := (c.acks.filterMap AckWire.seat?).dedup
/-- [PC-SA M1; pcsa34-r3 2.3] The structural check: a positive slot, a
non-genesis target of that slot, at least `q_A` acks with pairwise distinct
seats, each an exact ack of label `ack slot` on the root of the target. -/
def wellFormed (c : PC n) : Bool :=
  0 < c.slot && c.target != .genesis && c.target.slot == c.slot &&
    pcQuorum n ≤ c.acks.length && c.seats.length == c.acks.length &&
    c.acks.all (fun a => match a.decode? with
      | some (s, _, r) => s == c.slot && r == c.target.root
      | none => false)
end PC

/-- [PC-SA M1; pcsa34-r4.3 §3.7] The PC rank stored with a lease.
Compare `slot`, then `depth`, then `root`. -/
structure PCRank where
  slot : Slot
  depth : Nat
  root : BlockId
  deriving DecidableEq, Repr

/-- [PC-SA M1; pcsa34-r4.3 §3.7] Read the rank of a PC. -/
def PC.rank {n : Nat} (c : PC n) : PCRank :=
  ⟨c.slot, c.target.depth, c.target.root⟩

theorem PC.rank_def {n : Nat} (c : PC n) :
    c.rank = ⟨c.slot, c.target.depth, c.target.root⟩ := rfl

/-- [PC-SA M1; pcsa34-r4.3 §3.7] Test `rank(c) ≥ ρ`. Every PC rank
is greater than the empty rank `none`. -/
def rankAtLeast {n : Nat} (c : PC n) (ρ : Option PCRank) : Bool :=
  ρ.all (fun r => !(c.slot < r.slot || (c.slot == r.slot &&
    (c.target.depth < r.depth || (c.target.depth == r.depth && c.target.root < r.root)))))

theorem rankAtLeast_def {n : Nat} (c : PC n) (ρ : Option PCRank) :
    rankAtLeast c ρ = ρ.all (fun r => !(c.slot < r.slot || (c.slot == r.slot &&
      (c.target.depth < r.depth || (c.target.depth == r.depth && c.target.root < r.root))))) := rfl

/-- [PC-SA M1; pcsa-decisions R-f; SAPC Choice.lean preferPC] The PC rank
`(slot, depth, root)`: `a` ranks below `b`. -/
def pcBelow {n : Nat} (a b : PC n) : Bool :=
  a.slot < b.slot || (a.slot == b.slot && (a.target.depth < b.target.depth ||
    (a.target.depth == b.target.depth && a.target.root < b.target.root)))

/-- [PC-SA M1; SAPC Choice.lean:7–17] Keep the higher-ranked PC; keep the
existing one on a tie. -/
def preferPC {n : Nat} (old : Option (PC n)) (candidate : PC n) : Option (PC n) :=
  match old with
  | none => some candidate
  | some previous => if pcBelow previous candidate then some candidate else old

/-- [PC-SA M1; FG-SA ProposalContent.lean:107; DC NamedBlocks] Full recursive
proposal identity. The proposal carries the proposer's latest PC (`pc`). -/
inductive NamedProposal (n : Nat) where
  | genesis
  | node (parent : NamedProposal n) (slot : Slot) (root : BlockId)
      (body : Nat) (raw support : List (HeadWire n)) (rows : List (RowWire n))
      (pc : Option (PC n))
  deriving DecidableEq, Repr

namespace NamedProposal
variable {n : Nat}

/-- [PC-SA M1] Read the root field. -/
def root : NamedProposal n → BlockId
  | .genesis => genesisRoot
  | .node _ _ r _ _ _ _ _ => r

/-- [PC-SA M1] Read the slot field. -/
def slot : NamedProposal n → Slot
  | .genesis => 0
  | .node _ s _ _ _ _ _ _ => s

/-- [PC-SA M1] Read the parent field. -/
def parent : NamedProposal n → NamedProposal n
  | .genesis => .genesis
  | .node P _ _ _ _ _ _ _ => P

/-- [PC-SA M1] Read the body field. -/
def body : NamedProposal n → Nat
  | .genesis => 0
  | .node _ _ _ x _ _ _ _ => x

/-- [PC-SA M1] Read the raw field. -/
def raw : NamedProposal n → List (HeadWire n)
  | .genesis => []
  | .node _ _ _ _ xs _ _ _ => xs

/-- [PC-SA M1] Read the support field. -/
def support : NamedProposal n → List (HeadWire n)
  | .genesis => []
  | .node _ _ _ _ _ xs _ _ => xs

/-- [PC-SA M1] Read the rows field. -/
def rows : NamedProposal n → List (RowWire n)
  | .genesis => []
  | .node _ _ _ _ _ _ xs _ => xs

/-- [PC-SA M1; pcsa-decisions R-e] Read the carried PC. -/
def pc : NamedProposal n → Option (PC n)
  | .genesis => none
  | .node _ _ _ _ _ _ _ c => c

/-- [PC-SA M1] The acks of the carried PC (empty without a PC). -/
def pcAcks (N : NamedProposal n) : List (AckWire n) := (N.pc.map PC.acks).getD []

/-- [PC-SA M1; DC NamedBlocks.erase] Project proposal geometry. -/
def erase : NamedProposal n → Block
  | .genesis => .genesis
  | .node P s r x _ _ _ _ => .node P.erase s r x

/-- [PC-SA M1; DC NamedBlocks.preceq] Test full named ancestry. -/
def preceq (A : NamedProposal n) : NamedProposal n → Bool
  | .genesis => decide (A = .genesis)
  | B@(.node P _ _ _ _ _ _ _) => decide (A = B) || preceq A P

/-- [PC-SA M1; DC NamedBlocks.Preceq] Full named ancestry. -/
def Preceq (A B : NamedProposal n) : Prop := preceq A B = true

end NamedProposal

/-- [PC-SA M1; FG-SA ProposalContent.lean:165; pcsa-decisions R-e] The seven
full proposal fields: the six FG-SA fields and the carried PC. The signed
lists keep their order and duplicates. -/
structure DigestInput (n : Nat) where
  parent : BlockId
  slot : Slot
  app : Nat
  rows : List (RowWire n)
  raw : List (HeadWire n)
  support : List (HeadWire n)
  pc : Option (PC n)
  deriving DecidableEq, Repr

/-! ### The digest through the FG-SA parameters

`Params` is `FGSA.Params`, whose digest reads the six-field FG-SA input over
the FG-SA labels. The PC-SA digest input is embedded injectively: labels map
`head s ↦ head (2s)`, `ack s ↦ head (2s + 1)`, `fg ↦ fg`; the PC code joins
the application value. -/

/-- [PC-SA M1] The injective label map into the FG-SA labels. -/
def Label.toFGSA : Label → FGSA.Label
  | .head s => .head (2 * s)
  | .fg => .fg
  | .ack s => .head (2 * s + 1)

/-- [PC-SA M1] The injective auth map into the FG-SA auths. -/
def authToFGSA {n : Nat} : Auth Label n → Auth FGSA.Label n
  | .seat ℓ i => .seat ℓ.toFGSA i
  | .proposer s => .proposer s
  | .none => .none

/-- [PC-SA M1] A HEAD wire over the FG-SA labels. -/
def HeadWire.toFGSA {n : Nat} (o : HeadWire n) : FGSA.HeadWire n := ⟨authToFGSA o.auth, o.payload⟩

/-- [PC-SA M1] A row body over the FG-SA row body. -/
def RowBody.toFGSA (a : RowBody) : FGSA.RowBody := ⟨a.height_pair, a.finality_pair⟩

/-- [PC-SA M1] A row payload over the FG-SA row payload. -/
def RowPayload.toFGSA : RowPayload → FGSA.RowPayload
  | .vote body => .vote body.toFGSA

/-- [PC-SA M1] A row wire over the FG-SA labels. -/
def RowWire.toFGSA {n : Nat} (a : RowWire n) : FGSA.RowWire n :=
  ⟨authToFGSA a.auth, a.payload.toFGSA⟩

/-- [PC-SA M1; FG-SA Objects.lean encLabel] The label code: tag `0` for a
HEAD label, tag `1` for an FG label, tag `2` for an ack label. -/
def encLabel : Label → Nat
  | .head s => epair 0 s
  | .fg => epair 1 0
  | .ack s => epair 2 s

/-- [PC-SA M1; FG-SA Objects.lean encAuth] The auth code: tag `0` for a seat
(label and index), tag `1` for a proposer (slot), tag `2` for no auth. -/
def encAuth {n : Nat} : Auth Label n → Nat
  | .seat ℓ i => epair 0 (epair (encLabel ℓ) i.val)
  | .proposer s => epair 1 s
  | .none => epair 2 0

/-- [PC-SA M1] The code of an erased block: tag `0` for genesis; tag `1`
with the parent code, slot, root value and body. -/
def encBlock : Block → Nat
  | .genesis => epair 0 0
  | .node P s r x => epair 1 (epair (encBlock P) (epair s (epair r.value x)))

/-- [PC-SA M1] The code of an ack wire: its auth and the root value. -/
def encAckWire {n : Nat} (a : AckWire n) : Nat := epair (encAuth a.auth) a.payload.value

/-- [PC-SA M1] The code of a PC: slot, target, and the ack list. -/
def encPC {n : Nat} (c : PC n) : Nat :=
  epair c.slot (epair (encBlock c.target) (encList encAckWire c.acks))

/-- [PC-SA M1] The embedding of the digest input into the FG-SA digest
input: the PC code joins the application value. -/
def DigestInput.toFGSA {n : Nat} (d : DigestInput n) : FGSA.DigestInput n :=
  ⟨d.parent, d.slot, epair d.app (encOption encPC d.pc), d.rows.map RowWire.toFGSA,
    d.raw.map HeadWire.toFGSA, d.support.map HeadWire.toFGSA⟩

-- ROOT-DIGEST-2 option 3: generate equations in their home module (BUILD B3a).
private theorem pcsa_NamedProposal_Preceq_eq_1_export :
    type_of% (@NamedProposal.Preceq.eq_1) := @NamedProposal.Preceq.eq_1
private theorem pcsa_NamedProposal_erase_eq_1_export :
    type_of% (@NamedProposal.erase.eq_1) := @NamedProposal.erase.eq_1
private theorem pcsa_NamedProposal_erase_eq_2_export :
    type_of% (@NamedProposal.erase.eq_2) := @NamedProposal.erase.eq_2
private theorem pcsa_NamedProposal_erase_eq_def_export :
    type_of% (@NamedProposal.erase.eq_def) := @NamedProposal.erase.eq_def
private theorem pcsa_NamedProposal_preceq_eq_1_export :
    type_of% (@NamedProposal.preceq.eq_1) := @NamedProposal.preceq.eq_1
private theorem pcsa_NamedProposal_preceq_eq_2_export :
    type_of% (@NamedProposal.preceq.eq_2) := @NamedProposal.preceq.eq_2
private theorem pcsa_NamedProposal_preceq_eq_def_export :
    type_of% (@NamedProposal.preceq.eq_def) := @NamedProposal.preceq.eq_def

end AvailableChain.PCSA
end

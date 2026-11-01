module
public import AvailableChainModel.Objects.Seats
public import AvailableChainSimplexFG.Objects

@[expose] public section

namespace AvailableChain.FGSA

open AvailableChain.SimplexFG

/-- [ROOT-DIGEST-2 W1; DC NamedBlocks and RootInjectiveOnAncestors]
[spec 197–220; comp §4.2; model representation of the duty labels] Duty labels: the HEAD of
slot `s` and the fixed FG identity. -/
inductive Label where
  | head (s : Slot)
  | fg
  deriving DecidableEq, Repr

/-- [ROOT-DIGEST-2 W1; DC NamedBlocks and RootInjectiveOnAncestors]
[spec 230–237] An FG row without its identity: the height pair and
the finality pair. The identity is the seat index of the fixed FG signature. -/
structure RowBody where
  height_pair : NamedHeightPair
  finality_pair : Option FinalityPair
  deriving DecidableEq, Repr

/-- [ROOT-DIGEST-2 W1; DC NamedBlocks and RootInjectiveOnAncestors]
[spec 230–237; model representation of a row without its signer] The body of an FG
row: the row without its signer. -/
def RowBody.ofRow {V : Type} (a : Row V) : RowBody := ⟨a.height_pair, a.finality_pair⟩

/-- [ROOT-DIGEST-2 W1; DC NamedBlocks and RootInjectiveOnAncestors]
[R2/R3] A row needs a positive height. A present finality pair must
have a smaller height. An empty height pair is not a valid sent row. -/
def RowBody.valid (a : RowBody) : Bool :=
  match a.height_pair with
  | .empty => false
  | .vote h _ _ => decide (1 ≤ h) &&
      (a.finality_pair.map (fun fp => decide (fp.height < h))).getD true

/-- [ROOT-DIGEST-2 W1; DC NamedBlocks and RootInjectiveOnAncestors]
[R3] The signed row payload. Finality rides on a vote at a greater height. -/
inductive RowPayload where
  | vote (body : RowBody)
  deriving DecidableEq, Repr

/-- [ROOT-DIGEST-2 W1; DC NamedBlocks and RootInjectiveOnAncestors]
The height pair of the vote payload. -/
def RowPayload.height_pair : RowPayload → NamedHeightPair
  | .vote body => body.height_pair

/-- [ROOT-DIGEST-2 W1; DC NamedBlocks and RootInjectiveOnAncestors]
The finality pair of the vote payload. -/
def RowPayload.finality_pair : RowPayload → Option FinalityPair
  | .vote body => body.finality_pair

/-- [ROOT-DIGEST-2 W1; DC NamedBlocks and RootInjectiveOnAncestors]
The input check for the vote payload. -/
def RowPayload.valid : RowPayload → Bool
  | .vote body => body.valid

/-- [ROOT-DIGEST-2 W1; DC NamedBlocks and RootInjectiveOnAncestors]
Decode the payload with the supplied signing identity. -/
def RowPayload.toRow {V : Type} (a : RowPayload) (i : V) : Row V :=
  ⟨i, a.height_pair, a.finality_pair⟩

/-- [ROOT-DIGEST-2 W1; DC NamedBlocks and RootInjectiveOnAncestors]
[spec 225–228] A signed Goldfish vote, as a block carries it. -/
abbrev HeadWire (n : Nat) := Signed Label n BlockId
/-- [ROOT-DIGEST-2 W1; DC NamedBlocks and RootInjectiveOnAncestors]
[spec 230–237] A signed FG row. Its auth is `.seat .fg i`. -/
abbrev RowWire (n : Nat) := Signed Label n RowPayload

namespace HeadWire
variable {n : Nat}
/-- [ROOT-DIGEST-2 W1; DC NamedBlocks and RootInjectiveOnAncestors]
[spec 225–228, 510–511; J1] The one auth decoder of a carried vote: label `s`,
seat `i`, head. -/
def decode? (o : HeadWire n) : Option (Slot × Fin n × BlockId) :=
  match o.auth with
  | .seat (.head s) i => some (s, i, o.payload)
  | _ => none
end HeadWire

namespace RowWire
variable {n : Nat}
/-- [ROOT-DIGEST-2 W1; DC NamedBlocks and RootInjectiveOnAncestors]
[R1/R9] Decode the fixed FG seat and the full payload. -/
def decode? (a : RowWire n) : Option (Fin n × RowPayload) :=
  match a.auth with
  | .seat .fg i => some (i, a.payload)
  | _ => none
/-- [ROOT-DIGEST-2 W1; DC NamedBlocks and RootInjectiveOnAncestors]
[spec 230–237; M4] The FG row: the signer is the seat index of the fg-label
signature. The round is not a field of the FG row. -/
def toRow? (a : RowWire n) : Option (Row (Fin n)) :=
  a.decode?.map (fun x => x.2.toRow x.1)
/-- [ROOT-DIGEST-2 W1; DC NamedBlocks and RootInjectiveOnAncestors]
[spec 505–518; M12] The row input check: an FG signature and a valid body. -/
def valid (a : RowWire n) : Bool := (a.decode?.map (fun x => x.2.valid)).getD false
end RowWire

/-- [ROOT-DIGEST-2 W1; DC NamedBlocks] Full recursive proposal identity. -/
inductive NamedProposal (n : Nat) where
  | genesis
  | node (parent : NamedProposal n) (slot : Slot) (root : BlockId)
      (body : Nat) (raw support : List (HeadWire n)) (rows : List (RowWire n))
  deriving DecidableEq, Repr

namespace NamedProposal
variable {n : Nat}

/-- [ROOT-DIGEST-2 W1; DC NamedBlocks] Read the root field. -/
def root : NamedProposal n → BlockId
  | .genesis => genesisRoot
  | .node _ _ r _ _ _ _ => r

/-- [ROOT-DIGEST-2 W1; DC NamedBlocks] Read the slot field. -/
def slot : NamedProposal n → Slot
  | .genesis => 0
  | .node _ s _ _ _ _ _ => s

/-- [ROOT-DIGEST-2 W1; DC NamedBlocks] Read the parent field. -/
def parent : NamedProposal n → NamedProposal n
  | .genesis => .genesis
  | .node P _ _ _ _ _ _ => P

/-- [ROOT-DIGEST-2 W1; DC NamedBlocks] Read the body field. -/
def body : NamedProposal n → Nat
  | .genesis => 0
  | .node _ _ _ x _ _ _ => x

/-- [ROOT-DIGEST-2 W1; DC NamedBlocks] Read the raw field. -/
def raw : NamedProposal n → List (HeadWire n)
  | .genesis => []
  | .node _ _ _ _ xs _ _ => xs

/-- [ROOT-DIGEST-2 W1; DC NamedBlocks] Read the support field. -/
def support : NamedProposal n → List (HeadWire n)
  | .genesis => []
  | .node _ _ _ _ _ xs _ => xs

/-- [ROOT-DIGEST-2 W1; DC NamedBlocks] Read the rows field. -/
def rows : NamedProposal n → List (RowWire n)
  | .genesis => []
  | .node _ _ _ _ _ _ xs => xs

/-- [ROOT-DIGEST-2 W1; DC NamedBlocks.erase] Project proposal geometry. -/
def erase : NamedProposal n → Block
  | .genesis => .genesis
  | .node P s r x _ _ _ => .node P.erase s r x

/-- [ROOT-DIGEST-2 W1; DC NamedBlocks.preceq] Test full named ancestry. -/
def preceq (A : NamedProposal n) : NamedProposal n → Bool
  | .genesis => decide (A = .genesis)
  | B@(.node P _ _ _ _ _ _) => decide (A = B) || preceq A P

/-- [ROOT-DIGEST-2 W1; DC NamedBlocks.Preceq] Full named ancestry. -/
def Preceq (A B : NamedProposal n) : Prop := preceq A B = true

end NamedProposal

/-- [ROOT-DIGEST-2 W1; DC NamedBlocks] The six full proposal fields.
The signed lists keep their order and duplicates. -/
structure DigestInput (n : Nat) where
  parent : BlockId
  slot : Slot
  app : Nat
  rows : List (RowWire n)
  raw : List (HeadWire n)
  support : List (HeadWire n)
  deriving DecidableEq, Repr

-- ROOT-DIGEST-2 option 3: generate equations in their home module (BUILD B3a).
private theorem NamedProposal_Preceq_eq_1_export :
    type_of% (@NamedProposal.Preceq.eq_1) := @NamedProposal.Preceq.eq_1
private theorem NamedProposal_erase_eq_1_export :
    type_of% (@NamedProposal.erase.eq_1) := @NamedProposal.erase.eq_1
private theorem NamedProposal_erase_eq_2_export :
    type_of% (@NamedProposal.erase.eq_2) := @NamedProposal.erase.eq_2
private theorem NamedProposal_erase_eq_def_export :
    type_of% (@NamedProposal.erase.eq_def) := @NamedProposal.erase.eq_def
private theorem NamedProposal_preceq_eq_1_export :
    type_of% (@NamedProposal.preceq.eq_1) := @NamedProposal.preceq.eq_1
private theorem NamedProposal_preceq_eq_2_export :
    type_of% (@NamedProposal.preceq.eq_2) := @NamedProposal.preceq.eq_2
private theorem NamedProposal_preceq_eq_def_export :
    type_of% (@NamedProposal.preceq.eq_def) := @NamedProposal.preceq.eq_def

end AvailableChain.FGSA
end

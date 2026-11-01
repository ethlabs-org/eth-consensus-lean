module
public import AvailableChainFGSA.Model.Objects

@[expose] public section

namespace AvailableChain.FGSA.Spec

/-! Pure representation for spec d7a094e5 (WP12a; initially S0-C).

Lean's `NamedProposal` has no proposer field. `Block.representation` and
`BlockCorresponds` carry a separate list of proposer indices for the entire parent chain.
Only this complete representation is injective on arbitrary blocks. Raw `Block.embed`
and `Wire.embed` erase these indices. Ancestry after erasure requires `Block.Assigned`.
On the spec side, `.proposer s` denotes a valid slot-s signature by the block's declared
proposer; `.none` includes invalid signatures. The admission check compares that identity
with the assigned proposer (line 720). `deliveryWire` maps this refusal to absent Lean auth.
It is a refusal adapter, not an identity-preserving cryptographic encoding.

Modeled functions: block digest and wire checks; the first two `state_transition`
assertions, separate from the wire check; `ac_valid_payload`; `fg_to_ac`
with root and height-floor parameters; `viable_tree`; lock-entry projection,
live locks and expiry; record normalization and `advance`; `fg_on_attestation`
pool insertion; the refusal shell of `on_block`; tick step composition and
schedule times. No saved-head field is kept. The AC stores geometric block names;
the wire type below keeps complete recursive signed content. These names need
the usual admitted-store/root-uniqueness relation in a later simulation.

Not modeled: `fg_contest`, `head_height_floor`, `get_fc_root`, `is_viable`,
`has_viable_descendant`, `update_finality`, full `state_transition`,
`valid_attestation`, `process_attestation`, `process_height_events`,
`advance_height`, `fg_attest`, `finality_pair`, `height_pair`,
`create_attestation`, `record_attestation`, `proposal_attestations`,
`propose_block`, `attest`, full `fg_on_block`, full `on_block`,
`on_ac_message`, `on_attestation`, `ac_on_message`, `ac_on_block`,
`on_goldfish_vote`, full `on_tick` and `ac_on_tick`, `ac_proposal`, `ac_to_fg`,
`resolution_time`, `revoke_locks`, `update_confirmation`, `goldfish_score`,
`ghost`, `goldfish_eligible`, `goldfish_fork_choice`, `get_anchor`,
`get_head_in_tree`, `get_head`, `voter_block_tree`, `goldfish_vote`, `ac_head`,
and `ac_confirmed`. No run, sleep, output or claim correspondence is asserted.
Later run correspondence is restricted to the ordered, initialized,
always-awake fragment with immediate self-deliveries and fixed seat maps.
Frame correspondence uses only `FGSA.Next` readers and unchanged model parts.
`Transitions` adds the confirmation split and lock-update kernels with explicit
score inputs. These kernels do not assert a full handler or run correspondence.
-/

/-- [spec 237–258, 947–967] Full recursive block, with no application field.
The root is supplied, not recomputed: invalid and colliding deliveries remain expressible.
Proposer indices use the fixed validator set `Fin n`. -/
inductive Block (n : Nat) where
  | genesis
  | node (parent : Block n) (slot : Slot) (proposer : Fin n) (root : BlockId)
      (rows : List (RowWire n)) (raw support : List (HeadWire n))
  deriving DecidableEq, Repr

/-- [spec 237–245] The supplied root, including the genesis convention. -/
def Block.root {n : Nat} : Block n → BlockId
  | .genesis => genesisRoot
  | .node _ _ _ r _ _ _ => r

/-- [spec 237–245] The declared slot. -/
def Block.slot {n : Nat} : Block n → Slot
  | .genesis => 0
  | .node _ s _ _ _ _ _ => s

/-- [spec 237–242] The exact parent, including all its signed lists. -/
def Block.parent {n : Nat} : Block n → Block n
  | .genesis => .genesis
  | .node P _ _ _ _ _ _ => P

/-- [spec 237–258, 954–967] Embed every ancestor and every supplied signed list.
The Lean-only application value is zero at every node. -/
def Block.embed {n : Nat} : Block n → NamedProposal n
  | .genesis => .genesis
  | .node P s _ r rows raw support =>
      .node P.embed s r (packBody 0 rows) raw support rows

/-- [spec 238] Proposer identities from this node through all named ancestors. -/
def Block.identities {n : Nat} : Block n → List (Fin n)
  | .genesis => []
  | .node P _ i _ _ _ _ => i :: P.identities

/-- [spec 237–258] Complete representation: Lean content and separate proposer identities. -/
def Block.representation {n : Nat} (B : Block n) : NamedProposal n × List (Fin n) :=
  (B.embed, B.identities)

/-- [spec 237–258] The relation retains identities absent from Lean's named block. -/
def BlockCorresponds {n : Nat} (B : Block n) (N : NamedProposal n)
    (ids : List (Fin n)) : Prop := B.representation = (N, ids)

/-- [spec 720] Assigned identities for every ancestor; needed only for identity erasure. -/
def Block.Assigned {n : Nat} (assigned : Slot → Fin n) : Block n → Prop
  | .genesis => True
  | .node P s i _ _ _ _ => i = assigned s ∧ P.Assigned assigned

/-- [spec 237–245, 468–495] The FG carrier of a full spec block.
Raw and support lists stay in the named store, as in the unchanged Lean representation. -/
def Block.toFG {n : Nat} : Block n → SimplexFG.FGBlock (Fin n)
  | .genesis => .genesis
  | .node P s _ r rows _ _ =>
      .node P.toFG s r (packInner 0 rows) (rows.filterMap RowWire.toRow?)

/-- [spec 260–265] Exact named ancestry, including full signed ancestor content. -/
def Block.preceq {n : Nat} (A : Block n) : Block n → Bool
  | .genesis => decide (A = .genesis)
  | B@(.node P _ _ _ _ _ _) => decide (A = B) || Block.preceq A P

/-- [spec 249–258, 947–967] All payload kinds, before signature checks. -/
inductive Msg (n : Nat) where
  | head (target : BlockId)
  | proposal (B : Block n)
  | row (body : RowPayload)
  deriving DecidableEq, Repr

/-- [spec 249–258] Keep valid, absent, and mismatched authentication. -/
abbrev Wire (n : Nat) := Signed Label n (Msg n)

/-- [spec 249–258, 947–967] Raw erasure; `Wire.identities` retains proposer indices. -/
def Wire.embed {n : Nat} (o : Wire n) : FGSA.Wire n :=
  ⟨o.auth, match o.payload with
    | .head r => .head r
    | .proposal B => .proposal B.embed
    | .row a => .row a⟩

/-- [spec 238, 249–258] The identities omitted by the raw wire erasure. -/
def Wire.identities {n : Nat} (o : Wire n) : List (Fin n) :=
  match o.payload with
  | .proposal B => B.identities
  | _ => []

/-- [spec 249–258] Authenticated inputs; rejected auth is not an input. -/
inductive Input (n : Nat) where
  | vote (s : Slot) (i : Fin n) (target : BlockId)
  | row (i : Fin n) (body : RowPayload)
  | block (s : Slot) (B : Block n)
  deriving DecidableEq, Repr

/-- [spec 249–258] Signature decoding before the stateless payload tests. -/
def Wire.decode {n : Nat} (o : Wire n) : Option (Input n) :=
  match o.auth, o.payload with
  | .seat (.head s) i, .head r => some (.vote s i r)
  | .seat .fg i, .row a => some (.row i a)
  | .proposer s, .proposal B => some (.block s B)
  | _, _ => none

/-- [spec 249–258] Embed a decoded input without accepting a rejected object. -/
def Input.embed {n : Nat} : Input n → FGSA.Input n
  | .vote s i r => .vote s i r
  | .row i a => .row i a
  | .block s B => .block s B.embed

private theorem specBlockPreceq_eq_1_export :
    type_of% (@Block.preceq.eq_1) := @Block.preceq.eq_1
private theorem specBlockPreceq_eq_2_export :
    type_of% (@Block.preceq.eq_2) := @Block.preceq.eq_2
private theorem specBlockPreceq_eq_def_export :
    type_of% (@Block.preceq.eq_def) := @Block.preceq.eq_def

-- Generate equations in their owning model module (BUILD B3a).
private theorem Block_root_eq_1_export :
    type_of% (@Block.root.eq_1) := @Block.root.eq_1
private theorem Block_root_eq_2_export :
    type_of% (@Block.root.eq_2) := @Block.root.eq_2
private theorem Block_root_eq_def_export :
    type_of% (@Block.root.eq_def) := @Block.root.eq_def
private theorem Block_slot_eq_1_export :
    type_of% (@Block.slot.eq_1) := @Block.slot.eq_1
private theorem Block_slot_eq_2_export :
    type_of% (@Block.slot.eq_2) := @Block.slot.eq_2
private theorem Block_slot_eq_def_export :
    type_of% (@Block.slot.eq_def) := @Block.slot.eq_def
private theorem Block_parent_eq_1_export :
    type_of% (@Block.parent.eq_1) := @Block.parent.eq_1
private theorem Block_parent_eq_2_export :
    type_of% (@Block.parent.eq_2) := @Block.parent.eq_2
private theorem Block_parent_eq_def_export :
    type_of% (@Block.parent.eq_def) := @Block.parent.eq_def
private theorem Block_embed_eq_1_export :
    type_of% (@Block.embed.eq_1) := @Block.embed.eq_1
private theorem Block_embed_eq_2_export :
    type_of% (@Block.embed.eq_2) := @Block.embed.eq_2
private theorem Block_embed_eq_def_export :
    type_of% (@Block.embed.eq_def) := @Block.embed.eq_def
private theorem Block_toFG_eq_1_export :
    type_of% (@Block.toFG.eq_1) := @Block.toFG.eq_1
private theorem Block_toFG_eq_2_export :
    type_of% (@Block.toFG.eq_2) := @Block.toFG.eq_2
private theorem Block_toFG_eq_def_export :
    type_of% (@Block.toFG.eq_def) := @Block.toFG.eq_def
private theorem Wire_embed_eq_1_export :
    type_of% (@Wire.embed.eq_1) := @Wire.embed.eq_1
private theorem Wire_decode_eq_1_export :
    type_of% (@Wire.decode.eq_1) := @Wire.decode.eq_1
private theorem Input_embed_eq_1_export :
    type_of% (@Input.embed.eq_1) := @Input.embed.eq_1
private theorem Input_embed_eq_2_export :
    type_of% (@Input.embed.eq_2) := @Input.embed.eq_2
private theorem Input_embed_eq_3_export :
    type_of% (@Input.embed.eq_3) := @Input.embed.eq_3
private theorem Input_embed_eq_def_export :
    type_of% (@Input.embed.eq_def) := @Input.embed.eq_def

private theorem spec_Block_identities_eq_1_export :
    type_of% (@Block.identities.eq_1) := @Block.identities.eq_1

private theorem spec_Block_identities_eq_2_export :
    type_of% (@Block.identities.eq_2) := @Block.identities.eq_2

private theorem spec_Block_identities_eq_def_export :
    type_of% (@Block.identities.eq_def) := @Block.identities.eq_def

private theorem spec_Block_representation_eq_1_export :
    type_of% (@Block.representation.eq_1) := @Block.representation.eq_1

private theorem spec_BlockCorresponds_eq_1_export :
    type_of% (@BlockCorresponds.eq_1) := @BlockCorresponds.eq_1

private theorem spec_Block_Assigned_eq_1_export :
    type_of% (@Block.Assigned.eq_1) := @Block.Assigned.eq_1

private theorem spec_Block_Assigned_eq_2_export :
    type_of% (@Block.Assigned.eq_2) := @Block.Assigned.eq_2

private theorem spec_Block_Assigned_eq_def_export :
    type_of% (@Block.Assigned.eq_def) := @Block.Assigned.eq_def

private theorem spec_Wire_identities_eq_1_export :
    type_of% (@Wire.identities.eq_1) := @Wire.identities.eq_1

end AvailableChain.FGSA.Spec
end

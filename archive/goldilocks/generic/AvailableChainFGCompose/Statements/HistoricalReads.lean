module
public import AvailableChainFGCompose.Statements.CoreReads
public import AvailableChainGeneric.Statements.Pure.CommonAncestor -- shake: keep (re-export)

@[expose] public section

namespace AvailableChain.FGCompose

/-- Resolve one distinct full body. Identical copies do not create ambiguity. -/
def historicalLookup {Body : Type} [DecidableEq Body]
    (root : Body → BlockId) (bodies : List Body) (r : BlockId) : Option Body :=
  match (bodies.filter (fun b => root b == r)).eraseDups with
  | [b] => some b
  | _ => none

theorem historicalLookup_def {Body : Type} [DecidableEq Body]
    (root : Body → BlockId) (bodies : List Body) (r : BlockId) :
    historicalLookup root bodies r =
      (match (bodies.filter (fun b => root b == r)).eraseDups with
       | [b] => some b
       | _ => none) := rfl

/-- Reads over cumulative accepted storage, independent of the active frame. -/
structure FGHistoricalReads (State Body : Type) where
  acceptedBlocks : State → Finset Block
  acceptedBodies : State → List Body
  erase : Body → Block
  root : Body → BlockId
  parent : Body → Body
  slot : Body → Slot
  readBlock : State → BlockId → Option Body
  preceq : Body → Body → Prop
  depth : Body → Nat
  lca : Body → Body → Block

/-- Every protocol transition that must retain accepted full content. -/
inductive FGHistoryStep {In : Type} (P : V2.ProtocolSpecD In) : P.State → P.State → Prop
  | process (st : P.State) (o : P.Object) : FGHistoryStep P st (P.process st o)
  | own (st : P.State) (o : P.Object) : FGHistoryStep P st (P.recordOwn st o)
  | clock (st : P.State) (t : Time) : FGHistoryStep P st (P.clock st t)
  | restore (st : P.State) (t : Time) : FGHistoryStep P st (P.restore (P.durable st) t)

variable {In Body : Type} {P : V2.ProtocolSpecD In}
variable {n : Nat} {Base Proposal Wire : Type}

/-- Store laws hold on Good states. Lookup handles every domain, including malformed ones. -/
structure FGHistoricalLaws (R : FGCoreReads P n Base Proposal Wire)
    (H : FGHistoricalReads P.State Body) (Good : P.State → Prop) : Prop where
  blocks_eq : ∀ st, Good st →
    H.acceptedBlocks st = (R.core st).fg.TF.image R.erase
  bodies_eq : ∀ st, Good st → ∀ B,
    B ∈ H.acceptedBlocks st ↔ ∃ b ∈ H.acceptedBodies st, H.erase b = B
  root_eq : ∀ b, H.root b = (H.erase b).root
  parent_eq : ∀ b, H.erase (H.parent b) = (H.erase b).parent
  slot_eq : ∀ b, H.slot b = (H.erase b).slot
  parent_closed : ∀ st, Good st → ∀ b ∈ H.acceptedBodies st,
    H.parent b ∈ H.acceptedBodies st
  read_iff : ∀ st r b, H.readBlock st r = some b ↔
    b ∈ H.acceptedBodies st ∧ H.root b = r ∧
      ∀ c ∈ H.acceptedBodies st, H.root c = r → c = b
  reachable_unique : ∀ st, Good st → ∀ b ∈ H.acceptedBodies st,
    ∀ c ∈ H.acceptedBodies st, H.root b = H.root c → b = c
  geometry_eq : (∀ b c, H.preceq b c ↔ Block.Preceq (H.erase b) (H.erase c)) ∧
    (∀ b, H.depth b = (H.erase b).depth) ∧
    (∀ b c, H.lca b c = Block.meet (H.erase b) (H.erase c))
  step_keep : ∀ st st', FGHistoryStep P st st' → ∀ b ∈ H.acceptedBodies st,
    b ∈ H.acceptedBodies st'
  restore_eq : ∀ st t,
    H.acceptedBodies (P.restore (P.durable st) t) = H.acceptedBodies st ∧
    H.acceptedBlocks (P.restore (P.durable st) t) = H.acceptedBlocks st
  frame_independent : ∀ st st', H.acceptedBodies st = H.acceptedBodies st' →
    ∀ r, H.readBlock st r = H.readBlock st' r

end AvailableChain.FGCompose
end

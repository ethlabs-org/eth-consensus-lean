module
public import AvailableChainPCSA.Model.Store

@[expose] public section

namespace AvailableChain.PCSA

open AvailableChain.Generic AvailableChain.SimplexFG

/-! The PC operations of the store (pcsa34-r3 §2.3, §3.6; SAPC
`Model/Certificates.lean` templates) and the N count of the ack trigger
(§3.4 A1). A PC enters the store only by assembly from the ack pool: a
received PC wire and a carried PC contribute their acks. The ack rule itself
(`ackFor`, A1 and A2) is in `Frame` (A2 reads the frame); a later second ack
label adds its own trigger beside it. -/

variable {n : Nat}

/-- [PC-SA M1; pcsa34-r3 2.3, 2.6] A PC the store accepts: well formed, with a
target in the cumulative tree (usable) and compatible with F. -/
def pcValid (st : State n) (c : PC n) : Bool :=
  c.wellFormed && decide (c.target ∈ st.base.blocks) && activeCompatible st c.target

/-- [PC-SA M1; pcsa34-r4.3 §3.7 (iii)] Delete every lease whose target
conflicts with the new PC and whose stored rank is at most its rank. -/
def deleteConflictingLeases (st : State n) (c : PC n) : State n :=
  { st with base := { st.base with
    obligations := st.base.obligations.filter (fun row =>
      !(rankAtLeast c (leaseRank st row.1) && !Block.compatible c.target row.1)) } }

theorem deleteConflictingLeases_def (st : State n) (c : PC n) :
    deleteConflictingLeases st c =
      { st with base := { st.base with
        obligations := st.base.obligations.filter (fun row =>
          !(rankAtLeast c (leaseRank st row.1) && !Block.compatible c.target row.1)) } } := rfl

/-- [PC-SA M1; pcsa34-r4.3 §3.6 on_pc, §3.7 (iii)] Accept a PC unless
its slot and target are held. Record its first acceptance time, then delete
conflicting leases at or below its rank. All PC admission paths use this step. -/
def installPC (st : State n) (c : PC n) : State n :=
  if st.pcs.any (fun o => o.slot == c.slot && o.target == c.target) then st
  else deleteConflictingLeases { st with
    pcs := st.pcs ++ [c]
    pcStamps := st.pcStamps.filter (fun row => !(row.1 == c.slot && row.2.1 == c.target.root)) ++
      [(c.slot, c.target.root, st.base.now)] } c

theorem installPC_def (st : State n) (c : PC n) :
    installPC st c =
      (if st.pcs.any (fun o => o.slot == c.slot && o.target == c.target) then st
       else deleteConflictingLeases { st with
         pcs := st.pcs ++ [c]
         pcStamps := st.pcStamps.filter
           (fun row => !(row.1 == c.slot && row.2.1 == c.target.root)) ++
             [(c.slot, c.target.root, st.base.now)] } c) := rfl

/-- [PC-SA M1; SAPC firstPerSeat] Scan in receipt order; retain the first ack
of each seat. -/
def firstPerSeat (acks : List (AckWire n)) : List (AckWire n) :=
  acks.foldl (fun acc a =>
    if acc.any (fun old => old.seat? == a.seat?) then acc else acc ++ [a]) []

/-- [PC-SA M1] The pooled exact acks of slot `s` on the root `r`. -/
def acksOn (st : State n) (s : Slot) (r : BlockId) : List (AckWire n) :=
  st.ackPool.filter (fun a => match a.decode? with
    | some (s', _, r') => s' == s && r' == r
    | none => false)

/-- [PC-SA M1] The pooled acks of seat `i` at slot `s`, by distinct root. -/
def seatAcks (st : State n) (s : Slot) (i : Fin n) : List BlockId :=
  (st.ackPool.filterMap (fun a => match a.decode? with
    | some (s', i', r) => if s' == s && i' == i then some r else none
    | none => none)).eraseDups

/-- [PC-SA M1; pcsa34-r3 3.6 try_assemble] Assemble `PC(s, b)` from the pooled
acks on the root of `b`, one per seat, if the result is valid. -/
def assemblePC (st : State n) (s : Slot) (b : Block) : Option (PC n) :=
  let c : PC n := ⟨s, b, firstPerSeat (acksOn st s b.root)⟩
  if pcValid st c then some c else none

/-- [PC-SA M1; pcsa34-r3 3.6] Assemble and install every PC the pool
supports, in the order of the pool's `(slot, root)` candidates; a root
resolves in the cumulative tree. -/
def collectPCs (st : State n) : State n :=
  let candidates := (st.ackPool.filterMap (fun a =>
    a.decode?.map (fun x => (x.1, x.2.2)))).eraseDups
  candidates.foldl (fun acc sr =>
    match acc.base.blocks.find? (fun b => b.root == sr.2) with
    | none => acc
    | some b =>
      match assemblePC acc sr.1 b with
      | none => acc
      | some c => installPC acc c) st

/-- [PC-SA M1; review fix 1 (D4)] Pool one copy of a decodable ack with no
acceptance limit: the acks of a well-formed PC (received or carried) enter
the pool whole, as r3 `on_pc` accepts a valid PC whole, so a faulty seat's
earlier acks cannot keep a valid PC out of the store. -/
def poolAckRaw {n : Nat} (st : State n) (a : AckWire n) : State n :=
  match a.decode? with
  | some _ => if a ∈ st.ackPool then st else { st with ackPool := st.ackPool ++ [a] }
  | none => st

/-- [PC-SA M1; review fix 2] The slot test of an ack on a resolved root: the
block of slot `s` only (`B.slot = s`; spec r4). An unresolved root passes
(it can only join a PC through `pcValid`, which tests the slot). -/
def ackSlotOK {n : Nat} (st : State n) (s : Slot) (r : BlockId) : Bool :=
  match st.base.blocks.find? (fun b => b.root == r) with
  | some b => b.slot == s
  | none => true

/-- [PC-SA M1; pcsa34-r3 2.6, 3.6 on_ack] Pool one copy of a decodable ack
of a slot `≤ Σ.s` on a slot-`s` block (or an unresolved root), unless the
pool holds two distinct acks of its seat at its slot. No PC assembly. -/
def poolAck (p : Params) (st : State p.n) (a : AckWire p.n) : State p.n :=
  match a.decode? with
  | some (s, i, r) =>
      if st.slot p < s || !ackSlotOK st s r || a ∈ st.ackPool then st else
      if 2 ≤ (seatAcks st s i).length && !decide (r ∈ seatAcks st s i) then st else
      { st with ackPool := st.ackPool ++ [a] }
  | none => st

/-- [PC-SA M1; pcsa34-r3 3.4 A1; pcsa34-v2-delta (2)] The timely slot-`s`
HEADs of a base view: the label-`s` votes resolved before `e_s`
(`GridCO.earlyVotes`), without the seats that equivocate in the slot-`s`
pool. -/
def timelyHeads (p : Params) (v : GridCO.State p.n .root) (s : Slot) :
    List (GridCO.Wire p.n .root) :=
  (GridCO.earlyVotes p.toParams.engine v s).filter (fun o =>
    match GridCO.headSeat? o with
    | some i => !GridCO.equivocates (GridCO.votesAt v s) i
    | none => false)

/-- [PC-SA M1; pcsa34-r3 3.4 A1] `N_s(B)`: the number of distinct
non-equivocating seats with a timely slot-`s` HEAD whose head is exactly `B`. -/
def nCount (p : Params) (v : GridCO.State p.n .root) (s : Slot) (b : Block) : Nat :=
  (GridCO.seats p.n ((timelyHeads p v s).filter (fun o =>
    GridCO.resolvedHead? v o == some b))).length

/-- [PC-SA M1; pcsa34-r3 R2] `N_s(B) ≥ q_N`. -/
def holdsN (p : Params) (v : GridCO.State p.n .root) (s : Slot) (b : Block) : Bool :=
  decide (nQuorum p.n ≤ nCount p v s b)

/-- [PC-SA M1; pcsa34-r3 3.8; review fix 2] The N target of slot `s` on the
active view: the first timely head of slot `s` (`B.slot = s`, as
`PC.wellFormed` needs; spec r4) with `holdsN`. Two N targets of one slot need
`2⌈3n/4⌉ − n ≥ ⌈n/2⌉` equivocating seats, so under `a < ⌈n/2⌉` the choice
by `find?` is unreachable and the target is unique (r3 5.1; lead decision
G4). The active view gives `B ∈ Σ.T` and `B` compatible with `F`. -/
def nTarget? (p : Params) (st : State p.n) (s : Slot) : Option Block :=
  let v := actView st
  ((timelyHeads p v s).filterMap (GridCO.resolvedHead? v)).find? (fun b =>
    b.slot == s && holdsN p v s b)

end AvailableChain.PCSA
end

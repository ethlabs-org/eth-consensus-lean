module
public import AvailableChainFGSA.Model.Spec.ACState

@[expose] public section

namespace AvailableChain.FGSA.Spec

/-- [spec 1101–1104] Expire lock entries before any scheduled AC duty. -/
def expire (A : ACState n) (t : Time) : ACState n :=
  { A with locks := A.locks.filter (fun e => decide (t < e.2)) }

/-- [spec 1274–1283] `advance`: keep an in-tree record on an ancestor candidate. -/
def advance (tree : List AvailableChain.Block) (old : AvailableChain.Block)
    (candidate : Option AvailableChain.Block) : AvailableChain.Block :=
  match candidate with
  | none => old
  | some C => if old ∈ tree && AvailableChain.Block.preceq C old then old else C

/-- [spec 544–546] Append a new attestation once, in first-acceptance order.
Authentication and row validity are checked before this spec function. -/
def insertRow {n : Nat} (pool : List (RowWire n)) (a : RowWire n) : List (RowWire n) :=
  if a ∈ pool then pool else pool ++ [a]

/-- [spec 412–418, 527–541] Pure refusal shell. A failed FG step performs no AC step.
The supplied FG function must itself compute without writes on refusal. -/
def onBlock {σ α : Type} (future : Bool) (fg : σ → Option σ) (ac : α → α)
    (state : σ × α) : σ × α :=
  if future then state else
    match fg state.1 with
    | none => state
    | some next => (next, ac state.2)

/-- [spec 221–231, 370–375, 400–409] Pure tick order with scheduled steps as parameters.
Each step sees the previous step's result; no execution or delivery claim is made. -/
def tick {σ : Type} (setClock ac proposal attest : σ → σ) (state : σ) : σ :=
  attest (proposal (ac (setClock state)))

/-- [spec 924–945] Slot start, extended to integer slots for negative empty pools. -/
def slotTime (Δ : Time) (s : Int) : Time := 4 * Δ * s

/-- [spec 930–935] A scheduled phase at an offset from a slot start. -/
def phaseTime (Δ : Time) (s : Int) (offset : Int) : Time := slotTime Δ s + offset * Δ

/-- [d7a094e5: ac_on_tick] The call sites supply the evaluated slot, s-1.
The callbacks include the vote's immediate self-delivery. Public times are integers. -/
def acOnTick {σ : Type} (Δ : Time) (s : Slot) (t : Time)
    (expireStep : Time → σ → σ) (revoke vote confirm : Slot → σ → σ) (state : σ) : σ :=
  let state := expireStep t state
  let state := if t = phaseTime Δ s 1 then
    vote s (if 0 < s then revoke (s - 1) state else state) else state
  if t = phaseTime Δ s 2 ∧ 0 < s then confirm (s - 1) state else state

/-- [d7a094e5: confirmation_score] Distinct voters of the evaluated pool. -/
def confirmationVoters (votes : List (HeadWire n)) : List (Fin n) :=
  (votes.filterMap (fun v => v.decode?.map (fun x => x.2.1))).eraseDups

/-- [d7a094e5: confirmation_score] Count early supporters, excluding equivocators.
`early` is the strict resolution-time and prefix test for the candidate block.
The pool contains only votes of the evaluated slot. Duplicate copies do not equivocate. -/
def confirmationScore (votes : List (HeadWire n)) (early : HeadWire n → Bool) : Nat :=
  ((confirmationVoters votes).filter (fun i =>
    let own := (votes.filter (fun v =>
      v.decode?.any (fun x => x.2.1 == i))).eraseDups
    own.length == 1 && own.any early)).length

/-- [d7a094e5: get_confirmation] The score is supplied by `confirmationScore`.
The final strict-majority test applies to F as well as its descendants. -/
def getConfirmation (tree : List AvailableChain.Block) (F : AvailableChain.Block)
    (voters : Nat) (score : AvailableChain.Block → Nat) : Option AvailableChain.Block :=
  let eligible := fun B => decide (voters < 2 * score B)
  let H := GridCO.ghost F tree score eligible
  if eligible H then some H else none

/-- Deepest block, with the fixed root order as the tie breaker. -/
def deepestBlock (blocks : List AvailableChain.Block) : Option AvailableChain.Block :=
  blocks.foldl (fun best B => match best with
    | none => some B
    | some C => if C.depth < B.depth || (C.depth == B.depth && C.root < B.root)
        then some B else some C) none

/-- [d7a094e5: update_confirmation] Pure write kernel after score calculation.
It saves the result before a veto, clears fast_confirmed on each call, and writes
one top lock. The evaluated slot is s, not the current slot s+1. -/
def updateConfirmation (tree : List AvailableChain.Block) (F : AvailableChain.Block)
    (Δ : Time) (k committeeSize : Nat) (s : Int) (t : Time)
    (score : AvailableChain.Block → Nat) (A : ACState n) : ACState n :=
  let result := getConfirmation tree F (confirmationVoters (A.pool s)).length score
  let next : ACState n := { A with
    saved := fun j => if j = s then result else A.saved j
    fast_confirmed := [] }
  match result with
  | none => next
  | some C =>
      if (liveEntries tree t A.locks).any (fun e => !AvailableChain.Block.compatible e.1 C)
      then next else
        let path := tree.filter (fun B => B != .genesis && AvailableChain.Block.preceq B C)
        let fast := fun B => decide (committeeSize ≤ 2 * score B)
        let slow := fun B => (List.range (k - 1)).all (fun j =>
          (A.saved (s - (j + 1 : Nat))).any (fun D =>
            decide (D ∈ tree) && AvailableChain.Block.preceq B D))
        let top := deepestBlock (path.filter (fun B => fast B || slow B))
        { next with
          record := advance tree A.record result
          fast_confirmed := path.filter fast
          locks := A.locks ++ top.toList.map (fun B => (B, phaseTime Δ (s + k) 5)) }

/-- [d7a094e5: revoke_locks] Pure move-back kernel; opponent counts come from
resolved, non-equivocating votes of the evaluated slot. Deadlines stay fixed. -/
def revokeLocks (tree : List AvailableChain.Block) (t : Time) (committeeSize : Nat)
    (opponents : AvailableChain.Block → Nat) (A : ACState n) : ACState n :=
  { A with locks := (liveEntries tree t A.locks).filterMap (fun e =>
      (deepestBlock (tree.filter (fun B => B != .genesis &&
        AvailableChain.Block.preceq B e.1 &&
        decide (2 * opponents B < committeeSize)))).map (fun B => (B, e.2))) }

-- Generate equations in their owning model module (BUILD B3a).
private theorem specExpire_eq_1_export :
    type_of% (@expire.eq_1) := @expire.eq_1
private theorem advance_eq_1_export :
    type_of% (@advance.eq_1) := @advance.eq_1
private theorem insertRow_eq_1_export :
    type_of% (@insertRow.eq_1) := @insertRow.eq_1
private theorem onBlock_eq_1_export :
    type_of% (@onBlock.eq_1) := @onBlock.eq_1
private theorem tick_eq_1_export :
    type_of% (@tick.eq_1) := @tick.eq_1
private theorem slotTime_eq_1_export :
    type_of% (@slotTime.eq_1) := @slotTime.eq_1
private theorem phaseTime_eq_1_export :
    type_of% (@phaseTime.eq_1) := @phaseTime.eq_1

private theorem spec_acOnTick_eq_1_export :
    type_of% (@acOnTick.eq_1) := @acOnTick.eq_1

private theorem spec_confirmationVoters_eq_1_export :
    type_of% (@confirmationVoters.eq_1) := @confirmationVoters.eq_1

private theorem spec_confirmationScore_eq_1_export :
    type_of% (@confirmationScore.eq_1) := @confirmationScore.eq_1

private theorem spec_getConfirmation_eq_1_export :
    type_of% (@getConfirmation.eq_1) := @getConfirmation.eq_1

private theorem spec_deepestBlock_eq_1_export :
    type_of% (@deepestBlock.eq_1) := @deepestBlock.eq_1

private theorem spec_updateConfirmation_eq_1_export :
    type_of% (@updateConfirmation.eq_1) := @updateConfirmation.eq_1

private theorem spec_revokeLocks_eq_1_export :
    type_of% (@revokeLocks.eq_1) := @revokeLocks.eq_1

end AvailableChain.FGSA.Spec
end

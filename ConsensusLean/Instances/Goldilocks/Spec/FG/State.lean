module
public import Mathlib.Data.Fintype.Card
public import ConsensusLean.Init

@[expose] public section

/-! # Goldilocks FG: attestations, chain state and the state transition

The finality gadget of the Goldilocks spec as pure functions of a chain
(`specs/goldilocks/tex/shared/fg.tex` §"Attestations and chain state",
Figure "FG: state transition"; loose BJ). Blocks are seen through
`FGBlock`: their root, slot, proposer and attestations; the instance computes the
root as the digest of the block, and a chain lists the blocks from genesis, so the
parent links are implicit. Validators are `Fin n`, every weight is `1`, and the quorum
is `q = ⌈2n/3⌉`.

A chain is a list of blocks, oldest first, genesis implicit before the first.

This module holds only what the Challenge statements reach; the chain state of a whole chain
(`FGParams.chainState`) and its roots and attestations are in `Milestones/Spec/FG/State`
(`docs/decisions.md` §"Trusted surface and Challenge scope"). -/

namespace Consensus.Goldilocks.FG

/-- The FG parameters: `n ≥ 1` validators, the timeout delay `δt` in slots, the
genesis root. The proposer schedule is not runtime data.
The FG window is `K_W = 2` (`KW`). -/
structure FGParams where
  /-- The number of validators. -/
  n : Nat
  hn : 1 ≤ n
  /-- The timeout delay in slots. -/
  δt : Nat
  /-- The root of genesis. -/
  genesis : Nat

namespace FGParams

variable (gp : FGParams)

/-- The quorum `q = ⌈2n/3⌉`. -/
def q : Nat := (2 * gp.n + 2) / 3

/-- The FG window `K_W = 2`. -/
def KW : Nat := 2

end FGParams

/-- An attestation `(val_index, h, T, τ, h_f, T_f)`: its height pair names the block
`T` (by root) at height `h`, a timeout when `timeout`; its finality pair is
`fin = some (h_f, T_f)` or empty. -/
structure Att (n : Nat) where
  /-- The signer. -/
  val : Fin n
  /-- The height of the height pair. -/
  h : Nat
  /-- The root that the height pair names. -/
  T : Nat
  /-- Whether the height pair is a timeout. -/
  timeout : Bool
  /-- The finality pair `(h_f, T_f)`, or none. -/
  fin : Option (Nat × Nat)
  deriving DecidableEq

/-- The forms of an attestation (fg.tex): `h ≥ 1`, and a finality pair is below the
height pair. A block's attestations pass the wire checks (composition.tex §Blocks). -/
def Att.WellFormed {n : Nat} (a : Att n) : Prop := 1 ≤ a.h ∧ ∀ p ∈ a.fin.toList, p.1 < a.h

instance {n : Nat} (a : Att n) : Decidable a.WellFormed :=
  inferInstanceAs (Decidable (1 ≤ a.h ∧ ∀ p ∈ a.fin.toList, p.1 < a.h))

/-- What the FG sees of a block: root, slot, proposer and the attestation list
(order and repeats are content). The proposer is carried but read by no FG function: the paper's
`state_transition` proposer assertion is the run's credential (`stateTransition`,
`docs/decisions.md` §"Goldilocks model choices"). -/
structure FGBlock (n : Nat) where
  /-- The root of the block. -/
  root : Nat
  /-- The slot of the block. -/
  slot : Nat
  /-- The proposer index. -/
  proposer : Fin n
  /-- The attestations that the block carries. -/
  atts : List (Att n)

/-- The chain state `σ = (L, s, h, T_h, target, progress, pending, fin, J, h_j, F, h_F)`
of fg.tex, with blocks named by root; `ThSlot` is the slot of `T_h` (the timeout arm
reads it). -/
structure ChainState (n : Nat) where
  /-- The latest block. -/
  L : Nat
  /-- The slot of `L`. -/
  s : Nat
  /-- The current height. -/
  h : Nat
  /-- The block that brought the chain into height `h`. -/
  Th : Nat
  /-- The slot of `Th`. -/
  ThSlot : Nat
  /-- `Q_target`. -/
  target : Finset (Fin n)
  /-- `Q_prog`. -/
  prog : Finset (Fin n)
  /-- `pending_finality`: pairs `(j, T)`, oldest first. -/
  pending : List (Nat × Nat)
  /-- `Q_fin(σ, j)`. -/
  fin : Nat → Finset (Fin n)
  /-- The latest justification. -/
  J : Nat
  /-- Its height. -/
  hj : Nat
  /-- The latest finalization. -/
  F : Nat
  /-- Its height. -/
  hF : Nat

namespace ChainState

variable {n : Nat}

/-- The initial chain state (genesis): height `1`, everything at genesis, no bits. -/
def init (gp : FGParams) : ChainState gp.n where
  L := gp.genesis
  s := 0
  h := 1
  Th := gp.genesis
  ThSlot := 0
  target := ∅
  prog := ∅
  pending := []
  fin := fun _ => ∅
  J := gp.genesis
  hj := 0
  F := gp.genesis
  hF := 0

/-- The height has its *previous height justified* (`previous_height_justified`): the chain
entered it by justifying its predecessor. -/
def previousHeightJustified (σ : ChainState n) : Prop := 0 < σ.hj ∧ σ.hj + 1 = σ.h

instance (σ : ChainState n) : Decidable σ.previousHeightJustified :=
  inferInstanceAs (Decidable (0 < σ.hj ∧ σ.hj + 1 = σ.h))

/-- `valid_attestation`: the attestation names the chain's own entry, or it is an
older vote whose finality pair is pending. -/
def validAtt (σ : ChainState n) (a : Att n) : Prop :=
  (a.h = σ.h ∧ a.T = σ.Th) ∨ ∃ p ∈ a.fin.toList, p ∈ σ.pending ∧ p.1 < a.h ∧ a.h < σ.h

instance (σ : ChainState n) (a : Att n) : Decidable (σ.validAtt a) :=
  inferInstanceAs (Decidable ((a.h = σ.h ∧ a.T = σ.Th) ∨
    ∃ p ∈ a.fin.toList, p ∈ σ.pending ∧ p.1 < a.h ∧ a.h < σ.h))

/-- `process_attestation`: set the finality bit for a pending finality pair, and the
progress and target bits for the chain's own entry. -/
def processAtt (σ : ChainState n) (a : Att n) : ChainState n :=
  let σ₁ : ChainState n :=
    match a.fin with
    | some p =>
        if p ∈ σ.pending then
          { σ with fin := Function.update σ.fin p.1 (insert a.val (σ.fin p.1)) }
        else σ
    | none => σ
  if a.h = σ.h ∧ a.T = σ.Th then
    { σ₁ with prog := insert a.val σ₁.prog,
              target := if a.timeout then σ₁.target else insert a.val σ₁.target }
  else σ₁

/-- `advance_height`: the next height, entered by the latest block. -/
def advance (σ : ChainState n) : ChainState n :=
  { σ with h := σ.h + 1, Th := σ.L, ThSlot := σ.s, target := ∅, prog := ∅ }

end ChainState

namespace FGParams

variable (gp : FGParams)

/-- The pending pair with the greatest height among those with a finality quorum
(the first of equal heights). -/
def bestFinal (σ : ChainState gp.n) : Option (Nat × Nat) :=
  σ.pending.foldl (fun acc p =>
    if gp.q ≤ (σ.fin p.1).card then
      match acc with
      | none => some p
      | some r => if r.1 < p.1 then some p else some r
    else acc) none

/-- The finality step and the prune of `process_height_events`. -/
def finalizePrune (σ : ChainState gp.n) : ChainState gp.n :=
  let σ₁ : ChainState gp.n :=
    match gp.bestFinal σ with
    | some p => { σ with F := p.2, hF := p.1 }
    | none => σ
  { σ₁ with pending := σ₁.pending.filter (fun p => σ₁.hF < p.1) }

/-- The loose-BJ justification test, read after the finality step: a target quorum,
and at a height whose previous height is justified a finalized predecessor. -/
def justifies (σ : ChainState gp.n) : Prop :=
  gp.q ≤ σ.target.card ∧ (¬ σ.previousHeightJustified ∨ σ.hF = σ.hj)

instance (σ : ChainState gp.n) : Decidable (gp.justifies σ) :=
  inferInstanceAs (Decidable (gp.q ≤ σ.target.card ∧ (¬ σ.previousHeightJustified ∨ σ.hF = σ.hj)))

/-- The timeout test: a progress quorum and an entry at least `δt` slots old. -/
def timesOut (σ : ChainState gp.n) : Prop :=
  gp.q ≤ σ.prog.card ∧ σ.ThSlot + gp.δt ≤ σ.s

instance (σ : ChainState gp.n) : Decidable (gp.timesOut σ) :=
  inferInstanceAs (Decidable (gp.q ≤ σ.prog.card ∧ σ.ThSlot + gp.δt ≤ σ.s))

/-- `process_height_events`: finalize, prune, then justify (and append the entry,
keeping the newest `K_W` pairs) or time out. -/
def heightEvents (σ : ChainState gp.n) : ChainState gp.n :=
  let σ₁ := gp.finalizePrune σ
  if gp.justifies σ₁ then
    let ps := σ₁.pending ++ [(σ₁.h, σ₁.Th)]
    ChainState.advance
      { σ₁ with J := σ₁.Th, hj := σ₁.h, pending := ps.drop (ps.length - KW),
                fin := Function.update σ₁.fin σ₁.h ∅ }
  else if gp.timesOut σ₁ then ChainState.advance σ₁
  else σ₁

/-- `state_transition`: the assertions (increasing slot, every
attestation well formed and valid against the parent's state), then count the
attestations in order, set the latest block, and run the height events. `none`:
refused. Proposer-role syntax is checked when decoding the wire block; membership
in the run's selected proposer role is supplied by the execution's credentials. -/
def stateTransition (σ : ChainState gp.n) (B : FGBlock gp.n) : Option (ChainState gp.n) :=
  if σ.s < B.slot ∧
      ∀ a ∈ B.atts, a.WellFormed ∧ σ.validAtt a then
    some (gp.heightEvents
      { B.atts.foldl ChainState.processAtt { σ with s := B.slot } with L := B.root })
  else none

end FGParams

end Consensus.Goldilocks.FG

end

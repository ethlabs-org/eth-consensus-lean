module
public import ConsensusLean.Instances.Goldilocks.Spec.Node.State
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Store.Handlers
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Store.Duties

@[expose] public section

/-! # Goldilocks node: handlers and duties

composition.tex Figure "Node: handlers and duties", one function each, every handler returning
the new node state and its cuts in order (decomposition §1.5):

* `on_block(B)`: dropped when of a future slot (no call); else `fg_on_block(Σ, B)`, and, when
  the FG accepts, `ac_on_block(𝒜, fg_to_ac(Σ), t, B)` with the frame after the acceptance;
* `on_ac_message(m)`: `ac_on_message`; `on_attestation(a)`: `fg_on_attestation`;
* a restart: `ac_restart(𝒜, Φ, t)`; `Σ`, `Λ` and the clock are kept (composition.tex §"State").

`Event` is a top-level event of a node. Signatures are not modelled here: that a received object
signed by an honest key was sent by that node is a run condition (`Spec/Run`).

This module holds only what the Challenge statements reach; the duties, the tick steps, `exec` and
`WireOK` are in `Milestones/Spec/Node/Handlers` (docs/decisions.md, 2026-11-04). -/

namespace Consensus.Goldilocks.Node

variable {P : Params} {A : NodeAC P}

/-- `on_block(B)` at validator `self` and time `t`. -/
noncomputable def onBlock (self : Fin P.n) (st : NodeState A) (t : Time) (B : A.Blk) :
    NodeState A × List (Cut A) :=
  if P.slotOf t < B.slot then (st, [])
  else
    match st.fg.onBlock B with
    | none => (st, [.fg (.block B false)])
    | some fg' =>
        let r := acCall self { st with fg := fg' } t (.block B)
        (r.1, [.fg (.block B true), r.2])

/-- `on_ac_message(m)` at validator `self` and time `t`. -/
noncomputable def onMessage (self : Fin P.n) (st : NodeState A) (t : Time) (m : A.Msg) :
    NodeState A × List (Cut A) :=
  let r := acCall self st t (.message m)
  (r.1, [r.2])

/-- `on_attestation(a)`. -/
def onAttestation (st : NodeState A) (a : FG.Att P.n) : NodeState A × List (Cut A) :=
  ({ st with fg := st.fg.onAttestation a }, [.fg (.attestation a)])

/-- A restart at validator `self` and time `t`: `ac_restart` with the unchanged frame; `Σ` and
`Λ` are kept. -/
noncomputable def restart (self : Fin P.n) (st : NodeState A) (t : Time) :
    NodeState A × List (Cut A) :=
  let r := acCall self st t .restart
  (r.1, [r.2])

/-- A top-level event of a node: a tick, a delivery (a block, an AC message, an attestation),
a restart. -/
inductive Event (A : NodeAC P) where
  /-- The tick at a public time, with the input `x` (the encoded transactions the node's engine
  supplies for a proposal at this time; `Block.input`). -/
  | tick (x : Nat)
  /-- A block is received. -/
  | block (B : A.Blk)
  /-- An AC message is received. -/
  | message (m : A.Msg)
  /-- An attestation is received. -/
  | attestation (a : FG.Att P.n)
  /-- The node wakes. -/
  | restart

end Consensus.Goldilocks.Node

end

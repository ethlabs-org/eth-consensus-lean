module
public import ConsensusLean.Spec.Shape.Shape

@[expose] public section

/-! # Compilation of a chain shape to a model protocol (L2)

`compile S` is the model (L1) protocol of shape `S`. Its state is the shape's
state with the node's cumulative mempool; its roles are `ShapeRole`, its duties
`ShapeDuty`, its items headers. Selections come from the skeleton: the
proposer selection for every slot, the kind's selection for a committee duty,
the poll selection for the poll role.

Duties: the proposal of positive slot `s` at `slotTime s`; committee kind `k`
of slot `s` at `slotTime s + phase k · Δ`; the two poll duties at every unit tick
`t ≥ 0`. The duties at `t` are the steps of the skeleton's `order` due at `t`,
in that order (a repeated step gives its duty again). The engine writes every
proposal's payload (`input := encodeTxs mempool`, the post-clock mempool
`st.2`, which no step within a tick changes) and a slot proposal's position
(`pos := s`); a poll proposal's position is the shape's choice.

Same-tick semantics: the duties of a tick run one after the other (see
`Model.Run.tick`), each from the state the previous one left, including the
`recordOwn` of the messages released before it; gossip comes last, from the
final state. The poll steps are due at every unit tick; a shape that does not
poll returns `none` and sets `pollSel := .fixed ∅` (or leaves them out of
`order`). -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (Public Key SelSpec Obj Msg)

variable {Info : Type} [DecidableEq Info] [Countable Info]

namespace Skeleton

variable {n : Nat} (sk : Skeleton n)

/-- The selection specification of each role. -/
def selSpec : ShapeRole sk.Kind → SelSpec n
  | .proposer s => sk.proposerSel s
  | .duty _ k => sk.kindSel k
  | .poll => sk.pollSel

/-- The signing role of each duty. -/
def role : ShapeDuty sk.Kind → ShapeRole sk.Kind
  | .propose s _ => .proposer s
  | .act s k => .duty s k
  | .pollPropose _ => .poll
  | .poll _ => .poll

/-- The positive proposal slot at `t`, if any. -/
def proposeAt (Δ t : Time) : List (ShapeDuty sk.Kind) :=
  match sk.grid.slotAt? Δ 0 t with
  | some s => if h : 0 < s then [.propose s h] else []
  | none => []

/-- The duty of committee kind `k` at `t`, if any. -/
def kindAt (Δ t : Time) (k : sk.Kind) : List (ShapeDuty sk.Kind) :=
  ((sk.grid.slotAt? Δ ((sk.phase k : Time) * Δ) t).map fun s => .act s k).toList

/-- The duties of a step at `t`: the poll steps are due at every unit tick
`t ≥ 0`. -/
def stepAt (Δ t : Time) : Step sk.Kind → List (ShapeDuty sk.Kind)
  | .propose => sk.proposeAt Δ t
  | .kind k => sk.kindAt Δ t k
  | .pollPropose => if 0 ≤ t then [.pollPropose t.toNat] else []
  | .poll => if 0 ≤ t then [.poll t.toNat] else []

/-- The duties due at `t`, in `order`. -/
def duties (Δ t : Time) : List (ShapeDuty sk.Kind) :=
  sk.order.flatMap (sk.stepAt Δ t)

end Skeleton

variable {pub : Public} {Out : Type}

/-- A shape step's result in the compiled state: the shape's new state with
the mempool `xs` unchanged, and the message built by `f`. -/
def withMempool {σ α β : Type} (xs : List Tx) (f : α → β) (r : σ × Option α) :
    (σ × List Tx) × Option β :=
  ((r.1, xs), r.2.map f)

/-- The model protocol of a chain shape (see the module docstring). -/
def compile (S : ChainShape pub Out Info) : Model.Protocol pub Out where
  State := S.State × List Tx
  Role := ShapeRole S.skel.Kind
  Duty := ShapeDuty S.skel.Kind
  Item := Header Info
  Body := S.Body
  Durable := S.Durable
  decRole := inferInstance
  decItem := inferInstance
  decBody := inferInstance
  cntItem := inferInstance
  selSpec := S.skel.selSpec
  role := S.skel.role
  duties := S.skel.duties pub.Δ
  init k := (S.init k, [])
  clock st t xs := (S.clock st.1 t, xs)
  act st d := match d with
    | .propose s _ => withMempool st.2 (fun (par, info, cs) =>
        (.item ⟨par, s, encodeTxs st.2, info⟩, cs)) (S.propose st.1 s)
    | .act s k => withMempool st.2 (fun (b, cs) => (.data b, cs)) (S.act st.1 s k)
    | .pollPropose t => withMempool st.2 (fun (par, pos, info, cs) =>
        (.item ⟨par, pos, encodeTxs st.2, info⟩, cs)) (S.pollPropose st.1 (t : Time))
    | .poll t => withMempool st.2 (fun (b, cs) => (.data b, cs)) (S.poll st.1 (t : Time))
  gossip st t := S.gossip st.1 t
  process st o hs := (S.process st.1 o hs, st.2)
  recordOwn st o hs := (S.recordOwn st.1 o hs, st.2)
  durable st := S.durable st.1
  restore k d t := (S.restore k d t, [])
  out g st := ledgerOf (S.out g st.1)
  conflicts := S.conflicts

/-- The model family of a shape family. -/
abbrev compiled {O : OutputSchema} (F : ShapeFamily O Info) : Model.Family O :=
  fun pub => compile (F pub)

end Consensus.Shape

end

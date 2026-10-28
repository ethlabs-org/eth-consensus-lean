module
public import ConsensusShape.Shape

@[expose] public section

/-! # Compilation of a chain shape to a model protocol (L2)

`compile S` is the model (L1) protocol of shape `S`. Its state is the shape's
state with the node's cumulative mempool; its roles are `ShapeRole`, its duties
`ShapeDuty`, its items headers. Selections come from the skeleton: the
proposer selection for every slot, the kind's selection for a committee duty,
the poll selection for the poll role.

Duties: the proposal of positive slot `s` at `slotTime s`; committee kind `k`
of slot `s` at `slotTime s + phase k · Δ`; the two poll duties at every unit tick
`t ≥ 0`. The engine writes every proposal's payload (`input := encodeTxs
mempool`) and a slot proposal's position (`pos := s`); a poll proposal's
position is the shape's choice.

Same-tick semantics: all duties of a tick (the proposal, then the kinds in
`kinds` order, then the poll duties) and gossip are built from one post-clock
state; recording an earlier signature of the tick does not affect a later
action of the same tick. Poll duties exist at every unit tick; a shape that
does not poll returns `none` and sets `pollSel := .fixed ∅`. -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (Public Key SelSpec Obj Msg)

variable {Info : Type} [DecidableEq Info] [Countable Info]

namespace Skeleton

variable {n : Nat} (sk : Skeleton n)

/-- The selection specification of each role. -/
def selSpec : ShapeRole sk.Kind → SelSpec n
  | .proposer _ => sk.proposerSel
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

/-- The committee duties at `t`, kinds in `kinds` order. -/
def actAt (Δ t : Time) : List (ShapeDuty sk.Kind) :=
  sk.kinds.filterMap fun k => (sk.grid.slotAt? Δ ((sk.phase k : Time) * Δ) t).map fun s => .act s k

/-- The poll duties at `t` (every unit tick `t ≥ 0`). -/
def pollAt (t : Time) : List (ShapeDuty sk.Kind) :=
  if 0 ≤ t then [.pollPropose t.toNat, .poll t.toNat] else []

/-- The duties due at `t`, in signing order. -/
def duties (Δ t : Time) : List (ShapeDuty sk.Kind) :=
  sk.proposeAt Δ t ++ sk.actAt Δ t ++ sk.pollAt t

end Skeleton

variable {pub : Public} {Out : Type}

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
    | .propose s _ => (S.propose st.1 s).map fun (par, info, cs) =>
        (.item ⟨par, s, encodeTxs st.2, info⟩, cs)
    | .act s k => (S.act st.1 s k).map fun (b, cs) => (.data b, cs)
    | .pollPropose t => (S.pollPropose st.1 (t : Time)).map fun (par, pos, info, cs) =>
        (.item ⟨par, pos, encodeTxs st.2, info⟩, cs)
    | .poll t => (S.poll st.1 (t : Time)).map fun (b, cs) => (.data b, cs)
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

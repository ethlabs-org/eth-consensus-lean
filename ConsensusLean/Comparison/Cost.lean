module
public import ConsensusLean.Comparison.Basic
public import ConsensusLean.Spec.Shape.Run
public import Mathlib.Data.Set.Card

@[expose] public section

/-! # Cost over chain shapes (statements)

Cost reads signing roles, so it is stated over chain shapes (L2), on every valid run of a family's
compiled system (`System.HoldsAlways`): cost is structural, so there is no regime premise, no
progress premise and no excuse. The contract fixes no cost, so there is no default; `⊤` (no claim)
is the only generic value.

* `SlotClass` and `RoleClass`: a signing role without its slot. `SlotClass` has the roles that
  name a slot (the slot proposal, committee kind `k`); `RoleClass` adds the poll role. Signing and
  carrying bounds are vectors over them, one coordinate per duty kind (votes and acknowledgements of
  a protocol with two vote kinds are separate coordinates).
* `SigningRate F V σ`: in every valid run, for every slot `s`, every validator signs with its own
  key at most `σ pub c` distinct objects in a role of class `c` naming `s` that occur, at any depth,
  in what it releases while honest at the release. The poll role names no slot, so poll signatures
  are not bounded (no coordinate).
* `CarriedBound F V m`: every honest proposal (a header released in a proposal role by a key
  honest at the release) carries, at any depth, at most `m pub c ⟨h, f⟩` distinct objects signed in
  a role of class `c`, where `h` and `f` count the validators honest and compromised at the
  release. The bound is monotone in `(h, f)`.
* `StateBound F V μ κ` and `LockMemory F V locks saved κ κ'`: every honest node state has at most
  `κ pub` under the measure `μ` (live locks for `locks`, saved counts for `saved`, with `κ'`). The
  measures are the protocol's reading of its own state, fixed per family (see `StateBound`).

Bounds read environment quantities only: the public parameters, the role class, and the counts of
honest and compromised validators at the release. -/

namespace Consensus.Comparison

open Shape Blocks
open Consensus.Model (Public Obj pubOf)

/-- A signing role that names a slot, without its slot: the slot proposal, or committee kind
`k`. -/
inductive SlotClass (Kind : Type) where
  | proposer
  | duty (k : Kind)

/-- A signing role without its slot: the slot proposal, committee kind `k`, or the poll role. -/
inductive RoleClass (Kind : Type) where
  | proposer
  | duty (k : Kind)
  | poll

/-- The slot a signing role names, with its class: `.proposer s` names `s` as `proposer`,
`.duty s k` names `s` as `duty k`; the poll role names no slot. -/
def SlotClass.ofRole {Kind : Type} : ShapeRole Kind → Option (Slot × SlotClass Kind)
  | .proposer s => some (s, .proposer)
  | .duty s k => some (s, .duty k)
  | .poll => none

/-- The class of a signing role: `.proposer s` is `proposer`, `.duty s k` is `duty k`, `.poll` is
`poll`. -/
def RoleClass.ofRole {Kind : Type} : ShapeRole Kind → RoleClass Kind
  | .proposer _ => .proposer
  | .duty _ k => .duty k
  | .poll => .poll

/-- The parameters of a carried bound at a proposal's release: `h` validators honest and `f`
compromised then. Order: coordinatewise. -/
structure CarriedQ where
  h : ℕ
  f : ℕ

instance : LE CarriedQ := ⟨fun q q' => q.h ≤ q'.h ∧ q.f ≤ q'.f⟩

theorem CarriedQ.le_def (q q' : CarriedQ) : q ≤ q' ↔ q.h ≤ q'.h ∧ q.f ≤ q'.f := Iff.rfl

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]
  (F : ChainShapeFamily O Info) (V : Type) [Fintype V] [DecidableEq V]

section Objects

variable {F V} {E : Env V}

/-- The objects signed with `v`'s own key in a role of class `c` naming slot `s` that occur, at any
depth (`Obj.parts`: the object and everything it carries), in an object `v` releases while honest
at the release. An own vote released inside a container (an unsigned gossip object, a proposal) is
counted as the vote. -/
def signedFor (rho : Model.Run (compiled F) E) (v : V) (c : SlotClass (F (pubOf E)).skel.Kind)
    (s : Slot) : Set (Model.protoOf (compiled F) E).Object :=
  {d | ∃ o τ, rho.point.HonestAt v τ ∧ rho.releases v o τ ∧ d ∈ o.parts ∧
    ∃ r : ShapeRole (F (pubOf E)).skel.Kind, d.auth = .signed (rho.ownKey v) r ∧
      SlotClass.ofRole r = some (s, c)}

/-- The objects signed in a role of class `c` that the objects `cs` carry, at any depth (each
carried object and everything it carries, `Obj.parts`). -/
def signedCarried (cs : List (Model.protoOf (compiled F) E).Object)
    (c : RoleClass (F (pubOf E)).skel.Kind) : Set (Model.protoOf (compiled F) E).Object :=
  {d | (∃ o ∈ cs, d ∈ o.parts) ∧
    ∃ k, ∃ r : ShapeRole (F (pubOf E)).skel.Kind, d.auth = .signed k r ∧ RoleClass.ofRole r = c}

end Objects

/-- **Signing rate** `σ` of family `F` at validators `V`: in every valid run of the compiled
system, for every validator `v`, slot `s` and slot class `c` with `σ pub c` finite, at most
`σ pub c` distinct objects signed with `v`'s own key in a role of class `c` naming `s` occur, at
any depth, in the objects `v` releases while honest at the release (`signedFor`; `pub` the run's
public parameters). Honesty is read at each release; signatures released only while compromised
are not bounded. Poll signatures are not bounded: the poll role names no slot.

At Tier A, `SigningRateAC0` states the vote coordinate at `1` for every Goldilocks unlock stage
(at most one vote emission per slot of an honest node) over AC traces. -/
def SigningRate (σ : (pub : Public) → SlotClass (F pub).skel.Kind → WithTop ℕ) : Prop :=
  (Sys F V).HoldsAlways fun r => ∀ (v : V) c (s : Slot) (d : ℕ), σ (pubOf r.1) c = d →
    (signedFor r.2 v c s).encard ≤ d

/-- **Carried bound** `m` of family `F` at validators `V`: every honest proposal carries few signed
objects. In every valid run of the compiled system, if key `k`, honest at `τ`, releases at `τ` a
header `hd` in a proposal role carrying `cs`, then for every role class `c` with
`m pub c ⟨h, f⟩` finite (`h` and `f` the validators honest and compromised at `τ`) the objects `cs`
carry, at any depth, at most `m pub c ⟨h, f⟩` distinct objects signed in a role of class `c`. Signed
objects reach a proposal only as carried objects (the header's `info` and `input` are not objects).
`m` is monotone in `(h, f)`, so the claim at the counts at the release is the claim at every pair of
caps on them. -/
structure CarriedBound (m : (pub : Public) → RoleClass (F pub).skel.Kind → Bound CarriedQ) :
    Prop where
  mono : ∀ pub c, AdverseMonotone (m pub c)
  carried : (Sys F V).HoldsAlways fun r => ∀ (k : Fin (Fintype.card V)) (τ : Time)
    (hd : Header Info) (rl : ShapeRole (F (pubOf r.1)).skel.Kind) cs,
    r.2.point.HonestAt (r.2.key k) τ → ProposalRole hd rl →
    r.2.releases (r.2.key k) (Obj.mk (.signed k rl) (.item hd) cs) τ →
    ∀ c (d : ℕ), m (pubOf r.1) c ⟨(r.2.point.honestAt τ).card, r.2.point.faultCount τ⟩ = d →
      (signedCarried cs c).encard ≤ d

/-- **State bound** `κ` under the measure `μ`: in every valid run of the compiled system, at every
event cut `i`, every node honest at the cut's time has a shape state of measure at most `κ pub`
(when finite); the measure reads the state and the cut's time.

**Measure fidelity.** The measure is supplied per family, and a trivial measure (constantly `0`)
makes every bound hold vacuously. So the statement is only as good as its measure: each family
fixes its measures in its frozen Milestones Spec, reads them back against its protocol card, and
proves one sanity theorem tying each measure to the family's own state (for Goldilocks, the live
locks measure is the cardinality of `liveLocks` of the node's lock store at its frame and time).
The same holds for the reading of a bound's coordinates that an instance relies on (which of the
family's duty kinds is its vote kind, for `SigningRate` and `CarriedBound`). -/
def StateBound (μ : (pub : Public) → (F pub).State → Time → ℕ) (κ : Bound Public) : Prop :=
  (Sys F V).HoldsAlways fun r => ∀ (v : V) (i d : ℕ), i ≤ r.2.events.length →
    r.2.point.HonestAt v (r.2.cutTime i) → κ (pubOf r.1) = d →
      μ (pubOf r.1) (r.2.stateBefore i v).st.1 (r.2.cutTime i) ≤ d

/-- **Lock memory** `κ`, `κ'` of family `F` at validators `V`: every honest node state holds at most
`κ pub` live locks and `κ' pub` saved counts, as read by the family's measures `locks` and `saved`
(`StateBound`; a lock is live by the state and the time). The measures are per family, fixed in its
frozen Milestones Spec with a read-back against the protocol card and a sanity theorem
(`StateBound`, measure fidelity). -/
structure LockMemory (locks saved : (pub : Public) → (F pub).State → Time → ℕ)
    (κ κ' : Bound Public) : Prop where
  locks : StateBound F V locks κ
  saved : StateBound F V saved κ'

end Consensus.Comparison

end

module
public import ConsensusShape
public import ConsensusShapeTests.Common
public import ConsensusShapeTests.Support
public import Mathlib.Tactic
@[expose] public section

/-! # Shape tests

* A trivial slot shape (grid 1, one proposer per slot, polling disabled, one
  committee kind, nothing proposed): compiled roles and selections, duties at
  slot times, reads are empty chains mapped to empty ledgers, and polling is
  really disabled (`poll_disabled_forged`: a run delivering any
  `.poll`-signed object violates `Credentials`).
* A poll shape (decision T): the state is the own key and a local height; the
  round-robin leader of tick `t` proposes at height `ht + 1`, a position chosen
  locally, with the payload written by the engine
  (`poll_proposal_local_height`); poll duties exist at every unit tick, also
  off the slot grid (`poll_duty_every_tick`). -/

namespace Consensus.Shape.Tests.Shapes
open Consensus Blocks Shape
open Consensus.Model (Public Key Obj pubOf protoOf sysOf)

/-- The trivial skeleton: slots of one `Δ`, one proposer per slot, polling
disabled, one committee kind (phase 0, every key). -/
def trivialSkel (n : Nat) : Skeleton n where
  grid := ⟨1⟩
  proposerSel := .sized 1
  pollSel := .fixed ∅
  Kind := Unit
  decKind := inferInstance
  kinds := [()]
  kinds_nodup := List.nodup_singleton _
  kinds_complete := fun _ => List.mem_singleton_self _
  phase := fun _ => 0
  kindSel := fun _ => .fixed Finset.univ

/-- The trivial slot shape: nothing is proposed, signed or output. -/
def trivialShape (pub : Public) : ChainShape pub Unit Unit where
  skel := trivialSkel pub.n
  State := Unit
  Body := Unit
  Durable := Unit
  decBody := inferInstance
  init := fun _ => ()
  clock := fun s _ => s
  propose := fun _ _ => none
  act := fun _ _ _ => none
  pollPropose := fun _ _ => none
  poll := fun _ _ => none
  gossip := fun _ _ => []
  process := fun s _ _ => s
  recordOwn := fun s _ _ => s
  durable := fun s => s
  restore := fun _ d _ => d
  out := fun _ _ => []
  conflicts := fun _ _ => false

/-- The trivial slot shape family. -/
def trivialFamily : ShapeFamily schema Unit := trivialShape

-- Compiled roles and selections: a slot proposal signs as the slot's
-- proposer (one key), a committee duty as its kind (every key), the poll
-- duties in the poll role (no key).
example (pub : Public) : (compile (trivialShape pub)).role (.propose 3 (by decide)) =
    ShapeRole.proposer 3 := rfl
example (pub : Public) :
    (compile (trivialShape pub)).selSpec (ShapeRole.proposer 3) = .sized 1 := rfl
example (pub : Public) : (compile (trivialShape pub)).selSpec (ShapeRole.duty 3 ()) =
    .fixed Finset.univ := rfl
example (pub : Public) :
    (compile (trivialShape pub)).selSpec ((compile (trivialShape pub)).role (.pollPropose 3)) =
      .fixed ∅ := rfl

/-- The proposal of slot 2 is due at its slot time `2·Δ`. -/
theorem trivial_propose_due (pub : Public) :
    ShapeDuty.propose 2 (by decide) ∈ (compile (trivialShape pub)).duties (2 * pub.Δ) :=
  ((trivialShape pub).skel.duties_spec pub.Δ_pos _ _).mpr (by
    change (trivialSkel pub.n).grid.slotTime pub.Δ 2 = 2 * pub.Δ
    simp [TimeGrid.slotTime, TimeGrid.slotLen, trivialSkel])

/-- The committee duty of slot 3 is due at `3·Δ` (phase 0). -/
theorem trivial_act_due (pub : Public) :
    ShapeDuty.act 3 () ∈ (compile (trivialShape pub)).duties (3 * pub.Δ) :=
  ((trivialShape pub).skel.duties_spec pub.Δ_pos _ _).mpr (by
    change (trivialSkel pub.n).grid.slotTime pub.Δ 3 + ((0 : Nat) : Time) * pub.Δ = 3 * pub.Δ
    simp [TimeGrid.slotTime, TimeGrid.slotLen, trivialSkel])

/-- Every read of the trivial family is the empty ledger, the image of the
empty chain under `ledgerOf` (`ledgerTrace`). -/
theorem trivial_reads_empty {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (rho : Model.Run (compiled trivialFamily) E) (v : V) (i : Nat) :
    ((sysOf schema (compiled trivialFamily) V).trace ⟨E, rho⟩).read () v i = [] := by
  rw [ledgerTrace]
  rfl

/-- Polling disabled: with `pollSel := .fixed ∅`, a run with an admissible
selection that delivers any object carrying a `.poll`-signed object violates
`Credentials`. -/
theorem poll_disabled_forged {V : Type} [Fintype V] {E : Env V}
    (rho : Model.Run (compiled trivialFamily) E) (hsel : rho.SelValid) {i : Nat} {w : V}
    {o : (protoOf (compiled trivialFamily) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver w o t)) {o' : (protoOf (compiled trivialFamily) E).Object}
    (hc : Obj.Contains o o') {k : Fin (Fintype.card V)} (ha : o'.auth = .signed k ShapeRole.poll) :
    ¬ rho.Credentials := by
  intro hcr
  have hk := hcr i w o t he o' hc k ShapeRole.poll ha
  have hs : rho.sel ShapeRole.poll = ∅ := hsel ShapeRole.poll
  rw [hs] at hk
  exact Finset.notMem_empty _ hk

/-- The poll skeleton (decision T): slots of four `Δ`, no slot proposer, every
key may poll, no committee kinds. -/
def pollSkel (n : Nat) : Skeleton n where
  grid := ⟨4⟩
  proposerSel := .fixed ∅
  pollSel := .fixed Finset.univ
  Kind := Empty
  decKind := inferInstance
  kinds := []
  kinds_nodup := List.nodup_nil
  kinds_complete := fun k => k.elim
  phase := fun _ => 0
  kindSel := fun k => k.elim

/-- A poll shape: the state is the own key and a local height. The
round-robin leader of tick `t` (key `t mod n`) proposes a child of the root at
height `ht + 1`, chosen locally. -/
def pollShape (pub : Public) : ChainShape pub Unit Unit where
  skel := pollSkel pub.n
  State := Key pub × Nat
  Body := Unit
  Durable := Key pub × Nat
  decBody := inferInstance
  init := fun k => (k, 0)
  clock := fun s _ => s
  propose := fun _ _ => none
  act := fun _ _ _ => none
  pollPropose := fun s t =>
    if t.toNat % pub.n = s.1.val then some (.root, s.2 + 1, (), []) else none
  poll := fun _ _ => none
  gossip := fun _ _ => []
  process := fun s _ _ => s
  recordOwn := fun s _ _ => s
  durable := fun s => s
  restore := fun _ d _ => d
  out := fun _ _ => []
  conflicts := fun _ _ => false

/-- The leader of tick `t`, at local height 5, proposes at height 6 (a
position chosen by the protocol), with the payload written by the engine from
its mempool `xs`. -/
theorem poll_proposal_local_height (pub : Public) (k : Key pub) (t : Nat) (xs : List Tx)
    (h : t % pub.n = k.val) :
    (compile (pollShape pub)).act ((k, 5), xs) (ShapeDuty.pollPropose t) =
      some (.item ⟨.root, 6, encodeTxs xs, ()⟩, []) := by
  simp [compile, pollShape, h]

/-- Public parameters with `Δ = 2` and three keys. -/
def pub2 : Public := ⟨3, 2, by decide⟩

/-- Time 3 is off the slot grid (slots of `4·Δ = 8`), and yet the poll
proposal duty of tick 3 is due at 3: poll duties exist at every unit tick. -/
theorem poll_duty_every_tick :
    (pollSkel pub2.n).grid.slotAt? pub2.Δ 0 3 = none ∧
      ShapeDuty.pollPropose 3 ∈ (compile (pollShape pub2)).duties 3 :=
  ⟨by decide, ((pollShape pub2).skel.duties_spec pub2.Δ_pos _ _).mpr rfl⟩

end Consensus.Shape.Tests.Shapes

end

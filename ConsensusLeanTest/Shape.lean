module
public import ConsensusLean
public import Solution
public import ConsensusLeanTest.Common
public import ConsensusLeanTest.Support
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
def trivialSkel (pub : Public) : Skeleton pub.n where
  grid := ⟨pub.Δ, pub.Δ_pos⟩
  proposerSel := fun _ => .sized 1
  pollSel := .fixed ∅
  Kind := Unit
  decKind := inferInstance
  kinds := [()]
  phase := fun _ => 0
  kindSel := fun _ => .fixed Finset.univ

/-- An absolute grid need not be divisible by the environment delay. -/
def slackSkel : Skeleton 1 :=
  { trivialSkel ⟨1, 3, by decide⟩ with
    grid := ⟨16, by decide⟩
    phase := fun _ => 4 }

/-- Slot 1 with absolute offset 4 is time 20, not 19 or 15. -/
theorem slack_phase_timing :
    slackSkel.kindAt 20 () = [.act 1 ()] ∧
    slackSkel.kindAt 19 () = [] ∧ slackSkel.kindAt 15 () = [] ∧
    slackSkel.stepAt 19 .poll = [.poll 19] := by
  have hphase : slackSkel.phase () = 4 := rfl
  norm_num [Skeleton.kindAt, Skeleton.stepAt, TimeGrid.slotAt?, hphase, slackSkel]

/-- The trivial slot shape: nothing is proposed, signed or output. -/
def trivialShape (pub : Public) : ChainShape pub Unit Unit where
  skel := trivialSkel pub
  State := Unit
  Body := Unit
  Durable := Unit
  decBody := inferInstance
  init := fun _ => ()
  clock := fun s _ => s
  propose := fun s _ => (s, none)
  act := fun s _ _ => (s, none)
  pollPropose := fun s _ => (s, none)
  poll := fun s _ => (s, none)
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
theorem trivial_propose_role (pub : Public) :
    (compile (trivialShape pub)).role (.propose 3 (by decide)) = ShapeRole.proposer 3 := rfl
theorem trivial_proposer_selSpec (pub : Public) :
    (compile (trivialShape pub)).selSpec (ShapeRole.proposer 3) = .sized 1 := rfl
theorem trivial_duty_selSpec (pub : Public) :
    (compile (trivialShape pub)).selSpec (ShapeRole.duty 3 ()) = .fixed Finset.univ := rfl
theorem trivial_pollPropose_selSpec (pub : Public) :
    (compile (trivialShape pub)).selSpec ((compile (trivialShape pub)).role (.pollPropose 3)) =
      .fixed ∅ := rfl

/-- The proposal of slot 2 is due at its slot time `2·Δ`. -/
theorem trivial_propose_due (pub : Public) :
    ShapeDuty.propose 2 (by decide) ∈ (compile (trivialShape pub)).duties (2 * pub.Δ) :=
  ((trivialShape pub).skel.duties_spec _ _).mpr ⟨List.mem_cons_self, by
    change (trivialSkel pub).grid.slotTime 2 = 2 * pub.Δ
    simp [TimeGrid.slotTime, trivialSkel]⟩

/-- The committee duty of slot 3 is due at `3·Δ` (phase 0). -/
theorem trivial_act_due (pub : Public) :
    ShapeDuty.act 3 () ∈ (compile (trivialShape pub)).duties (3 * pub.Δ) :=
  ((trivialShape pub).skel.duties_spec _ _).mpr
    ⟨List.mem_cons_of_mem _ List.mem_cons_self, by
    change (trivialSkel pub).grid.slotTime 3 + ((0 : Nat) : Time) = 3 * pub.Δ
    simp [TimeGrid.slotTime, trivialSkel]⟩

/-- Every read of the trivial family is the empty ledger, the image of the
empty chain under `ledgerOf` (`ledgerTrace`). -/
theorem trivial_reads_empty {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (rho : Model.Run (compiled trivialFamily) E) (v : V) (i : Nat) :
    ((sysOf schema (compiled trivialFamily) V).trace ⟨E, rho⟩).read () v i = [] := by
  rw [ledgerTrace, Trace.map_read]
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
def pollSkel (pub : Public) : Skeleton pub.n where
  grid := ⟨4 * pub.Δ, mul_pos (by decide) pub.Δ_pos⟩
  proposerSel := fun _ => .fixed ∅
  pollSel := .fixed Finset.univ
  Kind := Empty
  decKind := inferInstance
  kinds := []
  phase := fun _ => 0
  kindSel := fun k => k.elim

/-- A poll shape: the state is the own key and a local height. The
round-robin leader of tick `t` (key `t mod n`) proposes a child of the root at
height `ht + 1`, chosen locally. -/
def pollShape (pub : Public) : ChainShape pub Unit Unit where
  skel := pollSkel pub
  State := Key pub × Nat
  Body := Unit
  Durable := Key pub × Nat
  decBody := inferInstance
  init := fun k => (k, 0)
  clock := fun s _ => s
  propose := fun s _ => (s, none)
  act := fun s _ _ => (s, none)
  pollPropose := fun s t =>
    (s, if t.toNat % pub.n = s.1.val then some (.root, s.2 + 1, (), []) else none)
  poll := fun s _ => (s, none)
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
    ((compile (pollShape pub)).act ((k, 5), xs) (ShapeDuty.pollPropose t)).2 =
      some (.item ⟨.root, 6, encodeTxs xs, ()⟩, []) := by
  simp [compile, withMempool, pollShape, h]

/-- Public parameters with `Δ = 2` and three keys. -/
def pub2 : Public := ⟨3, 2, by decide⟩

/-- Time 3 is off the slot grid (slots of `4·Δ = 8`), and yet the poll
proposal duty of tick 3 is due at 3: poll duties exist at every unit tick. -/
theorem poll_duty_every_tick :
    (pollSkel pub2).grid.slotAt? 0 3 = none ∧
      ShapeDuty.pollPropose 3 ∈ (compile (pollShape pub2)).duties 3 :=
  ⟨by decide, ((pollShape pub2).skel.duties_spec _ _).mpr
    ⟨List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩⟩

/-- `shapeProgress` keeps its data fields (plan §2.1: only its proof fields `mono`/`shrink`
were rewritten, to inline term proofs). -/
theorem shapeProgress_holds {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]
    (F : ShapeFamily O Info) (V : Type) [Fintype V] [DecidableEq V] :
    (shapeProgress F V).holds = shapeHolds F := rfl

theorem shapeProgress_toExternal {O : OutputSchema} {Info : Type} [DecidableEq Info]
    [Countable Info] (F : ShapeFamily O Info) (V : Type) [Fintype V] [DecidableEq V] :
    (shapeProgress F V).toExternal = Model.sysExternal O (compiled F) V := rfl

end Consensus.Shape.Tests.Shapes

end

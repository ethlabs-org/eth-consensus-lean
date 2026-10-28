module
public import ConsensusShape.Objects
@[expose] public section

namespace Consensus.Shape
open AvailableChain (Slot Time)
open Consensus.Model (Public)

def shapeSeats {L : Type} (n : Nat) : L ⊕ Slot → Nat
  | .inl _ => n
  | .inr _ => 1

/-- A protocol for public parameters `pub`. -/
structure ShapeProtocol (pub : Public) : Type 1 where
  State : Type
  /-- Committee labels. Every label has `pub.n` seats. -/
  Label : Type
  /-- Committee duties. A duty signs with its label. -/
  Duty : Type
  /-- Protocol data in objects. -/
  Body : Type
  /-- What a restart keeps. -/
  Durable : Type
  decLabel : DecidableEq Label
  decBody : DecidableEq Body
  /-- Slot length in units of `Δ`: slot `s` is proposed at `s * slotTicks * Δ`.
  A reported number. -/
  slotTicks : Nat
  slotTicks_pos : 0 < slotTicks
  init : State
  /-- The local clock update, at every tick (an asleep node has no ticks). -/
  clock : State → Time → State
  /-- The proposal choice for slot `s`: the parent's digest, protocol data
  `aux`, and carried objects. The engine builds the header
  `⟨parent, s, input, aux⟩` with the proposer's own input and signs it with the
  proposer key of `s`. -/
  propose : State → Slot → 
    Option (Nat × Nat × List (Model.Obj (Label ⊕ Slot) (shapeSeats pub.n) Header Body))
  label : Duty → Label
  actTime : Duty → Time
  duties : Time → List Duty
  duties_spec : ∀ d t, d ∈ duties t ↔ actTime d = t
  duties_nodup : ∀ t, (duties t).Nodup
  /-- What every seat of duty `d` signs: data and carried objects. -/
  act : State → Duty → 
    Option (Body × List (Model.Obj (Label ⊕ Slot) (shapeSeats pub.n) Header Body))
  /-- Unsigned objects. Relay of received objects is done here, by carrying
  them. -/
  gossip : State → Time → 
    List (Body × List (Model.Obj (Label ⊕ Slot) (shapeSeats pub.n) Header Body))
  /-- Process any delivered object, with digests of every item in its closure. -/
  process : State → Model.Obj (Label ⊕ Slot) (shapeSeats pub.n) Header Body →
    List (Header × Nat) → State
  /-- Record a signed object, with all item digests from its closure. -/
  recordOwn : State → Model.Obj (Label ⊕ Slot) (shapeSeats pub.n) Header Body →
    List (Header × Nat) → State
  durable : State → Durable
  restore : Durable → Time → State
  /-- The three outputs. -/
  confirmed : State → Chain
  stable : State → Chain
  finalized : State → Chain
  /-- The slashing rule: two objects that, signed by one validator, convict
  it. -/
  conflicts : Model.Obj (Label ⊕ Slot) (shapeSeats pub.n) Header Body →
    Model.Obj (Label ⊕ Slot) (shapeSeats pub.n) Header Body → Bool

attribute [instance] ShapeProtocol.decLabel ShapeProtocol.decBody

namespace ShapeProtocol

variable {pub : Public}

/-- Wire objects of a protocol. -/
abbrev Object (P : ShapeProtocol pub) : Type :=
  Model.Obj (P.Label ⊕ Slot) (shapeSeats pub.n) Header P.Body

/-- The slot length in time units. -/
def slotLen (P : ShapeProtocol pub) : Time := (P.slotTicks : Time) * pub.Δ

/-- The proposal time of slot `s`. -/
def proposalTime (P : ShapeProtocol pub) (s : Slot) : Time := (s : Time) * P.slotLen

/-- The slot proposed at time `t`, if any. -/
def slotAt? (P : ShapeProtocol pub) (t : Time) : Option Slot :=
  if 0 ≤ t ∧ t % P.slotLen = 0 then some (t / P.slotLen).toNat else none

theorem slotLen_pos (P : ShapeProtocol pub) : 0 < P.slotLen :=
  Int.mul_pos (by exact_mod_cast P.slotTicks_pos) pub.Δ_pos

theorem slotAt?_eq_some (P : ShapeProtocol pub) {t : Time} {s : Slot} :
    P.slotAt? t = some s ↔ P.proposalTime s = t := by
  have hl := P.slotLen_pos
  unfold slotAt? proposalTime
  by_cases hc : 0 ≤ t ∧ t % P.slotLen = 0
  · simp only [hc, and_self, ↓reduceIte, Option.some.injEq]
    obtain ⟨h0, hm⟩ := hc
    have hdiv : 0 ≤ t / P.slotLen := Int.ediv_nonneg h0 hl.le
    have ht : t / P.slotLen * P.slotLen = t := Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero hm)
    constructor
    · rintro rfl; rw [Int.toNat_of_nonneg hdiv, ht]
    · rintro rfl; rw [Int.mul_ediv_cancel _ hl.ne']; simp
  · simp only [hc, ↓reduceIte]
    simp only [reduceCtorEq, false_iff]
    rintro rfl
    exact hc ⟨Int.mul_nonneg (Int.natCast_nonneg s) hl.le, Int.mul_emod_left _ _⟩

end ShapeProtocol

/-- A protocol for every choice of the public parameters. -/
abbrev Family := (pub : Public) → ShapeProtocol pub

end Consensus.Shape
end

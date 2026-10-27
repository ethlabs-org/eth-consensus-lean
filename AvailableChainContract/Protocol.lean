module
public import AvailableChainContract.Objects

@[expose] public section

/-! # The protocol interface

What an instance supplies: a state machine, three output getters, and its
slashing rule. Nothing it supplies appears in a premise of a claim. The engine
(`Contract.Run`) runs the machine, signs its objects and builds its proposals.

The protocol knows only the public parameters `n` (the number of validators)
and `Δ`. It does not know the GST, the honest set, the awake profile, its own
seats, or any input but its own, which the engine puts into its proposal. -/

namespace AvailableChain.Contract

/-- The public parameters that honest code may depend on. -/
structure Public where
  n : Nat
  Δ : Time
  Δ_pos : 0 < Δ

/-- A protocol for public parameters `pub`. -/
structure Protocol (pub : Public) : Type 1 where
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
  /-- The local clock update, at every tick, awake or asleep. -/
  clock : State → Time → State
  /-- The proposal choice for slot `s`: a parent, protocol data `aux`, and
  carried objects. The engine builds the block `node parent s input aux` with
  the proposer's own input and signs it with the proposer key of `s`. -/
  propose : State → Slot → Option (CBlock × Nat × List (Obj Label pub.n Body))
  label : Duty → Label
  actTime : Duty → Time
  duties : Time → List Duty
  duties_spec : ∀ d t, d ∈ duties t ↔ actTime d = t
  duties_nodup : ∀ t, (duties t).Nodup
  /-- What every seat of duty `d` signs: data and carried objects. -/
  act : State → Duty → Option (Body × List (Obj Label pub.n Body))
  /-- Unsigned objects. Relay of received objects is done here, by carrying
  them. -/
  gossip : State → Time → List (Body × List (Obj Label pub.n Body))
  /-- Processing a delivered object. Total: any object, at any time. -/
  process : State → Obj Label pub.n Body → State
  /-- The node's record of an object that it has just signed. -/
  recordOwn : State → Obj Label pub.n Body → State
  durable : State → Durable
  restore : Durable → Time → State
  /-- The three outputs. -/
  confirmed : State → CBlock
  stable : State → CBlock
  finalized : State → CBlock
  /-- The slashing rule: two objects that, signed by one validator, convict
  it. -/
  conflicts : Obj Label pub.n Body → Obj Label pub.n Body → Bool

attribute [instance] Protocol.decLabel Protocol.decBody

namespace Protocol

variable {pub : Public}

/-- Wire objects of a protocol. -/
abbrev Object (P : Protocol pub) : Type := Obj P.Label pub.n P.Body

/-- The slot length in time units. -/
def slotLen (P : Protocol pub) : Time := (P.slotTicks : Time) * pub.Δ

/-- The proposal time of slot `s`. -/
def proposalTime (P : Protocol pub) (s : Slot) : Time := (s : Time) * P.slotLen

/-- The slot proposed at time `t`, if any. -/
def slotAt? (P : Protocol pub) (t : Time) : Option Slot :=
  if 0 ≤ t ∧ t % P.slotLen = 0 then some (t / P.slotLen).toNat else none

theorem slotLen_pos (P : Protocol pub) : 0 < P.slotLen :=
  Int.mul_pos (by exact_mod_cast P.slotTicks_pos) pub.Δ_pos

theorem slotAt?_eq_some (P : Protocol pub) {t : Time} {s : Slot} :
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

end Protocol

/-- A protocol for every choice of the public parameters. -/
abbrev Family := (pub : Public) → Protocol pub

end AvailableChain.Contract

end

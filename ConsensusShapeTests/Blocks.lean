module
public import ConsensusBlocks
public import Mathlib.Tactic
@[expose] public section

/-! # Building-block tests

`slotAt?` on concrete grids; pattern recurrence holds from any start when
every slot is honest and ready (the Streamlet pattern `[0,1,2,3,4]`); a negative
progress start means start 0 (D-22); the window guard counts the whole pattern
(`span_guard`); recurrence has teeth: on a two-node point
whose only selected proposer key is faulty it fails as soon as one window fits
in the horizon; `ledgerOf` of a two-header chain keeps first occurrences. -/

namespace Consensus.Shape.Tests.Blocks
open Consensus Blocks

/-- Slots of two `Δ`. -/
def grid : TimeGrid := ⟨2, by decide⟩

-- With `Δ = 3` slots are 6 units long: slot 2 starts at 12, slot 1 plus
-- offset 3 is at 9, and time 7 is no slot time.
example : grid.slotAt? 3 0 12 = some 2 := by decide
example : grid.slotAt? 3 3 9 = some 1 := by decide
example : grid.slotAt? 3 0 7 = none := by decide
example : grid.slotAt? 3 0 0 = some 0 := by decide
example : grid.slotAt? 3 0 (-6) = none := by decide

/-- One validator, always awake, `Δ = 1`, horizon 100. -/
def point1 : EnvPoint (Fin 1) :=
  ⟨⟨1, by decide, fun _ _ => true⟩, Finset.univ, 100, fun _ _ => []⟩

/-- The identity PKI on one validator. -/
def pki1 : Fin (Fintype.card (Fin 1)) ≃ Fin 1 := finCongr (Fintype.card_fin 1)

/-- The Streamlet pattern: five consecutive honest slots, within every window
of 3 slots. -/
def streamlet : Recurrence := ⟨⟨[0, 1, 2, 3, 4], by simp⟩, 3⟩

/-- Every slot is honest and ready on `point1`, so the Streamlet pattern recurs
from any start. -/
theorem streamlet_recurrence (c start stop : Time) :
    PatternRecurrence point1 pki1 (fun _ : Unit => Finset.univ) (fun _ => ()) grid streamlet
      c start stop := by
  apply patternRecurrence_of_all (by decide)
  intro s j _
  refine ⟨⟨0, Finset.mem_univ _⟩, fun k _ => ⟨Finset.mem_univ _, Finset.mem_univ _, ?_⟩⟩
  intro u _ _
  rfl

/-- A non-positive start is the same premise as start 0 (D-22). -/
theorem recurrence_nonpos_start {V R : Type} [Fintype V] (p : EnvPoint V)
    (key : Fin (Fintype.card V) ≃ V) (sel : R → Finset (Fin (Fintype.card V)))
    (lead : Slot → R) (G : TimeGrid) (π : Recurrence) (c start stop : Time) (hs : start ≤ 0) :
    PatternRecurrence p key sel lead G π c start stop ↔
      PatternRecurrence p key sel lead G π c 0 stop :=
  ⟨fun h t _ ht hw hh => h t (hs.trans ht) ht hw hh, fun h t _ ht hw hh => h t ht ht hw hh⟩

/-- Start `-5` is start `0`. -/
theorem recurrence_negative_start {V R : Type} [Fintype V] (p : EnvPoint V)
    (key : Fin (Fintype.card V) ≃ V) (sel : R → Finset (Fin (Fintype.card V)))
    (lead : Slot → R) (G : TimeGrid) (π : Recurrence) (c stop : Time) :
    PatternRecurrence p key sel lead G π c (-5) stop ↔
      PatternRecurrence p key sel lead G π c 0 stop :=
  recurrence_nonpos_start p key sel lead G π c (-5) stop (by decide)

/-- The whole-pattern guard: the Streamlet recurrence (gap 3, span 4) reads 7
slots per window, so with slots of `2·Δ` (`Δ = 1`) a window starting at `0`
is read only when `stop ≥ 14`; with `stop = 13` nothing is read and
recurrence holds vacuously, even with an empty selection. -/
theorem span_guard (c : Time) :
    PatternRecurrence point1 pki1 (fun _ : Unit => ∅) (fun _ => ()) grid streamlet c 0 13 := by
  intro t ht _ hst _
  exfalso
  change t + ((3 + 4 : Nat) : Time) * ((2 : Nat) * 1) ≤ 13 at hst
  push_cast at hst
  have : (0 : Time) ≤ t := ht
  have h14 : t + 14 ≤ 13 := by linarith
  linarith

/-- Two validators, always awake, `Δ = 1`, horizon 10; only validator 0 is
honest. -/
def point2 : EnvPoint (Fin 2) :=
  ⟨⟨1, by decide, fun _ _ => true⟩, {0}, 10, fun _ _ => []⟩

/-- The identity PKI on two validators. -/
def pki2 : Fin (Fintype.card (Fin 2)) ≃ Fin 2 := finCongr (Fintype.card_fin 2)

/-- The only proposer key is the faulty validator 1's. -/
def faultySel : Unit → Finset (Fin (Fintype.card (Fin 2))) := fun _ => {pki2.symm 1}

/-- Recurrence has teeth: when the only selected proposer key is faulty, no
start admits recurrence of one honest proposer once a window (one slot of one
`Δ`) fits in the horizon. -/
theorem recurrence_has_teeth (c start : Time) (hs : start ≤ 5) :
    ¬ PatternRecurrence point2 pki2 faultySel (fun _ => ()) ⟨1, by decide⟩
      ⟨Pattern.single, 1⟩ c start 10 := by
  intro h
  have hw : max start 0 + ((⟨Pattern.single, 1⟩ : Recurrence).len : Time) *
      (⟨1, by decide⟩ : TimeGrid).slotLen point2.env.Δ ≤ 10 := by
    change max start 0 + ((1 + 0 : Nat) : Time) * ((1 : Nat) * 1) ≤ 10
    have : max start 0 ≤ 5 := max_le hs (by norm_num)
    push_cast
    linarith
  obtain ⟨_, k, hk, hh⟩ := h.exists_honest hw hw
  simp only [faultySel, Finset.mem_singleton] at hk
  subst hk
  simp [point2] at hh

/-- A two-header chain: inputs `[1, 2]` and `[2, 3]`. -/
def twoHeaders : Chain Unit :=
  [⟨.root, 1, encodeTxs [1, 2], ()⟩, ⟨.digest 7, 2, encodeTxs [2, 3], ()⟩]

/-- Its ledger keeps the first occurrence of `2`. -/
theorem ledgerOf_twoHeaders : ledgerOf twoHeaders = [1, 2, 3] := by
  simp [twoHeaders, ledgerOf, keepFirst, keepFresh]

end Consensus.Shape.Tests.Blocks
end

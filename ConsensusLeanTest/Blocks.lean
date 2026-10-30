module
public import ConsensusLean.Lemmas.Blocks.Facts
public import ConsensusLeanTest.Common
public import Mathlib.Tactic
@[expose] public section

/-! # Building-block tests

`slotAt?` on concrete grids; pattern recurrence holds from any start when
every slot is honest and ready (the Streamlet pattern `[0,1,2,3,4]`); a negative
progress start means start 0; the window guard counts the whole pattern
(`span_guard`); recurrence has teeth: on a two-node point
whose only selected proposer key is faulty it fails as soon as one window fits
in the horizon; `ledgerOf` of a two-header chain keeps first occurrences. -/

namespace Consensus.Blocks

/-! ## Locality and non-vacuity of recurrence (moved from the library) -/

variable {V : Type} [Fintype V]
variable {p : EnvPoint V} {key : Fin (Fintype.card V) ≃ V}
  {sel : Slot → Finset (Fin (Fintype.card V))} {G : TimeGrid}
  {ρ : Recurrence} {c start stop : Time}

/-- Bounded dependence: recurrence on `[start, stop]` reads only `Δ` and the
honest-ready status of the keys at times up to `min stop horizon` (readiness
at `t` is the awake history up to `t`). A point `p'` with the same `Δ`, no
larger effective window, and every honest-ready key of `p` also honest-ready
in `p'` at those times inherits the recurrence; in particular a point that
agrees with `p` up to `min stop horizon` (suffix replacement). -/
theorem PatternRecurrence.reads_upTo {p' : EnvPoint V} (hΔ : p'.env.Δ = p.env.Δ)
    (hh : min stop p'.horizon ≤ p.horizon)
    (hr : ∀ v t, t ≤ min stop p'.horizon → v ∈ p.honest → p.Ready c v t →
      v ∈ p'.honest ∧ p'.Ready c v t)
    (h : PatternRecurrence p key sel G ρ c start stop) :
    PatternRecurrence p' key sel G ρ c start stop := by
  intro t ht hst hhz
  rw [hΔ] at hst hhz ⊢
  have hm : t + (ρ.len : Time) * G.slotLen p.env.Δ ≤ min stop p'.horizon := le_min hst hhz
  obtain ⟨s, hs1, hs2, hall⟩ := h t ht hst (le_trans hm hh)
  refine ⟨s, hs1, hs2, fun j hj => ?_⟩
  obtain ⟨hne, hk⟩ := hall j hj
  refine ⟨hne, fun k hk' => (hr _ _ ?_ (hk k hk').1 (hk k hk')).2⟩
  have hl := G.slotLen_pos p.env.Δ_pos
  have hj' : (j : Time) ≤ ρ.pattern.span := by exact_mod_cast Pattern.le_span hj
  have hlen : (ρ.len : Time) = ((ρ.gap : Nat) : Time) + (ρ.pattern.span : Time) := by
    simp [Recurrence.len]
  rw [hlen] at hm
  rw [G.slotTime_add]
  nlinarith

/-- Recurrence is non-vacuous: if one whole window fits in `[max start 0, stop]`
and the horizon, the requirement yields an honest selected key. -/
theorem PatternRecurrence.exists_honest (h : PatternRecurrence p key sel G ρ c start stop)
    (hs : max start 0 + (ρ.len : Time) * G.slotLen p.env.Δ ≤ stop)
    (ht : max start 0 + (ρ.len : Time) * G.slotLen p.env.Δ ≤ p.horizon) :
    ∃ s k, k ∈ sel s ∧ key k ∈ p.honest := by
  obtain ⟨s, -, -, hall⟩ := h (max start 0) le_rfl hs ht
  obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil _ ρ.pattern.nonempty
  obtain ⟨⟨k, hk⟩, hks⟩ := hall j hj
  exact ⟨s + j, k, hk, (hks k hk).1⟩

end Consensus.Blocks

namespace Consensus.Shape.Tests.Blocks
open Consensus Blocks

/-- Slots of two `Δ`. -/
def grid : TimeGrid := ⟨2⟩

-- With `Δ = 3` slots are 6 units long: slot 2 starts at 12, slot 1 plus
-- offset 3 is at 9, and time 7 is no slot time.
theorem slotAt_slot_two : grid.slotAt? 3 0 12 = some 2 := by decide
theorem slotAt_with_offset : grid.slotAt? 3 3 9 = some 1 := by decide
theorem slotAt_between_slots : grid.slotAt? 3 0 7 = none := by decide
theorem slotAt_zero : grid.slotAt? 3 0 0 = some 0 := by decide
theorem slotAt_negative : grid.slotAt? 3 0 (-6) = none := by decide

/-- One validator, always awake, `Δ = 1`, horizon 100. -/
def point1 : EnvPoint (Fin 1) :=
  ⟨⟨1, by decide, fun _ _ => true⟩, Finset.univ, 100, fun _ _ => []⟩

/-- The Streamlet pattern: five consecutive honest slots, within every window
of 3 slots. -/
def streamlet : Recurrence := ⟨Pattern.range 5, 3⟩

/-- Every slot is honest and ready on `point1`, so the Streamlet pattern recurs
from any start. -/
theorem streamlet_recurrence (c start stop : Time) :
    PatternRecurrence point1 (pkiFin 1) (fun _ => Finset.univ) grid streamlet c start stop := by
  apply patternRecurrence_of_all (by decide)
  intro s j _
  refine ⟨⟨0, Finset.mem_univ _⟩, fun k _ => ⟨Finset.mem_univ _, ?_⟩⟩
  intro u _ _
  rfl

/-- A non-positive start is the same premise as start 0. -/
theorem recurrence_nonpos_start {V : Type} [Fintype V] (p : EnvPoint V)
    (key : Fin (Fintype.card V) ≃ V) (sel : Slot → Finset (Fin (Fintype.card V)))
    (G : TimeGrid) (π : Recurrence) (c start stop : Time) (hs : start ≤ 0) :
    PatternRecurrence p key sel G π c start stop ↔ PatternRecurrence p key sel G π c 0 stop := by
  unfold PatternRecurrence
  rw [max_eq_right hs, max_self]

/-- Start `-5` is start `0`. -/
theorem recurrence_negative_start {V : Type} [Fintype V] (p : EnvPoint V)
    (key : Fin (Fintype.card V) ≃ V) (sel : Slot → Finset (Fin (Fintype.card V)))
    (G : TimeGrid) (π : Recurrence) (c stop : Time) :
    PatternRecurrence p key sel G π c (-5) stop ↔ PatternRecurrence p key sel G π c 0 stop :=
  recurrence_nonpos_start p key sel G π c (-5) stop (by decide)

/-- The whole-pattern guard: the Streamlet recurrence (gap 3, span 4) reads 7
slots per window, so with slots of `2·Δ` (`Δ = 1`) a window starting at `0`
is read only when `stop ≥ 14`; with `stop = 13` nothing is read and
recurrence holds vacuously, even with an empty selection. -/
theorem span_guard (c : Time) :
    PatternRecurrence point1 (pkiFin 1) (fun _ => ∅) grid streamlet c 0 13 := by
  intro t ht hst _
  exfalso
  change t + ((3 + 4 : Nat) : Time) * ((2 : Nat) * 1) ≤ 13 at hst
  push_cast at hst
  have : (0 : Time) ≤ t := le_trans (le_max_left _ _) ht
  have h14 : t + 14 ≤ 13 := by linarith
  linarith

/-- Two validators, always awake, `Δ = 1`, horizon 10; only validator 0 is
honest. -/
def point2 : EnvPoint (Fin 2) :=
  ⟨⟨1, by decide, fun _ _ => true⟩, {0}, 10, fun _ _ => []⟩

/-- The only proposer key is the faulty validator 1's. -/
def faultySel : Slot → Finset (Fin (Fintype.card (Fin 2))) := fun _ => {(pkiFin 2).symm 1}

/-- Recurrence has teeth: when the only selected proposer key is faulty, no
start admits recurrence of one honest proposer once a window (one slot of one
`Δ`) fits in the horizon. -/
theorem recurrence_has_teeth (c start : Time) (hs : start ≤ 5) :
    ¬ PatternRecurrence point2 (pkiFin 2) faultySel ⟨1⟩
      ⟨Pattern.single, 1⟩ c start 10 := by
  intro h
  have hw : max start 0 + ((⟨Pattern.single, 1⟩ : Recurrence).len : Time) *
      (⟨1⟩ : TimeGrid).slotLen point2.env.Δ ≤ 10 := by
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
  simp only [twoHeaders, ledgerOf, List.flatMap_cons, List.flatMap_nil, Function.comp_apply,
    decode_encodeTxs]
  decide

end Consensus.Shape.Tests.Blocks
end

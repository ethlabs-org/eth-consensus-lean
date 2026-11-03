module
public import ConsensusLean.Main

@[expose] public section

/-! # Goldilocks as a value: pinned numbers

The Goldilocks skeleton and contract, with every number pinned by the
round-model FG-SA parameters (`FGSAParams`: round length `R` slots, lock
lifetime `lockK` slots, outage look-back `eta`; `Δ_F = Δ`, `κ = 2`, slow
arming). Every number is a `Δ`-coefficient computed from formulas; there are
no free numbers. The properties sheet (`GoldilocksSheet.lean`) states what
this contract, and the Goldilocks extras, give.

* Schema: two outputs, `confirmed` (serving the available **and** the stable
  capability: in the round model stable = confirmed) and `finalized` (final).
* Skeleton: slot proposals by one selected key per slot on a grid of `4·Δ`
  slots; polling disabled. The committee kinds `head`/`fin` and their phases
  are placeholders until the FG-SA migration fixes them.
* Numbers (`FGSAParams.params`): standard thresholds (½ sleepy, healthy faults
  below ⅓, ½ cover, ⅓ accountable); catch-up `18` (two slots + the `6Δ` join + one gate,
  gate F-3); arming lag `4·lockK + 6` (slow arming, the label before the
  outage label armed by `b₀`); outage no-sleep margin `max 19 (4·lockK + 8)`
  and recovery delay `9`; outage budget
  `min eta (4·lockK − 5)` (implies the sheet's (V) at the lifetime `L = 4·lockK − 1`,
  `budget_implies_V`; not the node's phase-sensitive (V) at lifetime `(4k − 2)Δ`,
  `Regimes.OutageWindowTimes`, which needs `4k − 6`); outage look-back `η = eta` (the
  outage regime is η-sleepy, Francesco 2026-10-28); heal points from `max g 0`:
  `29 + B_H^F(k)` for the available and stable outputs at proposer gap `k`
  slots, `29 + B_H^F(gf·R) + W_W(gf)` (first finality) for the final output at
  finality index `gf` (`29 = catchUp 18 + 1` readiness rounding `+ 10` GST-shift
  rounding); latency `4k + 6` (gap plus the `6Δ` inclusion delay) and
  `4·gf·R + 6 + W_W(gf)` for final.
* Progress: one honest ready proposer in every window of `k` slots (available,
  stable); for final at index `gf`, `3R + κ` consecutive honest ready
  proposers (`Pattern.range`) in every window of `gf·R` slots. The whole
  pattern of a window must fit before the window's stop (the guard of
  `PatternRecurrence`): the final latency and heal numbers cover one window
  plus the `3R + κ − 1` slots of span for every `R` and `gf`
  (`final_latency_covers_window`, `final_heal_covers_window` in the sheet).

`reference_bounds` checks the formulas against the reference numbers of the
FG-SA paper (fgsa-protocol.tex 3018–3026). -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (Public SelSpec pubOf)

/-- The Goldilocks output identifiers. -/
inductive GOut where
  | confirmed
  | finalized
  deriving DecidableEq, Repr

/-- The Goldilocks schema: `confirmed` is available and stable (aliased: the
round model's stable ledger is the confirmed one), `finalized` final. -/
def goldilocksSchema : OutputSchema :=
  ⟨GOut, fun
    | .available => some .confirmed
    | .stable => some .confirmed
    | .final => some .finalized⟩

/-- Placeholder committee kinds (the FG-SA migration fixes them). -/
inductive GKind where
  | head
  | fin
  deriving DecidableEq, Repr

/-- Slots of `4·Δ`. -/
def goldilocksGrid (pub : Public) : TimeGrid := ⟨4 * pub.Δ, mul_pos (by decide) pub.Δ_pos⟩

/-- The Goldilocks skeleton: one proposer per slot, polling disabled, the two
placeholder committee kinds at phases 1 and 2, every key in each. -/
def goldilocksSkeleton (pub : Public) : Skeleton pub.n where
  grid := goldilocksGrid pub
  proposerSel := fun _ => .sized 1
  pollSel := .fixed ∅
  Kind := GKind
  decKind := inferInstance
  kinds := [.head, .fin]
  phase := fun | .head => pub.Δ.toNat | .fin => 2 * pub.Δ.toNat
  kindSel := fun _ => .fixed Finset.univ

/-- Round-model FG-SA parameters (`Δ_F = Δ`, `κ = 2`, slow arming): the round
length `R` (slots), the lock lifetime parameter `lockK` (slots; `L = (4·lockK −
1)·Δ`) and the outage look-back `eta` (`Δ`-coefficient; FG-SA's `η = eta·Δ`). -/
structure FGSAParams where
  R : Nat
  lockK : Nat
  eta : Nat
  hR : 2 ≤ R
  hLock : 2 ≤ lockK
  hEta : 1 ≤ eta

namespace FGSAParams

/-- The finality round offset `κ = 2` (at `Δ_F = Δ`). -/
def κ : Nat := 2

variable (pp : FGSAParams)

/-- The lock lifetime `L` (`Δ`-coefficient). -/
def L : Nat := 4 * pp.lockK - 1

/-- The round length `P` (`Δ`-coefficient). -/
def P : Nat := 4 * pp.R

/-- The healing gap of `k` slots, `Δ`-coefficient. -/
def Γ (k : Nat) : Nat := 4 * k

/-- `B_H^F` (second branch) at proposer gap `k` slots (fgsa-protocol.tex
549–561, `ε = 0` at `κ = 2`). -/
def bhf2 (k : Nat) : Nat :=
  max (12 * pp.L + 12 * Γ k + 12 * pp.P + 49) (8 * pp.L + 10 * Γ k + 14 * pp.P + 19)

/-- `B_H^F` (first branch, available when `lockK ≤ 2R + 1`). -/
def bhf1 (k : Nat) : Nat :=
  max (6 * pp.L + 12 * Γ k + 12 * pp.P + 61) (4 * pp.L + 10 * Γ k + 14 * pp.P + 27)

/-- The healing bound `B_H^F` at proposer gap `k` slots (`Δ`-coefficient). -/
def bhf (k : Nat) : Nat :=
  if pp.lockK ≤ 2 * pp.R + 1 then min (pp.bhf1 k) (pp.bhf2 k) else pp.bhf2 k

/-- The finality window `W_W(gf) = (gf + 2)·P + β + Δ` with `β = 4κΔ`
(`Δ`-coefficient). -/
def wW (gf : Nat) : Nat := (gf + 2) * pp.P + 4 * κ + 1

/-- The readers' catch-up: two slots, the `6Δ` join, one gate (gate F-3). -/
def catchUp : Nat := 18

/-- Heal points from `max g 0` (`Δ`-coefficients): `29 + B_H^F(k)` for the
available and stable outputs at gap `k`; first finality `29 + B_H^F(gf·R) +
W_W(gf)` for the final output at index `gf`. `29 = 18 + 1 + 10`: catch-up,
readiness rounding, GST-shift rounding. -/
def heal : Capability → ℕ+ → Nat
  | .final, gf => 29 + pp.bhf (gf * pp.R) + pp.wW gf
  | _, k => 29 + pp.bhf k

/-- Transaction latencies (`Δ`-coefficients): gap plus the `6Δ` inclusion
delay; for final, the inclusion `4·gf·R + 6` followed by the FF5 window
`W_W(gf)`. -/
def latency : Capability → ℕ+ → Nat
  | .final, gf => 4 * (gf * pp.R) + 6 + pp.wW gf
  | _, k => 4 * k + 6

/-- The arming lag `(4·lockK + 6)·Δ` (slow arming, one slot before the
outage label: the label before it is fully armed by `b₀`). -/
def lag : Nat := 4 * pp.lockK + 6

/-- The outage no-sleep margin `max 19 (4·lockK + 8)`: the formation window,
the restored votes, and catch-up plus one. -/
def noSleep : Nat := max 19 (4 * pp.lockK + 8)

/-- The outage recovery delay `9` (`Δ`-coefficient: the restored votes of
the locked validators, about two slots after the window). -/
def recovery : Nat := 9

/-- The outage budget `min eta (4·lockK − 5)` (implies the sheet's (V) at `L = 4·lockK − 1`,
`budget_implies_V`; the node's (V) at lifetime `(4k − 2)Δ` needs `4k − 6`). -/
def budget : Nat := min pp.eta (4 * pp.lockK - 5)

/-- The pinned Goldilocks numbers: standard thresholds, outage look-back
`η = eta`, no-sleep margin and recovery delay, and row ratio `1` (`Params.standard`;
transitional: the healthy regime assumes `ΔF ≤ Δ` until the arbitrary-ratio port). -/
def params : Params ℕ+ :=
  { Params.standard catchUp pp.lag pp.budget pp.heal pp.latency with
    η := pp.eta, noSleep := pp.noSleep, recovery := FGSAParams.recovery }

/-- The finality recurrence at index `gf`: `3R + κ` consecutive honest ready
proposers in every window of `gf·R` slots. -/
def finRec (gf : ℕ+) : Recurrence :=
  ⟨Pattern.range ⟨3 * pp.R + κ, by unfold κ; omega⟩,
    ⟨gf * pp.R, Nat.mul_pos gf.pos (by have := pp.hR; omega)⟩⟩

/-- The progress requirements: `finRec gf` for final, one honest ready
proposer in every window of `k` slots otherwise. -/
def progress : Capability → ℕ+ → ProgressReq
  | .final, gf => .recur (pp.finRec gf)
  | _, k => .recur ⟨Pattern.single, k⟩

end FGSAParams

/-- The Goldilocks contract at the pinned FG-SA numbers (index: the gap `k`
slots, for final the finality index `gf`). -/
def goldilocksContract (pp : FGSAParams) : Contract ProgressReq where
  Idx := ℕ+
  idx_nonempty := ⟨1⟩
  params := pp.params
  progress := pp.progress

/-- The pinned numbers are admissible (standard thresholds, catch-up `18`, a
positive budget). -/
theorem goldilocks_admissible (pp : FGSAParams) : (goldilocksContract pp).params.Admissible := by
  have hb : 1 ≤ pp.budget := by
    have := pp.hEta; have := pp.hLock
    unfold FGSAParams.budget; omega
  exact { Params.standard_admissible (Idx := ℕ+) (catchUp := FGSAParams.catchUp)
    (lag := pp.lag) (heal := pp.heal) (latency := pp.latency) (by decide) hb with }

/-- The Goldilocks progress fits every family with one proposer per slot. -/
theorem goldilocks_progressFits {Info : Type} [DecidableEq Info] [Countable Info]
    (pp : FGSAParams) (F : ShapeFamily goldilocksSchema Info)
    (hsel : ∀ pub s, (F pub).skel.proposerSel s = .sized 1) :
    ProgressFits (goldilocksContract pp) F := by
  intro cap k pub
  cases cap <;> exact hsel pub

/-- Goldilocks recurrence requirements tolerate any number not ready and a
bad proposer slot in every window: gap `2` for available and stable (one
honest ready proposer in every two slots), finality index `gf = 5` for final
(`5R ≥ 3R + κ + 1` slots for the pattern span `3R + κ − 1` plus two, as
`R ≥ 2`). -/
theorem goldilocks_progressTolerant (pp : FGSAParams) :
    ProgressTolerant goldilocksSchema (goldilocksContract pp) := by
  intro cap ho N
  cases cap
  · exact ⟨(2 : ℕ+), show (⟨Pattern.single, 2⟩ : Recurrence).BadSlotSlack by decide⟩
  · exact ⟨(2 : ℕ+), show (⟨Pattern.single, 2⟩ : Recurrence).BadSlotSlack by decide⟩
  · refine ⟨(5 : ℕ+), ?_⟩
    change (pp.finRec 5).pattern.span + 2 ≤ ((pp.finRec 5).gap : Nat)
    have := pp.hR
    have hs : (pp.finRec 5).pattern.span = 3 * pp.R + FGSAParams.κ - 1 :=
      Pattern.span_range _
    have hg : ((pp.finRec 5).gap : Nat) = 5 * pp.R := rfl
    rw [hs, hg]
    unfold FGSAParams.κ
    omega

/-- Reference numbers (fgsa-protocol.tex 3018–3026): `B_H^F` at `k = 2` is
`295Δ` (`R = 2`) and `343Δ` (`R = 3`); the paper's `344Δ` and `412Δ` add
`W_W(3)` to `B_H^F` at the **independent** healing gap `k = 2` (`lockK = 2`,
`κ = 2`). They are FG-SA reference values, not the pinned contract's
`heal .final 3`, which couples the gaps (`B_H^F(3·R)`). -/
theorem reference_bounds :
    (⟨2, 2, 1, le_rfl, le_rfl, le_rfl⟩ : FGSAParams).bhf 2 = 295 ∧
    (⟨3, 2, 1, by decide, le_rfl, le_rfl⟩ : FGSAParams).bhf 2 = 343 ∧
    (⟨2, 2, 1, le_rfl, le_rfl, le_rfl⟩ : FGSAParams).bhf 2 +
      (⟨2, 2, 1, le_rfl, le_rfl, le_rfl⟩ : FGSAParams).wW 3 = 344 ∧
    (⟨3, 2, 1, by decide, le_rfl, le_rfl⟩ : FGSAParams).bhf 2 +
      (⟨3, 2, 1, by decide, le_rfl, le_rfl⟩ : FGSAParams).wW 3 = 412 := by
  decide

end Consensus.Shape

end

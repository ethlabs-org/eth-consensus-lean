module
public import ConsensusLean.Spec.Problem.Basic

@[expose] public section

/-! # Goldilocks: shared parameters

The parameters both components read (composition.tex §"Model"; decomposition §1.1): `n ≥ 1`
validators `Fin n` of weight `1` and the quorum `q = ⌈2n/3⌉`; the delivery parameter `Δ > 0`;
the slot start times `t_s` (public times, `t_0 = 0`, strictly increasing; the AC fixes them);
the genesis root; and the FG timeout delay `δ_t` in slots (fg.tex: the AC
sets it). Time is integer (`Consensus.Time`). The FG's own parameter bundle `FG.FGParams` is
derived from these where both are in scope (the FG store), not declared twice.

This module holds only what the Challenge statements reach; `Params.q`, the quorum on `Params` (the
FG reads `FG.FGParams.q`), is in `Milestones/Spec/Common/Params` (docs/decisions.md, 2026-11-04). -/

namespace Consensus.Goldilocks

/-- The shared parameters of a Goldilocks node. -/
structure Params where
  /-- The number of validators. -/
  n : Nat
  hn : 1 ≤ n
  /-- The delivery parameter of blocks and AC messages; the public times are its multiples. -/
  Δ : Time
  hΔ : 0 < Δ
  /-- The start time `t_s` of slot `s`. -/
  slotTime : Nat → Time
  slotTime_zero : slotTime 0 = 0
  slotTime_strictMono : StrictMono slotTime
  /-- Every slot starts at a public time. -/
  slotTime_public : ∀ s, Δ ∣ slotTime s
  /-- The root of genesis. -/
  genesisRoot : Nat
  /-- The FG timeout delay `δ_t`, in slots. -/
  δt : Nat

namespace Params

variable (P : Params)

/-- A public time: a multiple of `Δ`. -/
def IsPublic (t : Time) : Prop := P.Δ ∣ t

/-- The slot of time `t`, `slot(t)`: the greatest `s` with `t_s ≤ t` (`0` before time `0`).
The search is bounded by `t` itself, since `t_s ≥ s` for strictly increasing integer start
times from `t_0 = 0`. -/
def slotOf (t : Time) : Nat := Nat.findGreatest (fun s => P.slotTime s ≤ t) t.toNat

end Params

end Consensus.Goldilocks

end

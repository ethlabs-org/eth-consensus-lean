module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.Healed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.EngineSteps
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Rows
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Records
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.FinPair

public section

/-! # Goldilocks Obligations: parents above a crossing report

Case (A) of `window_justifies_or_crossed` is an honest report `C` with `h < σ[C].h`. Through C3
(`Healed.c3`) it bounds the parents of later honest proposals.

* `toFG_live_fast_lock`: the block `C` that `ac_to_fg` returns at an honest call is in the
  frame, and its root is the block of a live fast lock of that call.
* `crossed_parents_above`: if the report is at a time `≥ tH`, every honest proposal of a slot
  `s` with `t_r + Δ ≤ t_s` has an honest parent `Pr ⪰ C` with `h < σ[Pr].h` at each holder.
* `window_justifies_or_parents_above`: `window_justifies_or_crossed` with case (A) in this form
  (a crossing report after cutZ by `v`; for proposals with `v + Δ ≤ t_s` when `tH ≤ t_r`).
* `window_justifies_or_parents_above_of_le_cutZ`: the same under `tH ≤ cutZ(gR)`, with case
  (A) without the condition on `t_r`. -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation

open AC (ACParams ReplayOrder Payload gbar)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **A report is a live fast lock block, or a deep candidate.** If `ac_to_fg` returns `C` at the
call of `z` at cut `r`, then `C` is in the frame and either some live fast lock `l` of that call
has `l.block = C.root` (and slot `≥ slot(t_r) − 2`), or, with deep sources on
(`deepDepth = some D`) and no fast-lock candidate, `C` is a deep candidate under the deep anchor. -/
theorem toFG_live_fast_lock {z : Fin sp.n} {r : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {C : AC.Blk sp.n (List (FG.Att sp.n))} (hto : AC.ToFGAt tr.projAC z r ell C) :
    C ∈ ell.frame.tree ∧
      ((∃ l ∈ AC.liveLocks sp (tr.projAC.state z r).locks ell.frame (tr.time r),
        l.block = C.root ∧ l.fast = true ∧ sp.slot (tr.time r) ≤ l.slot + 2) ∨
      ∃ D a, sp.deepDepth = some D ∧
        AC.deepest ell.frame (AC.toFGCandidates sp (tr.projAC.state z r) ell.frame
          (tr.projAC.time r)) = none ∧
        AC.deepAnchor sp (tr.projAC.state z r) ell.frame (tr.projAC.time r) = some a ∧
        C ∈ AC.toFGDeepCandidates sp D a (tr.projAC.state z r) ell.frame (tr.projAC.time r)) := by
  obtain ⟨-, -, h⟩ := hto
  obtain ⟨hCv, hs⟩ := AC.toFG_source h
  refine ⟨hCv.1, ?_⟩
  rcases hs with hC | ⟨D, a, hD, ha, hn, hC⟩
  · exact Or.inl hC.2
  · exact Or.inr ⟨D, a, hD, hn, ha, hC⟩

end Consensus.Goldilocks.Obligations

end

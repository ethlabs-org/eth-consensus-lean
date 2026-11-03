module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.ProposalWindow
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Healed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.EngineSteps
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Rows
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Records
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.FinPair
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Service

public section

/-! # Goldilocks Refinement: parents above a crossing report (L5.4, WI-18)

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

namespace Consensus.Goldilocks.Refinement

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **A report is a live fast lock block.** If `ac_to_fg` returns `C` at the call of `z` at
cut `r`, then `C` is in the frame and some live fast lock `l` of that call has
`l.block = C.root` (and slot `≥ slot(t_r) − 2`). -/
theorem toFG_live_fast_lock {z : Fin sp.n} {r : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} (hto : SA.ToFGAt tr.projAC z r ell C) :
    C ∈ ell.frame.tree ∧
      ∃ l ∈ SA.liveLocks sp (tr.projAC.state z r).locks ell.frame (tr.time r),
        l.block = C.root ∧ l.fast = true ∧ sp.slot (tr.time r) ≤ l.slot + 2 := by
  obtain ⟨-, -, h⟩ := hto
  have hC : C ∈ SA.toFGCandidates sp (tr.projAC.state z r) ell.frame (tr.projAC.time r) := by
    unfold SA.acToFG at h
    split_ifs at h
    split at h
    · cases h
    · rename_i C' hC'
      split_ifs at h
      cases h
      exact (SA.deepest_mem hC').1
  exact ⟨hC.1.1, hC.2⟩

end Consensus.Goldilocks.Refinement

end

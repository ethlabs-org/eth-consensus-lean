module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.WindowParents
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.OperationalReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeBase

public section

/-! # Goldilocks Obligations: window reports from a unanimous slot

`window_justifies_or_parents_above_after` takes the report duty `hreports'`: every honest node
reports some `C ⪰ X` at a cut in `[tH, v]`, for each held `X` with root `T`. Here a unanimous
slot `u` on an honest `P` with `X ⪯ P` discharges it, through
`UpTo.report_cover_of_unanimous`. That theorem has an escape case (an honest report `C ⪰ P`
strictly higher than `P`), which these statements keep as a separate disjunct.

* `report_slot_le_time`: an honest report `C ⪰ P` is at a cut `r` with `t_{P.slot} ≤ t_r`.
* `window_reports_of_unanimous`: the report duty from a unanimous slot, with `tH ≤ t_u` and
  `t_u + 6Δ ≤ v`, or the escape report in `[tH, v]`.
* `window_justifies_or_parents_above_unanimous`: the window theorem with the report duty
  replaced by the unanimous-slot premises.
* `window_justifies_or_parents_above_unanimous'`: the same with a held `X` of root `T` at
  height `h`; the escape folds into case (A), so the conclusion is two-way.
* `window_justifies_or_parents_above_unanimous''`: the same without `hXe`, from
  `lock_entry_block`. -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **A report above `P` is not before the slot of `P`.** If an honest `z` reports `C` at cut
`r` and `P ⪯ C` in the honest tree, then `t_{P.slot} ≤ t_r`. -/
theorem report_slot_le_time (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {z : Fin sp.n} (hz : z ∈ H) {r : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {P C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hto : SA.ToFGAt tr.projAC z r ell C) (hPC : Anc (tr.HonestBlocks H) P C) :
    sp.ts (P.slot : Int) ≤ tr.time r := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hC := (toFG_live_fast_lock hto).1
  have hCs : C.slot ≤ sp.slot (tr.time r) := SA.frame_slot_le sp hr hz hto.1 C hC
  have hPs := Healing.slot_le_of_anc hr.coherent hPC
  exact (SA.ts_le_iff_le_slot sp (hrun.time_nonneg r) _).2 (by omega)


end Consensus.Goldilocks.Obligations

end

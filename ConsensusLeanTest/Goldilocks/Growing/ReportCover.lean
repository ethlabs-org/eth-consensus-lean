module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.ReportCoverDelayed

public section

/-! # The growing report cover at the stock signing calendar

`report_cover_stock_calendar` reads the growing report cover from the stock calendar, which signs
at every public time (`SignCalendarAt … (fun _ _ => true)`), through its stock entry point
`report_cover_of_unanimous_responsive_at`: the delayed cover at signing gap `0`
(`signGapAt_true`). The arbitrary-trace form `report_cover_of_unanimous_at` takes
`GrowingAllTicksSign` instead. -/

namespace Consensus.Goldilocks.Healing.Growing.Test

open AC (ACParams Payload)

variable {sp : ACParams}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- Under the stock signing calendar, every node honest at `t_u + 6Δ` reports a descendant of a
unanimous post-drain proposal `P` of slot `u` by then, or a node honest at its report and at `c_z`
reports a strict height increase above `P` by then. -/
theorem report_cover_stock_calendar {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK)
    (hcal : tr.SignCalendarAt proposer dg H (fun _ _ => true))
    {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H) (hslot : P.slot = u) (hu : 0 < u)
    (hPg : P.root ≠ sp.genesisRoot)
    (hun : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u) (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hTb : sp.ts u + 6 * sp.Δ ≤ b) :
    (∀ y, y ∈ H (sp.ts u + 6 * sp.Δ) → ∃ r e R, AC.ToFGAt tr.projAC y r e R ∧
      tr.time r ≤ sp.ts u + 6 * sp.Δ ∧ Anc (tr.HonestBlocksAt H) P R) ∨
    (∃ x r e C, x ∈ H (max (cutZ sp.toParams g) (tr.time r)) ∧ AC.ToFGAt tr.projAC x r e C ∧
      tr.time r ≤ sp.ts u + 6 * sp.Δ ∧ Anc (tr.HonestBlocksAt H) P C ∧
      ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h) :=
  report_cover_of_unanimous_responsive_at hp hcal hP hslot hu hPg hun hgu hR hTb

end Consensus.Goldilocks.Healing.Growing.Test

end

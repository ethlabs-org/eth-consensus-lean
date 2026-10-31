module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Pivot

public section

/-! # Goldilocks under `Sleepy`: the updater's finalized tip is below the honest proposal (open)

workbench#12 §4, "`F ≤ P` through the update": at an honest node's joined update of slot `s`
(its tick at `t_s + 6Δ`), its `Σ.F` is at or below the honest proposal `P` of slot `s`. Before
`t_s + 6Δ` the honest sources have labels at most `s + 1` (`fcRoot_of_rows` with the rows the
updater holds); label-`s` sources are below `P`, older ones below `Q = P.parent`, and a
label-`(s+1)` optimistic source is an ancestor of an honest slot-`(s+1)` head extending `P`; a
finalized entry is a strict ancestor of its honest finality-pair source, of a smaller slot, so
on `P`'s chain it is at or below `P`. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- **The updater's `Σ.F` is at or below `P`** (workbench#12 §4; open). -/
theorem updater_F_anc_proposal {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {ΔF : Time} (hrun : GoldilocksRun dg H tr)
    (hnc : NoCollRun dg tr) (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {y : Fin sp.n}
    (hy : y ∈ H) {k₀ : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hu : SA.UpdateAt tr.projAC y k₀ s ℓ) :
    Anc (tr.HonestBlocks H) (tr.state y k₀).fg.F P := by
  sorry

end Consensus.Goldilocks.Compose

end

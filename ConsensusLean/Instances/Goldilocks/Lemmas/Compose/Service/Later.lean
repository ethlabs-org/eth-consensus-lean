module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Adopt

public section

/-! # Goldilocks under `Sleepy`: a later update adopts the honest proposal

For R.2 (`IncludeSleepy`, a reader that slept through `t_s + 6Δ`): after an honest node's joined
update of any slot `s' ≥ s`, its record names a block extending the honest proposal `P` of slot
`s`, or its `Σ.F` extends `P` (then the record, if in the frame, extends `Σ.F`, and otherwise the
confirmed tip is `Σ.F`). For `s' = s` this is `update_adopts`. For `s' > s`, `P` is a regular
origin (the update of slot `s` at an honest joined node adopts it), every honest vote of slot `s'`
extends it (S2), the honest batch of slot `s'` reaches the joined updater resolved, so when `P` is
in the frame it has a strict majority and the result extends it, and is not vetoed; when `Σ.F`
has passed `P`, the second disjunct holds. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- **A later update adopts `P`** (`s' > s`; open). -/
theorem later_update_adopts_gt {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {ΔF : Time} (hrun : GoldilocksRun dg H tr)
    (hnc : NoCollRun dg tr) (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {y : Fin sp.n}
    (hy : y ∈ H) {k₀ s' : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} (hss : s < s')
    (hu : SA.UpdateAt tr.projAC y k₀ s' ℓ) :
    ∃ E ∈ tr.HonestBlocks H, E.root = (tr.state y (k₀ + 1)).ac.latestConfirmed ∧
      (Anc (tr.HonestBlocks H) P E ∨ Anc (tr.HonestBlocks H) P (tr.state y (k₀ + 1)).fg.F) := by
  sorry

/-- **An update of a slot `s' ≥ s` adopts the honest proposal of slot `s`**: the record names a
block extending `P`, or `Σ.F` extends `P`. -/
theorem later_update_adopts {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {ΔF : Time} (hrun : GoldilocksRun dg H tr)
    (hnc : NoCollRun dg tr) (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {y : Fin sp.n}
    (hy : y ∈ H) {k₀ s' : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} (hss : s ≤ s')
    (hu : SA.UpdateAt tr.projAC y k₀ s' ℓ) :
    ∃ E ∈ tr.HonestBlocks H, E.root = (tr.state y (k₀ + 1)).ac.latestConfirmed ∧
      (Anc (tr.HonestBlocks H) P E ∨ Anc (tr.HonestBlocks H) P (tr.state y (k₀ + 1)).fg.F) := by
  rcases hss.lt_or_eq with hlt | rfl
  · exact later_update_adopts_gt hrun hnc hsl hp hP hPs hpj hy hlt hu
  · obtain ⟨E, hE, hEr, hPE⟩ := update_adopts hrun hnc hsl hp hP hPs hpj hy hu
    exact ⟨E, hE, hEr, Or.inl hPE⟩

end Consensus.Goldilocks.Compose

end

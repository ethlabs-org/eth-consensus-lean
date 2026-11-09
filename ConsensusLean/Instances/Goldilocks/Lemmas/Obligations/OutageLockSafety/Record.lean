module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthyEffective
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.FamilyRecord
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Reader
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageRead
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Outage lock safety: the record from a restored update (`record_above_from`)

The writes of an honest record after its update of a restored label `m ≥ r` come from results of
labels `> m` (compatible with `P` by (R)) and from optimistic selections (compatible with `P`,
`fastLock_compatible`); with OB-F (`OutageLockInv.caches`) this is the landed
`EffectiveRecordInterval` (`record_interval_after`). With the veto case of
`late_reader_record_cover` (the live locks are compatible with `P` by (i)), an update result above
`P` keeps the effective record above `P` at every later cut (`record_above_from`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}
  {D : OutageLockPremises tr H proposer dg}

/-- **The record interval after the restored labels**: from a cut at or after the update time of
label `r`, every write of `y`'s record is compatible with `P` and `Σ.F` is compatible with `P`. -/
theorem record_interval_after (hinv : ∀ i, OutageLockInv D i) {y : Fin sp.n} (hy : y ∈ H)
    {i j : Nat} (hi : sp.ts D.r + 6 * sp.Δ ≤ tr.time i) :
    Obligations.EffectiveRecordInterval tr H y i j D.P := by
  exact FamilySafety.record_interval_after_instance hinv hy hi

/-- **`record_above_from`**: after an honest update of a restored label `m ≥ r` whose result
`C` extends `P`, the effective record of the updater extends `P` at every later cut, whether the
result is accepted or vetoed. -/
theorem record_above_from (hinv : ∀ i, OutageLockInv D i) {w : Fin sp.n} (hw : w ∈ H)
    {c m : Nat} {ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)}
    (hu : SA.UpdateAt tr.projAC w c m ℓ) {C : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (Vote sp.n)} (hR : SA.ResultAt tr.projAC w c m C CV) (hrm : D.r ≤ m)
    (hPC : Anc (tr.HonestBlocks H) D.P C) :
    ∀ i, c < i → Anc (tr.HonestBlocks H) D.P ((SA.lookup (Node.frame (tr.state w i))
      (tr.state w i).ac.latestConfirmed).getD (tr.state w i).fg.F) := by
  exact FamilySafety.record_above_from_instance hinv hw hu hR hrm hPC

end Consensus.Goldilocks.Compose

end

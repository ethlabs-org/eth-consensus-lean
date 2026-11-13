module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Unlocked

public section

/-! # Fast locks under growing faults

Provenance returns the writing cut, not just the lock's slot. Counts are read at that cut;
subsequent compromise of the writer does not invalidate its historical write.
-/

namespace Consensus.Goldilocks.SA.Growing

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP}
  {tr : SATrace sp FGP ro} {H : Time → Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {proposer : Nat → Fin sp.n}

/-- A stored fast lock lies below a fast lock written earlier by the same node.
The returned cut `c` is the cut at which its votes were counted. -/
theorem fast_lock_provenance (hr : Goldilocks.Growing.ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {y : Fin sp.n} {n : Nat} (hy : y ∈ H (tr.time n))
    {l : Lock} (hl : l ∈ (tr.state y n).locks) (hf : l.fast = true) :
    ∃ c < n, ∃ B CV, FastLockAt tr y c l.slot B CV ∧ y ∈ H (tr.time c) ∧
      ∃ L ∈ U, L.root = l.block ∧ Anc U L B := by
  have hm := hr.time_mono
  have hs : (tr.upTo (tr.time n)).state y n = tr.state y n :=
    Trace.upTo_state tr y fun _ hk => hm hk.le
  obtain ⟨c, hc, B, CV, hfl, hL⟩ := SA.fast_lock_provenance (hr.upTo (hr.time_nonneg n))
    hy n l (hs ▸ hl) hf
  exact ⟨c, hc, B, CV, (upTo_fastLockAt hm).mp hfl |>.2,
    hr.antitone (hm hc.le) hy, hL⟩

/-- The fast-lock count is charged at its writing cut. Count validators, not raw votes:
the optimistic branch can include multiple votes from an equivocating validator. -/
theorem fastLock_counted (hrun : ACRun proposer tr H U)
    {y : Fin sp.n} {c s : Nat} (hy : y ∈ H (tr.time c))
    {B : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hfl : FastLockAt tr y c s B CV) :
    sp.committeeSize ≤ 2 * {u | ∃ v ∈ CV, v.val = u}.ncard ∧
      ∀ v ∈ CV, v.slot = s ∧ ∃ R ∈ U, R.root = v.head ∧ R.slot ≤ s ∧ Anc U B R := by
  exact SA.fastLock_counted (hrun.upTo (hrun.localRun.time_nonneg c)) hy
    ((upTo_fastLockAt hrun.localRun.time_mono).mpr ⟨le_rfl, hfl⟩)

end Consensus.Goldilocks.SA.Growing

end

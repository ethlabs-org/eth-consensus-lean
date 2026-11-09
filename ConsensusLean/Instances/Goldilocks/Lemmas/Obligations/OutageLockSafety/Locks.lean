module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.FamilyInstance
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.OutagePostStop
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Unlocked
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Outage lock safety: (i), no honest lock conflicting with `P`

Every stored honest lock lies below a block written at an earlier cut (`lock_origin`,
`fast_lock_provenance`, `slow_lock_compatible`):

* a lock of a label `< j₀` lies below an origin within `b₀` (`compatible_of_within`);
* a fast lock (update or optimistic) of a slot `≥ j₀` on a block conflicting with `P` would have
  its counted validators in `Hᶜ ∪ W` (OL-W), against `n ≤ 2·|counted|` and N6;
* a slow lock has an unpolluted label in its window (`exists_unpolluted_label`), whose results
  are compatible with `P` (R). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}
  {D : OutageLockPremises tr H proposer dg}

/-- A counted vote of an honest validator at an honest fast lock was cast at a cut no later than
the lock's. -/
theorem fastLock_honest_vote (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {j s : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (Vote sp.n)} (hfl : SA.FastLockAt tr.projAC y j s B CV) {v : Vote sp.n}
    (hv : v ∈ CV) (hvH : v.val ∈ H) :
    ∃ j' ≤ j, ∃ e, SA.VoteAt tr.projAC v.val j' e ∧ e.msg = v := by
  exact FamilySafety.fastLock_honest_vote_family
    (FamilySafety.lockFacts_goldilocks hrun hnc) hy hfl hv hvH

/-- An origin of a label below `j₀` whose event precedes the cut is within `b₀`. -/
private theorem within_of_label_lt (D : OutageLockPremises tr H proposer dg)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {s n : Nat} (hC : OriginBefore tr H C s n)
    (hs : s < D.j₀) : OriginWithin tr H C s D.b₀ := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer D.hrun D.hnc).localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨z, hz, k, -, CV, hRO⟩ := originBefore_iff.1 hC
  have hsj := ts_le_ts (sp := sp) (show s + 1 ≤ D.j₀ by omega)
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hj₀ := D.hj₀.1
  refine originWithin_iff.2 ⟨z, hz, k, CV, ?_, hRO⟩
  rcases hRO with ⟨ℓ, hu, -, -⟩ | ⟨ℓ, A, -, hslot, -⟩
  · have ht : tr.time k = sp.ts s + 6 * sp.Δ := hu.2.2.1
    linarith
  · have : tr.time k < sp.ts (s + 1 : Nat) := by
      by_contra h
      have := (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) ((s + 1 : Nat) : Int)).1 (not_lt.1 h)
      rw [hslot] at this
      omega
    linarith

/-- **(i) at a cut**: with (H)/S5V at the cuts before `n` and (R) at the cuts before `n`,
every lock stored at cut `n` by an honest node names a held block compatible with `P`. -/
theorem OutageVoteInv.locks_compatible {n : Nat} (hvi : OutageVoteInv D n)
    (hres : ∀ y ∈ H, ∀ k < n, ∀ m C CV, SA.ResultAt tr.projAC y k m C CV →
      (m ≤ D.j₀ ∨ D.r ≤ m) → Compatible (tr.HonestBlocks H) C D.P)
    {y : Fin sp.n} (hy : y ∈ H) {l : SA.Lock} (hl : l ∈ (tr.state y n).ac.locks) :
    ∃ L ∈ (tr.state y n).fg.tree, L.root = l.block ∧ Compatible (tr.HonestBlocks H) L D.P := by
  exact FamilySafety.locks_compatible_instance hvi hres hy hl

end Consensus.Goldilocks.Compose

end

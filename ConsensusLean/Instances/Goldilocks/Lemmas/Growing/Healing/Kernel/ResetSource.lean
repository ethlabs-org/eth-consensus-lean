module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Unlocked
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Reset
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Arith
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Reset sources and the original snapshot frontier

The reset signer is honest at its signing and at the snapshot `c_z` (`IsReset`), which bounds
the reset below by the snapshot alone: no fault count, service or awake premise.
-/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload Vote)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}
variable {hold : Time}

private theorem hmax_le_snapshot {y : Fin sp.n} (hy : y ∈ H (cutZ sp.toParams g))
    {j : Nat} (hj : FirstCutAfter tr j (cutZ sp.toParams g)) :
    (tr.state y j).fg.hmax ≤ HZ tr H g := by
  refine le_csSup (((Set.finite_range fun z => (tr.state z j).fg.hmax).subset ?_).bddAbove)
    ⟨y, hy, j, hj, rfl⟩
  rintro _ ⟨z, -, j', hj', rfl⟩
  obtain rfl := hj'.unique hj
  exact ⟨z, rfl⟩

/-- **The reset lies after the snapshot.** The reset signer is honest at `c_z` (`IsReset`), so a
reset at or before `c_z` signs from its own entry of height `H_z + 1`, which it still holds at the
snapshot cut, where its height is at most `H_z`. The growing form of `cutZ_lt_reset_of_snapshot`;
no fault count. -/
theorem cutZ_lt_reset_of_snapshot_at
    {ini} (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    (hsnapshot : ∃ j, FirstCutAfter tr j (cutZ sp.toParams g))
    (hR : IsReset tr H g a) : cutZ sp.toParams g < a := by
  obtain ⟨⟨y, k, att, hyz, hs, hh, rfl⟩, -⟩ := hR
  by_contra hlate
  have hka : tr.time k ≤ cutZ sp.toParams g := le_of_not_gt hlate
  rw [max_eq_left hka] at hyz
  have hk0 := hrun.time_nonneg k
  have hr := hrun.upTo hk0
  have hy := hrun.antitone hka hyz
  have hsign := (RunTrace.upTo_signAt tr).mpr ⟨le_rfl, hs⟩
  obtain ⟨r, rfl, hrt, -, C, E, -, -, hE, -, -, -, -, hEh, hCa⟩ :=
    Healing.signAt_report_entry hr hy hsign
  have hrZ : tr.time r ≤ cutZ sp.toParams g := (hrun.time_mono (Nat.le_succ r)).trans hka
  have hbr : ∀ i < r, tr.time i ≤ tr.time (r + 1) := fun _ hi => hrun.time_mono (by omega)
  rw [Trace.upTo_state tr y hbr] at hE hEh hCa
  obtain ⟨j, hj⟩ := hsnapshot
  have hrj : r ≤ j := by
    by_contra h
    exact (not_lt_of_ge hrZ) (hj.2.trans_le (hrun.time_mono (by omega)))
  have hz0 := hk0.trans hka
  have hbefore : ∀ i < j, tr.time i ≤ cutZ sp.toParams g := hj.1
  have hprefix := hrun.upTo hz0
  have hbZ : ∀ i < r, tr.time i ≤ cutZ sp.toParams g := fun _ hi =>
    (hrun.time_mono hi.le).trans hrZ
  have hEr : E ∈ ((tr.upTo (cutZ sp.toParams g)).state y r).fg.tree := by
    rw [Trace.upTo_state tr y hbZ]
    exact hE
  have hEj := Compose.tree_mono hprefix.toLocalRun hyz hrj hEr
  have hσj := Store.σ_eq_of_mem (Compose.fg_reachable hprefix.toLocalRun hyz r)
    (Compose.fg_reachable hprefix.toLocalRun hyz j)
    (Compose.honest_blocks_coherent hprefix.toLocalRun (hnc.upTo _)).1
    (fun _ hX => ⟨y, hyz, r, hX⟩) (fun _ hX => ⟨y, hyz, j, hX⟩) hEr hEj
  rw [Trace.upTo_state tr y hbefore] at hEj hσj
  rw [Trace.upTo_state tr y hbZ] at hσj
  have hbound :=
    ((Store.cache_invariants _ _ _ _ (fg_reachable_at hrun hz0 hbefore hyz)).2.2.2.2.1 E hEj).trans
      (hmax_le_snapshot hyz hj)
  rw [← hσj, hEh, hCa] at hbound
  omega

/-- Finite reset premises suffice; the snapshot is observed before their horizon. -/
theorem ResetPremisesUpTo.cutZ_lt_reset_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold) : cutZ sp.toParams g < a :=
  let ⟨j, hj, _⟩ := hp.snapshot
  cutZ_lt_reset_of_snapshot_at hp.run hp.noColl ⟨j, hj⟩ hp.reset

/-- A slot from the reset's clean label on starts after `ḡ`: the reset is after `c_z`, and the
clean label's slot after the reset's. -/
theorem ResetPremisesUpTo.gbar_le_ts_of_clean_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold) {s : Nat}
    (hs : cleanLabel sp a ≤ s) : AC.gbar g ≤ sp.ts s := by
  have hca := hp.cutZ_lt_reset_at
  have hlc := lt_cutZ sp g
  have hΔ := sp.toParams.hΔ
  have ha0 : 0 ≤ a := by linarith [gbar_nonneg g]
  rw [cleanLabel_eq] at hs
  by_contra h
  have hsa := (AC.ts_le_iff_le_slot sp ha0 s).mp (le_trans (not_le.mp h).le (by linarith))
  omega

end Consensus.Goldilocks.Healing.Growing

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameLag
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.PreAdvance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Reset
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The snapshot frontier is at most one ahead of a later cohort

A height more than one above the cohort frontier needs a quorum containing a signer
still honest at the cohort horizon. That signer's actual earlier signing bounds the height.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- Quorum intersection bounds the snapshot lag for every later cohort horizon. -/
theorem lagWithin_one (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {g D : Time} (hD : cutZ sp.toParams g ≤ D)
    (hq : (H D)ᶜ.ncard < sp.toParams.fg.q)
    {j : Nat} (hj : FirstCutAfter tr j (cutZ sp.toParams g)) :
    LagWithin tr H g D 1 := by
  have hcz : 0 ≤ cutZ sp.toParams g := by
    linarith [lt_cutZ sp g, SA.gbar_nonneg g, sp.toParams.hΔ]
  have hs := hrun.upTo hcz
  have hb : ∀ k < j, tr.time k ≤ cutZ sp.toParams g := hj.1
  have hstate : ∀ y, (tr.upTo (cutZ sp.toParams g)).state y j = tr.state y j :=
    fun y => Trace.upTo_state tr y hb
  apply csSup_le'
  · rintro h ⟨x, hx, j', hj', hh⟩
    obtain rfl := hj.unique hj'
    rw [← hh]
    have hR := Compose.fg_reachable hs.toLocalRun hx j
    obtain ⟨_, _, _, _, _, ⟨X, hX, hXh⟩, _⟩ := Store.cache_invariants _ _ _ _ hR
    by_contra hlt
    have hheight : HZ tr (fun _ => H D) g + 1 <
        (((tr.upTo (cutZ sp.toParams g)).state x j).fg.σ X.root).h := by
      rw [hXh, hstate]
      omega
    obtain ⟨Y, hYX, att, ha, haH, hah⟩ := Store.exists_honest_att_of_lt hR hq hX
      (HZ tr (fun _ => H D) g + 1) (by omega) hheight
    have hY : Y ∈ ((tr.upTo (cutZ sp.toParams g)).state x j).fg.tree := by
      by_cases he : Y = X
      · exact he ▸ hX
      · exact (Anc.mem hYX he).1
    rcases tree_accepted hs.toLocalRun hx hY with rfl | ⟨k, hkj, hacc⟩
    · cases ha
    have haC := hrun.antitone hD haH
    obtain ⟨q, hqk, hsign⟩ := hs.toLocalRun.att_unforgeable x hx k att
      (Or.inr ⟨Y, ⟨true, hacc⟩, ha⟩) haC
    have hqj : q ≤ j := by omega
    have hbound := (Healing.signAt_h_le hs haC hsign).trans
      (hmax_mono hs.toLocalRun haC hqj)
    dsimp only at hbound
    rw [hstate att.val] at hbound
    have hmax := Healing.hmax_le_HZ (tr := tr) haH hj
    change (tr.state att.val j).fg.hmax ≤ HZ tr (fun _ => H D) g at hmax
    omega

end Consensus.Goldilocks.Healing.Growing

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Reset

public section

/-! # Historical height advances and the finite pre-reset range

The quorum budget is read at the current honest observer. Historical rows recovered
from that observer's store keep honesty at their own signing cuts.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- Any honest height advance produces a growing reset no later than its signing. -/
theorem reset_of_height_advance_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {g : Time} {y : Fin sp.n} {k : Nat}
    (hq : (H (tr.time k))ᶜ.ncard < sp.toParams.fg.q) (hy : y ∈ H (tr.time k))
    {att : FG.Att sp.n} (hs : tr.SignAt y k att) (hh : HZ tr H g + 1 ≤ att.h) :
    ∃ a, IsReset tr H g a ∧ a ≤ tr.time k := by
  classical
  have hr := hrun.upTo (hrun.time_nonneg k)
  have hex₀ : ∃ j z a, z ∈ H (tr.time j) ∧ tr.SignAt z j a ∧
      a.h = HZ tr H g + 1 ∧ tr.time j ≤ tr.time k := by
    rcases hh.lt_or_eq with hlt | heq
    · have hs' := (RunTrace.upTo_signAt tr).mpr ⟨le_rfl, hs⟩
      obtain ⟨E, hE, _, hEh⟩ := Healing.signAt_entry hr hy hs'
      obtain ⟨Y, hYE, a, ha, haH, hah⟩ := Store.exists_honest_att_of_lt
        (Compose.fg_reachable hr.toLocalRun hy k) hq hE (HZ tr H g + 1)
        (by omega) (by omega)
      have hY : Y ∈ ((tr.upTo (tr.time k)).state y k).fg.tree := by
        by_cases he : Y = E
        · exact he ▸ hE
        · exact (Anc.mem hYE he).1
      obtain ⟨src, hc⟩ := hs'
      obtain ⟨j, hj, hjk⟩ := Healing.signed_before_attest hr.toLocalRun hy hc hY ha haH
      obtain ⟨hjt, hsign⟩ := (RunTrace.upTo_signAt tr).mp hj
      exact ⟨j, a.val, a, hrun.antitone hjt haH, hsign, hah, hjt⟩
    · exact ⟨k, y, att, hy, hs, heq.symm, le_rfl⟩
  obtain ⟨j, z, att, hz, hs, hh, hjk⟩ := hex₀
  have hex : ∃ j z att, z ∈ H (tr.time j) ∧ tr.SignAt z j att ∧
      att.h = HZ tr H g + 1 := ⟨j, z, att, hz, hs, hh⟩
  obtain ⟨v, c, hv, hc, hch⟩ := Nat.find_spec hex
  have hR : IsReset tr H g (tr.time (Nat.find hex)) :=
    ⟨⟨v, Nat.find hex, c, hv, hc, hch, rfl⟩, by
      intro v i c hv hc hch
      exact hrun.time_mono (Nat.find_min' hex ⟨v, c, hv, hc, hch⟩)⟩
  exact ⟨_, hR, (hR.2 z j att hz hs hh).trans hjk⟩

/-- Before any own-cut honest advance, an honest reader's height is at most HZ plus one. -/
theorem hmax_le_of_noAdvance_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) {g T : Time}
    (hna : ∀ v k att, v ∈ H (tr.time k) → tr.SignAt v k att →
      tr.time k < T → att.h ≤ HZ tr H g)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    (hq : (H (tr.time i))ᶜ.ncard < sp.toParams.fg.q) (hiT : tr.time i < T) :
    (tr.state y i).fg.hmax ≤ HZ tr H g + 1 := by
  have hr := hrun.upTo (hrun.time_nonneg i)
  have hs : (tr.upTo (tr.time i)).state y i = tr.state y i :=
    Trace.upTo_state tr y (fun _ hk => hrun.time_mono hk.le)
  have hR := Compose.fg_reachable hr.toLocalRun hy i
  obtain ⟨_, _, _, _, _, ⟨X, hX, hXh⟩, _⟩ := Store.cache_invariants _ _ _ _ hR
  by_contra hlt
  rw [← hs] at hlt
  obtain ⟨Y, hYX, a, ha, haH, hah⟩ := Store.exists_honest_att_of_lt hR hq hX
    (HZ tr H g + 1) (by omega) (by omega)
  have hY : Y ∈ ((tr.upTo (tr.time i)).state y i).fg.tree := by
    by_cases he : Y = X
    · exact he ▸ hX
    · exact (Anc.mem hYX he).1
  rcases Healing.tree_accepted hr.toLocalRun hy hY with rfl | ⟨k, hki, hA⟩
  · cases ha
  obtain ⟨j, hjk, hj⟩ := hr.toLocalRun.att_unforgeable y hy k a
    (Or.inr ⟨Y, ⟨true, hA⟩, ha⟩) haH
  have hjT : tr.time j < T := (hrun.time_mono (by omega)).trans_lt hiT
  obtain ⟨hjt, hj⟩ := (RunTrace.upTo_signAt tr).mp hj
  have := hna a.val j a (hrun.antitone hjt haH) hj hjT
  omega

end Consensus.Goldilocks.Healing.Growing

end

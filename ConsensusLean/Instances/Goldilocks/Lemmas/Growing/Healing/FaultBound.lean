module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Restart
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Defs
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The late fault bound without retention induction imports -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}

/-- From the cut on, the faults at `d ∈ [t, b]` are fewer than the validators
honest at `d` that are awake and joined at `t`. -/
theorem fault_bound_late_before_at {b : Time} (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {t d : Time} (ht : cutZ sp.toParams g ≤ t) (htd : t ≤ d) (hdb : d ≤ b) :
    tr.FaultBoundAt H t d := by
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hgt : gbar g ≤ t := by have := lt_cutZ sp g; linarith
  have ht0 : 0 ≤ t := (gbar_nonneg g).trans hgt
  have hs : sp.slot (gbar g) + 3 ≤ sp.slot t := by
    have h := (SA.ts_le_iff_le_slot sp ht0 ((sp.slot (gbar g) + 3 : Nat) : Int)).mp
      ((cutZ_eq sp g) ▸ ht)
    exact_mod_cast h
  have hsub : H d ⊆ {y | y ∈ H d ∧ tr.awake y t ∧ tr.JoinedAt y t} := by
    intro y hy
    have hyt := hp.run.antitone htd hy
    refine ⟨hy, hp.awake y t hyt hgt (htd.trans hdb), fun k hk hkt => ?_⟩
    change 0 < sp.slot t ∧ tr.time k ≤ sp.toParams.slotTime (sp.slot t - 1)
    have he : sp.toParams.slotTime (sp.slot t - 1) = sp.ts ((sp.slot t - 1 : Nat) : Int) :=
      sp.slotTime_eq _
    refine ⟨by omega, (hp.restart_le_before_at (hp.run.antitone hkt hyt) hk
      (hkt.trans (htd.trans hdb))).trans ?_⟩
    rw [he]
    exact (SA.ts_le_iff sp).mpr (by omega)
  have hle := Set.ncard_le_ncard hsub
  have hn : (H d).ncard + (H d)ᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h3 := hp.faults d (ht0.trans htd) hdb
  have hpos := sp.toParams.hn
  have hn' : sp.n = sp.toParams.n := rfl
  unfold RunTrace.FaultBoundAt
  refine lt_of_lt_of_le ?_ hle
  omega

end Consensus.Goldilocks.Healing.Growing

end

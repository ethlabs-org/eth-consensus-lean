module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Restart
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Arith
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Half of the committee votes after the reset's cut, under growing faults

`ResetPremisesUpTo.half_committee_at`: after the reset's cut, the validators honest at
`t ≥ t_m + Δ` that voted in slot `m` while honest are at least half of the committee. Each is
awake from `ḡ` and joined at `t_m + Δ` (its restarts are by the slot after `ḡ`,
`restart_le_before_at`), so it votes in slot `m` on the prefix through `t_m + Δ`; the count is
`3 f_t ≤ n − 1` at `t`. -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- **Half of the committee votes** after the reset's cut, counted at `t ≥ t_m + Δ`. -/
theorem ResetPremisesUpTo.half_committee_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {m : Nat} (hm : cutZ sp.toParams g ≤ sp.ts m) {t : Time} (hmt : sp.ts m + sp.Δ ≤ t)
    (htb : t ≤ b) :
    sp.n ≤ 2 * {z | z ∈ H t ∧ ∃ q e, z ∈ H (tr.time q) ∧ SA.VoteAt tr.projAC z q e ∧
      e.msg.slot = m}.ncard := by
  have hΔ := sp.toParams.hΔ
  have hgt : gbar g ≤ sp.ts m + sp.Δ := by have := lt_cutZ sp g; linarith
  have hd0 : 0 ≤ sp.ts m + sp.Δ := (gbar_nonneg g).trans hgt
  have hdb : sp.ts m + sp.Δ ≤ b := hmt.trans htb
  have hsl : sp.slot (sp.ts m + sp.Δ) = m :=
    SA.slot_of_mem sp m (by linarith) (by simp only [SAParams.ts]; push_cast; linarith)
  have hm3 : sp.slot (gbar g) + 3 ≤ m := by
    have h := (SA.ts_le_iff sp).mp ((cutZ_eq sp g) ▸ hm)
    exact_mod_cast h
  have hsub : H t ⊆ {z | z ∈ H t ∧ ∃ q e, z ∈ H (tr.time q) ∧ SA.VoteAt tr.projAC z q e ∧
      e.msg.slot = m} := by
    intro z hz
    have hzd : z ∈ H (sp.ts m + sp.Δ) := hp.run.antitone hmt hz
    have hj : (tr.upTo (sp.ts m + sp.Δ)).JoinedAt z (sp.ts m + sp.Δ) := fun k hk hkt => by
      obtain ⟨hkd, hk⟩ := (RunTrace.upTo_restartAt tr).mp hk
      change 0 < sp.slot (sp.ts m + sp.Δ) ∧
        tr.time k ≤ sp.toParams.slotTime (sp.slot (sp.ts m + sp.Δ) - 1)
      rw [hsl, sp.slotTime_eq]
      exact ⟨by omega, (hp.restart_le_before_at
        (hp.run.antitone (hkd.trans hmt) hz) hk (hkd.trans hdb)).trans
        ((SA.ts_le_iff sp).mpr (by exact_mod_cast (show sp.slot (gbar g) + 1 ≤ m - 1 by
          clear * - hm3; omega)))⟩
    obtain ⟨q, e, hv, he, -⟩ := Compose.vote_of_awake_joined (hp.run.upTo hd0)
      (hp.noColl.upTo _) hzd ⟨hp.awake z _ hzd hgt hdb, le_rfl⟩ hj
    rw [RunTrace.upTo_projAC] at hv
    obtain ⟨ℓ, hc, he'⟩ := hv
    obtain ⟨hq, hc⟩ := (Trace.upTo_callAt _).mp hc
    exact ⟨hz, q, e, hp.run.antitone hq hzd, ⟨ℓ, hc, he'⟩, he⟩
  have hle := Set.ncard_le_ncard hsub
  have hn : (H t).ncard + (H t)ᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hf := hp.faults t (hd0.trans hmt) htb
  have hn' : sp.n = sp.toParams.n := rfl
  omega

end Consensus.Goldilocks.Healing.Growing

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Restart
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Arith
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Half of the committee votes after the reset's cut, under growing faults

`ResetPremisesUpTo.committee_cs2_at`: the committee fault bound `βK ≤ 1/2` gives
`2 |K s ∩ (H d)ᶜ| < committeeSize` for a slot from `ḡ` on, at every `d ∈ [0, b]`.

`ResetPremisesUpTo.half_committee_at`: after the reset's cut, the validators honest at
`t ≥ t_m + Δ` that voted in slot `m` while honest are at least half of the committee size. Each
honest member of the slot-`m` committee is permitted to vote (the gate), awake from `ḡ` and joined
at `t_m + Δ` (its restarts are by the slot after `ḡ`, `restart_le_before_at`), so it votes in
slot `m` on the prefix through `t_m + Δ`; the count is `committee_cs2_at` at `t`. -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- **CS2 at a slot committee** from the committee fault bound: fewer than half of the slot-`s`
committee is faulty at any `d ∈ [0, b]`, for a slot starting from `ḡ` by `b`. -/
theorem ResetPremisesUpTo.committee_cs2_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK) {s : Nat}
    (hgs : gbar g ≤ sp.ts s) (hsb : sp.ts s ≤ b) {d : Time} (hd0 : 0 ≤ d) (hdb : d ≤ b) :
    2 * ((Generic.dictOfTime sp cm).committee s ∩ (H d)ᶜ).ncard < sp.committeeSize := by
  have hcard : (cm (sp.toParams.slotTime s)).card = sp.committeeSize := by
    have h := hp.committeeFacts.hsize s
    rwa [Generic.dictOfTime, SA.CommitteeDict.committee, Set.ncard_coe_finset] at h
  have hne : (cm (sp.toParams.slotTime s)).Nonempty :=
    Finset.card_pos.1 (hcard ▸ hp.committee_pos)
  have hts : sp.toParams.slotTime s = sp.ts s := sp.slotTime_eq s
  have h := hp.committeeFaults (sp.toParams.slotTime s) d (by rw [hts]; exact hgs)
    (by rw [hts]; exact hsb) hd0 hdb hne
  have hβ := hp.beta_le
  have hc : (0 : ℚ) ≤ (cm (sp.toParams.slotTime s)).card := Nat.cast_nonneg _
  have h2 : ((2 * ((Generic.dictOfTime sp cm).committee s ∩ (H d)ᶜ).ncard : Nat) : ℚ) <
      (cm (sp.toParams.slotTime s)).card := by
    push_cast
    change 2 * (((↑(cm (sp.toParams.slotTime s)) : Set (Fin sp.n)) ∩ (H d)ᶜ).ncard : ℚ) < _
    nlinarith
  rw [← hcard]
  exact_mod_cast h2

/-- A slot committee from `ḡ` by `b` has a member honest at any `d ∈ [0, b]` (CS2). -/
theorem ResetPremisesUpTo.committee_honest_nonempty_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK) {s : Nat}
    (hgs : gbar g ≤ sp.ts s) (hsb : sp.ts s ≤ b) {d : Time} (hd0 : 0 ≤ d) (hdb : d ≤ b) :
    ((Generic.dictOfTime sp cm).committee s ∩ H d).Nonempty := by
  have hf := hp.committee_cs2_at hgs hsb hd0 hdb
  have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard
    ((Generic.dictOfTime sp cm).committee s) (H d) (Set.toFinite _)
  rw [hp.committeeFacts.hsize s, Set.sdiff_eq_compl_inter, Set.inter_comm (H d)ᶜ] at hsplit
  exact Set.nonempty_of_ncard_ne_zero (by omega)

/-- **Half of the committee size votes** after the reset's cut, counted at `t ≥ t_m + Δ`. -/
theorem ResetPremisesUpTo.half_committee_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK)
    {m : Nat} (hm : cutZ sp.toParams g ≤ sp.ts m) {t : Time} (hmt : sp.ts m + sp.Δ ≤ t)
    (htb : t ≤ b) :
    sp.committeeSize ≤ 2 * {z | z ∈ H t ∧ ∃ q e, z ∈ H (tr.time q) ∧ SA.VoteAt tr.projAC z q e ∧
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
  have hsub : (Generic.dictOfTime sp cm).committee m ∩ H t ⊆ {z | z ∈ H t ∧ ∃ q e,
      z ∈ H (tr.time q) ∧ SA.VoteAt tr.projAC z q e ∧ e.msg.slot = m} := by
    rintro z ⟨hzK, hz⟩
    have hzd : z ∈ H (sp.ts m + sp.Δ) := hp.run.antitone hmt hz
    have hj : tr.JoinedAt z (sp.ts m + sp.Δ) := fun k hk hkt => by
      change 0 < sp.slot (sp.ts m + sp.Δ) ∧
        tr.time k ≤ sp.toParams.slotTime (sp.slot (sp.ts m + sp.Δ) - 1)
      rw [hsl, sp.slotTime_eq]
      exact ⟨by omega, (hp.restart_le_before_at
        (hp.run.antitone (hkt.trans hmt) hz) hk (hkt.trans hdb)).trans
        ((SA.ts_le_iff sp).mpr (by exact_mod_cast (show sp.slot (gbar g) + 1 ≤ m - 1 by
          clear * - hm3; omega)))⟩
    obtain ⟨q, e, hv, he, -⟩ := Compose.Growing.vote_of_awake_joined_at hp.run hp.noColl hzd
      (Compose.Growing.mayVote_of_committee hp.committeeFacts.hGate hd0 hzd hzK)
      (hp.awake z _ hzd hgt hdb) hj
    exact ⟨hz, q, e, (Compose.Growing.hVoteAt_iff.1 hv).1, (Compose.Growing.hVoteAt_iff.1 hv).2,
      he⟩
  have hle := Set.ncard_le_ncard hsub
  have hsplit : ((Generic.dictOfTime sp cm).committee m ∩ H t).ncard +
      ((Generic.dictOfTime sp cm).committee m ∩ (H t)ᶜ).ncard = sp.committeeSize := by
    rw [← hp.committeeFacts.hsize m]
    exact Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _ (Set.toFinite _)
  have hf := hp.committee_cs2_at (s := m) (by have := lt_cutZ sp g; linarith)
    (by linarith) (hd0.trans hmt) htb
  omega

end Consensus.Goldilocks.Healing.Growing

end

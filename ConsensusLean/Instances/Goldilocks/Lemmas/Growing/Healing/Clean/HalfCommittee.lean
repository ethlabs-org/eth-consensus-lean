module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Core
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.CommitteeFaults
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Restart
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Arith
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.CoreStock
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreFacts

public section

/-! # Half of the committee votes after the reset's cut, under growing faults

`ResetPremisesUpTo.committee_cs2_at`: the committee fault bound `βK ≤ 1/2` gives
`2 |K s ∩ (H d)ᶜ| < committeeSize` for a slot from `ḡ` on, at every `d ∈ [0, b]`
(`Generic.CommitteeFaultsUpTo.committee_cs2_at` at the record's fields).

`ResetPremisesUpTo.half_committee_at`: after the reset's cut, the validators honest at
`t ≥ t_m + Δ` that voted in slot `m` while honest are at least half of the committee size. Each
honest member of the slot-`m` committee is permitted to vote (the gate), awake from `ḡ` and joined
at `t_m + Δ` (its restarts are by the slot after `ḡ`, `restart_le_before_at`), so it votes in
slot `m` on the prefix through `t_m + Δ`; the count is `committee_cs2_at` at `t`. -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}
variable {hold : Time}
  {u : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n → Store sp.toParams (Payload sp.n)}
  {frameOf : NodeState (goldilocksNode sp) → AC.Frm sp.n (List (FG.Att sp.n))}

/-- `committee_cs2_at` over the reset core. -/
theorem ResetRunCore.committee_cs2_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetRunCore tr H u frameOf proposer dg g ΔF a b cm βK hold) {s : Nat}
    (hgs : gbar g ≤ sp.ts s) (hsb : sp.ts s ≤ b) {d : Time} (hd0 : 0 ≤ d) (hdb : d ≤ b) :
    2 * ((Generic.dictOfTime sp cm).committee s ∩ (H d)ᶜ).ncard < sp.committeeSize :=
  hp.committeeFaults.committee_cs2_at hp.beta_le hp.committee_pos (hp.committeeFacts.hsize s)
    hgs hsb hd0 hdb

/-- **CS2 at a slot committee** from the committee fault bound: fewer than half of the slot-`s`
committee is faulty at any `d ∈ [0, b]`, for a slot starting from `ḡ` by `b`. -/
theorem ResetPremisesUpTo.committee_cs2_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold) {s : Nat}
    (hgs : gbar g ≤ sp.ts s) (hsb : sp.ts s ≤ b) {d : Time} (hd0 : 0 ≤ d) (hdb : d ≤ b) :
    2 * ((Generic.dictOfTime sp cm).committee s ∩ (H d)ᶜ).ncard < sp.committeeSize :=
  hp.toCore.committee_cs2_at hgs hsb hd0 hdb

/-- A slot committee from `ḡ` by `b` has a member honest at any `d ∈ [0, b]` (CS2). -/
theorem ResetPremisesUpTo.committee_honest_nonempty_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold) {s : Nat}
    (hgs : gbar g ≤ sp.ts s) (hsb : sp.ts s ≤ b) {d : Time} (hd0 : 0 ≤ d) (hdb : d ≤ b) :
    ((Generic.dictOfTime sp cm).committee s ∩ H d).Nonempty := by
  have hf := hp.committee_cs2_at hgs hsb hd0 hdb
  have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard
    ((Generic.dictOfTime sp cm).committee s) (H d) (Set.toFinite _)
  rw [hp.committeeFacts.hsize s, Set.sdiff_eq_compl_inter, Set.inter_comm (H d)ᶜ] at hsplit
  exact Set.nonempty_of_ncard_ne_zero (by omega)

/-- **Half of the committee size votes** after the reset's cut, counted at `t ≥ t_m + Δ`. -/
theorem ResetRunCore.half_committee_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetRunCore tr H u frameOf proposer dg g ΔF a b cm βK hold)
    {m : Nat} (hm : cutZ sp.toParams g ≤ sp.ts m) {t : Time} (hmt : sp.ts m + sp.Δ ≤ t)
    (htb : t ≤ b) :
    sp.committeeSize ≤ 2 * {z | z ∈ H t ∧ ∃ q e, z ∈ H (tr.time q) ∧ AC.VoteAt tr.projAC z q e ∧
      e.msg.slot = m}.ncard := by
  have rc := hp.core
  have hΔ := sp.toParams.hΔ
  have hgt : gbar g ≤ sp.ts m + sp.Δ := by have := lt_cutZ sp g; linarith
  have hd0 : 0 ≤ sp.ts m + sp.Δ := (gbar_nonneg g).trans hgt
  have hdb : sp.ts m + sp.Δ ≤ b := hmt.trans htb
  have hsl : sp.slot (sp.ts m + sp.Δ) = m :=
    AC.slot_of_mem sp m (by linarith) (by simp only [ACParams.ts]; push_cast; linarith)
  have hm3 : sp.slot (gbar g) + 3 ≤ m := by
    have h := (AC.ts_le_iff sp).mp ((cutZ_eq sp g) ▸ hm)
    exact_mod_cast h
  have hsub : (Generic.dictOfTime sp cm).committee m ∩ H t ⊆ {z | z ∈ H t ∧ ∃ q e,
      z ∈ H (tr.time q) ∧ AC.VoteAt tr.projAC z q e ∧ e.msg.slot = m} := by
    rintro z ⟨hzK, hz⟩
    have hzd : z ∈ H (sp.ts m + sp.Δ) := rc.antitone hmt hz
    have hj : tr.JoinedAt z (sp.ts m + sp.Δ) := fun k hk hkt => by
      change 0 < sp.slot (sp.ts m + sp.Δ) ∧
        tr.time k ≤ sp.toParams.slotTime (sp.slot (sp.ts m + sp.Δ) - 1)
      rw [hsl, sp.slotTime_eq]
      exact ⟨by omega, (hp.restart_le_before_at
        (rc.antitone (hkt.trans hmt) hz) hk (hkt.trans hdb)).trans
        ((AC.ts_le_iff sp).mpr (by exact_mod_cast (show sp.slot (gbar g) + 1 ≤ m - 1 by
          clear * - hm3; omega)))⟩
    obtain ⟨q, e, hv, he, -⟩ := rc.vote_of_awake_joined_at hp.noColl hzd
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

/-- **Half of the committee size votes** after the reset's cut, counted at `t ≥ t_m + Δ`. -/
theorem ResetPremisesUpTo.half_committee_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {m : Nat} (hm : cutZ sp.toParams g ≤ sp.ts m) {t : Time} (hmt : sp.ts m + sp.Δ ≤ t)
    (htb : t ≤ b) :
    sp.committeeSize ≤ 2 * {z | z ∈ H t ∧ ∃ q e, z ∈ H (tr.time q) ∧ AC.VoteAt tr.projAC z q e ∧
      e.msg.slot = m}.ncard :=
  hp.toCore.half_committee_at hm hmt htb

end Consensus.Goldilocks.Healing.Growing

end

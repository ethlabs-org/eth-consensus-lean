module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.HealedMembers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.FoundationSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.Compatibility
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.OperationalReports
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Healed members below a unanimous operational proposal -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp} {g ΔF a b : Time}
  {cm : Time → Finset (Fin sp.n)} {βK : ℚ} {hold : Time}

/-- A healed member whose label starts after the snapshot has an honest supporter. -/
theorem healed_member_supporter_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {j : Nat} (hcut : cutZ sp.toParams g ≤ sp.ts j)
    {D : AC.Blk sp.n (List (FG.Att sp.n))}
    (hD : Compose.Growing.HealedOrigin tr H g (healedLockFloor sp a)
      (healedOriginFloor sp a) D j b) :
    ∃ z q e, z ∈ H (tr.time q) ∧ AC.VoteAt tr.projAC z q e ∧
      tr.time q ≤ b ∧ e.msg.slot = j ∧ AC.VoteExtends (tr.HonestBlocksAt H) e.msg D := by
  obtain ⟨O, hO, hDO⟩ := hD.below_origin hp.run hp.noColl
  obtain ⟨x, r, CV, hx, hrb, horigin⟩ := Compose.Growing.originWithin_iff.1 hO
  rcases horigin with hres | hop
  · obtain ⟨z, hz, q, hqr, e, hv, _, hs, ⟨B, hB, hBr, hOB⟩⟩ :=
      ProposalImpl.result_supporter_at hp hx hres hDO hrb hcut
    exact ⟨z, q, e, hp.run.antitone (hp.run.time_mono hqr.le) hz, hv,
      (hp.run.time_mono hqr.le).trans hrb, hs, B, hB, hBr, hOB⟩
  · obtain ⟨_, z, q, hz, hqr, e, hv, hs, ⟨B, hB, hBr, hOB⟩⟩ :=
      hp.optimistic_supporter_at hx hrb (by linarith [lt_cutZ sp g, sp.toParams.hΔ]) hop
    exact ⟨z, q, e, hp.run.antitone (hp.run.time_mono hqr) hz, hv,
      (hp.run.time_mono hqr).trans hrb, hs, B, hB, hBr, hDO.trans hOB⟩

/-- A healed member at or after an operational slot has an honest supporter at its label. -/
theorem healed_member_supporter_after_drain_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {u j : Nat} (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat)) (huj : u ≤ j)
    {D : AC.Blk sp.n (List (FG.Att sp.n))}
    (hD : Compose.Growing.HealedOrigin tr H g (healedLockFloor sp a)
      (healedOriginFloor sp a) D j b) :
    ∃ z q e, z ∈ H (tr.time q) ∧ AC.VoteAt tr.projAC z q e ∧
      tr.time q ≤ b ∧ e.msg.slot = j ∧ AC.VoteExtends (tr.HonestBlocksAt H) e.msg D := by
  apply healed_member_supporter_at hp ?_ hD
  have hca := hp.cutZ_lt_reset_at
  have ha0 : 0 ≤ a := by
    linarith [lt_cutZ sp g, Healing.gbar_nonneg g, sp.toParams.hΔ]
  have ha : a < sp.ts ((sp.slot a : Int) + 1) := not_le.1 fun h => by
    have := (AC.ts_le_iff_le_slot sp ha0 _).1 h
    omega
  rw [drainTime_eq] at hR
  have := (AC.ts_le_iff sp).1 hR
  push_cast at this
  have hle : sp.ts ((sp.slot a : Int) + 1) ≤ sp.ts j :=
    (AC.ts_le_iff sp).2 (by omega)
  exact hca.le.trans (ha.le.trans hle)

/-- Members through the unanimous slot lie below its proposal, independently of any
next-slot vote extension. -/
theorem healed_members_through_slot_below_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    (hc : HighSourceCover tr H g a b)
    {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H)
    (hun : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat)) (hub : sp.ts u + sp.Δ ≤ b) :
    ∀ D j, Compose.Growing.HealedOrigin tr H g (healedLockFloor sp a)
      (healedOriginFloor sp a) D j b → j ≤ u → Anc (tr.HonestBlocksAt H) D P := by
  intro D j hD hj
  have hU := Compose.Growing.honestBlocksAt_coherent hp.run hp.noColl
  by_cases hju : j < u
  · have hΔ := sp.toParams.hΔ
    obtain ⟨x, hxK, hx⟩ := hp.committee_honest_nonempty_at (s := u) (by linarith)
      (by linarith) (by linarith [Healing.gbar_nonneg g]) hub
    obtain ⟨q, e, hv, hes, hq⟩ := honest_votes_in_slot_at hp hgu hR hub x hx hxK
    have hxq := hp.run.antitone hq hx
    obtain ⟨B, hB, hBr, hDB⟩ := hc.s2 D j hD x q e
      (Compose.Growing.hVoteAt_iff.2 ⟨hxq, hv⟩) (hq.trans hub) (by omega)
    exact (hU.1 hB hP (hBr.trans (hun x q e hxq hv (hq.trans hub) hes))) ▸ hDB
  obtain rfl : j = u := by omega
  obtain ⟨z, q, e, hz, hv, hqb, hs, B, hB, hBr, hDB⟩ :=
    healed_member_supporter_after_drain_at hp hR le_rfl hD
  exact (hU.1 hB hP (hBr.trans (hun z q e hz hv hqb hs))) ▸ hDB

end Consensus.Goldilocks.Healing.Growing

end

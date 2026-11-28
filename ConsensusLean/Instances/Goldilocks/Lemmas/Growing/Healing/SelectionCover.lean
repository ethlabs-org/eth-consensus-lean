module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.UnanimousNext
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.SelectionMembers
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # A unanimous operational proposal compares with the covered family at its update -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp} {g ΔF a b : Time}
  {cm : Time → Finset (Fin sp.n)} {βK : ℚ} {hold : Time}

private theorem unanimous_next_votes_extend_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    (hc : HighSourceCover tr H g a b)
    {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H) (hslot : P.slot = u) (hu : 0 < u)
    (hun : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat)) (hub : sp.ts u + sp.Δ ≤ b) :
    ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u + 1 → AC.VoteExtends (tr.HonestBlocksAt H) e.msg P := by
  have hbound : ∀ x r l B, HighOrigin tr H g x r l B → tr.time r < sp.ts (u + 1 : Nat) →
      tr.time r ≤ b → Anc (tr.HonestBlocksAt H) B P :=
    fun _ _ _ _ ho ht hrb => high_origins_before_next_slot_below_at hp hP hun hgu hR hub ho ht hrb
  have hcovered : ∀ C s, Compose.Growing.HealedOrigin tr H g (healedLockFloor sp a)
      (healedOriginFloor sp a) C s b → s < u + 1 → Anc (tr.HonestBlocksAt H) C P :=
    fun C s hC hs => healed_members_through_slot_below_at hp hc hP hun hgu hR hub C s hC
      (by omega)
  exact unanimous_next_votes_extend_core_at hp.run hp.noColl hp.sync hp.catchUp hP hslot hu hun
    (by linarith [sp.toParams.hΔ]) hp.committeeFacts.hP
    (hp.committeeFacts.committeeTAt hp.run hp.noColl) hp.committeeFacts.hsize hp.noRestart
    (exists_honest_slot_vote_at hp hgu hR hub) (committee_voted_in_slot_at hp hgu hR hub)
    (faultBoundK_after_slot_at hp hgu hR)
    (fun i hti hib => hp.committee_cs2_at
      (by have := (AC.ts_le_iff sp).2 (show (u : Int) ≤ (u + 1 : Nat) by omega)
          linarith [sp.toParams.hΔ]) (hti.trans hib) (hp.run.time_nonneg i) hib)
    (fun _ _ _ _ hy hcast hs hjb => by
      have hF := congrArg Frame.fcRoot (Outcome.frame_of_call hp.run hy hcast.1)
      change _ = (tr.state _ _).fg.F at hF
      rw [← hF]
      exact (hp.cast_root_anc_analysis_root_at hy hcast).trans
        (hp.reset_vote_root_below_bound_or_covered_at hR hP hbound hcovered hy hcast hs hjb))
    (fun _ _ _ _ hy hcast hs hjb hstore =>
      hp.reset_vote_viable_above_old_or_covered_at hy hR hcast hs hjb hstore hbound
        (fun _ C s hC hs => hcovered C s hC.healedOrigin hs))

/-- Under the source cover, every healed member through the slot of the update deadline is
compatible with the unanimous proposal. Members may be written after that deadline, up to `b`.
Older members are extended by a slot-`u` vote (S2); same-slot members have a supporter voting `P`;
next-slot members have a supporter whose vote extends `P`. -/
theorem healed_member_compatible_before_update_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    (hc : HighSourceCover tr H g a b)
    {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H) (hslot : P.slot = u) (hu : 0 < u)
    (hun : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat)) (hTb : sp.ts u + 6 * sp.Δ ≤ b) :
    ∀ D j, Compose.Growing.HealedOrigin tr H g (healedLockFloor sp a)
      (healedOriginFloor sp a) D j b → j ≤ u + 1 → Compatible (tr.HonestBlocksAt H) D P := by
  have hΔ := sp.toParams.hΔ
  have hU := Compose.Growing.honestBlocksAt_coherent hp.run hp.noColl
  have hub : sp.ts u + sp.Δ ≤ b := by linarith
  have hext := unanimous_next_votes_extend_at hp hc hP hslot hu hun hgu hR hub
  intro D j hD hj
  by_cases hju : j ≤ u
  · exact Or.inl (healed_members_through_slot_below_at hp hc hP hun hgu hR hub D j hD hju)
  have hj' : j = u + 1 := by omega
  obtain ⟨z, q, e, hz, hv, hqb, hs, B, hB, hBr, hDB⟩ :=
    healed_member_supporter_after_drain_at hp hR (by omega) hD
  obtain ⟨B', hB', hBr', hPB'⟩ := hext z q e hz hv hqb (hj' ▸ hs)
  obtain rfl : B' = B := hU.1 hB' hB (hBr'.trans hBr.symm)
  exact AC.anc_total hU hDB hPB'

end Consensus.Goldilocks.Healing.Growing

end

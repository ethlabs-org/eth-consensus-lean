module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetFacts
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.UnanimousNextCore
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Floor
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.RootBound
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.OriginLabel
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.SameSlot
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.SelectionOrigins
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.SelectionMembers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Next
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.OperationalReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Ancestry
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameFrozen
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Timing
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Batch
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ETimeOrder
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Writer
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
import ConsensusLean.Lemmas.Tactic.Linarith

import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HalfCommittee
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.ResetSuppliers
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.Compatibility
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
public section

/-! # The slot after a unanimous slot, under growing faults

Under the reset premises, `UnanimousNextCore` extends a unanimous proposal `P` through every
slot-`(u+1)` vote of a node honest at its cast. A slot-`(u+1)` optimistic selection is then
compatible with `P` by applying that extension to an honest supporting vote.

Under the reset premises the votes come from `honest_votes_in_slot_at`, the fault bound from the
restart cutoff, and the finality and viability bounds from the reset
(`reset_vote_finality_below_bound_at`, `reset_vote_viable_above_old_or_covered_at`, with the
old-origin bound `high_origins_before_next_slot_below_at` of `Healing/SelectionOrigins`). Each node
is honest at its own cut. -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload Vote)

variable {sp : ACParams}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}
variable {hold : Time}

/-! ### Cast timing -/

/-! ### Under the reset premises -/

/-- The old origins written before slot `u + 1` are below `P`. -/
private theorem old_origins_below {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H)
    (hun : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u) (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hub : sp.ts u + sp.Δ ≤ b) :
    ∀ x r l B, HighOrigin tr H g x r l B → tr.time r < sp.ts (u + 1 : Nat) →
      tr.time r ≤ b → Anc (tr.HonestBlocksAt H) B P :=
  fun _ _ _ _ ho ht hrb => high_origins_before_next_slot_below_at hp hP hun hgu hR hub ho ht hrb

/-- The members of the slot-`u` committee honest at `t_{u+1}` voted in slot `u` by `t_u + Δ`. -/
theorem committee_voted_in_slot_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {u : Nat} (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat)) (hub : sp.ts u + sp.Δ ≤ b) :
    ∀ x, x ∈ H (sp.ts (u + 1 : Nat)) → x ∈ (Generic.dictOfTime sp cm).committee u →
      ∃ q e, AC.VoteAt tr.projAC x q e ∧ e.msg.slot = u ∧ tr.time q ≤ sp.ts u + sp.Δ := by
  intro x hx hxK
  exact honest_votes_in_slot_at hp hgu hR hub x
    (hp.run.antitone (by linarith [AC.ts_succ (sp := sp) u, sp.toParams.hΔ]) hx) hxK

/-- A member of the slot-`u` committee honest at its vote casts a slot-`u` vote by `t_u + Δ`. -/
theorem exists_honest_slot_vote_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {u : Nat} (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat)) (hub : sp.ts u + sp.Δ ≤ b) :
    ∃ w q e, w ∈ H (tr.time q) ∧ AC.VoteAt tr.projAC w q e ∧ e.msg.slot = u ∧
      tr.time q ≤ sp.ts u + sp.Δ := by
  have hΔ := sp.toParams.hΔ
  obtain ⟨w, hwK, hw⟩ := hp.committee_honest_nonempty_at (s := u) (by linarith)
    (by linarith) (by linarith [AC.gbar_nonneg g]) hub
  obtain ⟨q, e, hv, hs, hq⟩ := honest_votes_in_slot_at hp hgu hR hub w hw hwK
  exact ⟨w, q, e, hp.run.antitone hq hw, hv, hs, hq⟩

/-- After the drain, CS at the slot-`u` committee holds at every cut from `t_{u+1}` through `b`. -/
theorem faultBoundK_after_slot_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold) {u : Nat}
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u) (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat)) :
    ∀ i, sp.ts (u + 1 : Nat) ≤ tr.time i → tr.time i ≤ b →
      AC.FaultBoundK (Generic.dictOfTime sp cm) u tr.projAC (H (tr.time i)) (tr.time i) := by
  intro i hti hib
  have hΔ := sp.toParams.hΔ
  have hts1 := AC.ts_succ (sp := sp) u
  have hcut : cutZ sp.toParams g ≤ sp.ts u := by
    have hk := sp.two_le_k
    apply hp.clean_window_timing_at (s := u) ?_ u (by omega)
    rw [Healing.cleanLabel_eq]
    rw [Healing.drainTime_eq] at hR
    have := (AC.ts_le_iff sp).1 hR
    push_cast at this
    omega
  exact KernelProof.faultBoundK_late_at hp (by linarith) (by linarith) (by linarith) le_rfl hib

/-- The reset premises make a slot-`(u+1)` optimistic selection compatible with `P`. -/
theorem unanimous_next_optimistic_compatible_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))} (hP : P ∈ tr.HonestBlocksAt H)
    (hslot : P.slot = u) (hu : 0 < u)
    (hun : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u) (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hub : sp.ts u + sp.Δ ≤ b) {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {D : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (AC.Vote sp.n)}
    (hopt : AC.OptimisticLockAt tr.projAC y j (u + 1) D CV) (hjb : tr.time j ≤ b) :
    Compatible (tr.HonestBlocksAt H) D P := by
  have hbound := old_origins_below hp hP hun hgu hR hub
  have hΔ := sp.toParams.hΔ
  have hts1 := AC.ts_succ (sp := sp) u
  obtain ⟨_, z, q, hz, hqj, e, hv, hs, B, hB, hBr, hDB⟩ :=
    hp.optimistic_supporter_at hy hjb (by linarith) hopt
  have hext := unanimous_next_votes_extend_core_at hp.run hp.noColl hp.sync hp.catchUp
    hP hslot hu hun (by linarith) hp.committeeFacts.hP
    (hp.committeeFacts.committeeTAt hp.run hp.noColl) hp.committeeFacts.hsize hp.noRestart
    (exists_honest_slot_vote_at hp hgu hR hub) (committee_voted_in_slot_at hp hgu hR hub)
    (faultBoundK_after_slot_at hp hgu hR)
    (fun i hti hib => hp.committee_cs2_at
      (by linarith) (hti.trans hib) (hp.run.time_nonneg i) hib)
    (fun _ _ _ _ hy hcast hs hjb =>
      hp.reset_vote_finality_below_bound_at hR hP hbound
        (fun hcover C s hC hsu => healed_members_through_slot_below_at hp hcover
          hP hun hgu hR hub C s hC.healedOrigin (by omega)) hy hcast hs hjb)
    (fun _ _ _ _ hy hcast hs hjb hstore =>
      hp.reset_vote_viable_above_old_or_covered_at hy hR hcast hs hjb hstore hbound
        (fun hcover C s hC hsu => healed_members_through_slot_below_at hp hcover
          hP hun hgu hR hub C s hC.healedOrigin (by omega)))
  have hq := hp.run.time_mono hqj
  obtain ⟨B', hB', hB'r, hPB⟩ := hext z q e (hp.run.antitone hq hz) hv (hq.trans hjb) hs
  have hU := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  obtain rfl : B' = B := hU.1 hB' hB (hB'r.trans hBr.symm)
  exact AC.anc_total hU hDB hPB

end Consensus.Goldilocks.Healing.Growing

end

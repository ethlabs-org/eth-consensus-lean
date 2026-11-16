module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetFacts
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.UnanimousNextCore
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Floor
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.RootBound
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.OriginLabel
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.SameSlot
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.SelectionOrigins
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Next
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.OperationalReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Ancestry
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameFrozen
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
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
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
public section

/-! # The slot after a unanimous slot, under growing faults

The growing forms of the unanimous next-slot helpers of `Healing/OperationalReports`, under the
reset premises. Each is a corollary of a core (`*_core_at`, in `Healthy/UnanimousNextCore`) over
the run, `ResetService`, `Catch(2Δ)` and `ḡ ≤ t_u`, with its remaining inputs explicit:

* `unanimous_carry_votes_core_at`: the slot-`u` votes of nodes honest at their casts are carried
  to a slot-`(u+1)` cast;
* `unanimous_next_vote_viable_core_at`: the unanimous proposal `P` is in the frozen viable tree of
  a slot-`(u+1)` cast, given the caster's own slot-`u` vote by `t_u + Δ`, its fork-choice root
  below `P`, and its head-height floor at or below `P`;
* `unanimous_next_votes_extend_core_at`: every slot-`(u+1)` vote extends `P`, by strong induction
  on the vote's cut, with the batch counted at the voter's cut (every validator honest at
  `t_{u+1}` voted in slot `u` by `t_u + Δ`, and the fault bound at the cut);
* `unanimous_next_optimistic_compatible_core_at`: a slot-`(u+1)` optimistic selection is
  compatible with `P`, through a supporting vote of a node honest at its cast.

Under the reset premises the votes come from `honest_votes_in_slot_at`, the fault bound from the
restart cutoff, and the fork-choice root and floor from the reset (`reset_vote_root_below_bound_at`,
`reset_vote_floor_above_old_at`, with the old-origin bound `high_origins_before_next_slot_below_at`
of `Healing/SelectionOrigins`). Each node is honest at its own cut. -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-! ### Cast timing -/

/-- The static AC run of the prefix through `tr.time i`, for the validators honest then. -/
private theorem acRun_prefix {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) (i : Nat) :
    SA.ACRun proposer (tr.upTo (tr.time i)).projAC (H (tr.time i))
      ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i))) ini :=
  Compose.goldilocks_ac_projection_from (hrun.upTo (hrun.time_nonneg i)) (hnc.upTo _)

/-- A cast at a cut at or before `d` is one of the prefix through `d`. -/
private theorem castAt_prefix {d : Time} {y : Fin sp.n} {j : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))} (hjd : tr.time j ≤ d)
    (hc : SA.CastAt tr.projAC y j ell e) : SA.CastAt (tr.upTo d).projAC y j ell e := by
  rw [RunTrace.upTo_projAC]
  exact ⟨(Trace.upTo_callAt_of_le tr.projAC hjd).mpr hc.1, hc.2⟩

/-- A cast of a node honest at it is no earlier than the start of its slot and at most `Δ` after
it. -/
private theorem cast_time {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcast : SA.CastAt tr.projAC y j ell e) :
    sp.ts e.msg.slot ≤ tr.time j ∧ tr.time j ≤ sp.ts e.msg.slot + sp.Δ := by
  have hr := (acRun_prefix hrun hnc j).localRun
  have hc' := castAt_prefix le_rfl hcast
  have h := (SA.castAt_spec hr hy hc').2.1
  change e.msg.slot = sp.slot (tr.time j) at h
  refine ⟨(SA.ts_le_iff_le_slot sp (hrun.time_nonneg j) _).2 (by omega), ?_⟩
  exact (Compose.cast_head_fcRoot_from hr (acRun_prefix hrun hnc j).vstart hy hc').2

/-! ### Under the reset premises -/

/-- The reset premises carry the slot-`u` votes to a slot-`(u+1)` cast. -/
theorem unanimous_carry_votes_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK)
    {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H)
    (hun : ∀ y j e, y ∈ H (tr.time j) → SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) {ell : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcast : SA.CastAt tr.projAC y i ell e)
    (hs : e.msg.slot = u + 1) (hib : tr.time i ≤ b)
    (hFP : Anc (tr.HonestBlocksAt H) ell.frame.F P) :
    SA.CarryAt tr.projAC (tr.HonestBlocksAt H) y i e u (Compose.Growing.honestVotes tr H u) :=
  unanimous_carry_votes_core_at hp.run hp.noColl hp.sync hp.catchUp hP hun
    (by linarith [sp.toParams.hΔ]) hy hcast hs hib hFP

/-- The old origins written before slot `u + 1` are below `P`. -/
private theorem old_origins_below {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK)
    {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H)
    (hun : ∀ y j e, y ∈ H (tr.time j) → SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u) (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hub : sp.ts u + sp.Δ ≤ b) :
    ∀ x r l B, HighOrigin tr H g x r l B → tr.time r < sp.ts (u + 1 : Nat) →
      tr.time r ≤ b → Anc (tr.HonestBlocksAt H) B P :=
  fun _ _ _ _ ho ht hrb => high_origins_before_next_slot_below_at hp hP hun hgu hR hub ho ht hrb

/-- The members of the slot-`u` committee honest at `t_{u+1}` voted in slot `u` by `t_u + Δ`. -/
private theorem next_voters {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK)
    {u : Nat} (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat)) (hub : sp.ts u + sp.Δ ≤ b) :
    ∀ x, x ∈ H (sp.ts (u + 1 : Nat)) → x ∈ (Generic.dictOfTime sp cm).committee u →
      ∃ q e, SA.VoteAt tr.projAC x q e ∧ e.msg.slot = u ∧ tr.time q ≤ sp.ts u + sp.Δ := by
  have hts1 : sp.ts (u + 1 : Nat) = sp.ts u + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  intro x hx hxK
  exact honest_votes_in_slot_at hp hgu hR hub x
    (hp.run.antitone (by linarith [sp.toParams.hΔ]) hx) hxK

/-- A member of the slot-`u` committee honest at its vote casts a slot-`u` vote by `t_u + Δ`. -/
private theorem slot_witness {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK)
    {u : Nat} (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat)) (hub : sp.ts u + sp.Δ ≤ b) :
    ∃ w q e, w ∈ H (tr.time q) ∧ SA.VoteAt tr.projAC w q e ∧ e.msg.slot = u ∧
      tr.time q ≤ sp.ts u + sp.Δ := by
  have hΔ := sp.toParams.hΔ
  obtain ⟨w, hwK, hw⟩ := hp.committee_honest_nonempty_at (s := u) (by linarith)
    (by linarith) (by linarith [SA.gbar_nonneg g]) hub
  obtain ⟨q, e, hv, hs, hq⟩ := honest_votes_in_slot_at hp hgu hR hub w hw hwK
  exact ⟨w, q, e, hp.run.antitone hq hw, hv, hs, hq⟩

/-- After the drain, CS at the slot-`u` committee holds at every cut from `t_{u+1}` through `b`. -/
private theorem next_fault_bound {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK) {u : Nat}
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u) (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat)) :
    ∀ i, sp.ts (u + 1 : Nat) ≤ tr.time i → tr.time i ≤ b →
      SA.FaultBoundK (Generic.dictOfTime sp cm) u tr.projAC (H (tr.time i)) (tr.time i) := by
  intro i hti hib
  have hΔ := sp.toParams.hΔ
  have hts1 : sp.ts (u + 1 : Nat) = sp.ts u + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hcut : cutZ sp.toParams g ≤ sp.ts u := by
    have hk := sp.two_le_k
    apply hp.clean_window_timing_at (s := u) ?_ u (by omega)
    rw [Healing.cleanLabel_eq]
    rw [Healing.drainTime_eq] at hR
    have := (SA.ts_le_iff sp).1 hR
    push_cast at this
    omega
  exact KernelProof.faultBoundK_late_at hp (by linarith) (by linarith) (by linarith) le_rfl hib

/-- The reset premises put `P` in every slot-`(u+1)` frozen viable tree. -/
theorem unanimous_next_vote_viable_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK)
    {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H) (hslot : P.slot = u) (hu : 0 < u)
    (hun : ∀ y j e, y ∈ H (tr.time j) → SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u) (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hub : sp.ts u + sp.Δ ≤ b)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j)) {ell : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcast : SA.CastAt tr.projAC y j ell e)
    (hs : e.msg.slot = u + 1) (hjb : tr.time j ≤ b) :
    Anc (tr.HonestBlocksAt H) ell.frame.F P ∧
      P ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (u + 1)) := by
  have hbound := old_origins_below hp hP hun hgu hR hub
  have htime : sp.ts (u + 1 : Nat) ≤ tr.time j := by
    have := (cast_time hp.run hp.noColl hy hcast).1
    rwa [hs] at this
  exact unanimous_next_vote_viable_core_at hp.run hp.noColl hp.sync hp.catchUp hP hslot hu hun
    (by linarith [sp.toParams.hΔ]) hy hcast hs hjb
    (fun r hrj hrs => hp.noRestart y r (hp.run.antitone (hp.run.time_mono hrj) hy) hrs
      ((hp.run.time_mono hrj).trans hjb)) (slot_witness hp hgu hR hub)
    (hp.reset_vote_root_below_bound_at hR hP hbound hy hcast hs hjb)
    (fun hstore => hp.reset_vote_floor_above_old_at hy hR hcast hs hjb hstore hbound)

/-- The reset premises make every slot-`(u+1)` vote extend `P`. -/
theorem unanimous_next_votes_extend_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK)
    {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H) (hslot : P.slot = u) (hu : 0 < u)
    (hun : ∀ y j e, y ∈ H (tr.time j) → SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u) (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hub : sp.ts u + sp.Δ ≤ b) :
    ∀ y j e, y ∈ H (tr.time j) → SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u + 1 → SA.VoteExtends (tr.HonestBlocksAt H) e.msg P :=
  have hbound := old_origins_below hp hP hun hgu hR hub
  unanimous_next_votes_extend_core_at hp.run hp.noColl hp.sync hp.catchUp hP hslot hu hun
    (by linarith [sp.toParams.hΔ]) hp.committeeFacts.hP
    (hp.committeeFacts.committeeTAt hp.run hp.noColl) hp.committeeFacts.hsize hp.noRestart
    (slot_witness hp hgu hR hub) (next_voters hp hgu hR hub) (next_fault_bound hp hgu hR)
    (fun i hti hib => hp.committee_cs2_at
      (by have := (SA.ts_le_iff sp).2 (show (u : Int) ≤ (u + 1 : Nat) by omega)
          linarith [sp.toParams.hΔ]) (hti.trans hib)
      (hp.run.time_nonneg i) hib)
    (fun _ _ _ _ hy hcast hs hjb => hp.reset_vote_root_below_bound_at hR hP hbound hy hcast hs hjb)
    (fun _ _ _ _ hy hcast hs hjb hstore =>
      hp.reset_vote_floor_above_old_at hy hR hcast hs hjb hstore hbound)

/-- The reset premises make a slot-`(u+1)` optimistic selection compatible with `P`. -/
theorem unanimous_next_optimistic_compatible_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK)
    {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))} (hP : P ∈ tr.HonestBlocksAt H)
    (hslot : P.slot = u) (hu : 0 < u)
    (hun : ∀ y j e, y ∈ H (tr.time j) → SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u) (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hub : sp.ts u + sp.Δ ≤ b) {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {D : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hopt : SA.OptimisticLockAt tr.projAC y j (u + 1) D CV) (hjb : tr.time j ≤ b) :
    Compatible (tr.HonestBlocksAt H) D P :=
  have hbound := old_origins_below hp hP hun hgu hR hub
  unanimous_next_optimistic_compatible_core_at hp.run hp.noColl hp.sync hp.catchUp hP hslot hu hun
    (by linarith [sp.toParams.hΔ]) hp.committeeFacts.hP
    (hp.committeeFacts.committeeTAt hp.run hp.noColl) hp.committeeFacts.hsize hp.noRestart
    (slot_witness hp hgu hR hub) (next_voters hp hgu hR hub) (next_fault_bound hp hgu hR)
    (fun i hti hib => hp.committee_cs2_at
      (by have := (SA.ts_le_iff sp).2 (show (u : Int) ≤ (u + 1 : Nat) by omega)
          linarith [sp.toParams.hΔ]) (hti.trans hib)
      (hp.run.time_nonneg i) hib)
    (fun _ _ _ _ hy hcast hs hjb => hp.reset_vote_root_below_bound_at hR hP hbound hy hcast hs hjb)
    (fun _ _ _ _ hy hcast hs hjb hstore =>
      hp.reset_vote_floor_above_old_at hy hR hcast hs hjb hstore hbound) hy hopt hjb

end Consensus.Goldilocks.Healing.Growing

end

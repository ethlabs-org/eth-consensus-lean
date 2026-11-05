module
public import ConsensusLeanTest.Goldilocks.Runs.Asleep.Sleepy
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Inclusion
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthyRecordWriters
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Accountable
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Invariants
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Strict
public import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Order
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
@[expose] public section

/-! # A1.7 inclusion: the update clause is needed (consensus-lean#77)

Kind (r), a rejection test (CONTRIBUTING "Statements"), of the update clause
`UpdatedNoRestart tr y i s` of `Compose.Inclusion`. The run is the two-validator asleep run `tr2`
of `Goldilocks/Runs/Asleep/Run` and `Goldilocks/Runs/Asleep/Sleepy`: both validators are honest,
`w0` is awake at every `t ≥ 0` and proposes every slot, `w1` never wakes (`f = 0 < h_t = 1`,
`n = 2`). The honest proposal is `w0`'s own block `P` of slot `1` (cut `34`, `t_1 = 4`), and the cut
is `i = 80`, the first cut at `t_1 + 6Δ = 10`: the tick that runs the update of slot `1`, before the
update.

* `inclusion_update_rejection`: every premise of A1.7 other than the update clause, and the
  claims' extra ones, hold there (`GoldilocksRun`, `NoColl`, `Sleepy`, the genesis root, the
  joined proposer, `w0` awake and joined at `t` and at `t_1 + 6Δ`, no restart), the update clause
  fails, and `P` is **not** in the confirmed tip.
* `not_inclusionWithoutUpdate`: so A1.7 with the update clause dropped is false.
* `inclusion_control`: one cut later (cut `81`, after the update) the clause holds and `P` is in
  the confirmed tip (`inclusion_sleepy`), so the rejection turns on the clause alone.

**Why the tip is behind `P`** (proved as an invariant, not by evaluating states):
* an optimistic confirmation needs three quarters of the committee, so both validators, and
  `w1` never votes (`no_optimisticLock`);
* the record before the cut is genesis or the result of the update of slot `0` (at
  `t_0 + 6Δ = 6`; the update of slot `1` is at the cut itself), whose block is extended by a vote
  of slot `0` and so is of slot `0` (`result_slot`, `record_slot`);
* `Σ.F` stays genesis: a finalization needs `q = 2` signers, and every attestation on `w0`'s
  chains is its own (`F_genesis`);
* `ac_confirmed` is an ancestor of the effective record or `Σ.F`, so it is of slot `0`
  (`confirmed_slot`), while `P` is of slot `1`.

The witness half of this item (all premises with the clause, at cut `81`) is
`Goldilocks/AC/Inclusion`. -/

namespace Consensus.Goldilocks.Witness.Two

open SA Node

/-- The AC projection of the run is an AC run. -/
theorem acRun2 : SA.ACRun (fun _ => w0) tr2.projAC Set.univ (tr2.HonestBlocks Set.univ) :=
  Compose.goldilocks_ac_projection sp2 ro2 dg2 Set.univ tr2 (fun _ => w0)
    asleepRun_goldilocksRun (dg2_noColl _)

theorem projAC_state2 (i : Nat) : tr2.projAC.state w0 i = (tr2.state w0 i).ac :=
  Compose.projAC_state asleepRun_goldilocksRun.toLocalRun (Set.mem_univ _) i

theorem eq_w0_of_projAC {y : Fin sp2.n} {i : Nat} {ℓ : ACLabel N2}
    (h : tr2.projAC.CallAt y i ℓ) : y = w0 :=
  eq_v0_of_callAt (tr2_callAt.1 (Compose.projAC_callAt.1 h))

/-! ## `Σ.F` stays genesis -/

/-- An attestation that `w0` processes in a block is its own. -/
theorem payload_val {k : Nat} {X : N2.Blk} (h : tr2.BlockCallAt w0 k X) {a : FG.Att sp2.n}
    (ha : a ∈ X.fgPayload) : a.val = w0 := by
  obtain ⟨j, -, src, hc⟩ := asleepRun_goldilocksRun.att_unforgeable w0 (Set.mem_univ _) k a
    (Or.inr ⟨X, h, ha⟩) (Set.mem_univ _)
  exact eq_v0_of_callAt (tr2_callAt.1 hc)

/-- **`Σ.F` of `w0` stays genesis**: a positive finalized height needs a quorum of `q = 2`
signers on the chain, and every attestation on `w0`'s chains is its own. -/
theorem F_genesis (i : Nat) :
    (tr2.state w0 i).fg.F = sp2.toParams.genesisBlock N2.genesisPayload := by
  have hrun := asleepRun_goldilocksRun
  have hr := Compose.fg_reachable hrun.toLocalRun (Set.mem_univ w0) i
  by_contra hF
  obtain ⟨B, hB, hBF, -⟩ := Store.F_lt_finalizer hr hF
  obtain ⟨c, hc, -, -, hσ⟩ := Store.chain_state_of_chain sp2.toParams N2.Payload _ _ hr B hB
  rcases Nat.eq_zero_or_pos ((tr2.state w0 i).fg.σ B.root).hF with h0 | h1
  · have hFr : (tr2.state w0 i).fg.F.root = sp2.genesisRoot :=
      hBF.symm.trans ((FG.chain_invariants sp2.toParams.fg _ _ hσ).2.2.2.2.1 h0)
    obtain ⟨hFt, -⟩ := Store.cache_invariants sp2.toParams N2.Payload _ _ hr
    obtain ⟨-, ⟨hinj, -⟩, hg, -⟩ := Store.accepted_tree sp2.toParams N2.Payload _ _ hr
    exact hF (hinj hFt hg hFr)
  · obtain ⟨Q, hQ, hv⟩ := sp2.toParams.fg.finalized_quorum hσ h1
    have hsub : Q ⊆ {w0} := by
      intro v hvQ
      obtain ⟨a, ha, rfl, -⟩ := hv v hvQ
      obtain ⟨b, hb, haX⟩ := List.mem_flatMap.1 ha
      obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hb
      rcases Compose.tree_cases hrun.toLocalRun (Set.mem_univ w0) (hc X hX) with rfl | ⟨k, -, hk⟩
      · exact absurd haX List.not_mem_nil
      · exact Finset.mem_singleton.2 (payload_val ⟨true, hk⟩ haX)
    have h1 : Q.card ≤ 1 := (Finset.card_le_card hsub).trans (Finset.card_singleton _).le
    have hq : sp2.toParams.fg.q = 2 := rfl
    omega

/-! ## The record before the update of slot `1` -/

/-- **No optimistic confirmation**: it needs three quarters of the committee, so a vote of `w1`
in the pool, and `w1` never votes. -/
theorem no_optimisticLock {q σ : Nat} {R : N2.Blk} {CV : Set (Vote sp2.n)} :
    ¬ OptimisticLockAt tr2.projAC w0 q σ R CV := by
  rintro ⟨ℓ, A, hpt, -, hsel, -⟩
  unfold optimisticSelect at hsel
  dsimp only at hsel
  split_ifs at hsel
  have h34 := (deepest_mem hsel).1.2.1
  have hw1 : w1 ∈ optimisticVoters sp2 A ℓ.frame (sp2.slot (tr2.projAC.time q)) R := by
    by_contra hn
    have hsub : optimisticVoters sp2 A ℓ.frame (sp2.slot (tr2.projAC.time q)) R ⊆ {w0} :=
      fun y hy => by
        rcases eq_w0_or_w1 y with rfl | rfl
        · rfl
        · exact absurd hy hn
    have h1 := Set.ncard_le_ncard hsub (Set.finite_singleton _)
    rw [Set.ncard_singleton] at h1
    change 3 * 2 ≤ _ at h34
    omega
  obtain ⟨x, hx, hxv, -⟩ := hw1
  obtain ⟨-, j', -, e', ⟨ℓ', hc', -⟩, -⟩ :=
    optimisticPoint_pool_vote acRun2 (Set.mem_univ w0) hpt hx (Set.mem_univ _)
  rw [hxv] at hc'
  exact w1_ne (eq_w0_of_projAC hc')

/-- **A result before cut `80` is of slot `0`**: it is the update of slot `0` (the update of
slot `1` is at time `10`, at or after cut `80`), whose result a vote of slot `0` extends, and the
head of a vote of slot `0` is of slot `0`. -/
theorem result_slot {q s : Nat} {R : N2.Blk} {CV : Set (Vote sp2.n)} (hq : q < 80)
    (hres : ResultAt tr2.projAC w0 q s R CV) : R.slot = 0 := by
  have hr := acRun2.localRun
  have hU := hr.coherent
  obtain ⟨ℓ, ⟨hc, -, ht, -⟩, hconf, -⟩ := hres
  have hs : s = 0 := by
    change ((q / 8 : Nat) : Int) = 4 * 1 * (s : Int) + 6 * 1 at ht
    have : q / 8 ≤ 9 := by omega
    omega
  subst hs
  obtain ⟨⟨-, -, hmaj⟩, -⟩ := deepest_mem hconf
  unfold confirmationScore at hmaj
  dsimp only at hmaj
  have key : ∀ {S : Set (Fin sp2.n)} {a : Nat}, a < 2 * S.ncard → S.Nonempty :=
    fun h => Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨u, hu⟩ := key hmaj
  obtain ⟨-, x, ⟨hxp, -⟩, -, hxs, X, hXt, hXr, hRX⟩ := hu
  rw [projAC_state2, tr2_state] at hxp
  obtain ⟨j, -, ℓ', hc', e, he, rfl⟩ := asleepRun_votes q 0 _ hxp
  have hcast : CastAt tr2.projAC w0 j ℓ' e := ⟨Compose.projAC_callAt.2 hc', he⟩
  obtain ⟨⟨Hd, hHd, hHdr, -⟩, -⟩ := Compose.cast_head_fcRoot hr (Set.mem_univ w0) hcast
  have hHds := frame_slot_le sp2 hr (Set.mem_univ w0) hcast.1 Hd hHd
  rw [← (castAt_spec hr (Set.mem_univ w0) hcast).2.1] at hHds
  have hes : e.msg.slot = 0 := by exact_mod_cast hxs
  have hΦU := (frameIn_of_callAt hr (Set.mem_univ w0) hc).2
  have hΦ'U := (frameIn_of_callAt hr (Set.mem_univ w0) hcast.1).2
  obtain rfl : X = Hd := hU.1 (hΦU hXt) (hΦ'U hHd) (hXr.trans hHdr.symm)
  have := Anc.slot_le hU (Anc.mono hΦU hRX)
  omega

/-- **The record before cut `80` names a block of slot `0`**: genesis, or the last writer's
result (no optimistic writer, `no_optimisticLock`). -/
theorem record_slot {R : N2.Blk}
    (hl : lookup (Node.frame (tr2.state w0 80)) (tr2.state w0 80).ac.latestConfirmed = some R) :
    R.slot = 0 := by
  have hrun := asleepRun_goldilocksRun
  obtain ⟨hRm, -⟩ := lookup_eq_some hl
  by_cases hg : R.root = sp2.genesisRoot
  · obtain ⟨-, ⟨hinj, -⟩, hgm, -⟩ := Store.accepted_tree sp2.toParams N2.Payload _ _
      (Compose.fg_reachable hrun.toLocalRun (Set.mem_univ w0) 80)
    rw [hinj hRm.1 hgm hg]
    rfl
  · obtain ⟨q, hq, _, _, _, _, hsrc⟩ :=
      Obligations.last_record_writer hrun (dg2_noColl _) (Set.mem_univ w0) hl hg
    rcases hsrc with ⟨s, CV, hres⟩ | ⟨⟨CV, hopt⟩, -⟩
    · exact result_slot hq hres
    · exact absurd hopt no_optimisticLock

/-- **The confirmed tip before cut `80` is of slot `0`**: `ac_confirmed` is an ancestor of the
effective record (the record's block, or `Σ.F`), or `Σ.F`, and both are of slot `0`. -/
theorem confirmed_slot : (tr2.confirmedAt w0 80).slot = 0 := by
  have hΦ := Compose.frameOK_state asleepRun_goldilocksRun.toLocalRun (Set.mem_univ w0) 80
  have hF : (Node.frame (tr2.state w0 80)).F.slot = 0 := by
    change (tr2.state w0 80).fg.F.slot = 0
    rw [F_genesis]
    rfl
  have hC : ((lookup (Node.frame (tr2.state w0 80)) (tr2.state w0 80).ac.latestConfirmed).getD
      (Node.frame (tr2.state w0 80)).F).slot = 0 := by
    rcases hl : lookup (Node.frame (tr2.state w0 80)) (tr2.state w0 80).ac.latestConfirmed with
      _ | R
    · exact hF
    · exact record_slot hl
  change (acConfirmed sp2 (tr2.state w0 80).ac (Node.frame (tr2.state w0 80))
    (tr2.time 80)).slot = 0
  unfold acConfirmed
  dsimp only
  rcases hd : deepest (Node.frame (tr2.state w0 80)) {X | X ∈ (Node.frame (tr2.state w0 80)).tree ∧
      (Node.frame (tr2.state w0 80)).Anc X ((lookup (Node.frame (tr2.state w0 80))
        (tr2.state w0 80).ac.latestConfirmed).getD (Node.frame (tr2.state w0 80)).F) ∧
      (Node.frame (tr2.state w0 80)).Anc X (acHead sp2 (tr2.state w0 80).ac
        (Node.frame (tr2.state w0 80)) (tr2.time 80))} with _ | X
  · exact hF
  · obtain ⟨⟨-, hXC, -⟩, -⟩ := deepest_mem hd
    have := Anc.slot_le hΦ.coherent hXC
    change X.slot = 0
    omega

/-! ## The rejection -/

/-- The first cut at `t_1 + 6Δ = 10` is a call of `w0`: its tick. -/
theorem isCall_80 : tr2.IsCall w0 80 := by
  refine ⟨(acCall v0 (tickState N2 dg2 10) ((10 : Nat) : Int) .tick).2, rfl, ?_⟩
  change (tickRun N2 dg2).label (8 * 10) = _
  rw [tickRun_label, show 8 * 10 / 8 = 10 by omega, show 8 * 10 % 8 = 0 by omega]
  exact tickCuts_head N2 dg2 10

/-- (r) **A1.7's update clause is needed.** On the asleep run, at the first cut at `t_1 + 6Δ`
(cut `80`, before the update of slot `1`), every premise of A1.7 for `w0`'s proposal `P` of
slot `1` holds except the update clause, which fails, and `P` is not in the confirmed tip. -/
theorem inclusion_update_rejection : ∃ P : N2.Blk,
    GoldilocksRun (sp := sp2) (ro := ro2) (fun _ => w0) dg2 Set.univ tr2 ∧
      Compose.NoCollRun dg2 tr2 ∧ tr2.SleepyRun Set.univ 1 ∧
      (sp2.toParams.genesisBlock (goldilocksNode sp2 ro2).genesisPayload).RootOk dg2 ∧
      tr2.ProposesAt w0 34 P ∧ P.slot = 1 ∧ joined sp2 (tr2.state w0 34).ac (tr2.time 34) ∧
      tr2.IsCall w0 80 ∧ sp2.ts (1 : Nat) + 6 * sp2.Δ ≤ tr2.time 80 ∧
      tr2.awake w0 (tr2.time 80) ∧ tr2.JoinedAt w0 (tr2.time 80) ∧
      tr2.awake w0 (sp2.ts (1 : Nat) + 6 * sp2.Δ) ∧
      tr2.JoinedAt w0 (sp2.ts (1 : Nat) + 6 * sp2.Δ) ∧
      (∀ k', tr2.RestartAt w0 k' → sp2.ts (1 : Nat) + 6 * sp2.Δ < tr2.time k' →
        tr2.time k' ≤ tr2.time 80 → False) ∧
      ¬ Compose.UpdatedNoRestart tr2 w0 80 1 ∧
      ¬ Anc (tr2.HonestBlocks Set.univ) P (tr2.confirmedAt w0 80) := by
  obtain ⟨P, hP, hPs⟩ := tr2_proposesAt 1 le_rfl
  have hrun := asleepRun_goldilocksRun
  have hts : sp2.ts (1 : Nat) + 6 * sp2.Δ = 10 := by
    change 4 * 1 * ((1 : Nat) : Int) + 6 * 1 = 10; norm_num
  refine ⟨P, hrun, dg2_noColl _, tr2_sleepy, dg2_genesis, hP, hPs, joined_w0 34 _, isCall_80,
    by rw [hts]; rfl, ⟨rfl, by change (0 : Int) ≤ ((80 / 8 : Nat) : Int); omega⟩,
    joinedAt _ _, ⟨rfl, by rw [hts]; norm_num⟩, joinedAt _ _,
    fun k' hk' => absurd hk' (tr2_no_restart _ k'), ?_, ?_⟩
  · rintro ⟨k, hk, ℓ, ⟨-, -, ht, -⟩, -⟩
    change ((k / 8 : Nat) : Int) = 4 * 1 * ((1 : Nat) : Int) + 6 * 1 at ht
    omega
  · intro hanc
    have := Anc.slot_le (Compose.honest_blocks_coherent hrun.toLocalRun (dg2_noColl _)) hanc
    rw [hPs, confirmed_slot] at this
    omega

/-- Control: one cut later (cut `81`, the tick's next cut, after the update of slot `1`) the
update clause holds, and `P` is in the confirmed tip, as `inclusion_sleepy` gives. -/
theorem inclusion_control : ∃ P : N2.Blk, tr2.ProposesAt w0 34 P ∧ P.slot = 1 ∧
    Compose.UpdatedNoRestart tr2 w0 81 1 ∧
    Anc (tr2.HonestBlocks Set.univ) P (tr2.confirmedAt w0 81) := by
  obtain ⟨P, hP, hPs⟩ := tr2_proposesAt 1 le_rfl
  have hts : sp2.ts (1 : Nat) + 6 * sp2.Δ = 10 := by
    change 4 * 1 * ((1 : Nat) : Int) + 6 * 1 = 10; norm_num
  have hl80 : tr2.CallAt w0 80 (acCall v0 (tickState N2 dg2 10) ((10 : Nat) : Int) .tick).2 := by
    refine ⟨rfl, ?_⟩
    change (tickRun N2 dg2).label (8 * 10) = _
    rw [tickRun_label, show 8 * 10 / 8 = 10 by omega, show 8 * 10 % 8 = 0 by omega]
    exact tickCuts_head N2 dg2 10
  have hu : Compose.UpdatedNoRestart tr2 w0 81 1 :=
    ⟨80, by omega, _, ⟨Compose.projAC_callAt.2 hl80, rfl, by rw [hts]; rfl,
      by rw [projAC_state2]; exact joined_w0 80 _⟩, fun k' _ _ => tr2_no_restart _ k'⟩
  have hc81 : tr2.IsCall w0 81 := by
    obtain ⟨L2, ct, L3, he, -⟩ :=
      onTick_shape N2 dg2 v0 (tickState N2 dg2 10) ((10 : Nat) : Int) 0
    have hlen : 1 < (tickCuts N2 dg2 10).length := by
      change 1 < (onTick (fun _ => v0) dg2 v0 (tickState N2 dg2 10) ((10 : Nat) : Int) 0).2.length
      rw [he]; simp
    refine ⟨(tickCuts N2 dg2 10)[1], rfl, ?_⟩
    change (tickRun N2 dg2).label 81 = _
    rw [tickRun_label, show 81 / 8 = 10 by omega, show 81 % 8 = 1 by omega]
    exact List.getElem?_eq_getElem hlen
  refine ⟨P, hP, hPs, hu, Compose.inclusion_sleepy sp2 ro2 (fun _ => w0) dg2 Set.univ tr2 1
    asleepRun_goldilocksRun (dg2_noColl _) tr2_sleepy w0 (Set.mem_univ _) 34 P 1 hP
    hPs (joined_w0 34 _) w0 (Set.mem_univ _) 81 hc81 (joinedAt _ _)
    (fun k' hk' => absurd hk' (tr2_no_restart _ k')) hu⟩

/-- A1.7 with the update clause `UpdatedNoRestart tr y i s` dropped, keeping the premises the
statement leaves out because they follow from the clause and the call (awake at `t`, joined at
`t_s + 6Δ`), so that the rejection shows the clause is needed even with them. -/
def InclusionWithoutUpdate : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (ΔF : Time),
    GoldilocksRun proposer dg H tr → Compose.NoCollRun dg tr → tr.SleepyRun H ΔF →
    ∀ p ∈ H, ∀ k (P : SA.Blk sp.n (List (FG.Att sp.n))) (s : Nat),
      tr.ProposesAt p k P → P.slot = s → SA.joined sp (tr.state p k).ac (tr.time k) →
      ∀ y ∈ H, ∀ i, tr.IsCall y i →
        tr.awake y (tr.time i) → tr.JoinedAt y (tr.time i) →
        tr.JoinedAt y (sp.ts s + 6 * sp.Δ) →
        (∀ k', tr.RestartAt y k' → sp.ts s + 6 * sp.Δ < tr.time k' → tr.time k' ≤ tr.time i →
          False) →
        Anc (tr.HonestBlocks H) P (tr.confirmedAt y i)

/-- (r) **A1.7 without the update clause is false** (consensus-lean#77). -/
theorem not_inclusionWithoutUpdate : ¬ InclusionWithoutUpdate := by
  intro h
  obtain ⟨P, hrun, hnc, hsl, -, hP, hPs, hpj, hc, -, hyw, hyj, -, hyj₀, hnr, -, hnot⟩ :=
    inclusion_update_rejection
  exact hnot (h sp2 ro2 (fun _ => w0) dg2 Set.univ tr2 1 hrun hnc hsl w0 (Set.mem_univ _) 34 P
    1 hP hPs hpj w0 (Set.mem_univ _) 80 hc hyw hyj hyj₀ hnr)

end Consensus.Goldilocks.Witness.Two

end

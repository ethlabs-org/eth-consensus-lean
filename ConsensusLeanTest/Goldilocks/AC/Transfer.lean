module
public import ConsensusLeanTest.Goldilocks.AC.Optimistic
@[expose] public section

/-! # Witnesses for the premises of the growing Goldilocks transfer AC steps

The hypotheses of A1.2 `FirstTransfer` and A1.3 `NextTransfer` (`Statements/AC/Growing.lean`) hold
together of the run `trW` of `Goldilocks/AC/Optimistic` (one validator `v0`, `Δ = 1`,
`t_s = 4s`, `k = c = 2`, frame `Φ₁` with tree `{g, B1}`, coherent set `U₁ = {g, B1}`, honest set
all of `Fin 1`), so neither proved milestone is vacuous. Both are taken at the slot-`2` vote of
`v0` at cut 1 (time `9 = t_2 + Δ`), with head `B1`.

`*_premises_satisfiable` state, for each statement at `sp1`, `FGP := Unit`, `ro1`, that there are
values of all its universally bound variables satisfying `ACRun` and every hypothesis (copied from
the statement); `*_on_witness` apply `Growing.acStepsAt` with constant `H := fun _ => Set.univ`.

Limitations: `n = 1` and `f = 0`, so the participation and fault bounds hold trivially. The fast
lock of A1.2 has the optimistic origin (`v0`'s optimistic confirmation of slot `1` at cut 0,
`optimisticLock_W`). A `FastUpdateAt` origin of slot `1` would need the update of slot `1`, at
`t_1 + 6Δ = 10`, which is not a cut of `trW`; its only update (slot `2`, cut 3) could serve
`s = 2` only, whose A1.2 needs a slot-`3` vote, and `trW` has none. Both would need a new run. -/

namespace Consensus.Goldilocks.AC.Test

/-! ## The premises -/

/-- `f < h_t` at every time: no validator is faulty, and `v0` is awake and never restarts. -/
theorem faultBound_W (t : Time) : FaultBound trW Set.univ t := by
  have h : {y | y ∈ (Set.univ : Set (Fin sp1.n)) ∧ trW.awake y t ∧ JoinedAt trW y t} =
      Set.univ :=
    Set.eq_univ_of_forall fun y => ⟨trivial, trivial, fun k hk => absurd hk (trW_no_restart y k)⟩
  unfold FaultBound honestAwakeJoined
  rw [h, ncard_univ_v]
  simp

/-- `f < h_t` among the full committee at every time. -/
theorem faultBoundK_W (s : Nat) (t : Time) :
    FaultBoundK (CommitteeDict.full sp1.n) s trW Set.univ t :=
  (faultBoundK_full_iff s t).mpr (faultBound_W t)

theorem vote1_mem_CV1 : vote1 ∈ CV1 := by
  refine ⟨?_, B1, B1_mem, rfl, Relation.ReflTransGen.refl⟩
  rw [A0_eq]
  simp [vote1]

/-- The honest slot-`1` votes of the run are the counted votes `CV1` of the optimistic lock: both
are `{vote1}`. -/
theorem honestSlot1Votes_eq :
    {v | ∃ x ∈ (Set.univ : Set (Fin sp1.n)), ∃ j e', VoteAt trW x j e' ∧ e'.msg = v ∧
      v.slot = 1} = CV1 := by
  ext v
  refine ⟨fun ⟨x, _, j, e', he, hv, hs⟩ => ?_, fun hv => ?_⟩
  · subst hv
    rcases voteAt_cases he with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact vote1_mem_CV1
    · exact absurd hs (by decide)
  · obtain rfl := mem_CV1 hv
    exact ⟨v0, trivial, 0, e0, voteAt_0 v0, rfl, rfl⟩

/-- Every honest slot-`1` vote of the run extends `B1`: the only one is `vote1`, on `B1`. -/
theorem slot1_extend_W : ∀ x ∈ (Set.univ : Set (Fin sp1.n)), ∀ j e', VoteAt trW x j e' →
    e'.msg.slot = 1 → VoteExtends U₁ e'.msg B1 := fun _ _ j e he hs => by
  rcases voteAt_cases he with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact ⟨B1, B1_mem, rfl, Relation.ReflTransGen.refl⟩
  · exact absurd hs (by decide)

/-- The honest voters of slot `1` are the whole committee. -/
theorem participation1_W : sp1.n ≤ 2 * {x | x ∈ (Set.univ : Set (Fin sp1.n)) ∧
    ∃ j e', VoteAt trW x j e' ∧ e'.msg.slot = 1}.ncard := by
  have : {x | x ∈ (Set.univ : Set (Fin sp1.n)) ∧
      ∃ j e', VoteAt trW x j e' ∧ e'.msg.slot = 1} = Set.univ :=
    Set.eq_univ_of_forall fun x => ⟨trivial, 0, e0, voteAt_0 x, rfl⟩
  rw [this, ncard_univ_v]
  decide

/-- `Carry_{v0}(1, S_1, B1)` at the slot-`2` vote, for the honest slot-`1` votes. -/
theorem carryHonest_W : CarryAt trW U₁ v0 1 e1 1
    {v | ∃ x ∈ (Set.univ : Set (Fin sp1.n)), ∃ j e', VoteAt trW x j e' ∧ e'.msg = v ∧
      v.slot = 1} := by
  rw [honestSlot1Votes_eq]
  exact carry_W

/-! ## The witnesses -/

/-- (a) **A1.2, `FirstTransfer`: the premises are satisfiable.** Every hypothesis of the
statement holds of the run at `s = 1`, with the full committee: `v0`'s fast lock of slot `1` on
`B1` at cut 0 (optimistic origin) and its slot-`2` vote at cut 1, time `9`. -/
theorem firstTransfer_premises_satisfiable :
    ∃ (H : Set (Fin sp1.n)) (U : Set (Blk sp1.n Unit)) (tr : GTrace sp1 Unit ro1)
      (proposer : Nat → Fin sp1.n) (K : CommitteeDict sp1.n) (s : Nat) (x y : Fin sp1.n)
      (i₀ i : Nat) (B : Blk sp1.n Unit) (CV : Set (Vote sp1.n))
      (ℓ : ACLabel (goldilocksAC sp1 Unit ro1)) (e : Em sp1 Unit),
    ACRun proposer tr H U ∧
    CommitteeP K tr H ∧ CommitteeT K tr H ∧ (∀ σ, (K.committee σ).ncard = sp1.committeeSize) ∧
    x ∈ H ∧ FastLockAt tr x i₀ s B CV ∧
    y ∈ H ∧ CastAt tr y i ℓ e ∧ e.msg.slot = s + 1 ∧
    SyncAC (goldilocksAC sp1 Unit ro1) H U (sp1.ts s) (tr.time i) tr ∧
    CarryAt tr U y i e s CV ∧ FaultBoundK K s tr H (tr.time i) ∧
    2 * (K.committee (s + 1) ∩ Hᶜ).ncard < sp1.committeeSize ∧
    ViableAtVote ℓ e (s + 1) B ∧ EarlierVotesExtend tr H U i (s + 1) B :=
  ⟨Set.univ, U₁, trW, fun _ => v0, CommitteeDict.full sp1.n, 1, v0, v0, 0, 1, B1, CV1, ℓ1, e1,
    acRun_W, CommitteeP.full, CommitteeT.full, size_binding_full rfl, trivial,
    Or.inr optimisticLock_W, trivial, castAt_W, rfl, sync_W (by decide), carry_W,
    faultBoundK_W _ _, faultsK_W, viable_W, earlier_W⟩

/-- (a) **A1.3, `NextTransfer`: the premises are satisfiable.** Every hypothesis of the statement
holds of the run at `m = 1`, with the full committee: the honest slot-`1` votes (`{vote1}`, on
`B1`, the whole committee) and `v0`'s slot-`2` vote at cut 1, time `9`. -/
theorem nextTransfer_premises_satisfiable :
    ∃ (H : Set (Fin sp1.n)) (U : Set (Blk sp1.n Unit)) (tr : GTrace sp1 Unit ro1)
      (proposer : Nat → Fin sp1.n) (K : CommitteeDict sp1.n) (m : Nat) (y : Fin sp1.n) (i : Nat)
      (B : Blk sp1.n Unit) (ℓ : ACLabel (goldilocksAC sp1 Unit ro1)) (e : Em sp1 Unit),
    ACRun proposer tr H U ∧
    CommitteeP K tr H ∧ CommitteeT K tr H ∧ (∀ σ, (K.committee σ).ncard = sp1.committeeSize) ∧
    y ∈ H ∧ CastAt tr y i ℓ e ∧ e.msg.slot = m + 1 ∧
    (∀ x ∈ H, ∀ j e', VoteAt tr x j e' → e'.msg.slot = m → VoteExtends U e'.msg B) ∧
    sp1.committeeSize ≤ 2 * {x | x ∈ H ∧ ∃ j e', VoteAt tr x j e' ∧ e'.msg.slot = m}.ncard ∧
    CarryAt tr U y i e m {v | ∃ x ∈ H, ∃ j e', VoteAt tr x j e' ∧ e'.msg = v ∧ v.slot = m} ∧
    FaultBoundK K m tr H (tr.time i) ∧
    2 * (K.committee (m + 1) ∩ Hᶜ).ncard < sp1.committeeSize ∧
    ViableAtVote ℓ e (m + 1) B ∧ EarlierVotesExtend tr H U i (m + 1) B :=
  ⟨Set.univ, U₁, trW, fun _ => v0, CommitteeDict.full sp1.n, 1, v0, 1, B1, ℓ1, e1, acRun_W,
    CommitteeP.full, CommitteeT.full, size_binding_full rfl, trivial, castAt_W, rfl,
    slot1_extend_W, participation1_W, carryHonest_W, faultBoundK_W _ _, faultsK_W, viable_W,
    earlier_W⟩

/-! ## The milestones on the witness -/

private theorem constant_run : Growing.ACRun (fun _ => v0) trW (fun _ => Set.univ) U₁ := by
  let h := acRun_W
  let l := h.localRun
  refine ⟨{
    antitone := fun _ _ _ => Set.Subset.rfl
    coherent := l.coherent
    init := l.init
    exec := l.exec
    frameLaw := fun y i ℓ hy => l.frameLaw y hy i ℓ
    time_nonneg := l.time_nonneg
    time_mono := l.time_mono
    awake_of_call := fun y i ℓ hy => l.awake_of_call y hy i ℓ
    restart_of_sleep := fun y i ℓ u hy => l.restart_of_sleep y hy i ℓ u
    restart_at_wake := fun y u v hy => l.restart_at_wake y hy u v
    sleep_of_restart := fun y i ℓ hy => l.sleep_of_restart y hy i ℓ }, {
    pool_vote := fun y i σ hy => h.honest.pool_vote y hy i σ
    message_vote := fun y i ℓ v hy => h.honest.message_vote y hy i ℓ v
    proposer := ?_
    one_block := ?_ }, h.vstart⟩
  · rintro B ⟨y, i, ℓ, hy, hc, hB⟩
    exact h.honest.proposer B ⟨y, hy, i, ℓ, hc, hB⟩
  · intro y i ℓ B y' i' ℓ' B' hy hc hB hy' hc' hB'
    exact h.honest.one_block B B' ⟨y, hy, i, ℓ, hc, hB⟩ ⟨y', hy', i', ℓ', hc', hB'⟩

private theorem constant_sync {a b : Time} (h : SyncAC GA1 Set.univ U₁ a b trW) :
    SyncACAt GA1 (fun _ => Set.univ) U₁ a b trW :=
  ⟨fun x i m hx hs ha hb y j ℓ hy => h.1 x hx i m hs ha hb y hy j ℓ,
    fun x i B hx hs ha hb y j ℓ hy => h.2 x hx i B hs ha hb y hy j ℓ⟩

/-- (a) A1.2 on the run: the slot-`2` vote extends `B1`. -/
theorem firstTransfer_on_witness : VoteExtends U₁ e1.msg B1 :=
  (Growing.acStepsAt sp1).firstTransfer Unit ro1 (fun _ => Set.univ) U₁ trW
    (fun _ => v0) constant_run
    (CommitteeDict.full sp1.n) CommitteePAt.full
    (fun _ _ _ _ _ _ _ v _ => mem_full v.slot _) (size_binding_full rfl) 1 v0 v0 0 1
    B1 CV1 ℓ1 e1 trivial (Or.inr optimisticLock_W) trivial castAt_W rfl
    (constant_sync (sync_W (by decide)))
    carry_W (faultBoundK_W _ _) faultsK_W viable_W
    (fun x j hj hx e he hs => earlier_W x hx j hj e he hs)

/-- (a) A1.3 on the run: the slot-`2` vote extends `B1`. -/
theorem nextTransfer_on_witness : VoteExtends U₁ e1.msg B1 := by
  apply (Growing.acStepsAt sp1).nextTransfer Unit ro1 (fun _ => Set.univ) U₁ trW
    (fun _ => v0) constant_run
    (CommitteeDict.full sp1.n) CommitteePAt.full
    (fun _ _ _ _ _ _ _ v _ => mem_full v.slot _) (size_binding_full rfl) 1 v0 1 B1
    ℓ1 e1 trivial castAt_W rfl
    (fun x j e hx he hs => slot1_extend_W x hx j e he hs) _ _ (faultBoundK_W _ _)
    faultsK_W viable_W (fun x j hj hx e he hs => earlier_W x hx j hj e he hs)
  · simpa only [Set.mem_univ, true_and] using participation1_W
  · simpa only [Set.mem_univ, true_and] using carryHonest_W

end Consensus.Goldilocks.AC.Test

end

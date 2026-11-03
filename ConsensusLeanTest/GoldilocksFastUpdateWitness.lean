module
public import ConsensusLeanTest.GoldilocksPersistWitness
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
@[expose] public section

/-! # The one-validator tick run writes a fast lock by the fast test of the update

Kind (a), joint satisfiability (CONTRIBUTING "Statements"), on the one-validator tick run of
`GoldilocksWitness` (`n = 1`, `Δ = 1`, `t_s = 4s`, `k = c = 2`, a tick at every time, no
restart): the update origin of `FastLockAt` (`FastUpdateAt`, the fast test of the confirmation
update) is realized, for every slot `s ≥ 1`, at the tick of `t_s + 6Δ = 4s + 6`, cut
`8 · (4s + 6)` (its `ac_on_tick`; slot `1`: cut `80`, time `10`).

* `updateAt_tickRun`: the update of slot `s` runs there (`UpdateAt`: a tick, at `t_s + 6Δ`,
  joined), with the frame `Φ` of the tick state, the chain `blk f, …, blk (s + 1)`.
* `getConfirmation_update`: the result is `blk s`, the head of `cv s`, the only slot-`s` vote
  (one voter; its score is `1`, `1 < 2 · 1`). The vote counts as early support: it and `blk s`
  are stamped before `t_s + 2Δ` (`resolutionTime_update`; the own block is accepted at `t_s`).
* `notConflicts_update`: no live lock vetoes a block of the frame: every live lock block is a
  frame block, and the frame is one chain.
* `fastTest_update`: the fast test passes on `blk s` (`n = 1 ≤ 2 · 1`).
* `fastSelect_update`: the deepest unvetoed fast block of the path `{blk max(f, 1), …, blk s}`
  of the result is `blk s`.
* `fastCounted_update`: the counted votes are `{cv s}`.
* `fastUpdate_tickRun`: `FastUpdateAt (tickRun N1 dg1).projAC v0 (8 · (4s + 6)) s (blk s)
  {cv s}` from these facts; `fastUpdate_slot_one` at `s = 1`, cut `80`.
* `update_writes_fastLock`: the update's write: the post-state locks are `add_locks` of the
  stored locks with a set of new entries that holds `((blk s).root, true, s + 2)`
  (`fastExpiry = s + 2` at `k = c = 2`), and the post-state holds the lock
  `⟨(blk s).root, s, true, s + 2⟩` (live at `slot(4s + 6) = s + 1`, on a frame block).
* `fastLockAt_update`: `FastLockAt` by the update origin (`Or.inl`), as A1.2 and A1.9 consume it.
* `firstTransfer_premises_update`: the premises of A1.2 (`FirstTransfer`) at that lock and the
  slot-`(s + 1)` vote at cut `8 · t_{s+1} + 3` (`Sync`, `Carry`, `f < h_τ`, the viable voter
  block tree, no earlier vote); `firstTransfer_update` applies `FirstTransfer` to them. The vote's
  cut precedes the update's (`t_{s+1} < t_s + 6Δ`): A1.2 does not order the two.

Limitations: `n = 1` and `f = 0`, so this shows the update clause consistent, not met with
faults. No lock ever vetoes on a single chain, so the veto filter of the path is the identity
here (the vetoed case is exercised at the definition level by `GoldilocksGradedLocks`). Lock sets
do not record their origin, and the optimistic confirmation of slot `s` at `t_s` writes the same
tuple `⟨(blk s).root, s, true, s + 2⟩` (at `s = 1`, cut `35`: `persistPremises_tickRun`); the
update origin is witnessed by `FastUpdateAt` and by the entry of the update's own write, not by
the post-state membership alone. -/

namespace Consensus.Goldilocks.Witness.One

open SA Node ChainFrame

/-! ## The update cut -/

/-- The cut `8 · (4s + 6)` is the `ac_on_tick` of the tick of `4s + 6`, with no emission. -/
theorem update_label (s : Nat) : (tickRun N1 dg1).label (8 * (4 * s + 6)) =
    some (.ac ⟨.tick, Node.frame (tickState N1 dg1 (4 * s + 6)), []⟩) := by
  rw [tickRun_label, show 8 * (4 * s + 6) / 8 = 4 * s + 6 by omega,
    show 8 * (4 * s + 6) % 8 = 0 by omega, tickCuts_other (by omega) (by omega)]
  rfl

theorem update_callAt (s : Nat) : (tickRun N1 dg1).projAC.CallAt v0 (8 * (4 * s + 6))
    ⟨.tick, Node.frame (tickState N1 dg1 (4 * s + 6)), []⟩ :=
  Compose.projAC_callAt.2 ⟨rfl, update_label s⟩

theorem update_time (s : Nat) :
    (tickRun N1 dg1).projAC.time (8 * (4 * s + 6)) = ((4 * s + 6 : Nat) : Int) := by
  rw [time_eq, show 8 * (4 * s + 6) / 8 = 4 * s + 6 by omega]

/-- The frame of the update of slot `s`: the chain `blk f, …, blk (s + 1)`, with `f ≤ s`. -/
theorem update_frame (s : Nat) : ∃ f, f ≤ s ∧
    ChainFrame (Node.frame (tickState N1 dg1 (4 * s + 6))) f (jexp (s + 1)) (s + 1) := by
  obtain ⟨f, hf⟩ := good_frame (good_tick (4 * s + 6))
  rw [show tip (4 * s + 6) = s + 1 by unfold tip; omega] at hf
  exact ⟨f, le_trans hf.fj (jexp_succ_le s), hf⟩

/-- (a) **The update of slot `s` runs at cut `8 · (4s + 6)`**: the tick at `t_s + 6Δ`, joined. -/
theorem updateAt_tickRun (s : Nat) : UpdateAt (tickRun N1 dg1).projAC v0 (8 * (4 * s + 6)) s
    ⟨.tick, Node.frame (tickState N1 dg1 (4 * s + 6)), []⟩ := by
  refine ⟨update_callAt s, rfl, ?_, ?_⟩
  · rw [update_time, ts_nat, delta1]; push_cast; ring
  · rw [projAC_state']
    exact joined_of_bot (tickRun_restartTime _) _

/-! ## The state at the update -/

theorem update_pool_cv (s : Nat) :
    ∀ v ∈ ((tickRun N1 dg1).projAC.state v0 (8 * (4 * s + 6))).pool s, v = cv s := by
  rw [projAC_state']; exact pool_cv _ s

theorem update_pool_eq (s : Nat) :
    ((tickRun N1 dg1).projAC.state v0 (8 * (4 * s + 6))).pool s = [cv s] := by
  rw [projAC_state', state_tick, (good_tick (4 * s + 6)).ac.pool s,
    ite_pos ⟨by omega, by unfold tip; omega⟩]

/-- **The stamp of a held vote of slot `s`** is before `t_s + 2Δ`: it is the time of the cut
that sent or accepted it into the pool, before the tick of `t_s + 2Δ`, whose pool holds it. -/
theorem voteStamp_lt {s i : Nat} (hx : cv s ∈ ((tickRun N1 dg1).projAC.state v0 i).pool s) :
    ((tickRun N1 dg1).projAC.state v0 i).voteStamp (cv s) <
      ETime.of (sp1.ts s + 2 * sp1.Δ) := by
  rcases SA.pool_origin acRun.localRun (Set.mem_univ v0) i (cv s) hx with
    ⟨k, -, ⟨ℓ', hc', hk⟩, hstk, -⟩ | ⟨k, -, ℓ', hc', hrs, -⟩
  · rw [hstk]
    apply etime_of_lt
    suffices hlt : k < 8 * (4 * s + 2) by
      rw [time_eq, ts_nat]
      change (((k / 8 : Nat)) : Int) < 4 * (s : Int) + 2 * 1
      omega
    obtain ⟨-, -, hl⟩ := projAC_call hc'
    rcases hk with ⟨e', he', hm⟩ | ⟨-, hnot, -⟩
    · rcases emit_cases hl he' with ⟨rfl, hm', -⟩ | ⟨k', fg', rfl, -, -, -, hm', -⟩
      · omega
      · have : k' + 1 = s := congrArg Vote.slot (hm'.symm.trans hm)
        omega
    · by_contra hge
      apply hnot
      change cv s ∈ ((tickRun N1 dg1).projAC.state v0 k).pool s
      rw [projAC_state']
      refine tickRun_pool_mono (Nat.le_of_not_lt hge) s ?_
      rw [state_tick, (good_tick (4 * s + 2)).ac.pool s,
        ite_pos ⟨by omega, by unfold tip; omega⟩]
      exact List.mem_singleton_self _
  · exact absurd ⟨ℓ', Compose.projAC_callAt.1 hc', hrs⟩ (tickRun_no_restart v0 k)

/-- The block `blk s` is stamped before `t_s + 2Δ` at the update: the validator accepted it at
`t_s` (cut `8 · 4s + 3`, `ac_on_block` of its own block). -/
theorem blockStamp_lt {s : Nat} (hs : 1 ≤ s) :
    ((tickRun N1 dg1).projAC.state v0 (8 * (4 * s + 6))).blockStamp (blk s).root <
      ETime.of (sp1.ts s + 2 * sp1.Δ) := by
  obtain ⟨f, hfs, hf⟩ := update_frame s
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  obtain ⟨fg', e, hl, -⟩ := vote_label k
  refine blockStamp_lt_of_acceptedBefore sp1 acRun.localRun (Set.mem_univ v0) (update_callAt _)
    (hf.mem hfs (by omega)) (Or.inr ⟨8 * (4 * (k + 1)) + 3,
      ⟨_, Compose.projAC_callAt.2 ⟨rfl, hl⟩, rfl⟩, ?_⟩)
    (fun j _ ⟨ℓ, hc, hr⟩ => absurd ⟨ℓ, Compose.projAC_callAt.1 hc, hr⟩ (tickRun_no_restart v0 j))
    (Or.inl ?_)
  · rw [time_eq, ts_nat]
    change (((8 * (4 * (k + 1)) + 3) / 8 : Nat) : Int) < 4 * ((k + 1 : Nat) : Int) + 2 * 1
    omega
  · rw [update_time, ts_nat]
    change 4 * ((k + 1 : Nat) : Int) + 2 * 1 ≤ ((4 * (k + 1) + 6 : Nat) : Int)
    omega

/-- The vote `cv s` is resolved before `t_s + 2Δ` at the update. -/
theorem resolutionTime_update {s : Nat} (hs : 1 ≤ s) :
    resolutionTime ((tickRun N1 dg1).projAC.state v0 (8 * (4 * s + 6)))
      (Node.frame (tickState N1 dg1 (4 * s + 6))) (cv s) < ETime.of (sp1.ts s + 2 * sp1.Δ) := by
  obtain ⟨f, hfs, hf⟩ := update_frame s
  unfold resolutionTime
  rw [show (cv s).head = (blk s).root from rfl, hf.lookup_blk hfs (by omega)]
  dsimp only
  rw [ite_neg (by rw [blk_slot]; exact lt_irrefl s)]
  exact max_lt (voteStamp_lt (by rw [update_pool_eq]; exact List.mem_singleton_self _))
    (blockStamp_lt hs)

/-! ## The confirmation and the fast test -/

/-- A set of validators that holds `v0` has one element. -/
theorem ncard_of_v0 {S : Set (Fin sp1.n)} (h : v0 ∈ S) : S.ncard = 1 := by
  have hS : S = Set.univ := Set.eq_univ_of_forall fun y => by rw [eq_v0 rfl y]; exact h
  rw [hS, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- A vote set of copies of one vote has no equivocator. -/
theorem not_equivocator {S : Set (Vote sp1.n)} {w : Vote sp1.n} (hS : ∀ v ∈ S, v = w)
    (y : Fin sp1.n) : y ∉ equivocators S := by
  rintro ⟨x, hx, z, hz, hne, -, -⟩
  exact hne ((hS x hx).trans (hS z hz).symm)

/-- With every slot-`s` pool vote `cv s`, a block of positive score is an ancestor of `blk s`. -/
theorem ancR_of_score {Φ : N1.Frm} {A : SAState sp1.n} {s : Nat}
    (hpool : ∀ v ∈ A.pool s, v = cv s) {B : N1.Blk} (h : confirmationScore sp1 A Φ s B ≠ 0) :
    AncR Φ B (blk s).root := by
  unfold confirmationScore at h
  dsimp only at h
  obtain ⟨-, -, x, hx, -, -, hanc⟩ := Set.nonempty_of_ncard_ne_zero h
  rw [hpool x hx.1] at hanc
  exact hanc

/-- The score of an ancestor of `blk s` at the update of slot `s` is `1`: `cv s` is early
support, and nobody equivocates. -/
theorem score_update {s : Nat} (hs : 1 ≤ s) {X : N1.Blk}
    (hX : AncR (Node.frame (tickState N1 dg1 (4 * s + 6))) X (blk s).root) :
    confirmationScore sp1 ((tickRun N1 dg1).projAC.state v0 (8 * (4 * s + 6)))
      (Node.frame (tickState N1 dg1 (4 * s + 6))) s X = 1 := by
  unfold confirmationScore
  dsimp only
  refine ncard_of_v0 ⟨not_equivocator (update_pool_cv s) v0, cv s,
    ⟨?_, resolutionTime_update hs⟩, rfl, rfl, hX⟩
  rw [update_pool_eq]
  exact List.mem_singleton_self _

theorem voters_update (s : Nat) :
    (voters {v | v ∈ ((tickRun N1 dg1).projAC.state v0 (8 * (4 * s + 6))).pool s}).ncard = 1 :=
  ncard_of_v0 ⟨cv s, by rw [Set.mem_ofPred_eq, update_pool_eq]; exact List.mem_singleton_self _,
    rfl⟩

/-- (a) **The result of the update of slot `s` is `blk s`**, the head of the only vote `cv s`:
one voter, and `blk s` and its ancestors have score `1`, `1 < 2 · 1`. -/
theorem getConfirmation_update {s : Nat} (hs : 1 ≤ s) :
    getConfirmation sp1 ((tickRun N1 dg1).projAC.state v0 (8 * (4 * s + 6)))
      (Node.frame (tickState N1 dg1 (4 * s + 6))) s = some (blk s) := by
  obtain ⟨f, hfs, hf⟩ := update_frame s
  unfold getConfirmation
  refine hf.deepest_eq (fun B hB => hB.1) ⟨hf.mem hfs (by omega), ?_, ?_⟩ fun B hB => ?_
  · rw [hf.F]; exact hf.anc le_rfl hfs (by omega)
  · rw [voters_update, score_update hs ⟨blk s, hf.mem hfs (by omega), rfl,
      Relation.ReflTransGen.refl⟩]
    decide
  · have hlt := hB.2.2
    rw [voters_update] at hlt
    exact ancR_blk_le hf (ancR_of_score (update_pool_cv s) (by omega))

/-- (a) **No live lock vetoes a block of the frame of the update**: every live lock block is a
frame block, and the frame is one chain. So the veto filter of the path is the identity. -/
theorem notConflicts_update (s : Nat) {X : N1.Blk}
    (hX : X ∈ (Node.frame (tickState N1 dg1 (4 * s + 6))).tree) :
    ¬ conflictsWithLock sp1 ((tickRun N1 dg1).projAC.state v0 (8 * (4 * s + 6))).locks
      (Node.frame (tickState N1 dg1 (4 * s + 6))) ((tickRun N1 dg1).projAC.time (8 * (4 * s + 6)))
      X := by
  obtain ⟨f, -, hf⟩ := update_frame s
  rintro ⟨B, hB, hnc⟩
  exact hnc (compatible_chain hf hX hB.1)

/-- (a) **The fast test of the update of slot `s` passes on `blk s`**: `n = 1 ≤ 2 · 1`. -/
theorem fastTest_update {s : Nat} (hs : 1 ≤ s) :
    FastTest sp1 ((tickRun N1 dg1).projAC.state v0 (8 * (4 * s + 6)))
      (Node.frame (tickState N1 dg1 (4 * s + 6))) s (blk s) := by
  obtain ⟨f, hfs, hf⟩ := update_frame s
  unfold FastTest
  rw [score_update hs ⟨blk s, hf.mem hfs (by omega), rfl, Relation.ReflTransGen.refl⟩]
  decide

/-- (a) **The fast test selects `blk s`**: the deepest block of the path of the result `blk s`
that no live lock vetoes and that passes the fast test. -/
theorem fastSelect_update {s : Nat} (hs : 1 ≤ s) :
    deepest (Node.frame (tickState N1 dg1 (4 * s + 6)))
      {X | X ∈ confirmationPath sp1 (Node.frame (tickState N1 dg1 (4 * s + 6))) (blk s) ∧
        ¬ conflictsWithLock sp1 ((tickRun N1 dg1).projAC.state v0 (8 * (4 * s + 6))).locks
          (Node.frame (tickState N1 dg1 (4 * s + 6)))
          ((tickRun N1 dg1).projAC.time (8 * (4 * s + 6))) X ∧
        FastTest sp1 ((tickRun N1 dg1).projAC.state v0 (8 * (4 * s + 6)))
          (Node.frame (tickState N1 dg1 (4 * s + 6))) s X} = some (blk s) := by
  obtain ⟨f, hfs, hf⟩ := update_frame s
  have hmem := hf.mem hfs (by omega : s ≤ s + 1)
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  refine hf.deepest_eq (fun B hB => hB.1.1) ⟨⟨hmem, blk_root_succ_ne k,
    Relation.ReflTransGen.refl⟩, notConflicts_update _ hmem, fastTest_update hs⟩ fun B hB => ?_
  obtain ⟨b, hb, rfl, -⟩ := anc_blk_inv hf.onChain hB.1.2.2
  exact ⟨b, hb, rfl⟩

/-- (a) **The counted votes of the fast lock are `{cv s}`.** -/
theorem fastCounted_update {s : Nat} (hs : 1 ≤ s) :
    fastCounted sp1 ((tickRun N1 dg1).projAC.state v0 (8 * (4 * s + 6)))
      (Node.frame (tickState N1 dg1 (4 * s + 6))) s (blk s) = {cv s} := by
  obtain ⟨f, hfs, hf⟩ := update_frame s
  ext v
  constructor
  · rintro ⟨hv, -⟩
    exact update_pool_cv s v hv
  · rintro rfl
    refine ⟨?_, not_equivocator (update_pool_cv s) _, resolutionTime_update hs, blk s,
      hf.mem hfs (by omega), rfl, Relation.ReflTransGen.refl⟩
    rw [update_pool_eq]
    exact List.mem_singleton_self _

/-! ## The fast lock of the update -/

/-- (a) **`FastUpdateAt` on the tick run**: for every slot `s ≥ 1`, the update of slot `s` at
cut `8 · (4s + 6)` (label `⟨tick, Φ, []⟩`) has the result `blk s`, its fast test selects `blk s`
(no live lock vetoes it), and it counts `{cv s}`. -/
theorem fastUpdate_tickRun {s : Nat} (hs : 1 ≤ s) :
    FastUpdateAt (tickRun N1 dg1).projAC v0 (8 * (4 * s + 6)) s (blk s) {cv s} :=
  ⟨_, blk s, updateAt_tickRun s, getConfirmation_update hs, fastSelect_update hs,
    (fastCounted_update hs).symm⟩

/-- (a) `FastUpdateAt` at slot `1`: the update at `t_1 + 6Δ = 10`, cut `80`. -/
theorem fastUpdate_slot_one : FastUpdateAt (tickRun N1 dg1).projAC v0 80 1 (blk 1) {cv 1} := by
  rw [show 80 = 8 * (4 * 1 + 6) from rfl]
  exact fastUpdate_tickRun le_rfl

/-- (a) **`FastLockAt` by the update origin** (`Or.inl`), as A1.2 and A1.9 consume it. -/
theorem fastLockAt_update {s : Nat} (hs : 1 ≤ s) :
    FastLockAt (tickRun N1 dg1).projAC v0 (8 * (4 * s + 6)) s (blk s) {cv s} :=
  Or.inl (fastUpdate_tickRun hs)

open Classical in
/-- The locks after an update of slot `s` with result `C` whose fast test selects `D`: `add_locks`
of the stored locks with new entries, among them the fast entry on `D` with expiry `s + 2`. -/
theorem updateConfirmation_fastEntry {A : SAState sp1.n} {Φ : N1.Frm} {t : Time} {s : Nat}
    {C D : N1.Blk} (hC : getConfirmation sp1 A Φ s = some C)
    (hD : deepest Φ {X | X ∈ confirmationPath sp1 Φ C ∧ ¬ conflictsWithLock sp1 A.locks Φ t X ∧
      FastTest sp1 A Φ s X} = some D) :
    ∃ N : Set (Nat × Bool × Nat), (D.root, true, s + 2) ∈ N ∧
      (updateConfirmation sp1 A Φ t s).locks = addLocks sp1 A.locks Φ t s N := by
  have hD' : deepest Φ {X | (X ∈ confirmationPath sp1 Φ C ∧
      ¬ conflictsWithLock sp1 A.locks Φ t X) ∧ FastTest sp1 A Φ s X} = some D := by
    rw [← hD]; congr 1; ext X; exact and_assoc
  unfold updateConfirmation
  simp only [hC]
  split_ifs
  · refine ⟨_, ?_, rfl⟩
    exact Or.inl ⟨D, hD', by rw [fastExpiry_eq]⟩
  · unfold updateLatestConfirmed
    split_ifs <;> refine ⟨_, ?_, rfl⟩ <;> exact Or.inl ⟨D, hD', by rw [fastExpiry_eq]⟩

/-- The post-state of the update cut is the update of slot `s`. -/
theorem update_post (s : Nat) :
    (tickRun N1 dg1).projAC.state v0 (8 * (4 * s + 6) + 1) =
      updateConfirmation sp1 ((tickRun N1 dg1).projAC.state v0 (8 * (4 * s + 6)))
        (Node.frame (tickState N1 dg1 (4 * s + 6)))
        ((tickRun N1 dg1).projAC.time (8 * (4 * s + 6))) s := by
  rw [projAC_state', projAC_state', state_eq (8 * (4 * s + 6) + 1), state_tick, update_time,
    show (8 * (4 * s + 6) + 1) / 8 = 4 * s + 6 by omega,
    show (8 * (4 * s + 6) + 1) % 8 = 1 by omega, tickMid_one]
  change (acOnTick sp1 v0 (tickState N1 dg1 (4 * s + 6)).ac
    (Node.frame (tickState N1 dg1 (4 * s + 6))) ((4 * s + 6 : Nat) : Int)).1 = _
  rw [acOnTick_eq _ _ _ (good_tick _).ac.restart, ite_pos ⟨by omega, by omega⟩,
    show (4 * s + 6) / 4 - 1 = s by omega]

/-- (a) **The update writes the fast lock on `blk s` with expiry `s + 2`**: the post-state
locks of the update cut are `add_locks` of the stored locks with new entries that hold
`((blk s).root, true, s + 2)` (`fastExpiry = s + 2` at `k = c = 2`), and the post-state holds
`⟨(blk s).root, s, true, s + 2⟩` (live at `slot(4s + 6) = s + 1`, on a frame block). -/
theorem update_writes_fastLock {s : Nat} (hs : 1 ≤ s) :
    (∃ N : Set (Nat × Bool × Nat), ((blk s).root, true, s + 2) ∈ N ∧
      ((tickRun N1 dg1).projAC.state v0 (8 * (4 * s + 6) + 1)).locks =
        addLocks sp1 ((tickRun N1 dg1).projAC.state v0 (8 * (4 * s + 6))).locks
          (Node.frame (tickState N1 dg1 (4 * s + 6)))
          ((tickRun N1 dg1).projAC.time (8 * (4 * s + 6))) s N) ∧
    (⟨(blk s).root, s, true, s + 2⟩ : Lock) ∈
      ((tickRun N1 dg1).projAC.state v0 (8 * (4 * s + 6) + 1)).locks := by
  obtain ⟨f, hfs, hf⟩ := update_frame s
  obtain ⟨N, hN, hL⟩ :=
    updateConfirmation_fastEntry (getConfirmation_update hs) (fastSelect_update hs)
  rw [update_post]
  refine ⟨⟨N, hN, hL⟩, ?_⟩
  rw [hL]
  refine hf.mem_liveLocks (Or.inr ⟨_, hN, rfl⟩) hfs (by omega) rfl ?_
  rw [update_time, slot_nat]
  change (4 * s + 6) / 4 ≤ s + 2
  omega

/-! ## The premises of A1.2 at the update's fast lock -/

/-- `f < h_t` on the AC projection at every time `t ≥ 0`. -/
theorem tickRun_faultBound_proj {t : Time} (ht : 0 ≤ t) :
    SA.FaultBound (tickRun N1 dg1).projAC Set.univ t := by
  unfold SA.FaultBound
  rw [← (Compose.joined_projection sp1 ro1 dg1 Set.univ (tickRun N1 dg1) (fun _ => v0)
    tickRun_goldilocksRun v0 (Set.mem_univ _) t).2.2]
  exact tickRun_faultBound ht

/-- (a) **The premises of A1.2 (`FirstTransfer`) hold at the update's fast lock**: the fast lock
of slot `s ≥ 1` on `blk s` written by the update at cut `8 · (4s + 6)` (`FastLockAt` by the
update origin), counting `{cv s}`, and the validator's slot-`(s + 1)` vote at cut
`8 · t_{s+1} + 3` (`ac_on_block` of its own block): `Sync[t_s, t_{s+1}]`, `Carry`, `f < h_τ`,
`blk s` in the viable voter block tree at the vote, and no earlier honest slot-`(s + 1)` vote.
The vote's cut precedes the update's (`t_{s+1} < t_s + 6Δ`): A1.2 does not order them. -/
theorem firstTransfer_premises_update {s : Nat} (hs : 1 ≤ s) :
    ∃ (ℓ : ACLabel N1) (e : N1.Em),
      SA.ACRun (fun _ => v0) (tickRun N1 dg1).projAC Set.univ
        ((tickRun N1 dg1).HonestBlocks Set.univ) ∧
      FastLockAt (tickRun N1 dg1).projAC v0 (8 * (4 * s + 6)) s (blk s) {cv s} ∧
      CastAt (tickRun N1 dg1).projAC v0 (8 * (4 * (s + 1)) + 3) ℓ e ∧ e.msg.slot = s + 1 ∧
      SyncAC N1 Set.univ ((tickRun N1 dg1).HonestBlocks Set.univ) (sp1.ts s)
        ((tickRun N1 dg1).projAC.time (8 * (4 * (s + 1)) + 3)) (tickRun N1 dg1).projAC ∧
      CarryAt (tickRun N1 dg1).projAC ((tickRun N1 dg1).HonestBlocks Set.univ) v0
        (8 * (4 * (s + 1)) + 3) e s {cv s} ∧
      SA.FaultBound (tickRun N1 dg1).projAC Set.univ
        ((tickRun N1 dg1).projAC.time (8 * (4 * (s + 1)) + 3)) ∧
      ViableAtVote ℓ e (s + 1) (blk s) ∧
      EarlierVotesExtend (tickRun N1 dg1).projAC Set.univ ((tickRun N1 dg1).HonestBlocks Set.univ)
        (8 * (4 * (s + 1)) + 3) (s + 1) (blk s) := by
  obtain ⟨fg', e, hl, hfg', hm, -⟩ := vote_label s
  obtain ⟨f, hf⟩ := fgGood_frame hfg'
  have hfs : f ≤ s := le_trans hf.fj (jexp_succ_le s)
  have hc : (tickRun N1 dg1).projAC.CallAt v0 (8 * (4 * (s + 1)) + 3)
      ⟨.block (blk (s + 1)), fg'.toFrame, [e]⟩ := Compose.projAC_callAt.2 ⟨rfl, hl⟩
  have hcast : CastAt (tickRun N1 dg1).projAC v0 (8 * (4 * (s + 1)) + 3)
      ⟨.block (blk (s + 1)), fg'.toFrame, [e]⟩ e := ⟨hc, List.mem_singleton_self _⟩
  have hslot : e.msg.slot = s + 1 := by rw [hm]; rfl
  refine ⟨_, e, acRun, fastLockAt_update hs, hcast, hslot,
    Compose.sync_projection _ _ _ _ _ _ _ _ _ _ tickRun_goldilocksRun.toLocalRun
      (tickRun_syncOn _ _ id fun _ => le_rfl),
    carry_cv s (fun v hv => hv) v0 (Set.mem_univ _) _ e ⟨_, hcast⟩ hslot,
    tickRun_faultBound_proj (by rw [time_eq]; positivity), ?_, ?_⟩
  · exact Or.inl (hf.mem_viableTree (mem_voterBlockTree hf _ (by omega) le_rfl)
      (jexp_succ_le s) (by omega) (mem_voterBlockTree hf _ hfs (by omega)))
  · rintro x - j hj e' ⟨ℓ', hc', he'⟩ hs'
    obtain ⟨-, -, hl'⟩ := projAC_call hc'
    rcases emit_cases hl' he' with ⟨-, hm', -⟩ | ⟨k, -, rfl, -, -, -, hm', -⟩
    · rw [hm'] at hs'
      exact absurd hs' (by change 0 ≠ s + 1; omega)
    · rw [hm'] at hs'
      change k + 1 = s + 1 at hs'
      omega

/-- The bundle fits A1.2 as stated: `FirstTransfer` applies to it, and gives that the
slot-`(s + 1)` vote extends `blk s` inside the honest blocks. -/
theorem firstTransfer_update (hA : FirstTransfer sp1) {s : Nat} (hs : 1 ≤ s) :
    ∃ (ℓ : ACLabel N1) (e : N1.Em),
      CastAt (tickRun N1 dg1).projAC v0 (8 * (4 * (s + 1)) + 3) ℓ e ∧
      VoteExtends ((tickRun N1 dg1).HonestBlocks Set.univ) e.msg (blk s) := by
  obtain ⟨ℓ, e, hr, hfl, hc, hsl, hsy, hca, hfb, hv, hea⟩ := firstTransfer_premises_update hs
  exact ⟨ℓ, e, hc, hA _ ro1 Set.univ _ _ (fun _ => v0) hr s v0 v0 _ _ (blk s) {cv s} ℓ e
    (Set.mem_univ _) hfl (Set.mem_univ _) hc hsl hsy hca hfb hv hea⟩

end Consensus.Goldilocks.Witness.One

end

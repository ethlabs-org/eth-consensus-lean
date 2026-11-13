module
public import ConsensusLeanTest.Goldilocks.Runs.OneValidator.Run
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission
@[expose] public section

/-! # The one-validator tick run meets the premises of C1.1 and of the Service statements

Kind (a), joint satisfiability (CONTRIBUTING "Statements"), on the one-validator tick run of
`Goldilocks/Runs/OneValidator/Premises` (`n = 1`, `Δ = 1`, `t_s = 4s`, a tick at every time, no
restart):

* `persistPremises_tickRun`: Compose `PersistPremises` (the premises of C1.1,
  `HonestFastConfirmationsPersist`, and of `RecentSourceNextVote`) for the optimistic fast lock
  of slot `1` on `blk 1` that the validator writes when it admits its own vote at `t_1` (cut
  `35`, `ac_on_block` of its own block), with counted votes `{cv 1}` and `m = 2`. Every field
  holds outright: `Sync[t_1, t_2 + Δ]`, `Clean(1, 2, blk 1)` (honest caches and heights on the
  chain; no excluded entry, since every honest block is a chain block), half the committee
  votes, `f < h_t`, `NoColl`.
  - **`Carry`** (`carry_cv`, every slot): the vote of slot `s + 1` is cast in `ac_on_block` of
    the own block at `t_{s+1}`, when the validator has accepted `blk s` and its ancestors (at
    their slot starts) and holds `cv s` with a stamp before `t_s + 3Δ`. The stamp is traced
    through `SA.readPoint_pool` and `SA.pool_origin`: it is the time of the cut that sent or
    admitted `cv s`, and that cut is before the tick of `t_s + 2Δ`, whose pool already holds
    `cv s` (`readPoint_stamp`).
* `tickRun_sleepy`: `SleepyRun` (`Sync[0, ∞)` and `f < h_t` at every `t_s, t_s + Δ,
  t_s + 2Δ`), and `servedAt_tickRun`: A1.6's `ServedAt` at the tick of time `8` (slot `2`),
  after the update of slot `0` at `t_0 + 6Δ = 6`. `tickRun_service_premises` bundles them with
  `GoldilocksRun` and `NoColl`: the premises of `HeadExtendsRecord` are jointly satisfiable.

With `n = 1` and `f = 0` this shows the premises consistent, not met with faults. -/

namespace Consensus.Goldilocks.Witness.One

open SA Node ChainFrame

/-! ## Chain facts of the honest blocks -/

/-- Every honest block of the run is a chain block. -/
theorem honest_onChain : OnChain ((tickRun N1 dg1).HonestBlocks Set.univ) := by
  rintro B ⟨y, -, i, hB⟩
  obtain rfl := eq_v0 rfl y
  obtain ⟨m, -, rfl⟩ := (mem_tree_iff (state_fgGood i).blocks).1 hB
  exact ⟨m, rfl⟩

/-- A descendant of a chain block inside the honest blocks is a chain block. -/
theorem anc_eq_blk {a : Nat} {X : N1.Blk}
    (h : Anc ((tickRun N1 dg1).HonestBlocks Set.univ) (blk a) X) : ∃ b, X = blk b := by
  rcases Relation.ReflTransGen.cases_tail h with rfl | ⟨Y, -, hY⟩
  · exact ⟨a, rfl⟩
  · exact honest_onChain X hY.2.1

/-- Two chain blocks are compatible inside the honest blocks. -/
theorem compatible_blk (a b : Nat) :
    Compatible ((tickRun N1 dg1).HonestBlocks Set.univ) (blk a) (blk b) :=
  (le_total a b).elim (fun h => Or.inl (anc_honest h)) (fun h => Or.inr (anc_honest h))

/-! ## The vote cuts -/

/-- The `ac_on_block` cut of the own block of slot `k + 1`, which casts `cv (k + 1)`. -/
theorem vote_label (k : Nat) : ∃ (fg' : Store sp1.toParams N1.Payload) (e : N1.Em),
    (tickRun N1 dg1).label (8 * (4 * (k + 1)) + 3) =
      some (.ac ⟨.block (blk (k + 1)), fg'.toFrame, [e]⟩) ∧ FGGood fg' (k + 1) ∧
    e.msg = cv (k + 1) ∧ e.readPoint.pool = (tickState N1 dg1 (4 * (k + 1))).ac.pool := by
  obtain ⟨fg', e, -, hfg', he, hm, hp⟩ := tickCuts_A k
  refine ⟨fg', e, ?_, hfg', hm, hp⟩
  rw [tickRun_label, show (8 * (4 * (k + 1)) + 3) / 8 = 4 * (k + 1) by omega,
    show (8 * (4 * (k + 1)) + 3) % 8 = 3 by omega, he]
  rfl

/-- The AC projection of the tick run is an AC run. -/
theorem acRun : SA.ACRun (fun _ => v0) (tickRun N1 dg1).projAC Set.univ
    ((tickRun N1 dg1).HonestBlocks Set.univ) :=
  Compose.goldilocks_ac_projection sp1 ro1 dg1 Set.univ (tickRun N1 dg1) (fun _ => v0)
    tickRun_goldilocksRun (dg1_noColl _)

theorem etime_of_lt {a b : Time} (h : a < b) : ETime.of a < ETime.of b :=
  WithBot.coe_lt_coe.2 (WithTop.coe_lt_coe.2 h)

/-- **The stamp of a held vote at a later vote.** At the vote of cut `i`, the vote `cv s` that
the read point holds was received before `t_s + 3Δ`: its stamp is the time of the cut that sent
or admitted it, before the tick of `t_s + 2Δ` (whose pool already holds it). -/
theorem readPoint_stamp {s i : Nat} {ℓ : ACLabel N1} {e : N1.Em}
    (hc : SA.CastAt (tickRun N1 dg1).projAC v0 i ℓ e) (hx : cv s ∈ e.readPoint.pool s) :
    e.readPoint.voteStamp (cv s) < ETime.of (sp1.ts s + 3 * sp1.Δ) := by
  have hr := acRun.localRun
  obtain ⟨hpool, hst⟩ := SA.readPoint_pool hr (Set.mem_univ v0) hc hx
  rw [← hst rfl]
  rcases SA.pool_origin hr (Set.mem_univ v0) (i + 1) (cv s) hpool with
    ⟨k, -, ⟨ℓ', hc', hk⟩, hstk, -⟩ | ⟨k, -, ℓ', hc', hrs, -⟩
  · rw [hstk]
    apply etime_of_lt
    suffices hlt : k < 8 * (4 * s + 2) by
      rw [time_eq, ts_nat]
      change (((k / 8 : Nat)) : Int) < 4 * (s : Int) + 3 * 1
      omega
    obtain ⟨-, -, hl⟩ := projAC_call hc'
    rcases hk with ⟨e', he', hm⟩ | ⟨-, hnot, -⟩
    · rcases emit_cases hl he' with ⟨rfl, hm', -⟩ | ⟨k', fg', rfl, -, -, -, hm', -⟩
      · have : s = 0 := by have := congrArg Vote.slot (hm'.symm.trans hm); exact this.symm
        omega
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

/-- **`Carry(s, S, B)` holds on the tick run**, for every slot `s` and counted votes inside
`{cv s}`: at the vote of slot `s + 1` (cut `8·t_{s+1} + 3`) the validator is awake and joined,
has accepted `blk s` and its ancestors before `t_s + 3Δ`, and holds `cv s`, received before
`t_s + 3Δ`. -/
theorem carry_cv (s : Nat) {CV : Set (Vote sp1.n)} (hCV : ∀ v ∈ CV, v = cv s) :
    SA.Carry (tickRun N1 dg1).projAC Set.univ ((tickRun N1 dg1).HonestBlocks Set.univ) s CV := by
  rintro y - i e ⟨ℓ, hc, he⟩ hslot
  obtain ⟨rfl, -, hl⟩ := projAC_call hc
  have hcast : SA.CastAt (tickRun N1 dg1).projAC v0 i ℓ e := ⟨hc, he⟩
  rcases emit_cases hl he with ⟨-, hm, -⟩ | ⟨k, fg', -, -, -, -, hm, hp⟩
  · rw [hm] at hslot
    change 0 = s + 1 at hslot
    omega
  have hks : k = s := by
    rw [hm] at hslot
    change k + 1 = s + 1 at hslot
    omega
  subst hks
  have hx : cv k ∈ e.readPoint.pool k := by
    rw [hp, (good_tick (4 * (k + 1))).ac.pool k, tip_A, ite_pos ⟨by omega, le_rfl⟩]
    exact List.mem_singleton_self _
  refine ⟨?_, (SA.castAt_spec acRun.localRun (Set.mem_univ v0) hcast).2.2.1, ?_, ?_⟩
  · change (0 : Int) ≤ ((i / 8 : Nat) : Int)
    positivity
  · intro v hv
    obtain rfl := hCV v hv
    refine ⟨blk k, blk_mem_honest k, rfl, fun X hX => ?_⟩
    obtain ⟨a, ha, rfl, -⟩ := anc_blk_inv honest_onChain hX
    rcases a with _ | a
    · exact Or.inl blk_root_zero
    · obtain ⟨fg'', e'', hl'', -⟩ := vote_label a
      refine Or.inr ⟨8 * (4 * (a + 1)) + 3, ⟨_, Compose.projAC_callAt.2 ⟨rfl, hl''⟩, rfl⟩, ?_⟩
      rw [time_eq, ts_nat]
      change (((8 * (4 * (a + 1)) + 3) / 8 : Nat) : Int) < 4 * (k : Int) + 3 * 1
      omega
  · intro v hv
    obtain rfl := hCV v hv
    exact Or.inl ⟨hx, readPoint_stamp hcast hx⟩

/-- The honest votes of slot `σ` are `cv σ`. -/
theorem honestVotes_cv (σ : Nat) :
    ∀ v ∈ Compose.honestVotes (tickRun N1 dg1) Set.univ σ, v = cv σ := by
  rintro v ⟨x, -, j, e', ⟨ℓ, hc, he⟩, rfl, hsl⟩
  obtain ⟨rfl, -, hl⟩ := projAC_call hc
  rcases emit_cases hl he with ⟨-, hm, -⟩ | ⟨k, -, -, -, -, -, hm, -⟩ <;>
    rw [hm] at hsl ⊢ <;> subst hsl <;> rfl

/-- `f < h_t` at every time `t ≥ 0` (no faulty validator, the validator awake and joined). -/
theorem tickRun_faultBound {t : Time} (ht : 0 ≤ t) :
    (tickRun N1 dg1).FaultBound Set.univ t := by
  unfold RunTrace.FaultBound RunTrace.honestAwakeJoined
  have : {y | y ∈ (Set.univ : Set (Fin sp1.n)) ∧ (tickRun N1 dg1).awake y t ∧
      (tickRun N1 dg1).JoinedAt y t} = Set.univ := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_univ, true_and, iff_true]
    exact ⟨ht, fun k hk => absurd hk (tickRun_no_restart _ k)⟩
  rw [this, Set.compl_univ, Set.ncard_empty, Set.ncard_univ]
  simp

/-! ## The premises of C1.1 -/

/-- **`PersistPremises` holds on the tick run** (the premises of C1.1 and of
`RecentSourceNextVote`): the optimistic fast lock of slot `1` on `blk 1` written at cut `35`
(the admission of the own vote of slot `1` in `ac_on_block` at `t_1 = 4`), counting `{cv 1}`,
with `m = 2` and `Δ_F = 1`. -/
theorem persistPremises_tickRun :
    Compose.PersistPremises (tickRun N1 dg1) Set.univ dg1 1 v0 35 1 2 (blk 1) {cv 1} := by
  have hrun := tickRun_goldilocksRun
  refine ⟨Set.mem_univ _, ?_, ?_, by decide, tickRun_syncOn _ _ id (fun _ => le_rfl),
    carry_cv 1 (fun v hv => hv), ?_, fun s' _ _ => carry_cv s' (honestVotes_cv s'), ?_,
    dg1_noColl _, ?_, rfl⟩
  · -- the optimistic fast lock at the admission of the own vote of slot `1`
    obtain ⟨fg', e, hl, hfg', hm, hp⟩ := vote_label 0
    obtain ⟨f, hf⟩ := fgGood_frame hfg'
    have hf0 : f = 0 := by have := hf.fj; simp [jexp] at this; omega
    subst hf0
    have hc : (tickRun N1 dg1).projAC.CallAt v0 35 ⟨.block (blk 1), fg'.toFrame, [e]⟩ :=
      Compose.projAC_callAt.2 ⟨rfl, hl⟩
    have hj : SA.joined sp1 e.readPoint (((4 : Nat) : Int)) :=
      (SA.castAt_spec acRun.localRun (Set.mem_univ v0) (ℓ := ⟨.block (blk 1), fg'.toFrame, [e]⟩)
        ⟨hc, List.mem_singleton_self _⟩).2.2.1
    have hpool0 : e.readPoint.pool 1 = [] := by
      rw [hp, (good_tick (4 * (0 + 1))).ac.pool 1, tip_A, ite_neg (by omega)]
    have hst : sp1.slot (((4 : Nat) : Int)) = 1 := by rw [slot_nat]
    have hadm := admitVote_cv (t := ((4 : Nat) : Int)) hst hpool0
    have hsel : optimisticSelect sp1 (admitVote sp1 e.readPoint ((4 : Nat) : Int) (cv 1))
        fg'.toFrame ((4 : Nat) : Int) = some (blk 1) := by
      rw [hadm]
      exact optimisticSelect_vote hf le_rfl hst (by rw [ts_nat, delta1]; norm_num) hj
        (by simp)
    refine ⟨⟨.block (blk 1), fg'.toFrame, [e]⟩, blk 1, hc, Or.inr ⟨_, _,
      ⟨hc, Or.inr (Or.inr ⟨e, List.mem_singleton_self _, rfl⟩)⟩, hst, ?_, ?_⟩,
      (hf.viableAncestor_eq (by omega) le_rfl).symm⟩
    · change optimisticSelect sp1 (admitVote sp1 e.readPoint ((4 : Nat) : Int) e.msg)
        fg'.toFrame ((4 : Nat) : Int) = some (blk 1)
      rw [hm]
      exact hsel
    · change {cv 1} = {v | v ∈ (admitVote sp1 e.readPoint ((4 : Nat) : Int) e.msg).pool 1 ∧
        AncR fg'.toFrame (blk 1) v.head}
      rw [hm]
      change {cv 1} = {v | v ∈ (admitVote sp1 e.readPoint ((4 : Nat) : Int) (cv 1)).pool 1 ∧
        AncR fg'.toFrame (blk 1) v.head}
      rw [hadm]
      ext v
      simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq, Function.update_self,
        List.mem_singleton]
      constructor
      · rintro rfl
        exact ⟨rfl, blk 1, hf.mem (by omega) le_rfl, rfl, Relation.ReflTransGen.refl⟩
      · exact fun h => h.1
  · -- the writer is joined
    exact joined_of_bot (tickRun_restartTime 35) _
  · -- half of the committee votes in slot `2`
    intro s' h1 h2
    obtain rfl : s' = 2 := by omega
    obtain ⟨fg', e, hl, -, hm, -⟩ := vote_label 1
    have hmem : v0 ∈ {x' | x' ∈ (Set.univ : Set (Fin sp1.n)) ∧ ∃ j e',
        SA.VoteAt (tickRun N1 dg1).projAC x' j e' ∧ e'.msg.slot = 2} :=
      ⟨Set.mem_univ _, _, e, ⟨_, Compose.projAC_callAt.2 ⟨rfl, hl⟩, List.mem_singleton_self _⟩,
        by rw [hm]; rfl⟩
    have := (Set.ncard_pos (Set.toFinite _)).2 ⟨v0, hmem⟩
    change 1 ≤ 2 * _
    omega
  · -- `f < h_t` at the honest votes
    intro y _ i e _ _ _
    exact tickRun_faultBound (by change (0 : Int) ≤ ((i / 8 : Nat) : Int); positivity)
  · -- `Clean(1, 2, blk 1)`
    refine ⟨fun y _ j _ => ?_, fun E' hE' => ?_, fun y _ i ℓ e hcast hs hsm => ?_⟩
    · obtain rfl := eq_v0 rfl y
      have hg := state_fgGood j
      obtain ⟨f, -, hF⟩ := hg.F
      rw [hF, hg.J]
      exact ⟨compatible_blk _ _, compatible_blk _ _⟩
    · exfalso
      obtain ⟨hnc, y, -, j, -, hanc, -⟩ := hE'
      obtain rfl := eq_v0 rfl y
      obtain ⟨f, -, hF⟩ := (state_fgGood j).F
      rw [hF] at hanc
      obtain ⟨b, rfl⟩ := anc_eq_blk hanc
      exact hnc (compatible_blk b 1)
    · obtain ⟨hc, he⟩ := hcast
      obtain ⟨rfl, hfr, hl⟩ := projAC_call hc
      rcases emit_cases hl he with ⟨-, hm, -⟩ | ⟨k, fg', -, hfr', hfg', -, hm, -⟩
      · rw [hm] at hs; exact absurd hs (by decide)
      rw [hm] at hs hsm ⊢
      change 1 < k + 1 at hs
      change k + 1 ≤ 2 at hsm
      obtain rfl : k = 1 := by omega
      obtain ⟨f, hf⟩ := fgGood_frame hfg'
      have hf2 : f ≤ 2 := le_trans hf.fj (jexp_le _)
      left
      refine ⟨blk 2, ?_, anc_honest (by omega), ?_⟩
      · rw [hfr']
        exact mem_voterBlockTree hf e.readPoint hf2 le_rfl
      · have hh := hf.head_mem (m := 2) (jexp_le _) le_rfl
        rw [← hfr', hfr] at hh
        obtain ⟨-, -, -, hv⟩ := hh
        exact hv

/-- **The premises of C1.1 are jointly satisfiable**: the tick run is a Goldilocks run and meets
`PersistPremises` for the fast lock of slot `1` on `blk 1`. -/
theorem tickRun_persist_premises :
    GoldilocksRun (sp := sp1) (ro := ro1) (fun _ => v0) dg1 Set.univ (tickRun N1 dg1) ∧
      Compose.PersistPremises (tickRun N1 dg1) Set.univ dg1 1 v0 35 1 2 (blk 1) {cv 1} :=
  ⟨tickRun_goldilocksRun, persistPremises_tickRun⟩

/-! ## The premises of the Service statements -/

/-- (a) **`Sleepy` holds on the tick run** (with `Δ_F = 1`): `Sync[0, ∞)` and `f < h_t` at every
`t_s`, `t_s + Δ` and `t_s + 2Δ`. -/
theorem tickRun_sleepy : (tickRun N1 dg1).SleepyRun Set.univ 1 := by
  refine ⟨tickRun_syncOn _ _ id (fun _ => le_rfl), fun s =>
    ⟨tickRun_faultBound ?_, tickRun_faultBound ?_, tickRun_faultBound ?_⟩⟩
  · change (0 : Int) ≤ 4 * (s : Int); positivity
  · change (0 : Int) ≤ 4 * (s : Int) + 1; positivity
  · change (0 : Int) ≤ 4 * (s : Int) + 2 * 1; positivity

/-- A1.6's `ServedAt` at the tick of time `8` (cut `64`, slot `2`): a call of the validator, which
is joined and ran the update of slot `0` at the tick of `t_0 + 6Δ = 6` (cut `48`), with no restart
since. -/
theorem servedAt_tickRun : Compose.ServedAt (tickRun N1 dg1) v0 64 := by
  have hl : ∀ t : Nat, (tickRun N1 dg1).label (8 * t) =
      some (acCall v0 (tickState N1 dg1 t) (t : Int) .tick).2 := by
    intro t
    rw [tickRun_label, show 8 * t / 8 = t by omega, show 8 * t % 8 = 0 by omega]
    exact tickCuts_head N1 dg1 t
  refine ⟨⟨_, rfl, hl 8⟩, fun k hk => absurd hk (tickRun_no_restart _ k), 0,
    by rw [time_run, slot_nat], 48, by decide, _,
    ⟨Compose.projAC_callAt.2 ⟨rfl, hl 6⟩, rfl, ?_, ?_⟩, fun k' _ _ => tickRun_no_restart _ k'⟩
  · rw [time_eq, ts_nat]; rfl
  · rw [projAC_state']
    exact joined_of_bot (tickRun_restartTime 48) _

/-- **The premises of the Service statements are jointly satisfiable** (`HeadExtendsRecord`,
A1.6): a Goldilocks run with `NoColl` and `Sleepy`, and a cut where `ServedAt` holds. -/
theorem tickRun_service_premises :
    GoldilocksRun (sp := sp1) (ro := ro1) (fun _ => v0) dg1 Set.univ (tickRun N1 dg1) ∧
      Compose.NoCollRun dg1 (tickRun N1 dg1) ∧ (tickRun N1 dg1).SleepyRun Set.univ 1 ∧
      Compose.ServedAt (tickRun N1 dg1) v0 64 :=
  ⟨tickRun_goldilocksRun, dg1_noColl _, tickRun_sleepy, servedAt_tickRun⟩

end Consensus.Goldilocks.Witness.One

end

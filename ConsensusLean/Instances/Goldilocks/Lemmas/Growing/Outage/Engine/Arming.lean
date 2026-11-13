module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Engine.Query
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Schedule
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.State
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Engine.ArmingSteps
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Read
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Outage engine part under growing faults: an armed ready source

`OutageArmingAt Q v`: the read tip `P` of a source `v` ready at `T`, at the end-of-`T` cut, a held
origin `C ⪰ P` within `T` of a label `σ` more than `k` labels before the cover label `j₀`,
S-vote (every vote of a slot in `(σ, j₀]` by a node honest at its cast extends `C`), and O1 at the
labels `j₀ − 1` and `j₀` for the cohort `holdersAt` (O1 at `j₀` given (F), (VA) outside root
cover and (N), with (N) over the votes of the cohort cast while honest).

The cohort facts of the query, read on the view retained through `cohortAt = outageEnd = z`:
`holdersAt` and `lateKeysAt` are honest at `z` and disjoint, `|(H z)ᶜ ∪ W| < |A₀|`
(`cohort_lt`), a validator honest at `z` and awake in `[a, z]` is in `A₀ ∪ W` (`classify`), and
`A₀` is awake throughout `[a, z]` (`holder_awake`); `bounds` are the two count shapes through
every `b ≤ horizon`, from the η-sleepy premise.

`outage_arming_at`: every source ready at `T ≤ horizon` is armed. The Sleepy invariant up to
`min b₀ horizon` (from the pre-start service and the counts) gives the tip on the chain of the
origins within `T`, S-vote, and O1 at `j₀ − 1` (`armed_lock_formed_at`) and at `j₀`
(`armed_lock_cover_at`, with the opponents `(H z)ᶜ ∪ W`). -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation
open Blocks Shape
variable {S : BoundSetup} {A : ContractAssumptions S.toSetup} {V : Type} [Fintype V] [DecidableEq V]


namespace OutageQueryAt

/-- The two count shapes through every `b ≤ horizon`, from the η-sleepy premise (η-sleepy
implies sleepy, at half readiness, with look-ahead `5Δ`). -/
theorem bounds (Q : OutageQueryAt S A V)
    [Fact (S.vote.participationKind = none)] -- TEMP(C2)
    {b : Time} (hb : b ≤ Q.run.2.horizon) :
    Compose.Growing.SleepyBoundsFrom Q.trace Q.keys 0 b :=
  sleepy_bounds_at S Q.run.2 Q.hn Q.valid hb (fun t ht htb => by
    have h := (Q.outage.etaSleepy t ht (htb.trans hb)).readyAbove
      (by change (0 : ℚ) ≤ 1 / 2; norm_num)
    rw [Q.aheadDur_eq] at h
    exact half_ready_of_duration V _ (outage_duration_supply_at Q) h)
    (add_nonneg (Compose.Growing.ts_natCast_nonneg 0) Q.params.toParams.hΔ.le) (le_max_right _ _)

theorem end_le_horizon (Q : OutageQueryAt S A V) :
    (Sys (goldilocksWith S) V).outageEnd (K S.toSetup A) Q.stop Q.run ≤ Q.run.2.horizon :=
  min_le_right _ _

/-- A key is honest at the window end iff its validator is not compromised by the cohort time. -/
theorem mem_keys_end (Q : OutageQueryAt S A V) (x : Fin (Fintype.card V)) :
    x ∈ Q.keys ((Sys (goldilocksWith S) V).outageEnd (K S.toSetup A) Q.stop Q.run) ↔
      Q.run.2.key x ∉ Q.run.2.point.faultyAt
        ((Sys (goldilocksWith S) V).cohortAt (K S.toSetup A) Q.stop Q.run) := by
  rw [mem_honestKeysAt_iff, min_eq_left Q.end_le_horizon, Q.cohortAt_eq]; rfl

theorem holdersAt_subset (Q : OutageQueryAt S A V) :
    Q.holdersAt ⊆ Q.keys ((Sys (goldilocksWith S) V).outageEnd (K S.toSetup A) Q.stop Q.run) :=
  fun x hx => by
    obtain ⟨hxh, -⟩ := Finset.mem_filter.1 (OutageQueryAt.mem_holdersAt.1 hx)
    exact (Q.mem_keys_end x).2 (Finset.mem_sdiff.mp hxh).2

open Classical in
theorem lateKeysAt_subset (Q : OutageQueryAt S A V) :
    Q.lateKeysAt ⊆ Q.keys ((Sys (goldilocksWith S) V).outageEnd (K S.toSetup A) Q.stop Q.run) :=
  fun x hx => by
    obtain ⟨_, t, _, _, hh, _⟩ :=
      Finset.mem_filter.1 (Finset.mem_sdiff.1 (OutageQueryAt.mem_lateKeysAt.1 hx)).1
    exact (Q.mem_keys_end x).2 hh

theorem holdersAt_disjoint (Q : OutageQueryAt S A V) : Disjoint Q.holdersAt Q.lateKeysAt :=
  Set.disjoint_left.2 fun _ h₁ h₂ =>
    (Finset.mem_sdiff.1 (OutageQueryAt.mem_lateKeysAt.1 h₂)).2 (OutageQueryAt.mem_holdersAt.1 h₁)

open Classical in
/-- **The cohort count at the window end**: `|(H z)ᶜ ∪ W| < |A₀|`. -/
theorem cohort_lt (Q : OutageQueryAt S A V) :
    ((Q.keys ((Sys (goldilocksWith S) V).outageEnd (K S.toSetup A) Q.stop Q.run))ᶜ ∪
      Q.lateKeysAt).ncard <
      Q.holdersAt.ncard := by
  have heq : (Q.keys ((Sys (goldilocksWith S) V).outageEnd (K S.toSetup A) Q.stop Q.run))ᶜ ∪
      Q.lateKeysAt = Q.run.2.key ⁻¹'
      (↑(Q.run.2.point.faultyAt ((Sys (goldilocksWith S) V).cohortAt (K S.toSetup A) Q.stop Q.run) ∪
        (Q.run.2.point.retain ((Sys (goldilocksWith S) V).cohortAt (K S.toSetup A) Q.stop
          Q.run)).lateWakers ((Sys (goldilocksWith S) V).outageStart (K S.toSetup A) Q.start Q.run)
          ((Sys (goldilocksWith S) V).outageEnd (K S.toSetup A) Q.stop Q.run)) : Set V) := by
    ext x
    simp only [Set.mem_union, Set.mem_compl_iff, Q.mem_keys_end, not_not, Set.mem_preimage,
      Finset.coe_union, Finset.mem_coe, OutageQueryAt.mem_lateKeysAt]
  have hA : Q.holdersAt = Q.run.2.key ⁻¹' (↑((Q.run.2.point.retain
      ((Sys (goldilocksWith S) V).cohortAt (K S.toSetup A) Q.stop Q.run)).awakeAt
      ((Sys (goldilocksWith S) V).outageStart (K S.toSetup A) Q.start Q.run)) : Set V) := by
    ext x; simp [OutageQueryAt.mem_holdersAt]
  rw [heq, hA, Set.ncard_preimage_of_injective_subset_range Q.run.2.key.injective
      (by simp [Q.run.2.key.surjective.range_eq]),
    Set.ncard_preimage_of_injective_subset_range Q.run.2.key.injective
      (by simp [Q.run.2.key.surjective.range_eq]), Set.ncard_coe_finset,
    Set.ncard_coe_finset]
  exact Q.outage.cohort

/-- `2·|(H z)ᶜ ∪ W| < n`. -/
theorem two_mul_opp_lt (Q : OutageQueryAt S A V) :
    2 * ((Q.keys ((Sys (goldilocksWith S) V).outageEnd (K S.toSetup A) Q.stop Q.run))ᶜ ∪
      Q.lateKeysAt).ncard < Q.params.n := by
  have hdisj : Disjoint Q.holdersAt
      ((Q.keys ((Sys (goldilocksWith S) V).outageEnd (K S.toSetup A) Q.stop Q.run))ᶜ ∪
        Q.lateKeysAt) := by
    rw [Set.disjoint_union_right]
    exact ⟨Set.disjoint_left.2 fun x hx hxc => hxc (Q.holdersAt_subset hx), Q.holdersAt_disjoint⟩
  have h1 := Set.ncard_union_eq hdisj
  have h2 : (Q.holdersAt ∪ ((Q.keys ((Sys (goldilocksWith S) V).outageEnd (K S.toSetup A) Q.stop
      Q.run))ᶜ ∪ Q.lateKeysAt)).ncard ≤ Q.params.n := by
    calc _ ≤ (Set.univ : Set (Fin Q.params.n)).ncard := Set.ncard_le_ncard (Set.subset_univ _)
      _ = Q.params.n := by rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  have := Q.cohort_lt
  omega

open Classical in
/-- **The classification**: a validator honest at the window end and awake at a time of the
window is in the cohort or a late waker. -/
theorem classify (Q : OutageQueryAt S A V) {x : Fin (Fintype.card V)} {t : Time}
    (hat : (Sys (goldilocksWith S) V).outageStart (K S.toSetup A) Q.start Q.run ≤ t)
    (htz : t ≤ (Sys (goldilocksWith S) V).outageEnd (K S.toSetup A) Q.stop Q.run)
    (hxz : x ∈ Q.keys ((Sys (goldilocksWith S) V).outageEnd (K S.toSetup A) Q.stop Q.run))
    (haw : Q.trace.awake x t) : x ∈ Q.holdersAt ∪ Q.lateKeysAt := by
  rw [simTraceAt_awake_bounds] at haw
  by_cases hxa : Q.run.2.key x ∈ (Q.run.2.point.retain ((Sys (goldilocksWith S) V).cohortAt
      (K S.toSetup A) Q.stop Q.run)).awakeAt
        ((Sys (goldilocksWith S) V).outageStart (K S.toSetup A) Q.start Q.run)
  · exact Or.inl (OutageQueryAt.mem_holdersAt.2 hxa)
  · exact Or.inr (OutageQueryAt.mem_lateKeysAt.2 (Finset.mem_sdiff.2 ⟨Finset.mem_filter.2
      ⟨Finset.mem_univ _, t, hat, htz, (Q.mem_keys_end x).1 hxz, haw.1⟩, hxa⟩))

/-- The cohort is awake throughout the window. -/
theorem holder_awake (Q : OutageQueryAt S A V) {x : Fin (Fintype.card V)} (hx : x ∈ Q.holdersAt)
    {t : Time} (hat : (Sys (goldilocksWith S) V).outageStart (K S.toSetup A) Q.start Q.run ≤ t)
    (htz : t ≤ (Sys (goldilocksWith S) V).outageEnd (K S.toSetup A) Q.stop Q.run) :
    Q.trace.awake x t := by
  obtain ⟨hxh, hxa⟩ := Finset.mem_filter.1 (OutageQueryAt.mem_holdersAt.1 hx)
  rw [simTraceAt_awake_bounds]
  exact ⟨Q.outage.noSleep _ (Finset.mem_sdiff.mp hxh).2 _ le_rfl (hat.trans htz) hxa t hat htz,
    (outage_window_cover_at Q).1.trans hat, htz.trans Q.end_le_horizon⟩

end OutageQueryAt

/-- **An armed ready source** of an outage query under growing faults. -/
structure OutageArmingAt (Q : OutageQueryAt S A V) (v : V) where
  /-- `P`: the confirmed read's tip at the end-of-`T` cut. -/
  tip : SA.Blk Q.params.n (List (FG.Att Q.params.n))
  origin : SA.Blk Q.params.n (List (FG.Att Q.params.n))
  σ : Nat
  read : (chainTrace Q.run.2).readAt .confirmed v Q.T <+:
    chainTo (Q.trace.state (Q.run.2.ownKey v)
      (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut Q.T))).fg.blocks
      (tip.slot + 1) tip
  /-- `tip` is the `readAfter` read tip of `v` at the end-of-`T` cut, at clock `T`. -/
  tip_eq : tip = Regimes.readAfter Q.trace (Q.run.2.ownKey v)
    (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut Q.T)) Q.T
  /-- The tip and the origin are held while honest, the tip below the origin. -/
  tip_held : tip ∈ Q.trace.HonestBlocksAt Q.keys
  origin_held : origin ∈ Q.trace.HonestBlocksAt Q.keys
  tip_anc : Anc (Q.trace.HonestBlocksAt Q.keys) tip origin
  /-- Genesis tip (`origin := tip`), or an origin within `T`. -/
  armed : (tip.root = Q.params.genesisRoot ∧ origin = tip) ∨
    (Compose.Growing.OriginWithin Q.trace Q.keys origin σ Q.T ∧
      σ + Q.params.k < Compose.coverLabel Q.params Q.start)
  /-- S-vote. -/
  votes : ∀ x i e, Compose.Growing.HVoteAt Q.trace Q.keys x i e → σ < e.msg.slot →
    e.msg.slot ≤ Compose.coverLabel Q.params Q.start →
    SA.VoteExtends (Q.trace.HonestBlocksAt Q.keys) e.msg origin
  /-- O1 at `j₀ − 1`. -/
  lockPrev : ∀ w ∈ Q.holdersAt, origin.root ≠ Q.params.genesisRoot →
    Q.params.ts (Compose.coverLabel Q.params Q.start) + 2 * Q.params.Δ ≤ Q.run.2.horizon →
    ∃ c ℓ, SA.UpdateAt Q.trace.projAC w c (Compose.coverLabel Q.params Q.start - 1) ℓ ∧
      (Anc (Q.trace.HonestBlocksAt Q.keys) origin (Q.trace.state w c).fg.F ∨
       ∃ L f, L ∈ ℓ.frame.tree ∧ ℓ.frame.Anc origin L ∧
         (⟨L.root, Compose.coverLabel Q.params Q.start - 1, f,
           Compose.coverLabel Q.params Q.start - 1 + Q.params.k⟩ : SA.Lock) ∈
           (Q.trace.state w (c + 1)).ac.locks)
  /-- O1 at `j₀`, given (F), (VA) outside root cover and (N) at the first `j₀` update. -/
  lockCover : ∀ w ∈ Q.holdersAt, origin.root ≠ Q.params.genesisRoot →
    Q.params.ts (Compose.coverLabel Q.params Q.start) + 6 * Q.params.Δ ≤ Q.run.2.horizon →
    ∃ c ℓ, SA.UpdateAt Q.trace.projAC w c (Compose.coverLabel Q.params Q.start) ℓ ∧
      (∀ k < c, ∀ ℓ', ¬ SA.UpdateAt Q.trace.projAC w k (Compose.coverLabel Q.params Q.start) ℓ') ∧
      (Compatible (Q.trace.HonestBlocksAt Q.keys) (Q.trace.state w c).fg.F origin →
       (Anc (Q.trace.HonestBlocksAt Q.keys) (Q.trace.state w c).fg.F origin →
         ℓ.frame.AncestorCandidate origin) →
       (∀ x ∈ Q.holdersAt, ∀ j e, Compose.Growing.HVoteAt Q.trace Q.keys x j e →
          e.msg.slot = Compose.coverLabel Q.params Q.start + 1 → j < c →
          SA.VoteExtends (Q.trace.HonestBlocksAt Q.keys) e.msg origin) →
       Anc (Q.trace.HonestBlocksAt Q.keys) origin (Q.trace.state w c).fg.F ∨
       (∃ L f, ℓ.frame.Anc origin L ∧
          (⟨L.root, Compose.coverLabel Q.params Q.start, f,
            Compose.coverLabel Q.params Q.start + Q.params.k⟩ : SA.Lock) ∈
            (Q.trace.state w (c + 1)).ac.locks))

/-- **Arming under growing faults**: every source ready at `T ≤ horizon` is armed. -/
theorem outage_arming_at (Q : OutageQueryAt S A V)
    [Fact (S.vote.participationKind = none)] -- TEMP(C2)
    (service : Compose.Growing.SleepyServiceBefore Q.trace Q.keys Q.params.Δ Q.start)
    (v : V) (hv : Q.run.2.point.Ready Q.duration v Q.T) (hTh : Q.T ≤ Q.run.2.horizon) :
    Nonempty (OutageArmingAt Q v) := by
  classical
  obtain ⟨hT0, -, hb01, -⟩ := Q.outage.times
  have hrun := simTraceAt_goldilocksRun S Q.run.2 Q.hn Q.valid
  have hmv := simIni_mayVote S Q.run.2 Q.hn -- TEMP(C2): C3b replaces
  have hnc := noCollRun_simTraceAt S Q.run.2 Q.hn Q.valid Q.noCollision
  have hU := Compose.Growing.honestBlocksAt_coherent hrun hnc
  have hΔ := Q.params.toParams.hΔ
  have hk2 := Q.params.two_le_k
  have hlag := outage_node_lag_at Q
  have hhor : 0 ≤ Q.run.2.horizon := Q.valid.horizon_nonneg
  obtain ⟨ha0, haj, hzj⟩ := outage_window_cover_at Q
  have hTs : Q.T ≤ Q.start := by
    have : (0 : Time) ≤ (4 * Q.params.k + 6) * Q.params.Δ := by positivity
    linarith
  have hb0 : 0 ≤ min Q.start Q.run.2.horizon := le_min (hT0.trans hTs) hhor
  have hTb : Q.T ≤ min Q.start Q.run.2.horizon := le_min hTs hTh
  have hsvc := service.mono (min_le_left Q.start Q.run.2.horizon)
  have hBh := Q.bounds le_rfl
  have hinv := Compose.Growing.sleepy_invariant_at hrun hmv hnc hb0 hsvc (Q.bounds (min_le_right _
      _))
  have hinvT := Compose.Growing.sleepy_invariant_at hrun hmv hnc hT0 (service.mono hTs) (Q.bounds
      hTh)
  -- the tip at the end-of-`T` cut
  have hi : (chainTrace Q.run.2).endCut Q.T ≤ Q.run.2.events.length := Nat.findGreatest_le _
  obtain ⟨hcut, -, hnow⟩ := ready_read_cut_at S Q.run.2 Q.hn Q.valid (c := Q.duration)
    ((by unfold Regimes.catchUp; positivity : (0 : Time) ≤ Regimes.catchUp Q.params).trans
      (outage_duration_supply_at Q)) hT0 hTh hv
  have hŵ : Q.run.2.ownKey v ∈ Q.keys Q.T := honest_ownKey_at S Q.run.2 hv.1 hTh
  have hh : v ∉ Q.run.2.faultyAt (Q.run.2.cutTime ((chainTrace Q.run.2).endCut Q.T)) := fun h =>
    hv.1 (Q.run.2.faultyAt_mono (Nat.findGreatest_spec (P := fun i => Q.run.2.cutTime i ≤ Q.T)
      (Nat.zero_le _) (by simpa [Model.Run.cutTime] using hT0)) h)
  have hread : (chainTrace Q.run.2).readAt .confirmed v Q.T <+:
      chainTo (Q.trace.state (Q.run.2.ownKey v)
        (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut Q.T))).fg.blocks
        ((Regimes.readAfter Q.trace (Q.run.2.ownKey v)
          (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut Q.T)) Q.T).slot + 1)
        (Regimes.readAfter Q.trace (Q.run.2.ownKey v)
          (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut Q.T)) Q.T) := by
    change (chainTrace Q.run.2).read .confirmed v ((chainTrace Q.run.2).endCut Q.T) <+: _
    rw [read_eq_out S Q.run.2 Q.hn, outOf, ← simTraceAt_state S Q.run.2 Q.hn Q.valid hh hi]
    dsimp only
    rw [hnow]
    exact List.prefix_refl _
  obtain ⟨htipU, hchain⟩ : Regimes.readAfter Q.trace (Q.run.2.ownKey v)
        (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut Q.T)) Q.T ∈
          Q.trace.HonestBlocksAt Q.keys ∧
      Compose.Growing.OnOriginChainWithin Q.trace Q.keys
        (Regimes.readAfter Q.trace (Q.run.2.ownKey v)
          (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut Q.T)) Q.T) Q.T :=
    Compose.Growing.confirmed_read_on_chain_at hinvT hrun hnc hT0 hcut.1 le_rfl hŵ Q.T
  by_cases htg : (Regimes.readAfter Q.trace (Q.run.2.ownKey v)
      (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut Q.T)) Q.T).root = Q.params.genesisRoot
  · -- a genesis tip: every vote of a node honest at its cast extends it
    refine ⟨⟨_, _, 0, hread, rfl, htipU, htipU, .refl, Or.inl ⟨htg, rfl⟩,
      fun x i e hve _ _ => ?_, fun w _ hg => absurd htg hg, fun w _ hg => absurd htg hg⟩⟩
    obtain ⟨Hd, hHdU, hHdr⟩ := hve.head_mem hrun hnc
    refine ⟨Hd, hHdU, hHdr, ?_⟩
    rw [Compose.Growing.honestAt_eq_genesis hrun hU htipU htg]
    exact (Compose.Growing.honestAt_genesis_anc hrun hHdU).2
  obtain ⟨C, σ, hCw, htC⟩ :=
    (Compose.Growing.onOriginChainWithin_iff.1 hchain).resolve_left htg
  have hCU : C ∈ Q.trace.HonestBlocksAt Q.keys := by
    by_cases he : Regimes.readAfter Q.trace (Q.run.2.ownKey v)
        (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut Q.T)) Q.T = C
    · exact he ▸ htipU
    · exact (htC.mem he).2
  have hσT : Q.params.ts σ ≤ Q.T := by
    obtain ⟨x, i, CV, -, hiT, ⟨ℓ, hu, -⟩ | ⟨ℓ, A', -, hs, -⟩⟩ :=
      Compose.Growing.originWithin_iff.1 hCw
    · have ht : Q.trace.time i = Q.params.ts σ + 6 * Q.params.Δ := hu.2.2.1
      linarith
    · exact ((SA.ts_le_iff_le_slot Q.params (hrun.time_nonneg i) σ).2 (by
        have hs' : Q.params.slot (Q.trace.time i) = σ := hs
        rw [hs'])).trans hiT
  obtain ⟨hσk, hkj⟩ := Compose.armed_label_lt hT0 hlag hσT
  have hCb := hCw.mono hTb
  obtain ⟨hg₁, -⟩ := Compose.coverLabel_gates (sp := Q.params) (b₀ := Q.start) (by
    have : (0 : Time) ≤ (4 * Q.params.k + 4) * Q.params.Δ := by positivity
    linarith)
  have hts1 : Q.params.ts ((Compose.coverLabel Q.params Q.start : Int) - Q.params.k) ≤
      Q.params.ts ((Compose.coverLabel Q.params Q.start : Int) - Q.params.k + 1) :=
    (SA.ts_le_iff _).2 (by omega)
  have hjI : ((Compose.coverLabel Q.params Q.start - 1 : Nat) : Int) =
      (Compose.coverLabel Q.params Q.start : Int) - 1 := by omega
  have hjk : Q.params.ts ((Compose.coverLabel Q.params Q.start : Int) - Q.params.k) ≤
      Q.params.ts (Compose.coverLabel Q.params Q.start) := (SA.ts_le_iff _).2 (by omega)
  refine ⟨⟨_, C, σ, hread, rfl, htipU, hCU, htC, Or.inr ⟨hCw, hσk⟩,
    fun x i e hve hσe hej => ?_, fun w hw hCg hhz => ?_, fun w hw hCg hhz => ?_⟩⟩
  · -- S-vote
    obtain ⟨hx, ℓx, hcx, hex⟩ := Compose.Growing.hVoteAt_iff.1 hve
    have hvt := (Compose.Growing.cast_head_fcRoot_at hrun hnc hx ⟨hcx, hex⟩).2
    have hts := (SA.ts_le_iff Q.params).2 (show (e.msg.slot : Int) ≤ Compose.coverLabel Q.params
      Q.start by exact_mod_cast hej)
    have hih : Q.trace.time i ≤ Q.run.2.horizon :=
      Q.call_le_horizon ⟨_, Compose.projAC_callAt.1 hcx⟩
    exact hinv.vote_extends C σ hCb x i e hve
      (le_min (by change Q.trace.time i ≤ _ at hvt; linarith) hih) hσe
  · -- O1 at `j₀ − 1`
    have hsz := hzj (2 * Q.params.Δ) (by linarith) hhz
    have hsz' : Q.params.ts ((Compose.coverLabel Q.params Q.start - 1 : Nat) : Int) +
        6 * Q.params.Δ = Q.params.ts (Compose.coverLabel Q.params Q.start) + 2 * Q.params.Δ := by
      rw [hjI]; simp only [SA.SAParams.ts]; ring
    have h1 : Q.params.k ≤ Compose.coverLabel Q.params Q.start - 1 := by omega
    have h2 : σ + Q.params.k ≤ Compose.coverLabel Q.params Q.start - 1 := by omega
    have h3 : (Sys (goldilocksWith S) V).outageStart (K S.toSetup A) Q.start Q.run ≤
        Q.params.ts (((Compose.coverLabel Q.params Q.start - 1 : Nat) : Int) - Q.params.k + 1) := by
      rw [hjI, show (Compose.coverLabel Q.params Q.start : Int) - 1 - Q.params.k + 1 =
        (Compose.coverLabel Q.params Q.start : Int) - Q.params.k by ring]
      exact haj
    exact Compose.Growing.armed_lock_formed_at hrun hmv hnc hinv hsvc hBh hCb hCU hCg
      (Q.holdersAt_subset hw) Q.end_le_horizon (fun u hu₁ hu₂ => Q.holder_awake hw hu₁ hu₂)
      (s := Compose.coverLabel Q.params Q.start - 1) h1 h2 h3 (hsz' ▸ hsz)
      (hsz' ▸ le_min hg₁ hhz)
  · -- O1 at `j₀`
    have hsz := hzj (6 * Q.params.Δ) le_rfl hhz
    have h1 : Q.params.k ≤ Compose.coverLabel Q.params Q.start := by omega
    have h2 : σ + Q.params.k ≤ Compose.coverLabel Q.params Q.start := by omega
    have hF : (Q.keys (Q.params.ts (Compose.coverLabel Q.params Q.start) + 6 * Q.params.Δ))ᶜ ⊆
        (Q.keys ((Sys (goldilocksWith S) V).outageEnd (K S.toSetup A) Q.stop Q.run))ᶜ ∪
          Q.lateKeysAt :=
      fun x hx => Or.inl fun hxz => hx (honestKeysAt_antitone S Q.run.2 hsz hxz)
    exact Compose.Growing.armed_lock_cover_at hrun hmv hnc hinv hsvc hBh hCb hCg
      (Q.holdersAt_subset hw) Q.end_le_horizon (fun u hu₁ hu₂ => Q.holder_awake hw hu₁ hu₂)
      (s := Compose.coverLabel Q.params Q.start) h1 h2 (haj.trans hts1) hsz
      (le_min hg₁ (by linarith)) Q.holdersAt _ hF Q.two_mul_opp_lt
      fun x j e hve hx hes hjt => by
        by_cases hxz :
            x ∈ Q.keys ((Sys (goldilocksWith S) V).outageEnd (K S.toSetup A) Q.stop Q.run)
        · obtain ⟨hxj, ℓx, hcx, hex⟩ := Compose.Growing.hVoteAt_iff.1 hve
          have hxs := (Compose.Growing.castAt_spec_at hrun hnc hxj ⟨hcx, hex⟩).2.1
          have hjs : Q.params.ts ((Compose.coverLabel Q.params Q.start + 1 : Nat) : Int) ≤
              Q.trace.time j :=
            (SA.ts_le_iff_le_slot _ (hrun.time_nonneg j) _).2 (by
              change ((Compose.coverLabel Q.params Q.start + 1 : Nat) : Int) ≤
                (Q.params.slot (Q.trace.time j) : Int)
              rw [← hes]; exact_mod_cast hxs.le)
          have hjk' : Q.params.ts ((Compose.coverLabel Q.params Q.start : Int) - Q.params.k) ≤
              Q.params.ts ((Compose.coverLabel Q.params Q.start + 1 : Nat) : Int) :=
            (SA.ts_le_iff _).2 (by omega)
          have haw := hrun.awake_of_call x j hxj ⟨_, Compose.projAC_callAt.1 hcx⟩
          rcases Q.classify (by linarith) (hjt.trans hsz) hxz haw with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        · exact Or.inr (Or.inl hxz)

end Consensus.Goldilocks.Obligations.Growing

end

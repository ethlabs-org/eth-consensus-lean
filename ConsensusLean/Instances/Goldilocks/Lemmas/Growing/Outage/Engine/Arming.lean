module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Engine.Query
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Engine.Members
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Population
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.SleepyWindows
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
labels `j₀ − 1` and `j₀` for the holders `holdersAt` (O1 at `j₀` given (F), (VA) outside root
cover and (N), with (N) over the votes of the holders cast while honest).

The holder facts of the query, read on the view retained through the window end `z`:
`holdersAt` (ready at `z` with the outage catch-up) and `opponentsAt` (the other validators awake in
the look-back) are honest at `z` and disjoint, inside each band committee
`|K m ∩ ((H z)ᶜ ∪ W)| < |K m ∩ A₀|` (`opponents_lt_K`, from the look-back committee clause at `z`),
a validator honest at `z` and awake in `[a, z]` is in `A₀ ∪ W` (`classify`, since the look-back
covers `[a, z]`), and `A₀` is awake throughout `[a, z]` (`holder_awake`, since the outage catch-up
covers it); `bounds` are the two count shapes through every `b ≤ horizon`, from the η-sleepy
premise, and `boundsK` their committee forms, from the shifted committee clauses.

`outage_arming_at`: every source ready at `T ≤ horizon` is armed. The Sleepy invariant up to
`min b₀ horizon` (from the pre-start service and the counts) gives the tip on the chain of the
origins within `T`, S-vote, and O1 at `j₀ − 1` (`armed_lock_formed_at`) and at `j₀`
(`armed_lock_cover_at`, with the opponents `(H z)ᶜ ∪ W`). -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation
open Blocks Shape
variable {S : Setup} {A : ContractAssumptions S} {V : Type} [Fintype V] [DecidableEq V]


namespace OutageQueryAt

private theorem point_binding (Q : OutageQueryAt S A V) :
    Generic.RunPointBinding Q.trace Q.keys (goldilocksPoint Q.run.2) := by
  have h := goldilocksPoint_binding (S := S) Q.hn Q.valid
  rw [goldilocksRunMap_trace S Q.run.2 Q.hn Q.valid,
    goldilocksRunMap_honest S Q.run.2 Q.hn Q.valid] at h
  exact h

private theorem holders_eq (Q : OutageQueryAt S A V) : Q.holdersAt =
    Compose.Growing.outageHolders (sp := Q.params)
      (goldilocksPoint Q.run.2) Q.outCatch Q.winEnd := by
  classical
  have h := goldilocksPoint_readyAt (rho := Q.run.2) Q.outCatch Q.winEnd Q.winEnd
    (min_le_right _ _)
  rw [min_eq_left (min_le_right _ _)] at h
  ext x
  rw [Compose.Growing.mem_outageHolders, OutageQueryAt.mem_holdersAt, ← h]
  simp only [Finset.mem_map, Equiv.toEmbedding_apply, Q.run.2.key.injective.eq_iff,
    exists_eq_right]

private theorem opponents_eq (Q : OutageQueryAt S A V) : Q.opponentsAt =
    Compose.Growing.outageOpponents (sp := Q.params)
      (goldilocksPoint Q.run.2) Q.lookBack Q.outCatch Q.winEnd := by
  classical
  have hr := goldilocksPoint_readyAt (rho := Q.run.2) Q.outCatch Q.winEnd Q.winEnd
    (min_le_right _ _)
  have ha := goldilocksPoint_awakeIn (rho := Q.run.2) Q.winEnd
    (max 0 (Q.winEnd - Q.lookBack)) Q.winEnd (le_max_left _ _) (min_le_right _ _)
  rw [min_eq_left (min_le_right _ _)] at hr ha
  ext x
  rw [Compose.Growing.mem_outageOpponents, OutageQueryAt.mem_opponentsAt,
    Finset.mem_sdiff, Finset.mem_sdiff, ← hr, ← ha]
  simp only [Finset.mem_map, Equiv.toEmbedding_apply, Q.run.2.key.injective.eq_iff,
    exists_eq_right]

private theorem participation (Q : OutageQueryAt S A V) :
    (goldilocksPoint Q.run.2).EtaSleepyOn (1 / 2) Q.lookBack Q.outCatch
      (5 * Q.params.Δ) 0 Q.run.2.horizon ∧
    ∀ δ, 0 ≤ δ → δ ≤ Q.lookBack →
      (goldilocksPoint Q.run.2).CommitteeSleepyOn
        (fun t => runCommittee S Q.run.2 Q.hn (max 0 (t - δ))) (1 / 2) Q.lookBack
        Q.outCatch (5 * Q.params.Δ) 0 Q.run.2.horizon := by
  have h := (goldilocks_outageTransport S Q.run.2 Q.hn Q.valid (Obligations.K S A)).participation
    Q.valid Q.T Q.start Q.stop Q.outage
  rw [goldilocksOutagePolicy_point S Q.run.2 Q.hn Q.valid] at h
  simp only [goldilocksPoint_horizon, Params.standard] at h
  rw [goldilocksRunMap_committee S Q.run.2 Q.hn Q.valid] at h
  exact h

private theorem bounds_pair (Q : OutageQueryAt S A V) {ini}
    (hrun : Growing.GoldilocksRun (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2) Q.keys Q.trace
      ini) {b : Time} (hb : b ≤ Q.run.2.horizon) :
    Compose.Growing.SleepyBoundsFrom Q.trace Q.keys 0 b ∧
      Compose.Growing.CommitteeBoundsFrom Q.trace Q.keys Q.K 0 b := by
  have hη : Q.params.Δ ≤ Q.lookBack := by
    change Q.run.1.ΔAC ≤ ((12 * S.k + 7 : Nat) : Time) * Q.run.1.ΔAC
    have hcoeff : (1 : Time) ≤ ((12 * S.k + 7 : Nat) : Time) := by
      have : 1 ≤ 12 * S.k + 7 := by omega
      exact_mod_cast this
    nlinarith [Q.run.1.ΔAC_pos]
  have hsize : ∀ s,
      ((Generic.dictOfTime Q.params (runCommittee S Q.run.2 Q.hn)).committee s).ncard =
        Q.params.committeeSize := by
    rw [dictOfTime_runCommittee]
    exact voteK_ncard S Q.run.2 Q.hn Q.valid
  have h := Compose.Growing.outage_bounds (b := b) hrun Q.point_binding
    (S.committeeSize_pos (Model.pubOf Q.run.1) Q.hn) hsize hη
    ((outage_duration_supply_at Q).trans (le_max_left Q.duration (Q.lookBack - 1)))
    (by simpa only [goldilocksPoint_horizon] using Q.participation.1)
    (by simpa only [goldilocksPoint_horizon] using Q.participation.2)
    (by rw [goldilocksPoint_horizon]; exact hb)
  rwa [dictOfTime_runCommittee] at h

/-- The two count shapes through every `b ≤ horizon`, from the η-sleepy premise (η-sleepy
implies sleepy, at half readiness, with look-ahead `5Δ`). -/
theorem bounds (Q : OutageQueryAt S A V)
    {b : Time} (hb : b ≤ Q.run.2.horizon) :
    Compose.Growing.SleepyBoundsFrom Q.trace Q.keys 0 b :=
  (Q.bounds_pair (simTraceAt_goldilocksRun S Q.run.2 Q.hn Q.valid) hb).1

/-- CS and current-slot CS2 through every `b ≤ horizon`, from the node population bounds
with shifts `Δ` and `0`, respectively. -/
theorem boundsK (Q : OutageQueryAt S A V) {ini}
    (hrun : Growing.GoldilocksRun (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2) Q.keys Q.trace
      ini) {b : Time} (hb : b ≤ Q.run.2.horizon) :
    Compose.Growing.CommitteeBoundsFrom Q.trace Q.keys Q.K 0 b :=
  (Q.bounds_pair hrun hb).2

theorem end_le_horizon (Q : OutageQueryAt S A V) : Q.winEnd ≤ Q.run.2.horizon :=
  min_le_right _ _

open Classical in
theorem holdersAt_subset (Q : OutageQueryAt S A V) : Q.holdersAt ⊆ Q.keys Q.winEnd :=
  Q.holders_eq ▸ Compose.Growing.outageHolders_subset Q.point_binding

open Classical in
theorem opponentsAt_subset (Q : OutageQueryAt S A V) : Q.opponentsAt ⊆ Q.keys Q.winEnd :=
  Q.opponents_eq ▸ Compose.Growing.outageOpponents_subset Q.point_binding

theorem holdersAt_disjoint (Q : OutageQueryAt S A V) : Disjoint Q.holdersAt Q.opponentsAt := by
  rw [Q.holders_eq, Q.opponents_eq]
  exact Compose.Growing.outageHolders_disjoint

/-- **The opponents count inside a band committee**: at a label `m ∈ [j₀, j₀ + k]` whose start is
within the horizon (and the outage start too), `|K m ∩ ((H z)ᶜ ∪ W)| < |K m ∩ A₀|`. The band
`[b₀ − 2Δ, b₀ + (4k − 2)Δ]` holds a time `t ∈ [0, horizon]` of slot `m` (`b₀ − 2Δ` for `j₀`,
else `t_m`), with `t ≤ z` and `z − t ≤ (8k + 3)Δ ≤ η·Δ`; the look-back committee clause at `z`
with look-back `δ = z − t` reads the selection at `max 0 (z − δ) = t`, which is `K m`
(`mem_K_iff_selected`, nonempty by `K_nonempty`). -/
theorem opponents_lt_K (Q : OutageQueryAt S A V) {m : Nat}
    (h₁ : Compose.coverLabel Q.params Q.start ≤ m)
    (h₂ : m ≤ Compose.coverLabel Q.params Q.start + Q.params.k)
    (hq : Q.params.ts m ≤ Q.run.2.horizon) (hsh : Q.start ≤ Q.run.2.horizon) :
    (Q.K.committee m ∩ ((Q.keys Q.winEnd)ᶜ ∪ Q.opponentsAt)).ncard <
      (Q.K.committee m ∩ Q.holdersAt).ncard := by
  have hΔ := Q.params.toParams.hΔ
  have hlag := outage_node_lag_at Q
  have hT0 : 0 ≤ Q.T := Q.outage.times.1
  have h2 : 2 * Q.params.Δ ≤ Q.start := by
    have : (0 : Time) ≤ (4 * Q.params.k + 4) * Q.params.Δ := by positivity
    linarith
  obtain ⟨hg₁, hg₂⟩ := Compose.coverLabel_gates (sp := Q.params) h2
  obtain ⟨t, ht0, hslot, htb₁, htb₂, hth⟩ : ∃ t, 0 ≤ t ∧ Q.params.slot t = m ∧
      Q.start - 2 * Q.params.Δ ≤ t ∧
      t ≤ Q.start - 2 * Q.params.Δ + 4 * Q.params.k * Q.params.Δ ∧ t ≤ Q.run.2.horizon := by
    rcases h₁.eq_or_lt with rfl | hlt
    · refine ⟨Q.start - 2 * Q.params.Δ, by linarith, (Compose.coverLabel_eq _ _).symm, le_rfl, ?_,
        by linarith⟩
      have : (0 : Time) ≤ 4 * Q.params.k * Q.params.Δ := by positivity
      linarith
    · have hm1 := (SA.ts_le_iff Q.params).2
        (show ((Compose.coverLabel Q.params Q.start + 1 : Nat) : Int) ≤ m by omega)
      have hmk := (SA.ts_le_iff Q.params).2
        (show (m : Int) ≤ ((Compose.coverLabel Q.params Q.start + Q.params.k : Nat) : Int) by
          omega)
      refine ⟨Q.params.ts m, ?_, SA.slot_of_mem _ m le_rfl ((SA.ts_lt_iff _).2 (by omega)), ?_, ?_,
        hq⟩
      · simp only [SA.SAParams.ts]; positivity
      · simp only [SA.SAParams.ts] at hm1 hg₂ ⊢; push_cast at hm1 hg₂ ⊢; linarith
      · simp only [SA.SAParams.ts] at hmk hg₁ ⊢; push_cast at hmk hg₁ ⊢; linarith
  subst hslot
  -- the look-back `δ = z − t` reaches the band time `t` from the window end `z`
  obtain ⟨-, -, -, hbud⟩ := Q.outage.times
  have hd : (1 : Time) ≤ Q.run.1.ΔAC := Q.run.1.ΔAC_pos
  have hk2 : (2 : Int) ≤ S.k := by exact_mod_cast S.two_le_k
  have hbcast : ((4 * S.k - 5 : Nat) : Int) = 4 * (S.k : Int) - 5 := by omega
  change Q.stop ≤ Q.start + ((4 * S.k - 5 : Nat) : Int) * Q.run.1.ΔAC at hbud
  rw [hbcast] at hbud
  have hL : ((4 * S.k + 6 : Nat) : Int) = 4 * (S.k : Int) + 6 := by push_cast; ring
  have hη : ((Obligations.K S A).params.η : Time) = 12 * (S.k : Int) + 7 := by
    change ((12 * S.k + 7 : Nat) : Int) = _; push_cast; ring
  have hk : (Q.params.k : Int) = S.k := rfl
  have hΔeq : Q.params.Δ = Q.run.1.ΔAC := rfl
  rw [hk, hΔeq] at htb₂
  rw [hΔeq] at htb₁
  have hb01 : Q.start ≤ Q.stop := Q.outage.times.2.2.1
  have htz : t ≤ Q.winEnd := by
    refine le_min ?_ hth
    rw [hL]
    linarith
  have hz0 : 0 ≤ Q.winEnd := ht0.trans htz
  -- the band committees are selected at most `(8k + 3)Δ` before `z`, within the look-back
  have hδ₀ : Q.winEnd - t ≤ (8 * (S.k : Int) + 3) * Q.run.1.ΔAC := by
    have hz' : Q.winEnd ≤ Q.stop + (4 * (S.k : Int) + 6) * Q.run.1.ΔAC := by
      rw [← hL]; exact min_le_left _ _
    linarith
  have hδ : Q.winEnd - t ≤ Q.lookBack := by
    have hkΔ : (0 : Time) ≤ (S.k : Int) * Q.run.1.ΔAC := mul_nonneg (by positivity) (by linarith)
    change Q.winEnd - t ≤ ((Obligations.K S A).params.η : Time) * Q.run.1.ΔAC
    rw [hη]
    linarith
  have hpos : 0 < Q.lookBack := by
    change 0 < ((Obligations.K S A).params.η : Time) * Q.run.1.ΔAC
    rw [hη]
    exact mul_pos (by linarith) (by linarith)
  have hne : (runCommittee S Q.run.2 Q.hn t).Nonempty := by
    have hcard := runCommittee_card S Q.run.2 Q.hn Q.valid t
    exact Finset.card_pos.mp (by rw [hcard]; exact S.committeeSize_pos _ Q.hn)
  have h := Compose.Growing.outage_opponents_lt_at Q.point_binding hpos
    (show 0 ≤ 5 * Q.params.Δ by positivity) hz0
    (by rw [goldilocksPoint_horizon]; exact Q.end_le_horizon)
    (by simpa only [goldilocksPoint_horizon] using Q.participation.2)
    hne (max_le ht0 (by linarith)) htz
  rw [← Q.holders_eq, ← Q.opponents_eq] at h
  have hK : (runCommittee S Q.run.2 Q.hn t : Set (Fin (Fintype.card V))) =
      Q.K.committee (Q.params.slot t) := by
    ext x
    rw [Finset.mem_coe, runCommittee_eq S Q.run.2 Q.hn Q.valid x t ht0]
    exact (mem_voteK_iff_selected S Q.run.2 Q.hn Q.valid ht0).symm
  rwa [hK] at h

/-- **N6 inside a band committee**: `2·|K m ∩ ((H z)ᶜ ∪ W)| < committeeSize` (`opponents_lt_K`, the
holders being disjoint from the opponents). -/
theorem two_mul_opp_lt (Q : OutageQueryAt S A V) {m : Nat}
    (h₁ : Compose.coverLabel Q.params Q.start ≤ m)
    (h₂ : m ≤ Compose.coverLabel Q.params Q.start + Q.params.k)
    (hq : Q.params.ts m ≤ Q.run.2.horizon) (hsh : Q.start ≤ Q.run.2.horizon) :
    2 * (Q.K.committee m ∩ ((Q.keys Q.winEnd)ᶜ ∪ Q.opponentsAt)).ncard <
      Q.params.committeeSize := by
  have h := Q.opponents_lt_K h₁ h₂ hq hsh
  rw [Q.holders_eq, Q.opponents_eq] at h
  have hhalf := Compose.Growing.outage_two_mul_opponents_lt Q.point_binding h
  rw [← Q.opponents_eq, voteK_ncard S Q.run.2 Q.hn Q.valid m] at hhalf
  exact hhalf

open Classical in
/-- **The classification**: a validator honest at the window end and awake at a time of the
window is a holder or a look-back opponent, since the look-back covers the window. -/
theorem classify (Q : OutageQueryAt S A V) {x : Fin (Fintype.card V)} {t : Time}
    (hat : Q.winStart ≤ t) (htz : t ≤ Q.winEnd) (hxz : x ∈ Q.keys Q.winEnd)
    (haw : Q.trace.awake x t) : x ∈ Q.holdersAt ∪ Q.opponentsAt := by
  rw [Q.holders_eq, Q.opponents_eq]
  exact Compose.Growing.outage_classify Q.point_binding
    (look_back_le_winStart Q) hat htz hxz haw

open Classical in
/-- The holders are awake throughout the window: it is ready at the window end with the outage
catch-up, which covers the window. -/
theorem holder_awake (Q : OutageQueryAt S A V) {x : Fin (Fintype.card V)} (hx : x ∈ Q.holdersAt)
    {t : Time} (hat : Q.winStart ≤ t) (htz : t ≤ Q.winEnd) : Q.trace.awake x t := by
  rw [Q.holders_eq] at hx
  exact Compose.Growing.outage_holder_awake Q.point_binding
    (ready_window_le_winStart Q) hx hat htz

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
    (service : Compose.Growing.SleepyServiceBefore Q.trace Q.keys Q.params.Δ Q.start)
    (v : V) (hv : Q.run.2.point.Ready Q.duration v Q.T) (hTh : Q.T ≤ Q.run.2.horizon) :
    Nonempty (OutageArmingAt Q v) := by
  classical
  obtain ⟨hT0, -, hb01, -⟩ := Q.outage.times
  have hrun := simTraceAt_goldilocksRun S Q.run.2 Q.hn Q.valid
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
  have hKB := voteK_facts S Q.run.2 Q.hn Q.valid hnc hrun
  have hBKh := Q.boundsK hrun le_rfl
  have hinv := Compose.Growing.sleepy_invariant_at hrun hnc hKB hb0 hsvc
    (Q.bounds (min_le_right _ _)) (hBKh.mono (min_le_right _ _))
  have hinvT := Compose.Growing.sleepy_invariant_at hrun hnc hKB hT0 (service.mono hTs)
    (Q.bounds hTh) (hBKh.mono hTh)
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
  obtain ⟨hg₁, hg₂⟩ := Compose.coverLabel_gates (sp := Q.params) (b₀ := Q.start) (by
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
    have h3 : Q.winStart ≤
        Q.params.ts (((Compose.coverLabel Q.params Q.start - 1 : Nat) : Int) - Q.params.k + 1) := by
      rw [hjI, show (Compose.coverLabel Q.params Q.start : Int) - 1 - Q.params.k + 1 =
        (Compose.coverLabel Q.params Q.start : Int) - Q.params.k by ring]
      exact haj
    exact Compose.Growing.armed_lock_formed_at hrun hnc hKB hinv hsvc hBKh hCb hCU hCg
      (Q.holdersAt_subset hw) Q.end_le_horizon (fun u hu₁ hu₂ => Q.holder_awake hw hu₁ hu₂)
      (s := Compose.coverLabel Q.params Q.start - 1) h1 h2 h3 (hsz' ▸ hsz)
      (hsz' ▸ le_min hg₁ hhz)
  · -- O1 at `j₀`
    have hsz := hzj (6 * Q.params.Δ) le_rfl hhz
    have h1 : Q.params.k ≤ Compose.coverLabel Q.params Q.start := by omega
    have h2 : σ + Q.params.k ≤ Compose.coverLabel Q.params Q.start := by omega
    have hF : (Q.keys (Q.params.ts (Compose.coverLabel Q.params Q.start) + 6 * Q.params.Δ))ᶜ ⊆
        (Q.keys Q.winEnd)ᶜ ∪
          Q.opponentsAt :=
      fun x hx => Or.inl fun hxz => hx (honestKeysAt_antitone S Q.run.2 hsz hxz)
    have hsh : Q.start ≤ Q.run.2.horizon := by linarith
    have hq1 : Q.params.ts ((Compose.coverLabel Q.params Q.start + 1 : Nat) : Int) ≤
        Q.run.2.horizon := by
      have h := hhz
      simp only [SA.SAParams.ts] at h ⊢; push_cast; linarith
    exact Compose.Growing.armed_lock_cover_at hrun hnc hKB hinv hsvc hBKh hCb hCg
      (Q.holdersAt_subset hw) Q.end_le_horizon (fun u hu₁ hu₂ => Q.holder_awake hw hu₁ hu₂)
      (s := Compose.coverLabel Q.params Q.start) h1 h2 (haj.trans hts1) hsz
      (le_min hg₁ (by linarith)) Q.holdersAt _ hF
      (Q.two_mul_opp_lt (by omega) (by omega) hq1 hsh)
      fun x j e hve hx hes hjt => by
        by_cases hxz :
            x ∈ Q.keys Q.winEnd
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

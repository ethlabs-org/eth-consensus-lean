module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageSuppliers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageArmingSteps
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks outage: arming of a ready source

Workbench `notes/outage/outage_arming.md` (b4ba553), §§1–7 and §10: the read tip `P` of a ready
source at the end-of-`T` cut, an origin `C ⪰ P` within `T` of a label `σ` more than `k` labels
before the cover label `j₀`, S-vote, and O1 at the labels `j₀ − 1` and `j₀` for the honest
validators awake at the no-sleep window start. O1 at `j₀` takes the lock-safety inputs (F), (VA)
(outside root cover) and (N) as premises of `lockCover`. -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation
open Blocks Shape
variable (S : Setup) (A : ContractAssumptions S) (V : Type)
  [Fintype V] [DecidableEq V]

namespace OutageQuery
variable {S A V}

/-- The no-sleep holders: honest validators awake at the window start, as keys. -/
noncomputable def holders (Q : OutageQuery S A V) : Set (Fin (Fintype.card V)) :=
  {x | Q.run.2.key x ∈
    Q.run.2.point.awakeAt ((Sys (goldilocks S) V).outageStart (K S A) Q.start Q.run)}

theorem mem_holders {Q : OutageQuery S A V} {x : Fin (Fintype.card V)} :
    x ∈ Q.holders ↔ Q.run.2.key x ∈
      Q.run.2.point.awakeAt ((Sys (goldilocks S) V).outageStart (K S A) Q.start Q.run) := Iff.rfl

end OutageQuery

/-- The catch-up duration of an outage query covers the node catch-up `18Δ`. -/
theorem outage_duration_supply (Q : OutageQuery S A V) :
    Regimes.catchUp Q.params ≤ Q.duration := by
  have hc : (19 : Time) ≤ (contract_catchUp S A : Nat) := by
    exact_mod_cast contract_catchUp_ge_sleepy S A
  have hd : (1 : Time) ≤ Q.run.1.Δ := Q.run.1.Δ_pos
  simp only [OutageQuery.duration, System.cDur, Params.standard, contract_coefficients_catchUp]
  change 18 * Q.run.1.Δ ≤ (contract_catchUp S A : Nat) * Q.run.1.Δ
  nlinarith

/-- (A1) The lag `4k + 6` is the node lag `(4k+6)Δ`. -/
theorem outage_node_lag (Q : OutageQuery S A V) :
    Q.T + (4 * Q.params.k + 6) * Q.params.Δ ≤ Q.start := by
  obtain ⟨⟨-, hlag, -, -⟩, -⟩ := Q.outage
  have hd : (1 : Time) ≤ Q.run.1.Δ := Q.run.1.Δ_pos
  have hk : (0 : Time) ≤ S.k := by positivity
  change Q.T + ((4 * S.k + 6 : Nat) : Int) * Q.run.1.Δ ≤ Q.start at hlag
  change Q.T + (4 * (S.k : Int) + 6) * Q.run.1.Δ ≤ Q.start
  push_cast at hlag
  nlinarith

/-- (A4)/(A5) The no-sleep window `[a, z]` starts by `t_{j₀−k}` (from `0`) and ends at or after
every update of a label `≤ j₀` within the horizon. -/
theorem outage_window_cover (Q : OutageQuery S A V) :
    0 ≤ (Sys (goldilocks S) V).outageStart (K S A) Q.start Q.run ∧
      (Sys (goldilocks S) V).outageStart (K S A) Q.start Q.run ≤
        Q.params.ts ((Compose.coverLabel Q.params Q.start : Int) - Q.params.k) ∧
      ∀ d ≤ 6 * Q.params.Δ, Q.params.ts (Compose.coverLabel Q.params Q.start) + d ≤
          Q.run.2.horizon →
        Q.params.ts (Compose.coverLabel Q.params Q.start) + d ≤
          (Sys (goldilocks S) V).outageEnd (K S A) Q.stop Q.run := by
  obtain ⟨⟨hT, -, hb01, -⟩, -⟩ := Q.outage
  have hlag := outage_node_lag S A V Q
  have hΔ := Q.params.toParams.hΔ
  have hd : (1 : Time) ≤ Q.run.1.Δ := Q.run.1.Δ_pos
  have hk : (0 : Time) ≤ S.k := by positivity
  have hkj := (Compose.armed_label_lt (σ := 0) hT hlag (by simp [SA.SAParams.ts]; exact hT)).2
  obtain ⟨hg₁, hg₂⟩ := Compose.coverLabel_gates (sp := Q.params) (b₀ := Q.start) (by
    have : (0 : Time) ≤ (4 * Q.params.k + 4) * Q.params.Δ := by positivity
    nlinarith)
  have hhor : 0 ≤ Q.run.2.horizon := Q.valid.horizon_nonneg
  have hC : ((4 * S.k + 6 : Nat) : Int) = 4 * (S.k : Int) + 6 := by push_cast; ring
  set j₀ := Compose.coverLabel Q.params Q.start
  have hkj' : ((S.k : Nat) : Int) < j₀ := by exact_mod_cast hkj
  change 0 ≤ min (max 0 (Q.start - ((4 * S.k + 6 : Nat) : Int) * Q.run.1.Δ))
      Q.run.2.horizon ∧
    min (max 0 (Q.start - ((4 * S.k + 6 : Nat) : Int) * Q.run.1.Δ)) Q.run.2.horizon ≤
      4 * Q.run.1.Δ * ((j₀ : Int) - S.k) ∧
    ∀ d ≤ 6 * Q.run.1.Δ, 4 * Q.run.1.Δ * (j₀ : Int) + d ≤ Q.run.2.horizon →
      4 * Q.run.1.Δ * (j₀ : Int) + d ≤
        min (Q.stop + ((4 * S.k + 6 : Nat) : Int) * Q.run.1.Δ) Q.run.2.horizon
  change 4 * Q.run.1.Δ * (j₀ : Int) + 2 * Q.run.1.Δ ≤ Q.start at hg₁
  change Q.start < 4 * Q.run.1.Δ * (j₀ : Int) + 6 * Q.run.1.Δ at hg₂
  refine ⟨le_min (le_max_left _ _) hhor, (min_le_left _ _).trans (max_le ?_ ?_),
    fun d hd6 hdh => le_min ?_ hdh⟩
  · have : (0 : Time) ≤ (j₀ : Int) - S.k := by linarith
    positivity
  · rw [hC]
    nlinarith
  · rw [hC]
    nlinarith

/-- **Arming of a ready source** (§10): the read tip `P` at the end-of-`T` cut, an armed origin
`C ⪰ P`, S-vote, and O1 at the labels `j₀ − 1` and `j₀ = coverLabel b₀` for the holders. -/
structure OutageArming (Q : OutageQuery S A V) (v : V) where
  /-- `P`: the confirmed read's tip at the end-of-`T` cut. -/
  tip : SA.Blk Q.params.n (List (FG.Att Q.params.n))
  origin : SA.Blk Q.params.n (List (FG.Att Q.params.n))
  σ : Nat
  read : (chainTrace Q.run.2).readAt .confirmed v Q.T <+:
    chainTo (Q.trace.state (Q.run.2.ownKey v)
      (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut Q.T))).fg.blocks
      (tip.slot + 1) tip
  /-- `tip` is the `readAfter` read tip of `v` at the end-of-`T` cut, at clock `T` (§3). -/
  tip_eq : tip = Regimes.readAfter Q.trace (Q.run.2.ownKey v)
    (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut Q.T)) Q.T
  /-- Genesis tip (`origin := tip`), or `P ⪯ C` for an origin within `T` (§3). -/
  armed : (tip.root = Q.params.genesisRoot ∧ origin = tip) ∨
    (Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) tip origin ∧
      Compose.OriginWithin Q.trace (honestKeys S Q.run.2) origin σ Q.T ∧
      σ + Q.params.k < Compose.coverLabel Q.params Q.start)
  /-- S-vote (§3). -/
  votes : ∀ x ∈ honestKeys S Q.run.2, ∀ i e, SA.VoteAt Q.trace.projAC x i e → σ < e.msg.slot →
    e.msg.slot ≤ Compose.coverLabel Q.params Q.start →
    SA.VoteExtends (Q.trace.HonestBlocks (honestKeys S Q.run.2)) e.msg origin
  /-- O1 at `j₀ − 1`, unconditional (§6). -/
  lockPrev : ∀ w ∈ Q.holders, origin.root ≠ Q.params.genesisRoot →
    Q.params.ts (Compose.coverLabel Q.params Q.start) + 2 * Q.params.Δ ≤ Q.run.2.horizon →
    ∃ c ℓ, SA.UpdateAt Q.trace.projAC w c (Compose.coverLabel Q.params Q.start - 1) ℓ ∧
      (Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) origin (Q.trace.state w c).fg.F ∨
       ∃ L f, L ∈ ℓ.frame.tree ∧ ℓ.frame.Anc origin L ∧
         (⟨L.root, Compose.coverLabel Q.params Q.start - 1, f,
           Compose.coverLabel Q.params Q.start - 1 + Q.params.k⟩ : SA.Lock) ∈
           (Q.trace.state w (c + 1)).ac.locks)
  /-- O1 at `j₀`, given (F), (VA) outside root cover and (N) at the first `j₀` update (§7). -/
  lockCover : ∀ w ∈ Q.holders, origin.root ≠ Q.params.genesisRoot →
    Q.params.ts (Compose.coverLabel Q.params Q.start) + 6 * Q.params.Δ ≤ Q.run.2.horizon →
    ∃ c ℓ, SA.UpdateAt Q.trace.projAC w c (Compose.coverLabel Q.params Q.start) ℓ ∧
      (∀ k < c, ∀ ℓ', ¬ SA.UpdateAt Q.trace.projAC w k (Compose.coverLabel Q.params Q.start) ℓ') ∧
      (Compatible (Q.trace.HonestBlocks (honestKeys S Q.run.2)) (Q.trace.state w c).fg.F origin →
       (Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) (Q.trace.state w c).fg.F origin →
         ℓ.frame.AncestorCandidate origin) →
       (∀ x ∈ Q.holders, ∀ j e, SA.VoteAt Q.trace.projAC x j e →
          e.msg.slot = Compose.coverLabel Q.params Q.start + 1 → j < c →
          SA.VoteExtends (Q.trace.HonestBlocks (honestKeys S Q.run.2)) e.msg origin) →
       Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) origin (Q.trace.state w c).fg.F ∨
       (∃ L f, ℓ.frame.Anc origin L ∧
          (⟨L.root, Compose.coverLabel Q.params Q.start, f,
            Compose.coverLabel Q.params Q.start + Q.params.k⟩ : SA.Lock) ∈
            (Q.trace.state w (c + 1)).ac.locks))

/-- **Arming** (§§1–7): every ready source at `T` within the horizon is armed. -/
theorem outage_arming (Q : OutageQuery S A V)
    (service : Compose.SleepyServiceBefore Q.trace (honestKeys S Q.run.2) Q.params.Δ Q.start)
    (v : V) (hv : Q.run.2.point.Ready Q.duration v Q.T) (hTh : Q.T ≤ Q.run.2.horizon) :
    Nonempty (OutageArming S A V Q v) := by
  classical
  obtain ⟨⟨hT0, -, hb01, -⟩, -, heta, hns, hcoh⟩ := Q.outage
  have hrun := simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid
  have hnc := noCollRun_simTrace S Q.run.2 Q.hn Q.valid Q.noCollision
  have hr := (Compose.goldilocks_ac_projection _ _ _ _ _ _ hrun hnc).localRun
  have hU := hr.coherent
  have hΔ := Q.params.toParams.hΔ
  have hk2 := Q.params.two_le_k
  have hlag := outage_node_lag S A V Q
  have hhor : 0 ≤ Q.run.2.horizon := Q.valid.horizon_nonneg
  obtain ⟨ha0, haj, hzj⟩ := outage_window_cover S A V Q
  have hTs : Q.T ≤ Q.start := by
    have : (0 : Time) ≤ (4 * Q.params.k + 6) * Q.params.Δ := by positivity
    linarith
  have hb0 : 0 ≤ min Q.start Q.run.2.horizon := le_min (hT0.trans hTs) hhor
  have hTb : Q.T ≤ min Q.start Q.run.2.horizon := le_min hTs hTh
  have hsvc := Compose.SleepyServiceBefore.mono service (min_le_left Q.start Q.run.2.horizon)
  have hfball : ∀ s : Nat, ∀ d ∈ ({0, Q.params.Δ, 2 * Q.params.Δ} : Set Time),
      Q.params.ts s + d ≤ min Q.start Q.run.2.horizon →
        Q.trace.FaultBound (honestKeys S Q.run.2) (Q.params.ts s + d) :=
    sleepy_faultBound S Q.run.2 Q.hn Q.valid (min_le_right _ _) fun t ht htb =>
      half_ready_of_duration V Q.run.2.point (outage_duration_supply S A V Q)
        ((show Q.run.2.point.EtaReadyAbove (1 / 2) _ Q.duration t from
          heta t ht (htb.trans (min_le_right _ _))).readyAbove (by norm_num))
  have hinv := Compose.sleepy_invariant_before hrun hnc hb0 hsvc hfball
  have hinvT := Compose.sleepy_invariant_before hrun hnc hT0 (service.mono hTs)
    fun s d hd h => hfball s d hd (h.trans hTb)
  have hfb : ∀ q : Nat, Q.params.ts q + Q.params.Δ ≤ min Q.start Q.run.2.horizon →
      Q.trace.FaultBound (honestKeys S Q.run.2) (Q.params.ts q + Q.params.Δ) :=
    fun q h => hfball q _ (by simp) h
  -- the tip at the end-of-`T` cut
  have hi : (chainTrace Q.run.2).endCut Q.T ≤ Q.run.2.events.length := Nat.findGreatest_le _
  obtain ⟨hcut, -, hnow⟩ := ready_read_cut S Q.run.2 Q.hn Q.valid (c := Q.duration)
    ((by unfold Regimes.catchUp; positivity : (0 : Time) ≤ Regimes.catchUp Q.params).trans
      (outage_duration_supply S A V Q)) hT0 hTh hv
  have hŵ := honest_ownKey (S := S) hv.1
  have hread : (chainTrace Q.run.2).readAt .confirmed v Q.T <+:
      chainTo (Q.trace.state (Q.run.2.ownKey v)
        (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut Q.T))).fg.blocks
        ((Regimes.readAfter Q.trace (Q.run.2.ownKey v)
          (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut Q.T)) Q.T).slot + 1)
        (Regimes.readAfter Q.trace (Q.run.2.ownKey v)
          (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut Q.T)) Q.T) := by
    change (chainTrace Q.run.2).read .confirmed v ((chainTrace Q.run.2).endCut Q.T) <+: _
    rw [read_eq_out S Q.run.2 Q.hn, outOf,
      simTrace_state S Q.run.2 Q.hn Q.valid v hv.1 _ hi]
    dsimp only
    rw [hnow]
    exact List.prefix_refl _
  obtain ⟨htipU, hchain⟩ : Regimes.readAfter Q.trace (Q.run.2.ownKey v)
        (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut Q.T)) Q.T ∈
          Q.trace.HonestBlocks (honestKeys S Q.run.2) ∧
      Compose.OnOriginChainWithin Q.trace (honestKeys S Q.run.2)
        (Regimes.readAfter Q.trace (Q.run.2.ownKey v)
          (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut Q.T)) Q.T) Q.T :=
    Compose.confirmed_read_on_chain_upTo hinvT hrun hnc hŵ hcut.1 Q.T
  by_cases htg : (Regimes.readAfter Q.trace (Q.run.2.ownKey v)
      (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut Q.T)) Q.T).root = Q.params.genesisRoot
  · -- a genesis tip: every honest vote extends it
    refine ⟨⟨_, _, 0, hread, rfl, Or.inl ⟨htg, rfl⟩, fun x hx i e hve _ _ => ?_,
      fun w _ hg => absurd htg hg, fun w _ hg => absurd htg hg⟩⟩
    obtain ⟨ℓx, hcx, hex⟩ := hve
    obtain ⟨⟨Hd, hHd, hHdr, -⟩, -⟩ := Compose.cast_head_fcRoot hr hx ⟨hcx, hex⟩
    have hHdU := (SA.frameIn_of_callAt hr hx hcx).2 hHd
    refine ⟨Hd, hHdU, hHdr, ?_⟩
    rw [Compose.honest_eq_genesis hrun hU htipU htg]
    exact (Compose.honest_genesis_anc hrun hHdU).2
  obtain ⟨C, σ, hCw, htC⟩ := (Compose.onOriginChainWithin_iff.1 hchain).resolve_left htg
  have hCU : C ∈ Q.trace.HonestBlocks (honestKeys S Q.run.2) := by
    by_cases he : Regimes.readAfter Q.trace (Q.run.2.ownKey v)
        (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut Q.T)) Q.T = C
    · exact he ▸ htipU
    · exact (htC.mem he).2
  obtain ⟨hσk, hkj⟩ := Compose.armed_label_lt hT0 hlag (hCw.ts_le hrun)
  have hCb := hCw.mono hTb
  obtain ⟨hg₁, -⟩ := Compose.coverLabel_gates (sp := Q.params) (b₀ := Q.start) (by
    have : (0 : Time) ≤ (4 * Q.params.k + 4) * Q.params.Δ := by positivity
    nlinarith)
  -- the holders are honest and awake on the no-sleep window
  have hhold : ∀ w ∈ Q.holders,
      (Sys (goldilocks S) V).outageStart (K S A) Q.start Q.run ≤
        (Sys (goldilocks S) V).outageEnd (K S A) Q.stop Q.run →
      w ∈ honestKeys S Q.run.2 ∧ ∀ u, (Sys (goldilocks S) V).outageStart (K S A) Q.start Q.run ≤ u →
        u ≤ (Sys (goldilocks S) V).outageEnd (K S A) Q.stop Q.run → Q.trace.awake w u := by
    intro w hw haz
    obtain ⟨hwh, hwa⟩ := Finset.mem_filter.1 hw
    refine ⟨(mem_honestKeys_iff S Q.run.2 w).mpr hwh, fun u hu₁ hu₂ => ?_⟩
    rw [simTrace_awake_iff, awakeAt_iff]
    exact ⟨hns _ hwh _ le_rfl haz hwa u hu₁ hu₂, ha0.trans hu₁, hu₂.trans (min_le_right _ _)⟩
  have hts1 : Q.params.ts ((Compose.coverLabel Q.params Q.start : Int) - Q.params.k) ≤
      Q.params.ts ((Compose.coverLabel Q.params Q.start : Int) - Q.params.k + 1) :=
    (SA.ts_le_iff _).2 (by omega)
  have hjI : ((Compose.coverLabel Q.params Q.start - 1 : Nat) : Int) =
      (Compose.coverLabel Q.params Q.start : Int) - 1 := by omega
  refine ⟨⟨_, C, σ, hread, rfl, Or.inr ⟨htC, hCw, hσk⟩, fun x hx i e hve hσe hej => ?_,
    fun w hw hCg hhz => ?_, fun w hw hCg hhz => ?_⟩⟩
  · -- S-vote
    obtain ⟨ℓx, hcx, hex⟩ := hve
    have hvt := (Compose.cast_head_fcRoot hr hx ⟨hcx, hex⟩).2
    have hts := (SA.ts_le_iff Q.params).2 (show (e.msg.slot : Int) ≤ Compose.coverLabel Q.params
      Q.start by exact_mod_cast hej)
    have hih : Q.trace.time i ≤ Q.run.2.horizon :=
      simTrace_labelled_time_le S Q.run.2 Q.hn Q.valid (by
        rw [(Compose.projAC_callAt.1 hcx).2]; simp)
    exact hinv.vote_extends C σ hCb x hx i e ⟨ℓx, hcx, hex⟩
      (le_min (by change Q.trace.time i ≤ _ at hvt; linarith) hih) hσe
  · -- O1 at `j₀ − 1`
    have hsz := hzj (2 * Q.params.Δ) (by linarith) hhz
    have hsz' : Q.params.ts ((Compose.coverLabel Q.params Q.start - 1 : Nat) : Int) +
        6 * Q.params.Δ = Q.params.ts (Compose.coverLabel Q.params Q.start) + 2 * Q.params.Δ := by
      rw [hjI]; simp only [SA.SAParams.ts]; ring
    have hjk : Q.params.ts ((Compose.coverLabel Q.params Q.start : Int) - Q.params.k) ≤
        Q.params.ts (Compose.coverLabel Q.params Q.start) := (SA.ts_le_iff _).2 (by omega)
    obtain ⟨hwH, haw⟩ := hhold w hw (by linarith)
    have h1 : Q.params.k ≤ Compose.coverLabel Q.params Q.start - 1 := by omega
    have h2 : σ + Q.params.k ≤ Compose.coverLabel Q.params Q.start - 1 := by omega
    have h3 : (Sys (goldilocks S) V).outageStart (K S A) Q.start Q.run ≤
        Q.params.ts (((Compose.coverLabel Q.params Q.start - 1 : Nat) : Int) - Q.params.k + 1) := by
      rw [hjI, show (Compose.coverLabel Q.params Q.start : Int) - 1 - Q.params.k + 1 =
        (Compose.coverLabel Q.params Q.start : Int) - Q.params.k by ring]
      exact haj
    exact Compose.armed_lock_formed hrun hnc hinv hsvc.ac hfb hCb hCU hCg hwH haw
      (s := Compose.coverLabel Q.params Q.start - 1) h1 h2 h3 (hsz' ▸ hsz)
      (hsz' ▸ le_min hg₁ hhz)
  · -- O1 at `j₀`
    have hsz := hzj (6 * Q.params.Δ) le_rfl hhz
    have hjk : Q.params.ts ((Compose.coverLabel Q.params Q.start : Int) - Q.params.k) ≤
        Q.params.ts (Compose.coverLabel Q.params Q.start) := (SA.ts_le_iff _).2 (by omega)
    obtain ⟨hwH, haw⟩ := hhold w hw (by linarith)
    have h1 : Q.params.k ≤ Compose.coverLabel Q.params Q.start := by omega
    have h2 : σ + Q.params.k ≤ Compose.coverLabel Q.params Q.start := by omega
    -- the opponents: the faulty validators and the late wakers, as keys
    let Opp : Set (Fin (Fintype.card V)) := {x | Q.run.2.key x ∈ Q.run.2.point.faulty ∪
      Q.run.2.point.lateWakers ((Sys (goldilocks S) V).outageStart (K S A) Q.start Q.run)
        ((Sys (goldilocks S) V).outageEnd (K S A) Q.stop Q.run)}
    have hF : (honestKeys S Q.run.2)ᶜ ⊆ Opp := by
      intro x hx
      refine Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, ?_⟩)
      exact fun h => hx ((mem_honestKeys_iff S Q.run.2 x).mpr h)
    have hopp : 2 * Opp.ncard < Q.params.n := by
      have heq : Opp = Q.run.2.key ⁻¹' (↑(Q.run.2.point.faulty ∪ Q.run.2.point.lateWakers
          ((Sys (goldilocks S) V).outageStart (K S A) Q.start Q.run)
          ((Sys (goldilocks S) V).outageEnd (K S A) Q.stop Q.run)) : Set V) := by
        ext x; simp [Opp]
      rw [heq, Set.ncard_preimage_of_injective_subset_range Q.run.2.key.injective
        (by simp [Q.run.2.key.surjective.range_eq]), Set.ncard_coe_finset]
      exact EnvPoint.CohortOn.two_mul_lt hcoh
    have hcast : ∀ x ∈ honestKeys S Q.run.2, ∀ j e, SA.VoteAt Q.trace.projAC x j e →
        e.msg.slot = Compose.coverLabel Q.params Q.start + 1 →
        Q.trace.time j ≤ Q.params.ts (Compose.coverLabel Q.params Q.start) + 6 * Q.params.Δ →
        x ∈ Q.holders ∨ x ∈ Opp := by
      intro x hx j e hve hes hjt
      obtain ⟨ℓx, hcx, hex⟩ := hve
      have hxs := (SA.castAt_spec hr hx ⟨hcx, hex⟩).2.1
      have hjs : Q.params.ts ((Compose.coverLabel Q.params Q.start + 1 : Nat) : Int) ≤
          Q.trace.time j :=
        (SA.ts_le_iff_le_slot _ (hrun.time_nonneg j) _).2 (by
          change ((Compose.coverLabel Q.params Q.start + 1 : Nat) : Int) ≤
            (Q.params.slot (Q.trace.time j) : Int)
          rw [← hes]; exact_mod_cast hxs.le)
      have hjk' : Q.params.ts ((Compose.coverLabel Q.params Q.start : Int) - Q.params.k) ≤
          Q.params.ts ((Compose.coverLabel Q.params Q.start + 1 : Nat) : Int) :=
        (SA.ts_le_iff _).2 (by omega)
      have haw' := hrun.awake_of_call x hx j ⟨_, Compose.projAC_callAt.1 hcx⟩
      rw [simTrace_awake_iff, awakeAt_iff] at haw'
      by_cases hxa : Q.run.2.key x ∈
          Q.run.2.point.awakeAt ((Sys (goldilocks S) V).outageStart (K S A) Q.start Q.run)
      · exact Or.inl hxa
      · refine Or.inr (Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨?_, hxa⟩))
        exact Finset.mem_filter.2 ⟨(mem_honestKeys_iff S Q.run.2 x).mp hx,
          _, by linarith, by linarith, haw'.1⟩
    exact Compose.armed_lock_cover hrun hnc hinv hsvc.ac hfb hCb hCg hwH haw
      (s := Compose.coverLabel Q.params Q.start) h1 h2 (haj.trans hts1) hsz
      (le_min hg₁ (by linarith)) Q.holders Opp hF hopp hcast

end Consensus.Goldilocks.Obligations

end

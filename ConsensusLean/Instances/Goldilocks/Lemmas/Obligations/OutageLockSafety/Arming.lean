module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageArming
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageReader
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Induction
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Reader
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Record
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Lemmas.Model.Constant

public section

/-! # Outage lock safety: the arming adapter and the query-level headers

`outageLockPremises_of_arming` builds the trace-level premise package of the lock module from an
outage query, its pre-`b₀` service and an armed ready source (`OutageArming`, with `P` its
origin). The post-GST pool delivery `OutageLockOthers.pg` is discharged by
`outage_pool_delivery` (its premise `b₁ ≤ t_m + Δ` is paid by `r ≤ m`, the restored label).
It proves the arithmetic N1–N6 from
`OutageTimes` and the accepted numbers (lag `4k + 6`, no-sleep `4k + 6`, budget
`4k − 5`), the Sleepy invariant and service up to `b₀`, the fault bounds from `EtaSleepyOn`, and
the cohort premises from `NoSleepOn` and `CohortOn` through the key transport. The arming fields
are used as they are. Two inputs are hypotheses of the adapter: `Q.T ≤ horizon` (as for
`outage_arming`) and `Q.start ≤ horizon`; beyond the horizon the reader conclusion is vacuous
(the degenerate case).

The headers (`outage_locks`, `outage_reader_locks`, `outage_reader_frame`,
`outage_record_above_from`) take the step `OutageS5Step` as a
hypothesis. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **A restart of a node awake on `[a, z]`** at a time `≤ z` is by `a + Δ`: the node ticks at the
first public time from `a`, so the restart (its first call after a sleep) cannot be later. -/
theorem restart_le_of_awake (hrun : GoldilocksRun proposer dg H tr) {x : Fin sp.n} (hx : x ∈ H)
    {a z : Time} (ha0 : 0 ≤ a) (haw : ∀ u, a ≤ u → u ≤ z → tr.awake x u) {k : Nat}
    (hk : tr.RestartAt x k) (hkz : tr.time k ≤ z) : tr.time k ≤ a + sp.Δ := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  by_contra hlt
  push Not at hlt
  set p := a + (-a) % sp.Δ with hp
  have hm0 : 0 ≤ (-a) % sp.Δ := Int.emod_nonneg _ hΔ.ne'
  have hm1 : (-a) % sp.Δ < sp.Δ := Int.emod_lt_of_pos _ hΔ
  have hpub : sp.toParams.IsPublic p :=
    ⟨-((-a) / sp.Δ), by rw [hp, Int.emod_def]; ring⟩
  obtain ⟨j, y, hg⟩ :=
    hrun.tick_of_awake x hx p (by linarith) hpub (haw p (by linarith) (by linarith))
  obtain ⟨hne, hks, -⟩ := hg
  obtain ⟨hn0, ht0, -, -, hl0⟩ := hks 0 (List.length_pos_of_ne_nil hne)
  simp only [Nat.add_zero] at hn0 ht0 hl0
  have hcall : tr.IsCall x j := ⟨_, hn0, hl0⟩
  obtain ⟨u, -, huk, hnaw, hcalls⟩ := hrun.sleep_of_restart x hx k hk
  have hjk : j < k := by
    by_contra h
    have := hrun.time_mono (show k ≤ j by omega)
    linarith
  have hpu := hcalls j hjk hcall
  exact hnaw (haw u (by linarith) (by linarith))

end Consensus.Goldilocks.Compose

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation
open Blocks Shape
variable (S : Setup) (A : ContractAssumptions S) (V : Type)
  [Fintype V] [DecidableEq V]

/-- The non-arming network input of the lock module, in query form: post-GST pool delivery.
An honest update of a label whose last cast time is at or after the stop holds every honest vote
of that slot. -/
structure OutageLockOthers (Q : OutageQuery S A V) : Prop where
  pg : ∀ w ∈ honestKeys ⟨S, stock⟩ Q.run.2, ∀ c m ℓ, SA.UpdateAt Q.trace.projAC w c m ℓ →
    Q.stop ≤ Q.params.ts m + Q.params.Δ →
    ∀ x ∈ honestKeys ⟨S, stock⟩ Q.run.2, ∀ i e, SA.VoteAt Q.trace.projAC x i e → e.msg.slot = m →
      e.msg ∈ (Q.trace.state w c).ac.pool m

variable {S A V}

/-- **PG is discharged** by the engine's partial synchrony from the stop
(`outage_pool_delivery`). -/
theorem outage_lock_others (Q : OutageQuery S A V) : OutageLockOthers S A V Q :=
  ⟨outage_pool_delivery S A V Q⟩

/-- The cohort's late wakers, as keys. -/
noncomputable def OutageQuery.lateKeys (Q : OutageQuery S A V) : Set (Fin (Fintype.card V)) :=
  {x | Q.run.2.key x ∈ Q.run.2.point.lateWakers
    ((Sys (goldilocks S) V).outageStart (K S A) Q.start Q.run)
    ((Sys (goldilocks S) V).outageEnd (K S A) Q.stop Q.run)}

/-- The first restored label: the least `r` with `b₁ ≤ t_r + Δ`. -/
noncomputable def OutageQuery.restoredLabel (Q : OutageQuery S A V) : Nat := by
  classical
  exact if h : ∃ s : Nat, Q.stop ≤ Q.params.ts s + Q.params.Δ then Nat.find h else 0

/-- The numbers of an outage query in node units: the gates of the cover label, the restored
label in `(j₀, j₀ + k]`, the budget and the no-sleep window. -/
private theorem query_numbers (Q : OutageQuery S A V) :
    let j₀ := Compose.coverLabel Q.params Q.start
    Q.params.ts j₀ + 2 * Q.params.Δ ≤ Q.start ∧
      Q.start < Q.params.ts (j₀ + 1 : Nat) + 2 * Q.params.Δ ∧
      Q.stop - Q.start ≤ (4 * (Q.params.k : Time) - 5) * Q.params.Δ ∧
      Q.start ≤ Q.stop ∧ Q.stop ≤ Q.params.ts (j₀ + Q.params.k : Nat) + Q.params.Δ ∧
      Q.params.ts (j₀ : Nat) + Q.params.Δ < Q.stop ∧
      (∀ t, t ≤ Q.params.ts (j₀ + Q.params.k : Nat) + Q.params.Δ → t ≤ Q.run.2.horizon →
        t ≤ (Sys (goldilocks S) V).outageEnd (K S A) Q.stop Q.run) := by
  intro j₀
  obtain ⟨⟨hT, -, hb01, hbud⟩, -⟩ := Q.outage
  have hlag := outage_node_lag S A V Q
  have hd : (1 : Time) ≤ Q.run.1.ΔAC := Q.run.1.ΔAC_pos
  have hk2 : (2 : Int) ≤ S.k := by exact_mod_cast S.two_le_k
  obtain ⟨hg₁, hg₂⟩ := Compose.coverLabel_gates (sp := Q.params) (b₀ := Q.start) (by
    have : (0 : Time) ≤ (4 * Q.params.k + 4) * Q.params.Δ := by positivity
    have hΔ := Q.params.toParams.hΔ
    linarith)
  have hbcast : ((4 * S.k - 5 : Nat) : Int) = 4 * (S.k : Int) - 5 := by omega
  have hb : ((4 * S.k - 5 : Nat) : Int) ≤ 4 * (S.k : Int) - 5 := hbcast.le
  change Q.stop ≤ Q.start + ((4 * S.k - 5 : Nat) : Int) * Q.run.1.ΔAC at hbud
  have hmul := mul_le_mul_of_nonneg_right hb (le_of_lt Q.run.1.ΔAC_pos)
  change 4 * Q.run.1.ΔAC * (j₀ : Int) + 2 * Q.run.1.ΔAC ≤ Q.start at hg₁
  change Q.start < 4 * Q.run.1.ΔAC * (j₀ : Int) + 6 * Q.run.1.ΔAC at hg₂
  change 4 * Q.run.1.ΔAC * (j₀ : Int) + 2 * Q.run.1.ΔAC ≤ Q.start ∧
    Q.start < 4 * Q.run.1.ΔAC * ((j₀ + 1 : Nat) : Int) + 2 * Q.run.1.ΔAC ∧
    Q.stop - Q.start ≤ (4 * (S.k : Time) - 5) * Q.run.1.ΔAC ∧ Q.start ≤ Q.stop ∧
    Q.stop ≤ 4 * Q.run.1.ΔAC * ((j₀ + S.k : Nat) : Int) + Q.run.1.ΔAC ∧
    4 * Q.run.1.ΔAC * ((j₀ : Nat) : Int) + Q.run.1.ΔAC < Q.stop ∧
    ∀ t, t ≤ 4 * Q.run.1.ΔAC * ((j₀ + S.k : Nat) : Int) + Q.run.1.ΔAC →
      t ≤ Q.run.2.horizon →
      t ≤ min (Q.stop + ((4 * S.k + 6 : Nat) : Int) * Q.run.1.ΔAC) Q.run.2.horizon
  push_cast
  refine ⟨hg₁, by linarith, by linarith, hb01, by linarith, by linarith,
    fun t ht hth => le_min ?_ hth⟩
  linarith

/-- The restored label is the least `r` with `b₁ ≤ t_r + Δ`. -/
theorem restoredLabel_spec (Q : OutageQuery S A V) :
    Q.stop ≤ Q.params.ts Q.restoredLabel + Q.params.Δ ∧
      ∀ s : Nat, Q.stop ≤ Q.params.ts s + Q.params.Δ → Q.restoredLabel ≤ s := by
  classical
  obtain ⟨-, -, -, -, hK, -, -⟩ := query_numbers Q
  have h : ∃ s : Nat, Q.stop ≤ Q.params.ts s + Q.params.Δ := ⟨_, hK⟩
  unfold OutageQuery.restoredLabel
  simp only [h, ↓reduceDIte]
  exact ⟨Nat.find_spec h, fun s hs => Nat.find_min' h hs⟩

/-- The protected origin is an honest block, genesis or an origin within `b₀`. -/
private theorem origin_facts (Q : OutageQuery S A V)
    (service : Compose.SleepyServiceBefore Q.trace (honestKeys ⟨S, stock⟩ Q.run.2) Q.params.Δ
        Q.start)
    {v : V} (hv : Q.run.2.point.Ready Q.duration v Q.T) (hTh : Q.T ≤ Q.run.2.horizon)
    (ar : OutageArming S A V Q v) :
    ar.tip ∈ Q.trace.HonestBlocks (honestKeys ⟨S, stock⟩ Q.run.2) ∧
      Anc (Q.trace.HonestBlocks (honestKeys ⟨S, stock⟩ Q.run.2)) ar.tip ar.origin ∧
      ar.origin ∈ Q.trace.HonestBlocks (honestKeys ⟨S, stock⟩ Q.run.2) := by
  obtain ⟨⟨hT0, -, -, -⟩, -, heta, -, -⟩ := Q.outage
  have hrun := simTrace_goldilocksRun S Q.run.2 Q.hn Q.constant Q.valid
  have hnc := noCollRun_simTrace S Q.run.2 Q.hn Q.constant Q.valid Q.noCollision
  have hlag := outage_node_lag S A V Q
  have hΔ := Q.params.toParams.hΔ
  have hTs : Q.T ≤ Q.start := by
    have : (0 : Time) ≤ (4 * Q.params.k + 6) * Q.params.Δ := by positivity
    linarith
  have hfb : ∀ s : Nat, ∀ d ∈ ({0, Q.params.Δ, 2 * Q.params.Δ} : Set Time),
      Q.params.ts s + d ≤ Q.T →
        Q.trace.FaultBound (honestKeys ⟨S, stock⟩ Q.run.2) (Q.params.ts s + d) :=
    sleepy_faultBound S Q.run.2 Q.hn Q.constant Q.valid
      (W := (Sys (goldilocks S) V).aheadDur (K S A) Q.run) hTh
      ((Q.run.2.point.sleepyOn_iff Q.constant _ _ _ _ _).mpr fun t ht htb =>
        half_ready_of_duration V Q.run.2.point (outage_duration_supply S A V Q)
          (((Q.run.2.point.etaSleepyOn_iff Q.constant _ _ _ _ _ _).mp heta
            t ht (htb.trans hTh)).readyAbove (by change (0 : ℚ) ≤ 1 / 2; norm_num)))
  have hinvT := Compose.sleepy_invariant_before hrun hnc hT0 (service.mono hTs) hfb rfl
  obtain ⟨hcut, -, -⟩ := ready_read_cut S Q.run.2 Q.hn Q.constant Q.valid (c := Q.duration)
    ((by unfold Regimes.catchUp; positivity : (0 : Time) ≤ Regimes.catchUp Q.params).trans
      (outage_duration_supply S A V Q)) hT0 hTh hv
  have hŵ := honest_ownKey (S := ⟨S, stock⟩)
    ((Q.run.2.point.honestAt_iff_zero Q.constant _ _).mp hv.1)
  have htipU : Regimes.readAfter Q.trace (Q.run.2.ownKey v)
      (cutMap ⟨S, stock⟩ Q.run.2 Q.hn ((chainTrace Q.run.2).endCut Q.T)) Q.T ∈
        Q.trace.HonestBlocks (honestKeys ⟨S, stock⟩ Q.run.2) :=
    (Compose.confirmed_read_on_chain_upTo hinvT hrun hnc hŵ hcut.1 Q.T).1
  rw [← ar.tip_eq] at htipU
  rcases ar.armed with ⟨-, ho⟩ | ⟨htC, -, -⟩
  · rw [ho]; exact ⟨htipU, .refl, htipU⟩
  · refine ⟨htipU, htC, ?_⟩
    by_cases he : ar.tip = ar.origin
    · exact he ▸ htipU
    · exact (htC.mem he).2

open Classical in
/-- **The adapter**: the premise package of the lock module from an armed ready source,
with `P` its origin, `A₀` the holders, `W` the late wakers, `j₀` the cover label and `r` the
restored label. -/
noncomputable def outageLockPremises_of_arming (Q : OutageQuery S A V)
    (service : Compose.SleepyServiceBefore Q.trace (honestKeys ⟨S, stock⟩ Q.run.2) Q.params.Δ
        Q.start)
    {v : V} (hv : Q.run.2.point.Ready Q.duration v Q.T) (hTh : Q.T ≤ Q.run.2.horizon)
    (hsh : Q.start ≤ Q.run.2.horizon) (ar : OutageArming S A V Q v) :
    Compose.OutageLockPremises Q.trace (honestKeys ⟨S, stock⟩ Q.run.2)
        (runProposer ⟨S, stock⟩ Q.run.2 Q.hn)
      (digestOf ⟨S, stock⟩ Q.run.2) :=
  have hrun := simTrace_goldilocksRun S Q.run.2 Q.hn Q.constant Q.valid
  have hnc := noCollRun_simTrace S Q.run.2 Q.hn Q.constant Q.valid Q.noCollision
  have hnum := query_numbers Q
  have hr := restoredLabel_spec Q
  have hΔ := Q.params.toParams.hΔ
  have hk2 := Q.params.two_le_k
  have hT0 : 0 ≤ Q.T := Q.outage.times.1
  have hlag := outage_node_lag S A V Q
  have hTs : Q.T ≤ Q.start := by
    have : (0 : Time) ≤ (4 * Q.params.k + 6) * Q.params.Δ := by positivity
    linarith
  have hhalf : Q.run.2.point.SleepyOn (1 / 2) (Regimes.catchUp Q.params)
      ((Sys (goldilocks S) V).aheadDur (K S A) Q.run) 0 Q.run.2.horizon :=
    (Q.run.2.point.sleepyOn_iff Q.constant _ _ _ _ _).mpr fun t ht htb =>
      half_ready_of_duration V Q.run.2.point (outage_duration_supply S A V Q)
        (((Q.run.2.point.etaSleepyOn_iff Q.constant _ _ _ _ _ _).mp Q.outage.etaSleepy
          t ht htb).readyAbove (by change (0 : ℚ) ≤ 1 / 2; norm_num))
  have hcallh : ∀ {y : Fin (Fintype.card V)} {i : Nat}, Q.trace.IsCall y i →
      Q.trace.time i ≤ Q.run.2.horizon := fun {_ _} h => by
    obtain ⟨l, hl⟩ := h
    exact simTrace_labelled_time_le ⟨S, stock⟩ Q.run.2 Q.hn Q.valid (by rw [hl.2]; simp)
  have hwin := outage_window_cover S A V Q
  have hP := origin_facts Q service hv hTh ar
  { b₀ := Q.start
    b₁ := Q.stop
    a := (Sys (goldilocks S) V).outageStart (K S A) Q.start Q.run
    z := (Sys (goldilocks S) V).outageEnd (K S A) Q.stop Q.run
    P := ar.origin
    σ := if ar.origin.root = Q.params.genesisRoot then 0 else ar.σ
    j₀ := Compose.coverLabel Q.params Q.start
    r := Q.restoredLabel
    A₀ := Q.holders
    W := Q.lateKeys
    hrun := hrun
    hnc := hnc
    hj₀ := ⟨hnum.1, hnum.2.1⟩
    hr := hr
    hσ := by
      split_ifs with hg
      · have := (Compose.armed_label_lt (σ := 0) hT0 hlag
          (by simp only [SA.SAParams.ts]; simpa using hT0)).2
        change 0 + Q.params.k < _
        omega
      · rcases ar.armed with ⟨htg, ho⟩ | ⟨-, -, hσk⟩
        · exact absurd (ho ▸ htg) hg
        · exact hσk
    hrk := by
      obtain ⟨-, -, -, -, hK, hjs, -⟩ := hnum
      refine ⟨?_, hr.2 _ hK⟩
      by_contra h
      have := (SA.ts_le_iff Q.params).2
        (show (Q.restoredLabel : Int) ≤ (Compose.coverLabel Q.params Q.start : Nat) by omega)
      linarith [hr.1]
    hgap := hnum.2.2.1
    hb₀ := hnum.2.2.2.1
    hP := by
      refine ⟨hP.2.2, ?_⟩
      split_ifs with hg
      · exact Or.inl hg
      · rcases ar.armed with ⟨htg, ho⟩ | ⟨-, hCw, -⟩
        · exact absurd (ho ▸ htg) hg
        · exact Or.inr (hCw.mono hTs)
    hpre := Compose.sleepy_invariant_before hrun hnc (hT0.trans hTs) service
      (sleepy_faultBound S Q.run.2 Q.hn Q.constant Q.valid hsh
        (W := (Sys (goldilocks S) V).aheadDur (K S A) Q.run)
        ((Q.run.2.point.sleepyOn_iff Q.constant _ _ _ 0 _).mpr fun t ht htb =>
          (Q.run.2.point.sleepyOn_iff Q.constant _ _ _ _ _).mp hhalf t ht (htb.trans hsh))) rfl
    hpreSvc := service
    hFB := fun s ⟨_, _, _, hc, hle⟩ =>
      sleepy_faultBound S Q.run.2 Q.hn Q.constant Q.valid le_rfl hhalf s _ (by simp)
        (hle.trans (hcallh hc))
    hA₀ := fun x hx => (mem_honestKeys_iff ⟨S, stock⟩ Q.run.2 x).mpr
      ((Q.run.2.point.honestAt_iff_zero Q.constant _ _).mp
        (Finset.mem_sdiff.mp (Finset.mem_filter.1 (OutageQuery.mem_holders.1 hx)).1).2)
    hW := ⟨fun x hx => (mem_honestKeys_iff ⟨S, stock⟩ Q.run.2 x).mpr
        (by
          obtain ⟨_, t, _, _, hh, _⟩ := Finset.mem_filter.1 (Finset.mem_sdiff.1 hx).1
          exact (Q.run.2.point.honestAt_iff_zero Q.constant _ t).mp hh),
      Set.disjoint_left.2 fun _ h₁ h₂ => (Finset.mem_sdiff.1 h₂).2 (OutageQuery.mem_holders.1 h₁)⟩
    hcohort := by
      have heq : (honestKeys ⟨S, stock⟩ Q.run.2)ᶜ ∪ Q.lateKeys = Q.run.2.key ⁻¹'
          (↑(Q.run.2.point.faultyAt 0 ∪ Q.run.2.point.lateWakers
            ((Sys (goldilocks S) V).outageStart (K S A) Q.start Q.run)
            ((Sys (goldilocks S) V).outageEnd (K S A) Q.stop Q.run)) : Set V) := by
        ext x
        simp [OutageQuery.lateKeys, mem_honestKeys_iff ⟨S, stock⟩ Q.run.2]
        exact Iff.rfl
      have hA : Q.holders = Q.run.2.key ⁻¹' (↑(Q.run.2.point.awakeAt
          ((Sys (goldilocks S) V).outageStart (K S A) Q.start Q.run)) : Set V) := by
        ext x; simp [OutageQuery.mem_holders]
      rw [heq, hA, Set.ncard_preimage_of_injective_subset_range Q.run.2.key.injective
          (by simp [Q.run.2.key.surjective.range_eq]),
        Set.ncard_preimage_of_injective_subset_range Q.run.2.key.injective
          (by simp [Q.run.2.key.surjective.range_eq]), Set.ncard_coe_finset,
        Set.ncard_coe_finset]
      have hc := Q.outage.cohort
      change (Q.run.2.point.retain _).CohortOn _ _ at hc
      rw [Q.run.2.point.retain_eq Q.constant] at hc
      unfold EnvPoint.CohortOn at hc
      rw [Q.constant _] at hc
      exact hc
    hawake := fun x hx t hat htz haw => by
      rw [simTrace_awake_iff ⟨S, stock⟩ Q.run.2 Q.hn, awakeAt_iff ⟨S, stock⟩ Q.run.2 Q.hn] at haw
      by_cases hxa : Q.run.2.key x ∈
          Q.run.2.point.awakeAt ((Sys (goldilocks S) V).outageStart (K S A) Q.start Q.run)
      · exact Or.inl (OutageQuery.mem_holders.2 hxa)
      · exact Or.inr (Finset.mem_sdiff.2 ⟨Finset.mem_filter.2
          ⟨Finset.mem_univ _, t, hat, htz,
            (Q.run.2.point.honestAt_iff_zero Q.constant _ _).mpr
              ((mem_honestKeys_iff ⟨S, stock⟩ Q.run.2 x).mp hx), haw.1⟩, hxa⟩)
    hA₀awake := fun x hx t hat htz => by
      obtain ⟨hxh, hxa⟩ := Finset.mem_filter.1 (OutageQuery.mem_holders.1 hx)
      have hxh := (Q.run.2.point.honestAt_iff_zero Q.constant _ _).mp
        (Finset.mem_sdiff.mp hxh).2
      have hns := Q.outage.noSleep
      change (Q.run.2.point.retain _).NoSleepOn _ _ at hns
      rw [Q.run.2.point.retain_eq Q.constant] at hns
      rw [simTrace_awake_iff ⟨S, stock⟩ Q.run.2 Q.hn, awakeAt_iff ⟨S, stock⟩ Q.run.2 Q.hn]
      exact ⟨hns _ ((Q.run.2.point.honestAt_iff_zero Q.constant _ _).mpr hxh)
        _ le_rfl (hat.trans htz) hxa t hat htz,
        hwin.1.trans hat, htz.trans (min_le_right _ _)⟩
    hA₀join := fun x hx k hk hkz => by
      obtain ⟨hxh, hxa⟩ := Finset.mem_filter.1 (OutageQuery.mem_holders.1 hx)
      have hxh := (Q.run.2.point.honestAt_iff_zero Q.constant _ _).mp
        (Finset.mem_sdiff.mp hxh).2
      have hns := Q.outage.noSleep
      change (Q.run.2.point.retain _).NoSleepOn _ _ at hns
      rw [Q.run.2.point.retain_eq Q.constant] at hns
      refine Compose.restart_le_of_awake hrun ((mem_honestKeys_iff ⟨S, stock⟩ Q.run.2 x).mpr hxh)
        hwin.1 (fun u hau huz => ?_) hk hkz
      rw [simTrace_awake_iff ⟨S, stock⟩ Q.run.2 Q.hn, awakeAt_iff ⟨S, stock⟩ Q.run.2 Q.hn]
      exact ⟨hns _ ((Q.run.2.point.honestAt_iff_zero Q.constant _ _).mpr hxh)
        _ le_rfl (hau.trans huz) hxa u hau huz,
        hwin.1.trans hau, huz.trans (min_le_right _ _)⟩
    ha := by
      have h := hwin.2.1
      have hj : (Q.params.k : Int) < Compose.coverLabel Q.params Q.start :=
        by exact_mod_cast (Compose.armed_label_lt (σ := 0) hT0 hlag
          (by simp only [SA.SAParams.ts]; simpa using hT0)).2
      simp only [SA.SAParams.ts] at h ⊢
      have : (0 : Time) ≤ (Q.params.k : Int) - 1 := by linarith
      linarith [mul_nonneg this Q.params.toParams.hΔ.le]
    hz := fun t ht ⟨_, _, _, hc, hle⟩ => hnum.2.2.2.2.2.2 t ht (hle.trans (hcallh hc))
    lockPrev := fun x hx hg ⟨_, _, _, hc, hle⟩ => by
      obtain ⟨c, ℓ, hu, hb⟩ := ar.lockPrev x hx hg (hle.trans (hcallh hc))
      exact ⟨c, ℓ, hu, Compose.prevBase_iff.2 hb⟩
    lockCover := fun x hx hg ⟨_, _, _, hc, hle⟩ => by
      obtain ⟨c, ℓ, hu, hfirst, hcond⟩ := ar.lockCover x hx hg (hle.trans (hcallh hc))
      exact ⟨c, ℓ, hu, hfirst, fun hF hVA hN => Compose.coverBase_iff.2 (hcond hF hVA hN)⟩
    PG := fun w hw c m ℓ hu hrm x hx i e hve hes =>
      (outage_lock_others Q).pg w hw c m ℓ hu (hr.1.trans (by
        have := (SA.ts_le_iff Q.params).2 (show (Q.restoredLabel : Int) ≤ m by exact_mod_cast hrm)
        linarith)) x hx i e hve hes
    stock := rfl }

section Headers

variable (Q : OutageQuery S A V)
  (service : Compose.SleepyServiceBefore Q.trace (honestKeys ⟨S, stock⟩ Q.run.2) Q.params.Δ Q.start)
  {v : V} (hv : Q.run.2.point.Ready Q.duration v Q.T) (hTh : Q.T ≤ Q.run.2.horizon)
  (hsh : Q.start ≤ Q.run.2.horizon) (ar : OutageArming S A V Q v)

theorem outageLockPremises_of_arming_P :
    (outageLockPremises_of_arming Q service hv hTh hsh ar).P = ar.origin := by rfl

theorem outageLockPremises_of_arming_j₀ :
    (outageLockPremises_of_arming Q service hv hTh hsh ar).j₀ =
      Compose.coverLabel Q.params Q.start := by rfl

theorem outageLockPremises_of_arming_b₁ :
    (outageLockPremises_of_arming Q service hv hTh hsh ar).b₁ = Q.stop := by rfl

theorem outageLockPremises_of_arming_r :
    (outageLockPremises_of_arming Q service hv hTh hsh ar).r = Q.restoredLabel := by rfl

/-- The restored-vote step that the lock module consumes (restated cut-indexed): from the lock
invariant at `i`, the votes of cut `i` past the lock lifetime have heads compatible with the
origin. -/
abbrev OutageS5Step : Prop :=
  ∀ i, Compose.OutageLockInv (outageLockPremises_of_arming Q service hv hTh hsh ar) i →
    ∀ y ∈ honestKeys ⟨S, stock⟩ Q.run.2, ∀ e, SA.VoteAt Q.trace.projAC y i e →
      Compose.coverLabel Q.params Q.start + Q.params.k < e.msg.slot →
      Compose.VoteCompat (Q.trace.HonestBlocks (honestKeys ⟨S, stock⟩ Q.run.2)) e.msg ar.origin

/-- **The outage lock invariant at every cut** (`OutageLockInv`), given the step `OutageS5Step`. -/
theorem outage_locks (hS5 : OutageS5Step Q service hv hTh hsh ar) :
    ∀ i, Compose.OutageLockInv (outageLockPremises_of_arming Q service hv hTh hsh ar) i :=
  Compose.outage_lock_inv _ (Compose.outageS5StepAt_iff.2 hS5)

/-- **(i) at a reader** (`outage_reader_locks`): at every honest cut and time, the live
lock blocks are compatible with the read tip. -/
theorem outage_reader_locks (hS5 : OutageS5Step Q service hv hTh hsh ar) :
    ∀ y ∈ honestKeys ⟨S, stock⟩ Q.run.2, ∀ (m : Nat) (τ : Time),
      ∀ X ∈ SA.liveLockBlocks Q.params (Q.trace.state y m).ac.locks
        (Node.frame (Q.trace.state y m)) τ,
      Compatible (Q.trace.HonestBlocks (honestKeys ⟨S, stock⟩ Q.run.2)) X ar.tip :=
  fun _ hy m τ => Compose.liveLockBlocks_compatible (outage_locks Q service hv hTh hsh ar hS5)
    hy m τ (origin_facts Q service hv hTh ar).2.1

/-- **The reader frame** (`outage_reader_frame`): `fc_root` is compatible with the read
tip, and the tip, when in the frame, is below the anchor or in the full viable tree, at every
honest cut. -/
theorem outage_reader_frame (hS5 : OutageS5Step Q service hv hTh hsh ar)
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys ⟨S, stock⟩ Q.run.2) (m : Nat) (t : Time) :
    Compatible (Q.trace.HonestBlocks (honestKeys ⟨S, stock⟩ Q.run.2))
        (Node.frame (Q.trace.state y m)).fcRoot ar.tip ∧
      (ar.tip ∈ (Node.frame (Q.trace.state y m)).tree →
        (Node.frame (Q.trace.state y m)).Anc ar.tip
            (SA.getAnchor Q.params (Q.trace.state y m).ac (Node.frame (Q.trace.state y m)) t) ∨
          ar.tip ∈ (Node.frame (Q.trace.state y m)).viableTree
            (Node.frame (Q.trace.state y m)).tree) :=
  Compose.reader_frame (outage_locks Q service hv hTh hsh ar hS5) hy m t
    (origin_facts Q service hv hTh ar).2.1

/-- **(iii) + record** (`outage_record_above_from`): from a restored honest update with result
above the origin, the effective record is above the origin at every later cut. -/
theorem outage_record_above_from (hS5 : OutageS5Step Q service hv hTh hsh ar)
    {w : Fin (Fintype.card V)} (hw : w ∈ honestKeys ⟨S, stock⟩ Q.run.2) {c m : Nat}
    {ℓ : ACLabel (SA.goldilocksSA Q.params (List (FG.Att Q.params.n)) (S.ro Q.params.n))}
    (hu : SA.UpdateAt Q.trace.projAC w c m ℓ) (hrm : Q.stop ≤ Q.params.ts m + Q.params.Δ)
    {C : SA.Blk Q.params.n (List (FG.Att Q.params.n))} {CV : Set (SA.Vote Q.params.n)}
    (hR : SA.ResultAt Q.trace.projAC w c m C CV)
    (hPC : Anc (Q.trace.HonestBlocks (honestKeys ⟨S, stock⟩ Q.run.2)) ar.origin C) :
    ∀ c', c < c' → Anc (Q.trace.HonestBlocks (honestKeys ⟨S, stock⟩ Q.run.2)) ar.origin
      ((SA.lookup (Node.frame (Q.trace.state w c'))
        (Q.trace.state w c').ac.latestConfirmed).getD (Q.trace.state w c').fg.F) :=
  Compose.record_above_from (outage_locks Q service hv hTh hsh ar hS5) hw hu hR
    ((restoredLabel_spec Q).2 m hrm) hPC

end Headers

end Consensus.Goldilocks.Obligations

end

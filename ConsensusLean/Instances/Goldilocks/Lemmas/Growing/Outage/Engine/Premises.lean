module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Engine.Arming
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Schedule
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Outage under growing faults: the premise package of the lock module

`Compose.Growing.outageLockPremises_of_arming` builds the premise package
`OutageLockPremises` of the lock module on a node trace from an armed source
(`OutageArming`), with `P` its origin, `A₀` the holders, `W` their opponents, `j₀` the cover
label and `r` the first restored label. Its inputs are node facts: the run interface, collision
freedom and the committee facts, the call bound `hor`, the pre-start sleepy service and post-stop
service, both count shapes through `hor`, the window numbers, and the holder and opponent facts
on `[a, z]`. Every count reached by an honest call is within `hor`; `hA₀join` comes from the run
law (`restart_le_of_awake_at`), pool delivery from post-stop service (`outage_pool_delivery_at`),
and the Sleepy invariant up to the start from the service and the counts
(`sleepy_invariant_at`).

`outageLockPremises_of_arming_at` is the package at an outage query's data: the holders and
opponents read on the view retained through the window end, the slot committees `Q.K` with their
facts `voteK_facts`, and the query's numbers and counts. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **A restart of a node awake on `[a, z]`** and honest at `z`, at a time `≤ z`, is by `a + Δ`:
the node ticks at the first public time from `a`, so the restart (its first call after a sleep)
cannot be later. -/
theorem restart_le_of_awake_at
    {ini} (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini) {x : Fin sp.n}
    {a z : Time}
    (hx : x ∈ H z) (ha0 : 0 ≤ a) (haw : ∀ u, a ≤ u → u ≤ z → tr.awake x u) {k : Nat}
    (hk : tr.RestartAt x k) (hkz : tr.time k ≤ z) : tr.time k ≤ a + sp.Δ := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  by_contra hlt
  push Not at hlt
  set p := a + (-a) % sp.Δ with hp
  have hm0 : 0 ≤ (-a) % sp.Δ := Int.emod_nonneg _ hΔ.ne'
  have hm1 : (-a) % sp.Δ < sp.Δ := Int.emod_lt_of_pos _ hΔ
  have hpub : sp.toParams.IsPublic p :=
    ⟨-((-a) / sp.Δ), by rw [hp, Int.emod_def]; ring⟩
  obtain ⟨j, y, hg⟩ := hrun.tick_of_awake x p (hrun.antitone (by linarith) hx) (by linarith) hpub
    (haw p (by linarith) (by linarith))
  obtain ⟨hne, hks, -⟩ := hg
  obtain ⟨hn0, ht0, -, -, hl0⟩ := hks 0 (List.length_pos_of_ne_nil hne)
  simp only [Nat.add_zero] at hn0 ht0 hl0
  have hcall : tr.IsCall x j := ⟨_, hn0, hl0⟩
  obtain ⟨u, -, huk, hnaw, hcalls⟩ := hrun.sleep_of_restart x k (hrun.antitone hkz hx) hk
  have hjk : j < k := by
    by_contra h
    have := hrun.time_mono (show k ≤ j by omega)
    linarith
  have hpu := hcalls j hjk hcall
  exact hnaw (haw u (by linarith) (by linarith))

open Classical in
/-- **The lock module's premise package from an armed source** on a node trace, with `P` its
origin, `A₀` the holders, `W` their opponents, `j₀` the cover label of `b₀` and `r` the first
restored label of `b₁`. Every count reached by an honest call is within the call bound `hor`;
pool delivery is post-stop service (`outage_pool_delivery_at`). -/
noncomputable def outageLockPremises_of_arming {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {K : SA.CommitteeDict sp.n} (hKB : CommitteeFacts tr H K)
    {T b₀ b₁ hor a z : Time} {A₀ W : Set (Fin sp.n)} {r : Nat}
    (hT0 : 0 ≤ T) (hlag : T + (4 * sp.k + 6) * sp.Δ ≤ b₀) (hsh : b₀ ≤ hor)
    (hcall : ∀ x k, tr.IsCall x k → tr.time k ≤ hor)
    (service : SleepyServiceBefore tr H sp.Δ b₀) (hpost : Generic.PostStopService tr H b₁)
    (hB : ∀ b ≤ hor, SleepyBoundsFrom tr H 0 b) (hBK : ∀ b ≤ hor, CommitteeBoundsFrom tr H K 0 b)
    (hnum : sp.ts (coverLabel sp b₀) + 2 * sp.Δ ≤ b₀ ∧
      b₀ < sp.ts (coverLabel sp b₀ + 1 : Nat) + 2 * sp.Δ ∧
      b₁ - b₀ ≤ (4 * (sp.k : Time) - 5) * sp.Δ ∧ b₀ ≤ b₁ ∧
      b₁ ≤ sp.ts (coverLabel sp b₀ + sp.k : Nat) + sp.Δ ∧
      sp.ts (coverLabel sp b₀ : Nat) + sp.Δ < b₁ ∧
      ∀ t, t ≤ sp.ts (coverLabel sp b₀ + sp.k : Nat) + 6 * sp.Δ → t ≤ hor → t ≤ z)
    (hr : b₁ ≤ sp.ts r + sp.Δ ∧ ∀ s : Nat, b₁ ≤ sp.ts s + sp.Δ → r ≤ s)
    (ha0 : 0 ≤ a) (haj : a ≤ sp.ts ((coverLabel sp b₀ : Int) - sp.k))
    (hA₀ : A₀ ⊆ H z) (hW : W ⊆ H z) (hdisj : Disjoint A₀ W)
    (hawake : ∀ x ∈ A₀, ∀ u, a ≤ u → u ≤ z → tr.awake x u)
    (hclass : ∀ x u, a ≤ u → u ≤ z → x ∈ H z → tr.awake x u → x ∈ A₀ ∪ W)
    (hopp : ∀ m, coverLabel sp b₀ ≤ m → m ≤ coverLabel sp b₀ + sp.k → sp.ts m ≤ hor →
      (K.committee m ∩ ((H z)ᶜ ∪ W)).ncard < (K.committee m ∩ A₀).ncard)
    {y : Fin sp.n} {i : Nat} (ar : OutageArming tr H (coverLabel sp b₀) hor A₀ y i T) :
    OutageLockPremises tr H proposer dg ini :=
  have hΔ := sp.toParams.hΔ
  have hk2 := sp.two_le_k
  have hTs : T ≤ b₀ := by
    have : (0 : Time) ≤ (4 * sp.k + 6) * sp.Δ := by positivity
    linarith
  have hkj : sp.k < coverLabel sp b₀ :=
    (Compose.armed_label_lt (σ := 0) hT0 hlag (by simp only [SA.SAParams.ts]; simpa using hT0)).2
  { b₀ := b₀
    b₁ := b₁
    a := a
    z := z
    P := ar.origin
    σ := if ar.origin.root = sp.genesisRoot then 0 else ar.σ
    j₀ := coverLabel sp b₀
    r := r
    A₀ := A₀
    W := W
    hrun := hrun
    K := K
    facts := hKB
    hnc := hnc
    hj₀ := ⟨hnum.1, hnum.2.1⟩
    hr := hr
    hσ := by
      split_ifs with hg
      · omega
      · rcases ar.armed with ⟨htg, ho⟩ | ⟨-, hσk⟩
        · exact absurd (ho ▸ htg) hg
        · exact hσk
    hrk := by
      obtain ⟨-, -, -, -, hK, hjs, -⟩ := hnum
      refine ⟨?_, hr.2 _ hK⟩
      by_contra h
      have := (SA.ts_le_iff sp).2
        (show (r : Int) ≤ (coverLabel sp b₀ : Nat) by omega)
      linarith [hr.1]
    hgap := hnum.2.2.1
    hb₀ := hnum.2.2.2.1
    hP := by
      refine ⟨ar.origin_held, ?_⟩
      split_ifs with hg
      · exact Or.inl hg
      · rcases ar.armed with ⟨htg, ho⟩ | ⟨hCw, -⟩
        · exact absurd (ho ▸ htg) hg
        · exact Or.inr (hCw.mono hTs)
    hpre := sleepy_invariant_at hrun hnc hKB (hT0.trans hTs) service (hB _ hsh) (hBK _ hsh)
    hpreSvc := service
    hB := fun b ⟨_, _, _, hc, hle⟩ => hB b (hle.trans (hcall _ _ hc))
    hBK := fun b ⟨_, _, _, hc, hle⟩ => hBK b (hle.trans (hcall _ _ hc))
    hA₀ := hA₀
    hW := ⟨hW, hdisj⟩
    hopponentsK := fun m h₁ h₂ ⟨_, _, _, hc, hle⟩ => hopp m h₁ h₂ (hle.trans (hcall _ _ hc))
    hawake := hclass
    hA₀awake := hawake
    hA₀join := fun x hx k hk hkz =>
      restart_le_of_awake_at hrun (hA₀ hx) ha0 (fun u hau huz => hawake x hx u hau huz) hk hkz
    ha := by
      have h := haj
      have hj : (sp.k : Int) < coverLabel sp b₀ := by exact_mod_cast hkj
      simp only [SA.SAParams.ts] at h ⊢
      have : (0 : Time) ≤ (sp.k : Int) - 1 := by linarith
      linarith [mul_nonneg this hΔ.le]
    hzc := fun t ht ⟨_, _, _, hc, hle⟩ => hnum.2.2.2.2.2.2 t ht (hle.trans (hcall _ _ hc))
    lockPrev := fun x hx hg ⟨_, _, _, hc, hle⟩ => by
      obtain ⟨c, ℓ, hu, hb⟩ := ar.lockPrev x hx hg (hle.trans (hcall _ _ hc))
      exact ⟨c, ℓ, hu, prevBaseAt_iff.2 hb⟩
    lockCover := fun x hx hg ⟨_, _, _, hc, hle⟩ => by
      obtain ⟨c, ℓ, hu, hfirst, hcond⟩ := ar.lockCover x hx hg (hle.trans (hcall _ _ hc))
      exact ⟨c, ℓ, hu, hfirst, fun hF hVA hN => coverBaseAt_iff.2 (hcond hF hVA hN)⟩
    PG := fun w c m ℓ hw hu hrm x i e hve hes =>
      Simulation.outage_pool_delivery_at hrun hnc hpost w c m ℓ hw hu (hr.1.trans (by
        have := (SA.ts_le_iff sp).2 (show (r : Int) ≤ m by exact_mod_cast hrm)
        linarith)) x i e (hVoteAt_iff.1 hve).1 (hVoteAt_iff.1 hve).2 hes }

end Consensus.Goldilocks.Compose.Growing

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation
open Blocks Shape
variable {S : Setup} {A : ContractAssumptions S} {V : Type} [Fintype V] [DecidableEq V]

/-- **The adapter**: the premise package of the lock module under growing faults from an armed
ready source, with `P` its origin, `A₀` the holders, `W` its opponents awake in the look-back,
`j₀` the cover label and `r` the restored label: the node package at the query's data. -/
noncomputable def outageLockPremises_of_arming_at (Q : OutageQueryAt S A V)
    (service : Compose.Growing.SleepyServiceBefore Q.trace Q.keys Q.params.Δ Q.start)
    {v : V} (hsh : Q.start ≤ Q.run.2.horizon)
    (ar : OutageArmingAt Q v) :
    Compose.Growing.OutageLockPremises Q.trace Q.keys (runProposer S Q.run.2 Q.hn)
      (digestOf S Q.run.2) (simIni S Q.run.2 Q.hn) :=
  have hrun := simTraceAt_goldilocksRun S Q.run.2 Q.hn Q.valid
  have hnc := noCollRun_simTraceAt S Q.run.2 Q.hn Q.valid Q.noCollision
  have hnum := query_numbers_at Q
  have hwin := outage_window_cover_at Q
  Compose.Growing.outageLockPremises_of_arming hrun hnc
    (voteK_facts S Q.run.2 Q.hn Q.valid hnc hrun) Q.outage.times.1 (outage_node_lag_at Q) hsh
    (fun _ _ h => Q.call_le_horizon h) service (outage_postStopService_at Q)
    (fun _ hb => Q.bounds hb) (fun _ hb => Q.boundsK hrun hb) hnum (restoredLabel_spec Q)
    hwin.1 hwin.2.1 Q.holdersAt_subset Q.opponentsAt_subset Q.holdersAt_disjoint
    (fun _ hx _ h₁ h₂ => Q.holder_awake hx h₁ h₂) (fun _ _ h₁ h₂ hx haw => Q.classify h₁ h₂ hx haw)
    (fun _ h₁ h₂ hq => Q.opponents_lt_K h₁ h₂ hq hsh) ar.toOutageArming

section Projections

variable {Q : OutageQueryAt S A V}
  {service : Compose.Growing.SleepyServiceBefore Q.trace Q.keys Q.params.Δ Q.start} {v : V}
  {hsh : Q.start ≤ Q.run.2.horizon} {ar : OutageArmingAt Q v}

theorem outageLockPremises_of_arming_at_P :
    (outageLockPremises_of_arming_at Q service hsh ar).P = ar.origin := by rfl

theorem outageLockPremises_of_arming_at_b₁ :
    (outageLockPremises_of_arming_at Q service hsh ar).b₁ = Q.stop := by rfl

theorem outageLockPremises_of_arming_at_K :
    (outageLockPremises_of_arming_at Q service hsh ar).K = Q.K := by rfl

end Projections

end Consensus.Goldilocks.Obligations.Growing

end

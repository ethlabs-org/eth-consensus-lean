module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeMature
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Defs

public section

/-! # Goldilocks Healing: the shared HS premises through a finite horizon (#137)

consensus-lean#137 (finite-horizon port). `HSShared.healthy` is `HealthyRun`, which asks every
honest node to be awake at all `t ≥ ḡ`; a finite trace is not awake after its horizon, so a
finite query cannot supply `HSShared`. `HSSharedUpTo … b` keeps the other fields and replaces
`Healthy(g)` and `NoRestartAfter ḡ` by their restrictions to the horizon `b`: the signed-row
service of `ResetService` at receiver calls by `b`, wakefulness on `[ḡ, b]`, the fault bound,
and no honest restart in `(ḡ, b]`. `HSShared.toUpTo` restricts the whole-run premises to any
horizon. `rows_delivered_upTo` is `rows_delivered` for a proposal cut by `b`. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF b : Time}

/-- **The shared HS premises through the horizon `b`.** `HSShared` with `Healthy(g)` and
`NoRestartAfter ḡ` restricted to the cuts by `b`. -/
structure HSSharedUpTo (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (g ΔF b : Time) : Prop where
  /-- `NoColl` on the blocks of the run. -/
  noColl : Compose.NoCollRun dg tr
  /-- Genesis's root is its digest (as in `HSShared`). -/
  genesisRoot : (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload).RootOk dg
  /-- GST service with signed-row delivery at receiver calls by `b`. -/
  sync : ResetService tr H g ΔF b
  /-- Every honest node is awake on `[ḡ, b]`. -/
  awake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t
  /-- The fault bound of `Healthy(g)`. -/
  faults : 3 * Hᶜ.ncard ≤ sp.n - 1
  /-- No honest restart in `(ḡ, b]`. -/
  noRestart : ∀ y ∈ H, ∀ k, tr.RestartAt y k → tr.time k ≤ b → tr.time k ≤ gbar g
  /-- `δ_t ≥ ⌈(6Δ + Δ_F)/(4Δ)⌉`. -/
  timeoutDelay : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (sp.toParams.δt : Time)

/-- The whole-run shared premises restrict to every horizon. -/
theorem HSShared.toUpTo (hs : HSShared tr H dg g ΔF) (b : Time) :
    HSSharedUpTo tr H dg g ΔF b :=
  ⟨hs.noColl, hs.genesisRoot, ResetService.of_gst tr H hs.healthy.1,
    fun y hy t ht _ => hs.healthy.2.1 y hy t ht, hs.healthy.2.2,
    fun y hy k hk _ => hs.noRestart y hy k hk, hs.timeoutDelay⟩

/-- **Deadlines after `ḡ` through the horizon** (`deadline_le_of_healthy` at a cut by `b`). -/
theorem HSSharedUpTo.deadline_le (hrun : GoldilocksRun proposer dg H tr)
    (hs : HSSharedUpTo tr H dg g ΔF b) {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} (hkb : tr.time k ≤ b) (τ Δ' : Time) :
    tr.deadline y k τ Δ' ≤ max τ (gbar g) + Δ' := by
  have h := deadline_le_restarts (T := tr.projAC) (c := k)
    (fun k' hk' hr => hs.noRestart y hy k' (Compose.projAC_restartAt.1 hr)
      ((hrun.time_mono hk').trans hkb)) τ
  simp only [ACTrace.deadline, RunTrace.deadline, Compose.projAC_lastWake] at h ⊢
  linarith

/-- **The rows reach the proposer before `t_x`, through the horizon** (`rows_delivered` for a
proposal cut `kX` with `time kX ≤ b`): a row signed by an honest validator by `v ≥ ḡ` is
processed by the honest proposer before its proposal cut when `v + Δ_F ≤ time kX`. -/
theorem rows_delivered_upTo (hrun : GoldilocksRun proposer dg H tr)
    (hs : HSSharedUpTo tr H dg g ΔF b) {v : Time}
    (hv : gbar g ≤ v) {p : Fin sp.n} (hp : p ∈ H) {kX : Nat}
    {X : SA.Blk sp.n (List (FG.Att sp.n))} (hX : tr.ProposesAt p kX X)
    (hvx : v + ΔF ≤ tr.time kX) (hkb : tr.time kX ≤ b) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {att : FG.Att sp.n} (hsig : tr.SignAt y k att) (hk : tr.time k ≤ v) :
    ∃ k' < kX, tr.ProcessAttAt p k' att := by
  have hg : max (tr.time k) g ≤ v := max_le hk ((le_gbar g).trans hv)
  have hdl : ∀ j ≤ kX, tr.deadline p j (max (tr.time k) g) ΔF ≤ v + ΔF := fun j hj => by
    have := hs.deadline_le hrun hp ((hrun.time_mono hj).trans hkb) (max (tr.time k) g) ΔF
    have := max_le hg hv
    linarith
  obtain ⟨acc, hcall⟩ := hX.1.1
  obtain ⟨k', hk', hproc, hlt⟩ := hs.sync.signedRow y hy k att hsig p hp kX ⟨_, hcall⟩ hkb
    (by linarith [hdl kX le_rfl])
  refine ⟨k', lt_of_le_of_ne hk' fun h => ?_, hproc⟩
  subst h
  linarith [hdl k' le_rfl]

end Consensus.Goldilocks.Healing

end

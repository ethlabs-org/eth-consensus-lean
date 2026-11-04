module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeMature
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Defs
import ConsensusLean.Lemmas.Tactic.Linarith

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

/-- **The rows reach the proposer strictly before `t_x`, through the horizon.** Signed-row
service and a proposer restart-prefix bound suffice: when `v + Δ_F ≤ time kX ≤ b`, a row
signed by `v ≥ ḡ` is processed at an earlier cut and strictly earlier time. No timeout-delay
bound is needed, including when `v + Δ_F = time kX`. -/
theorem rows_delivered_upTo (hrun : GoldilocksRun proposer dg H tr)
    (hsvc : ResetService tr H g ΔF b) {v : Time}
    (hv : gbar g ≤ v) {p : Fin sp.n} (hp : p ∈ H) {kX : Nat}
    (hnr : ∀ r ≤ kX, tr.RestartAt p r → tr.time r ≤ gbar g)
    {X : SA.Blk sp.n (List (FG.Att sp.n))} (hX : tr.ProposesAt p kX X)
    (hvx : v + ΔF ≤ tr.time kX) (hkb : tr.time kX ≤ b)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {att : FG.Att sp.n}
    (hsig : tr.SignAt y k att) (hk : tr.time k ≤ v) :
    ∃ k' < kX, tr.ProcessAttAt p k' att ∧ tr.time k' < tr.time kX := by
  have hg : max (tr.time k) g ≤ v := max_le hk ((le_gbar g).trans hv)
  have hdl : ∀ j ≤ kX, tr.deadline p j (max (tr.time k) g) ΔF ≤ v + ΔF := fun j hj => by
    have h := deadline_le_restarts (T := tr.projAC) (c := j)
      (fun r hr hrs => hnr r (hr.trans hj) (Compose.projAC_restartAt.1 hrs)) (max (tr.time k) g)
    simp only [ACTrace.deadline, RunTrace.deadline, Compose.projAC_lastWake] at h ⊢
    have := max_le hg hv
    linarith
  obtain ⟨acc, hcall⟩ := hX.1.1
  obtain ⟨k', hk', hproc, hlt⟩ := hsvc.signedRow y hy k att hsig p hp kX ⟨_, hcall⟩ hkb
    (by linarith [hdl kX le_rfl])
  have htime : tr.time k' < tr.time kX := hlt.trans_le ((hdl k' hk').trans hvx)
  exact ⟨k', lt_of_not_ge (fun h => (not_lt_of_ge (hrun.time_mono h)) htime), hproc, htime⟩

end Consensus.Goldilocks.Healing

end

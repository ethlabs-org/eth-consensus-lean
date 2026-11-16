module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.GoldilocksBridge
import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.GoldilocksHealing
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.RecordRead
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.CurrentSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Queries.Confirmed
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.UpdateCalls
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks healthy read points at committee size

Fields of the healthy read-point contract (`HealthyReadPoint`) for the intended Goldilocks local
supplier at its data equations (`GoldilocksLocalData`), over the shared run interface
`goldilocksRunInterface`:

* `goldilocks_healed_compatible` (the first arm of L6, `healed`): after the reset's drain, an
  honest opening proposal at `s₁`, with its update `t_{s₁} + 6Δ` by the horizon and
  `ḡ + 4Δ ≤ t_{s₁}`, makes any two ready reads strictly after its update compatible.

The bundled premises give the finite reset record (`resetPremisesUpTo_of_premises`); the reset
and the opening form a trace repair schedule (`RepairSchedule`, `RepairOpening`). Each ready read
has its read context (`repair_read_context_at`) and reads its effective record
(`current_record_read_of_context_at`), whose updates due strictly before the read are made at
their update cuts, before the read cut. The two records are covered
(`record_sources_before_now_at`) and compare (`healthy_current_sources_compatible_at`). -/

namespace Consensus.Goldilocks.Generic

open SA (SAParams ReplayOrder Payload gbar)
open Obligations.Growing

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- **L6, healed agreement**: after a reset by the horizon and its drain, an honest opening
proposal at `s₁` with its update by the horizon and `ḡ + 4Δ ≤ t_{s₁}` makes any two ready reads
strictly after `t_{s₁} + 6Δ` compatible in the blocks held while honest. -/
theorem goldilocks_healed_compatible
    (C : ACCorrectLocal (goldilocksNode sp ro) (fun v => v.val))
    (hdata : GoldilocksLocalData sp ro C) {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {ΔF g a b : Time} {s₁ : Nat}
    (hβ : βK ≤ 1 / 2) (hrun : C.run.Run cm proposer dg H tr)
    (hp : Premises tr H cm βK proposer dg (fun v => v.val) g ΔF b)
    (hr : Healing.Growing.IsReset tr H g a) (hab : a ≤ b)
    (hs₁ : sp.toParams.slotOf a + C.healing.drain ≤ s₁)
    (hX : ∃ z k X, HonestProposal tr H proposer s₁ z k X)
    (hTb : sp.toParams.slotTime s₁ + 6 * sp.Δ ≤ b)
    (hgu : gbar g + 4 * sp.Δ ≤ sp.toParams.slotTime s₁)
    {y z : Fin sp.n} {i j : Nat} {t u : Time}
    (ht : sp.toParams.slotTime s₁ + C.margin < t) (hu : sp.toParams.slotTime s₁ + C.margin < u)
    (hy : ReadyReadPoint tr H b C.catchUp y i t) (hz : ReadyReadPoint tr H b C.catchUp z j u) :
    Compatible (tr.HonestBlocksAt H) (confirmedRead tr y i t) (confirmedRead tr z j u) := by
  obtain ⟨⟨⟨hrunEq, -⟩, -, -, hdrain, -⟩, -, hcatch, -, -, -, hmargin, -⟩ := hdata
  rw [hrunEq] at hrun
  replace hrun := (goldilocksRunInterface_run_iff cm).mpr hrun
  rw [hdrain] at hs₁
  rw [hmargin] at ht hu
  rw [hcatch] at hy hz
  have hq := resetPremisesUpTo_of_premises hβ hrun hp hr hab
  have hΔ := sp.toParams.hΔ
  have hts : sp.toParams.slotTime s₁ = sp.ts s₁ := by
    rw [sp.slotTime_eq]; simp [SAParams.ts]
  rw [hts] at hTb hgu ht hu
  have hslot : sp.slot a + 2 * sp.k + 5 ≤ s₁ := by
    have : sp.toParams.slotOf a = sp.slot a := rfl
    omega
  -- the reset and the opening as a trace repair schedule
  let D : RepairSchedule tr H proposer dg g b cm βK :=
    { resetTime := a
      deltaF := ΔF
      reset := hq
      cleanLabel := Healing.cleanLabel sp a
      cleanLabel_eq := rfl
      oldLabel := sp.slot a + 2 * sp.k + 4
      old_bound := by rw [Healing.cleanLabel_eq]; omega }
  obtain ⟨w, k, X, hX⟩ := hX
  have hw : w ∈ H (sp.ts s₁ + sp.Δ) := hts ▸ hX.honest
  have hP : tr.ProposesAt (proposer s₁) k X := hX.designated ▸ hX.proposes
  have hkt : tr.time k = sp.ts s₁ := by rw [hP.2.2, hX.slot, hts]
  have hpk : proposer s₁ ∈ H (tr.time k) :=
    hq.run.antitone (by rw [hkt]; linarith) (hX.designated ▸ hw)
  let O : RepairOpening D :=
    { slot := s₁
      cut := k
      block := X
      drain := by
        rw [Healing.drainTime_eq]
        exact (SA.ts_le_iff sp).2 (by exact_mod_cast hslot)
      late := hgu
      service := hTb
      old_lt := by change sp.slot a + 2 * sp.k + 4 < s₁; omega
      label := hX.slot
      proposes := hP
      accepts := proposal_accepted_at hq.run hq.noColl hpk hP
      time := hkt
      held := hX.designated ▸ hw }
  -- each ready read strictly after the update reads its effective record
  have hread : ∀ {x : Fin sp.n} {m : Nat} {τ : Time}, ReadyReadPoint tr H b (18 * sp.Δ) x m τ →
      sp.ts s₁ + 6 * sp.Δ < τ →
      Nonempty (RepairReadContext D O x m τ) ∧
        Regimes.readAfter tr x m τ =
          (SA.lookup (Node.frame (tr.state x m)) (tr.state x m).ac.latestConfirmed).getD
            (tr.state x m).fg.F := by
    intro x m τ hx hτ
    obtain ⟨⟨hxτ, hrp, hτ0, hτb⟩, hawake⟩ := hx
    obtain ⟨Cx⟩ := repair_read_context_at D O hrp hτ0 hτb hxτ (by linarith only [hΔ]) hawake hτ.le
      (hτ.trans_le hrp.2)
    refine ⟨⟨Cx⟩, current_record_read_of_context_at D Cx fun v hv hvτ hvn => ?_⟩
    obtain ⟨c, ell, -, hup, -⟩ := hq.update_toFG_calls_at (hq.run.antitone hvτ hxτ) hv
      (by linarith only [hvτ, hτb])
    refine ⟨c, ell, hup, ?_⟩
    by_contra hc
    have := hq.run.time_mono (Nat.le_of_not_lt hc)
    have hct : tr.time c = sp.ts v + 6 * sp.Δ := hup.2.2.1
    linarith only [this, hct, hvn]
  obtain ⟨⟨Cy⟩, hRy⟩ := hread hy ht
  obtain ⟨⟨Cz⟩, hRz⟩ := hread hz hu
  change Compatible (tr.HonestBlocksAt H) (Regimes.readAfter tr y i t) (Regimes.readAfter tr z j u)
  rw [hRy, hRz]
  exact healthy_current_sources_compatible_at D Cy.time_nonneg Cy.readPoint Cy.time_bound
    Cy.honest Cz.time_nonneg Cz.readPoint Cz.time_bound Cz.honest
    (record_sources_before_now_at D O Cy.readPoint Cy.honest Cy.repaired Cy.repairedCut)
    (record_sources_before_now_at D O Cz.readPoint Cz.honest Cz.repaired Cz.repairedCut)

end Consensus.Goldilocks.Generic

end

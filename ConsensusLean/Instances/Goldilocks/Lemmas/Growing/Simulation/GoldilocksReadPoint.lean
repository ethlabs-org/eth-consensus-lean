module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.GoldilocksBridge
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.GoldilocksHealing
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.RecordRead
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.CurrentSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Queries.Confirmed
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.UpdateCalls
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.ConfirmedSupply
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks healthy read points at committee size

Fields of the healthy read-point contract (`HealthyReadPoint`) for the intended Goldilocks local
supplier at its data equations (`GoldilocksLocalData`), over the shared run interface
`goldilocksRunInterface`:

* `goldilocks_healed_compatible` (the first arm of L6, `healed`): after the reset's drain, an
  honest opening proposal at `s₁`, with its update `t_{s₁} + 6Δ` by the horizon and
  `ḡ + 4Δ ≤ t_{s₁}`, makes any two ready reads strictly after its update compatible;
* `goldilocks_healed_proposal` (the second arm of L6): an honest proposal at `s₁` is an ancestor
  of every ready read at or after its update `t_{s₁} + 6Δ`, strictly before the read cut;
* `goldilocks_proposal_read` (L7, `proposal`): the same for a ready proposal after the drain,
  within the latency `6Δ`;
* `goldilocks_healthyReadPoint`: the contract `HealthyReadPoint` from the three.

The bundled premises give the finite reset record (`resetPremisesUpTo_of_premises`); the reset
and an honest proposal after its drain form a trace repair schedule and opening
(`exists_repair_opening`). A ready read at or after the opening's update, strictly before its read
cut, has its read context (`repair_read_context_at`) and reads its effective record
(`ready_read_record`): its updates due by the read are made at their update cuts, before the read
cut. Two records are covered (`record_sources_before_now_at`) and compare
(`healthy_current_sources_compatible_at`). The opening's proposal is held under the read at the
first cut after its update (`operational_proposal_read_after_at`), and a reader's effective record
only extends from there (`healthy_current_record_interval_at`, `effective_record_of_interval_at`):
`proposal_below_ready_read`. -/

namespace Consensus.Goldilocks.Generic

open AC (ACParams Payload gbar)
open Obligations.Growing

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp} {cm : Time → Finset (Fin sp.n)}
  {βK : ℚ} {g ΔF a b : Time}
variable {hold : Time}

/-- A slot after the reset's drain starts `24Δ` after `ḡ`: the reset is after the snapshot cut
`c_z > ḡ + 8Δ`, and its drain slot is `2k + 4` slots past the slot after it. -/
private theorem gbar_lt_of_drain (hq : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF
      a b cm βK hold) {u : Nat} (hu : Healing.drainTime sp a ≤ sp.ts u) :
    gbar g + 24 * sp.Δ ≤ sp.ts u := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hca := hq.cutZ_lt_reset_at
  have hcz := Healing.lt_cutZ sp g
  have ha0 : 0 ≤ a := by linarith [Healing.gbar_nonneg g]
  have ha : a < sp.ts (sp.slot a + 1 : Nat) := by
    have hh := Int.lt_ediv_add_one_mul_self a (by linarith only [hΔ] : 0 < 4 * sp.Δ)
    rw [← AC.slot_eq sp ha0] at hh
    rw [AC.ACParams.ts, mul_comm]; exact_mod_cast hh
  have hk := sp.two_le_k
  have hdr : sp.ts (sp.slot a + 1 : Nat) + 32 * sp.Δ ≤ Healing.drainTime sp a := by
    rw [Healing.drainTime_eq]
    simp only [AC.ACParams.ts]
    push_cast
    have : (8 : Time) ≤ 2 * (sp.k : Time) + 4 := by
      have : (2 : Time) ≤ sp.k := by exact_mod_cast hk
      linarith
    nlinarith
  linarith

/-- **An honest proposal after the drain is a repair opening**: a proposal of the designated
proposer of a slot `u` after the reset's drain, honest `Δ` after the slot start, with its update by
the horizon and `ḡ + 4Δ ≤ t_u`, is an opening of the reset's repair schedule (old label
`slot a + 2k + 4`). -/
private theorem exists_repair_opening
    (hq : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold) {u : Nat}
    (hslot : sp.slot a + 2 * sp.k + 5 ≤ u) {k : Nat} {X : AC.Blk sp.n (List (FG.Att sp.n))}
    (hheld : proposer u ∈ H (sp.ts u + sp.Δ)) (hP : tr.ProposesAt (proposer u) k X)
    (hXs : X.slot = u) (hgu : gbar g + 4 * sp.Δ ≤ sp.ts u) (hTb : sp.ts u + 6 * sp.Δ ≤ b) :
    ∃ (D : RepairSchedule tr H proposer dg g b cm βK) (O : RepairOpening D),
      O.slot = u ∧ O.block = X := by
  have hΔ := sp.toParams.hΔ
  have hkt : tr.time k = sp.ts u := by
    rw [hP.2.2, hXs, sp.slotTime_eq]; simp [ACParams.ts]
  have hpk : proposer u ∈ H (tr.time k) :=
    hq.run.antitone (by rw [hkt]; linarith) hheld
  let D : RepairSchedule tr H proposer dg g b cm βK :=
    { resetTime := a
      deltaF := ΔF
      reset := hq
      cleanLabel := Healing.cleanLabel sp a
      cleanLabel_eq := rfl
      oldLabel := sp.slot a + 2 * sp.k + 4
      old_bound := by rw [Healing.cleanLabel_eq]; omega }
  exact ⟨D, { slot := u
              cut := k
              block := X
              drain := by
                rw [Healing.drainTime_eq]
                exact (AC.ts_le_iff sp).2 (by exact_mod_cast hslot)
              late := hgu
              service := hTb
              old_lt := by change sp.slot a + 2 * sp.k + 4 < u; omega
              label := hXs
              proposes := hP
              accepts := proposal_accepted_at hq.run hq.noColl hpk hP
              time := hkt
              held := hheld }, rfl, rfl⟩

/-- **A ready read at or after the opening's update reads its effective record**, with its read
cut after the update: its read context (`repair_read_context_at`), and its updates due by the read,
whose update cuts are before the read cut (`current_record_read_of_context_at`). -/
private theorem ready_read_record {D : RepairSchedule tr H proposer dg g b cm βK}
    (O : RepairOpening D) {x : Fin sp.n} {m : Nat} {τ : Time}
    (hx : ReadyReadPoint tr H b (18 * sp.Δ) x m τ) (hτ : sp.ts O.slot + 6 * sp.Δ ≤ τ)
    (hτn : sp.ts O.slot + 6 * sp.Δ < tr.time m) :
    Nonempty (RepairReadContext D O x m τ) ∧
      Regimes.readAfter tr x m τ =
        (AC.lookup (Node.frame (tr.state x m)) (tr.state x m).ac.latestConfirmed).getD
          (tr.state x m).fg.F := by
  have hΔ := sp.toParams.hΔ
  obtain ⟨⟨hxτ, hrp, hτ0, hτb⟩, hawake⟩ := hx
  obtain ⟨Cx⟩ := repair_read_context_at D O hrp hτ0 hτb hxτ (by linarith only [hΔ]) hawake hτ
    hτn
  refine ⟨⟨Cx⟩, current_record_read_of_context_at D Cx fun v hv hvτ hvn => ?_⟩
  obtain ⟨c, ell, hup⟩ := D.reset.update_call_of_awake (D.reset.run.antitone hvτ hxτ) hv
    (by linarith only [hvτ, hτb])
  refine ⟨c, ell, hup, ?_⟩
  by_contra hc
  have := D.reset.run.time_mono (Nat.le_of_not_lt hc)
  have hct : tr.time c = sp.ts v + 6 * sp.Δ := hup.2.2.1
  linarith only [this, hct, hvn]

/-- **The opening's proposal is below every ready read at or after its update**, strictly before
the read cut. At the first cut `J` after the update `T = t_u + 6Δ` the read holds the proposal:
every update of slot `u` by a node honest at it writes the proposal's fresh fast lock
(`operational_update_fresh_lock_at`, `operational_proposal_read_after_at`). That read is the
reader's effective record, which only extends to the later read cut (`J ≤ j`, the interval
contract from `T`). -/
private theorem proposal_below_ready_read {D : RepairSchedule tr H proposer dg g b cm βK}
    (O : RepairOpening D) {y : Fin sp.n} {j : Nat} {t : Time}
    (hy : ReadyReadPoint tr H b (18 * sp.Δ) y j t) (ht : sp.ts O.slot + 6 * sp.Δ ≤ t)
    (hjt : t < tr.time j) :
    Anc (tr.HonestBlocksAt H) O.block (Regimes.readAfter tr y j t) := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hΔ1 : (1 : Time) ≤ sp.Δ := hΔ
  have hrun := D.reset.run
  obtain ⟨⟨hyt, hrp, ht0, htb⟩, hawake⟩ := hy
  set T := sp.ts O.slot + 6 * sp.Δ with hTdef
  have hT0 : 0 ≤ T := by
    have := Compose.Growing.ts_natCast_nonneg (sp := sp) O.slot
    linarith only [this, hΔ]
  have hyT : y ∈ H T := hrun.antitone ht hyt
  have hex : ∃ J, T < tr.time J := ⟨j, ht.trans_lt hjt⟩
  classical
  have hJ : Regimes.CutAfter tr (Nat.find hex) T :=
    ⟨fun k hk => le_of_not_gt (Nat.find_min hex hk), Nat.find_spec hex⟩
  have hJj : Nat.find hex ≤ j := Nat.find_min' hex (ht.trans_lt hjt)
  have hgu := gbar_lt_of_drain D.reset O.drain
  have hreadyT : ReadyReadPoint tr H b (18 * sp.Δ) y (Nat.find hex) T :=
    ⟨⟨hyT, ⟨hJ.1, hJ.2.le⟩, hT0, ht.trans htb⟩, fun u hu huT =>
      D.reset.awake y u (hrun.antitone huT hyT)
        (by linarith only [(le_max_right _ _).trans hu, hgu, hΔ1, hTdef])
        (huT.trans (ht.trans htb))⟩
  obtain ⟨⟨CJ⟩, hRJ⟩ := ready_read_record O hreadyT le_rfl hJ.2
  obtain ⟨⟨Cj⟩, hRj⟩ := ready_read_record O ⟨⟨hyt, hrp, ht0, htb⟩, hawake⟩ ht (ht.trans_lt hjt)
  have hX := Healing.Growing.operational_proposal_read_after_at D.reset O.held rfl O.proposes
    O.label O.drain O.late O.service (fun y' j' ell hy' hup =>
      Healing.Growing.operational_update_fresh_lock_at D.reset O.held rfl O.proposes O.label
        O.drain O.late O.service hy' hup) y (Nat.find hex) hyT hJ
  rw [hRJ] at hX
  have hint := healthy_current_record_interval_at D O CJ.readPoint Cj.readPoint ht htb hyt le_rfl
    hJ.2
  rw [hRj]
  exact hX.trans (effective_record_of_interval_at hrun D.reset.noColl ht0 hrp.1 hyt hJj hint .refl)

/-- The supplier's data equations give the interface run, the drain `2k + 5`, the catch-up `18Δ`,
the hold `Δ`, the margin and the latency `6Δ`. -/
private theorem localData_eqs
      {fgHold : Time} {C : ACCorrectLocal (goldilocksNode sp) (fun v => v.val) fgHold}
    {sign : Fin sp.n → Time → Bool} {G : Nat}
    {Rg : Nat} (hdata : GoldilocksLocalData sp C sign G Rg) :
    (∀ cm proposer dg H (tr : GoldilocksTrace sp), C.run.Run cm proposer dg H tr →
      (goldilocksRunInterface sp sign G).Run cm proposer dg H tr) ∧
    C.healing.drain = 2 * sp.k + 5 ∧ C.healing.deepBudget = sp.deepDepth ∧
    C.catchUp = 18 * sp.Δ ∧ C.hold = sp.Δ ∧ C.margin = 6 * sp.Δ ∧ C.latency = 6 * sp.Δ := by
  obtain ⟨⟨⟨hrunEq, -⟩, -, -, -, hdrain, hbudget, -⟩, -, hcatch, -, -, hhold, hmargin, hlat, -⟩ :=
    hdata
  refine ⟨fun cm proposer dg H tr hrun => ?_, hdrain, hbudget, hcatch, hhold, hmargin, hlat⟩
  rw [hrunEq] at hrun
  exact (goldilocksRunInterface_run_iff cm).mpr hrun

/-- **L6, healed agreement**: after a reset by the horizon and its drain, an honest opening
proposal at `s₁` with its update by the horizon and `ḡ + 4Δ ≤ t_{s₁}` makes any two ready reads
strictly after `t_{s₁} + 6Δ` compatible in the blocks held while honest. -/
private theorem goldilocks_healed_compatible
    {fgHold : Time} (C : ACCorrectLocal (goldilocksNode sp) (fun v => v.val) fgHold)
    {sign : Fin sp.n → Time → Bool} {G : Nat}
    {Rg : Nat} (hdata : GoldilocksLocalData sp C sign G Rg) {s₁ : Nat}
    (hβ : βK ≤ 1 / 2) (hrun : C.run.Run cm proposer dg H tr)
    (hp : Premises tr H cm βK proposer dg (fun v => v.val) g ΔF b fgHold)
    (hr : Healing.Growing.IsReset tr H g a) (hab : a ≤ b)
    (hbud : ResetInBudget sp.toParams C.healing.deepBudget C.healing.drain g a)
    (hs₁ : sp.toParams.slotOf a + C.healing.drain ≤ s₁)
    (hX : ∃ z k X, HonestProposal tr H proposer s₁ z k X)
    (hTb : sp.toParams.slotTime s₁ + 6 * sp.Δ ≤ b)
    (hgu : gbar g + 4 * sp.Δ ≤ sp.toParams.slotTime s₁)
    {y z : Fin sp.n} {i j : Nat} {t u : Time}
    (ht : sp.toParams.slotTime s₁ + C.margin < t) (hu : sp.toParams.slotTime s₁ + C.margin < u)
    (hy : ReadyReadPoint tr H b C.catchUp y i t) (hz : ReadyReadPoint tr H b C.catchUp z j u) :
    Compatible (tr.HonestBlocksAt H) (confirmedRead tr y i t) (confirmedRead tr z j u) := by
  obtain ⟨hrunI, hdrain, hbudget, hcatch, -, hmargin, -⟩ := localData_eqs hdata
  rw [hdrain] at hs₁ hbud
  rw [hbudget] at hbud
  rw [hmargin] at ht hu
  rw [hcatch] at hy hz
  have hq := resetPremisesUpTo_of_premises_budget hβ (hrunI _ _ _ _ _ hrun) hp hr hab hbud
  have hts : sp.toParams.slotTime s₁ = sp.ts s₁ := by
    rw [sp.slotTime_eq]; simp [ACParams.ts]
  rw [hts] at hTb hgu ht hu
  obtain ⟨w, k, X, hX⟩ := hX
  obtain ⟨D, O, hOs, -⟩ := exists_repair_opening hq (by
      have : sp.toParams.slotOf a = sp.slot a := rfl
      omega) (hX.designated ▸ hts ▸ hX.honest) (hX.designated ▸ hX.proposes) hX.slot hgu hTb
  subst hOs
  obtain ⟨⟨Cy⟩, hRy⟩ := ready_read_record O hy ht.le (ht.trans_le hy.1.2.1.2)
  obtain ⟨⟨Cz⟩, hRz⟩ := ready_read_record O hz hu.le (hu.trans_le hz.1.2.1.2)
  change Compatible (tr.HonestBlocksAt H) (Regimes.readAfter tr y i t) (Regimes.readAfter tr z j u)
  rw [hRy, hRz]
  exact healthy_current_sources_compatible_at D Cy.time_nonneg Cy.readPoint Cy.time_bound
    Cy.honest Cz.time_nonneg Cz.readPoint Cz.time_bound Cz.honest
    (record_sources_before_now_at D O Cy.readPoint Cy.honest Cy.repaired Cy.repairedCut)
    (record_sources_before_now_at D O Cz.readPoint Cz.honest Cz.repaired Cz.repairedCut)

/-- **L6, healed proposal ancestry**: after a reset by the horizon and its drain, an honest
proposal at `s₁` by the horizon is an ancestor of every ready read at or after its update
`t_{s₁} + 6Δ`, strictly before the read cut. -/
private theorem goldilocks_healed_proposal
    {fgHold : Time} (C : ACCorrectLocal (goldilocksNode sp) (fun v => v.val) fgHold)
    {sign : Fin sp.n → Time → Bool} {G : Nat}
    {Rg : Nat} (hdata : GoldilocksLocalData sp C sign G Rg) {s₁ : Nat}
    (hβ : βK ≤ 1 / 2) (hrun : C.run.Run cm proposer dg H tr)
    (hp : Premises tr H cm βK proposer dg (fun v => v.val) g ΔF b fgHold)
    (hr : Healing.Growing.IsReset tr H g a) (hab : a ≤ b)
    (hbud : ResetInBudget sp.toParams C.healing.deepBudget C.healing.drain g a)
    (hs₁ : sp.toParams.slotOf a + C.healing.drain ≤ s₁)
    {z : Fin sp.n} {k : Nat} {X : AC.Blk sp.n (List (FG.Att sp.n))}
    (hX : HonestProposal tr H proposer s₁ z k X)
    {y : Fin sp.n} {j : Nat} {t : Time} (ht : tr.time k + C.margin ≤ t)
    (hy : ReadyReadPoint tr H b C.catchUp y j t) (hjt : t < tr.time j) :
    Anc (tr.HonestBlocksAt H) X (confirmedRead tr y j t) := by
  obtain ⟨hrunI, hdrain, hbudget, hcatch, -, hmargin, -⟩ := localData_eqs hdata
  rw [hdrain] at hs₁ hbud
  rw [hbudget] at hbud
  rw [hmargin] at ht
  rw [hcatch] at hy
  have hq := resetPremisesUpTo_of_premises_budget hβ (hrunI _ _ _ _ _ hrun) hp hr hab hbud
  have hts : sp.toParams.slotTime s₁ = sp.ts s₁ := by
    rw [sp.slotTime_eq]; simp [ACParams.ts]
  have hP := hX.designated ▸ hX.proposes
  have hkt : tr.time k = sp.ts s₁ := by rw [hP.2.2, hX.slot, hts]
  rw [hkt] at ht
  have hslot : sp.slot a + 2 * sp.k + 5 ≤ s₁ := by
    have : sp.toParams.slotOf a = sp.slot a := rfl
    omega
  have hgu := gbar_lt_of_drain hq (u := s₁) (by
    rw [Healing.drainTime_eq]; exact (AC.ts_le_iff sp).2 (by exact_mod_cast hslot))
  obtain ⟨D, O, hOs, hOX⟩ := exists_repair_opening hq hslot (hX.designated ▸ hts ▸ hX.honest) hP
    hX.slot (by linarith only [hgu, sp.toParams.hΔ]) (ht.trans hy.1.2.2.2)
  subst hOs hOX
  exact proposal_below_ready_read O hy ht hjt

/-- **L7, ready proposal inclusion**: after a reset by the horizon, a ready proposal, still honest
`Δ` after it, at a slot after the drain with `ḡ + 4Δ ≤ t_s`, is an ancestor of every ready read at
or after `t_s + 6Δ`, strictly before the read cut. -/
private theorem goldilocks_proposal_read
    {fgHold : Time} (C : ACCorrectLocal (goldilocksNode sp) (fun v => v.val) fgHold)
    {sign : Fin sp.n → Time → Bool} {G : Nat}
    {Rg : Nat} (hdata : GoldilocksLocalData sp C sign G Rg)
    (hβ : βK ≤ 1 / 2) (hrun : C.run.Run cm proposer dg H tr)
    (hp : Premises tr H cm βK proposer dg (fun v => v.val) g ΔF b fgHold)
    (hr : Healing.Growing.IsReset tr H g a) (hab : a ≤ b)
    (hbud : ResetInBudget sp.toParams C.healing.deepBudget C.healing.drain g a)
    {B : AC.Blk sp.n (List (FG.Att sp.n))} {k : Nat} {y : Fin sp.n} {j : Nat} {t : Time}
    (hB : ReadyProposal tr H C.catchUp C.hold B k)
    (hBs : sp.toParams.slotOf a + C.healing.drain ≤ B.slot)
    (hgu : gbar g + 4 * sp.Δ ≤ sp.toParams.slotTime B.slot)
    (ht : tr.time k + C.latency ≤ t)
    (hy : ReadyReadPoint tr H b C.catchUp y j t) (hjt : t < tr.time j) :
    Anc (tr.HonestBlocksAt H) B (confirmedRead tr y j t) := by
  obtain ⟨hrunI, hdrain, hbudget, hcatch, hhold, -, hlat⟩ := localData_eqs hdata
  rw [hdrain] at hBs hbud
  rw [hbudget] at hbud
  rw [hlat] at ht
  rw [hcatch] at hy
  rw [hhold] at hB
  have hq := resetPremisesUpTo_of_premises_budget hβ (hrunI _ _ _ _ _ hrun) hp hr hab hbud
  obtain ⟨hP, -, hheld⟩ := hB
  have hts : sp.toParams.slotTime B.slot = sp.ts B.slot := by
    rw [sp.slotTime_eq]; simp [ACParams.ts]
  have hkt : tr.time k = sp.ts B.slot := by rw [hP.2.2, hts]
  rw [hkt] at ht hheld
  rw [hts] at hgu
  have hdes := proposesAt_designated_at hq.run
    (hq.run.antitone (by rw [hkt]; linarith [sp.toParams.hΔ]) hheld) hP
  rw [hdes] at hP hheld
  obtain ⟨D, O, hOs, hOX⟩ := exists_repair_opening hq (by
      have : sp.toParams.slotOf a = sp.slot a := rfl
      omega) hheld hP rfl hgu (ht.trans hy.1.2.2.2)
  rw [← hOX]
  exact proposal_below_ready_read O hy (hOs ▸ ht) hjt

/-- **The healthy read points of the Goldilocks supplier** (L6 and L7) at its data equations. -/
theorem goldilocks_healthyReadPoint
    {fgHold : Time} (C : ACCorrectLocal (goldilocksNode sp) (fun v => v.val) fgHold)
    {sign : Fin sp.n → Time → Bool} {G : Nat}
    {Rg : Nat} (hdata : GoldilocksLocalData sp C sign G Rg) : HealthyReadPoint C where
  healed := fun _ _ _ _ _ _ _ _ _ _ _ hβ hrun hp hr hab hbud hs₁ _ _ =>
    ⟨fun hX hTb hgu _ _ _ _ _ _ ht hu hy hz _ _ =>
      goldilocks_healed_compatible C hdata hβ hrun hp hr hab hbud hs₁ hX hTb hgu ht hu hy hz,
     fun _ _ _ hX _ _ _ _ _ ht hy _ hjt =>
      goldilocks_healed_proposal C hdata hβ hrun hp hr hab hbud hs₁ hX ht hy hjt⟩
  proposal := fun _ _ _ _ _ _ _ _ _ _ _ hβ hrun hp hr hab hbud _ _ _ _ _ _ hB hBs hgu _ _ _ _ ht hy
    _ hjt => goldilocks_proposal_read C hdata hβ hrun hp hr hab hbud hB hBs hgu ht hy hjt

end Consensus.Goldilocks.Generic

end

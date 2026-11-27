module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.GoldilocksBridge
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Components
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.HonestProposal
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetRounds
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.OperationalPersistence
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.BoundariesCover
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Frontier.HealedCoverSupply
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks healing fields at committee size

Fields of the committee-indexed Goldilocks healing supplier (`goldilocksACHealing`) over the shared
run interface `goldilocksRunInterface`, whose runs start each node with its committee permission
and carry the committee facts under collision freedom:

* `report_in_frame`: `goldilocks_report_in_frame`, the report's frame root ancestry
  (`report_root_at` at the committee start);
* `origins_comparable`: `goldilocks_origins_comparable`, at the joined stored-fast-lock origin of
  `GoldilocksHealingData`, by `ResetPremisesUpTo.origins_compatible_at`;
* `heal_after_reset`: `goldilocks_heal_after_reset`, at the drain `2k + 5` of
  `GoldilocksHealingData`, by `honest_proposal_below_next_upTo_at` and
  `honest_proposal_below_later_upTo_at`.

The last two read the bundled premises through the finite reset record
`resetPremisesUpTo_of_premises`. `follow_le` is the explicit timeout bound `3 ≤ δt` itself.
-/

namespace Consensus.Goldilocks.Generic

open AC (ACParams Payload)
open Healing (cutZ)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
  {sign : Fin sp.n → Time → Bool} {G : Nat}


/-- The bundled premises of an interface run with a reset by its horizon form the finite reset
record: the committee facts come from the run under collision freedom, the service fields are the
same, and restarts after `ḡ` are excluded at every cut, so also at those by the horizon. -/
theorem resetPremisesUpTo_of_premises {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    {g ΔF a b hold : Time} (hβ : βK ≤ 1 / 2)
    (hrun : (goldilocksRunInterface sp sign G).Run cm proposer dg H tr)
    (hp : Premises tr H cm βK proposer dg (fun v => v.val) g ΔF b hold)
    (hr : Healing.Growing.IsReset tr H g a) (hab : a ≤ b)
    (hdeep : ∀ D, sp.deepDepth = some D →
      b ≤ cutZ sp.toParams g + 4 * D * sp.Δ ∨ Healing.Growing.HighSourceCover tr H g a b) :
    Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold :=
  have hrun := (goldilocksRunInterface_run_iff cm).mp hrun
  { beta_le := hβ
    run := hrun.1
    committee_pos := hrun.2.1
    committeeFacts := hrun.2.2.2.1 hp.noColl
    committeeFaults := hp.committee
    noColl := hp.noColl
    sync := ⟨hp.sync.deltaF, hp.sync.message, hp.sync.block, hp.sync.relay, hp.sync.signedRow,
      hp.sync.hold_le⟩
    awake := hp.awake
    faults := hp.faults
    reset := hr
    reset_le := hab
    snapshot := hp.snapshot
    catchUp := hp.catchUp
    noRestart := fun y k hy hk _ => hp.noRestart y k hy hk
    timeoutDelay := hp.timeoutDelay
    nonempty := hp.nonempty
    deepCover := hdeep }

/-- The time `t_{slot c_z + m}` is at most `c_z + 4mΔ`: `c_z ≥ 0` is at or after the start of its
own slot. -/
private theorem slotTime_cutZ_add_le (g : Time) (m : Nat) :
    sp.toParams.slotTime (sp.toParams.slotOf (cutZ sp.toParams g) + m) ≤
      cutZ sp.toParams g + 4 * m * sp.Δ := by
  have hΔ := sp.toParams.hΔ
  have hz0 : 0 ≤ cutZ sp.toParams g := by
    have := Healing.lt_cutZ sp g; linarith [AC.gbar_nonneg g]
  have hfl : sp.ts (sp.slot (cutZ sp.toParams g)) ≤ cutZ sp.toParams g :=
    (AC.ts_le_iff_le_slot sp hz0 _).2 le_rfl
  have : sp.toParams.slotTime (sp.toParams.slotOf (cutZ sp.toParams g) + m) =
      sp.ts (sp.slot (cutZ sp.toParams g)) + 4 * m * sp.Δ := by
    rw [sp.slotTime_eq]; simp only [ACParams.ts]; push_cast
    change 4 * sp.Δ * ((sp.slot (cutZ sp.toParams g) + m : Nat) : Int) = _
    push_cast; ring
  linarith

/-- The capped horizon is at most the horizon. -/
private theorem originCapTime_le (g b : Time) :
    originCapTime sp.toParams sp.deepDepth g b ≤ b := by
  unfold originCapTime
  cases sp.deepDepth with
  | none => exact le_rfl
  | some m => exact min_le_left _ _

/-- A time by the horizon and within the origin cap is by the capped horizon. -/
private theorem le_originCapTime {g t b : Time} (htb : t ≤ b)
    (hc : OriginInCap sp.toParams sp.deepDepth g t) :
    t ≤ originCapTime sp.toParams sp.deepDepth g b := by
  unfold originCapTime
  cases hD : sp.deepDepth with
  | none => exact htb
  | some m => exact le_min htb (hc m hD)

/-- The capped horizon is inside the deep quarantine `c_z + 4DΔ`. -/
private theorem originCapTime_quarantine (g b : Time) :
    ∀ D, sp.deepDepth = some D →
      originCapTime sp.toParams sp.deepDepth g b ≤ cutZ sp.toParams g + 4 * D * sp.Δ := by
  intro D hD
  unfold originCapTime
  rw [hD]
  exact (min_le_right _ _).trans (slotTime_cutZ_add_le g D)

/-- The reset `a` is at or after the time of the first cut after `c_z` (its signing cut is after
`c_z`). -/
private theorem snapshot_le_reset {g a : Time} {hold ΔF b : Time} {cm : Time → Finset (Fin sp.n)}
    {βK : ℚ}
    (hrun : (goldilocksRunInterface sp sign G).Run cm proposer dg H tr)
    (hp : Premises tr H cm βK proposer dg (fun v => v.val) g ΔF b hold)
    (hr : Healing.Growing.IsReset tr H g a) :
    ∃ k, Healing.FirstCutAfter tr k (cutZ sp.toParams g) ∧ tr.time k ≤ a := by
  have hrun := ((goldilocksRunInterface_run_iff cm).mp hrun).1
  obtain ⟨k, hk, -⟩ := hp.snapshot
  have hza := Healing.Growing.cutZ_lt_reset_of_snapshot_at hrun hp.noColl ⟨k, hk⟩ hr
  obtain ⟨⟨y, q, att, -, -, -, hqa⟩, -⟩ := hr
  refine ⟨k, hk, ?_⟩
  by_contra hlt
  rcases lt_or_ge q k with hqk | hkq
  · have := hk.1 q hqk; linarith
  · have := hrun.time_mono hkq; linarith

/-- The per-slot timeout delay of the bundled premises, on the four-`Δ` slot grid. -/
private theorem timeoutDelay_scalar {cm : Time → Finset (Fin sp.n)} {βK : ℚ} {g ΔF b hold : Time}
    (hp : Premises tr H cm βK proposer dg (fun v => v.val) g ΔF b hold) :
    6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time) := by
  have h := hp.timeoutDelay 0
  rw [sp.slotTime_eq, sp.slotTime_eq] at h
  have hδ : (sp.toParams.δt : Time) = sp.toParams.fg.δt := rfl
  rw [← hδ]
  push_cast at h
  linarith

/-- The bundled premises at the capped horizon: a reset within the origin cap gives the finite
reset record through `originCapTime`, inside the deep quarantine. -/
theorem resetPremisesUpTo_of_premises_cap {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    {g ΔF a b hold : Time} (hβ : βK ≤ 1 / 2)
    (hrun : (goldilocksRunInterface sp sign G).Run cm proposer dg H tr)
    (hp : Premises tr H cm βK proposer dg (fun v => v.val) g ΔF b hold)
    (hr : Healing.Growing.IsReset tr H g a) (hab : a ≤ b)
    (hac : OriginInCap sp.toParams sp.deepDepth g a) :
    Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a
      (originCapTime sp.toParams sp.deepDepth g b) cm βK hold := by
  have hrun' := (goldilocksRunInterface_run_iff cm).mp hrun
  have hcb := originCapTime_le (sp := sp) g b
  have hac' := le_originCapTime hab hac
  obtain ⟨k, hk, hka⟩ := snapshot_le_reset hrun hp hr
  have hΔF := timeoutDelay_scalar hp
  exact Healing.Growing.resetPremisesUpTo_of_reset_at hrun'.1 hp.noColl
    ⟨hp.sync.deltaF, hp.sync.message, hp.sync.block, hp.sync.relay,
      fun x i att hx hs hh y j hy hc hjT hd =>
        hp.sync.signedRow x i att hx hs hh y j hy hc (hjT.trans hcb) hd, hp.sync.hold_le⟩
    (fun y t hy hg ht => hp.awake y t hy hg (ht.trans hcb))
    (fun t h0 ht => hp.faults t h0 (ht.trans hcb)) hr hac' ⟨k, hk, hka.trans hac'⟩ hp.catchUp
    (Healing.Growing.noRestartUpTo_iff.2 fun y q hy hq _ => hp.noRestart y q hy hq) hΔF
    (hp.nonempty.mono (hrun'.1.antitone hcb)) (hrun'.2.2.2.1 hp.noColl) hβ hrun'.2.1
    (fun t d h1 h2 h3 h4 hne => hp.committee t d h1 (h2.trans hcb) h3 (h4.trans hcb) hne)
    fun D hD => Or.inl (originCapTime_quarantine g b D hD)

/-- **The bundled premises with a reset in the deep budget**: the finite reset record through the
horizon, its deep cover built inside (`resetPremisesUpTo_of_reset_cover_at`): the quarantine arm
when the horizon is inside `c_z + 4DΔ`; otherwise the record restricted to `T = c_z + 4DΔ`, with
the drain of `a` at least `4Δ` before `T` (the budget: `slot a + drain + 1 ≤ slot c_z + D`), gives
the high-source cover through the horizon (`healthy_high_source_cover_at`). -/
theorem resetPremisesUpTo_of_premises_budget {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    {g ΔF a b hold : Time} (hβ : βK ≤ 1 / 2)
    (hrun : (goldilocksRunInterface sp sign G).Run cm proposer dg H tr)
    (hp : Premises tr H cm βK proposer dg (fun v => v.val) g ΔF b hold)
    (hr : Healing.Growing.IsReset tr H g a) (hab : a ≤ b)
    (hbud : ResetInBudget sp.toParams sp.deepDepth (2 * sp.k + 5) g a) :
    Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold := by
  have hrun' := (goldilocksRunInterface_run_iff cm).mp hrun
  have hΔ := sp.toParams.hΔ
  have ha0 : 0 ≤ a := by
    obtain ⟨⟨_, q, _, _, _, _, hqa⟩, _⟩ := hr
    rw [← hqa]; exact hrun'.1.time_nonneg q
  have hΔF := timeoutDelay_scalar hp
  have hsvc : Healing.Growing.ResetService tr H g ΔF b hold :=
    ⟨hp.sync.deltaF, hp.sync.message, hp.sync.block, hp.sync.relay, hp.sync.signedRow,
      hp.sync.hold_le⟩
  refine Healing.Growing.resetPremisesUpTo_of_reset_cover_at hrun'.1 hp.noColl hsvc hp.awake
    hp.faults hr ha0 hab hp.snapshot hp.catchUp
    (Healing.Growing.noRestartUpTo_iff.2 fun y q hy hq _ => hp.noRestart y q hy hq) hΔF
    hp.nonempty (hrun'.2.2.2.1 hp.noColl) hβ hrun'.2.1 hp.committee (fun D hD => ?_)
    fun T hpT hT hd hTb => Healing.Growing.healthy_high_source_cover_at hpT hT hd hTb hsvc.toAC
      hp.awake hp.faults hp.committee
  -- the budget: `t_{slot a + 2k + 6} ≤ t_{slot c_z + D} ≤ c_z + 4DΔ`
  have hb := hbud D hD
  have hsl : sp.toParams.slotOf a = sp.slot a := rfl
  rw [hsl] at hb
  have hle := slotTime_cutZ_add_le (sp := sp) g D
  have hmono : sp.ts (sp.slot a + 2 * sp.k + 6 : Nat) ≤
      sp.toParams.slotTime (sp.toParams.slotOf (cutZ sp.toParams g) + D) := by
    rw [sp.slotTime_eq]
    exact (AC.ts_le_iff sp).2 (by exact_mod_cast (show sp.slot a + 2 * sp.k + 6 ≤
      sp.toParams.slotOf (cutZ sp.toParams g) + D by omega))
  have hts : sp.ts (sp.slot a + 2 * sp.k + 6 : Nat) =
      Healing.drainTime sp a + 4 * sp.Δ := by
    rw [Healing.drainTime_eq]; simp only [ACParams.ts]; push_cast; ring
  linarith

/-- `report_in_frame`: an honest report lies in its reporter's tree above the fork-choice root. -/
theorem goldilocks_report_in_frame {cm : Time → Finset (Fin sp.n)}
    {y : Fin sp.n} {i : Nat} {R : AC.Blk sp.n (List (FG.Att sp.n))}
    (hrun : (goldilocksRunInterface sp sign G).Run cm proposer dg H tr)
    (hy : y ∈ H (tr.time i)) (hR : ReportAt tr y i R) :
    R ∈ (tr.state y i).fg.tree ∧ (tr.state y i).fg.Anc (tr.state y i).fg.fcRoot R := by
  have hrun := ((goldilocksRunInterface_run_iff cm).mp hrun).1
  obtain ⟨ell, hc, hto, hret⟩ := hR
  refine Healing.Growing.KernelProof.report_root_at hrun hy
    ⟨Compose.projAC_callAt.mpr hc, hto, ?_⟩
  rw [Obligations.Growing.projAC_state_at hrun hy]
  exact hret

/-- `origins_comparable` at the joined stored-fast-lock origin: two high honest origins by the
horizon, after a reset by it, are compatible. -/
theorem goldilocks_origins_comparable {cm : Time → Finset (Fin sp.n)} {βK : ℚ} {hold : Time}
    {g ΔF a b : Time} {x x' : Fin sp.n} {i j i' j' : Nat}
    {B B' : AC.Blk sp.n (List (FG.Att sp.n))} (hβ : βK ≤ 1 / 2)
    (hrun : (goldilocksRunInterface sp sign G).Run cm proposer dg H tr)
    (hp : Premises tr H cm βK proposer dg (fun v => v.val) g ΔF b hold)
    (hr : Healing.Growing.IsReset tr H g a) (hab : a ≤ b)
    (hac : OriginInCap sp.toParams sp.deepDepth g a)
    (hx : x ∈ H (max (cutZ sp.toParams g) (tr.time i)))
    (ho : tr.JoinedAt x (tr.time i) ∧ ∃ CV, Compose.StoredFastLockAt tr x i j B CV)
    (hib : tr.time i ≤ b) (hic : OriginInCap sp.toParams sp.deepDepth g (tr.time i))
    (hh : Healing.Growing.HZ tr H g + 1 ≤ ((tr.state x i).fg.σ B.root).h)
    (hx' : x' ∈ H (max (cutZ sp.toParams g) (tr.time i')))
    (ho' : tr.JoinedAt x' (tr.time i') ∧ ∃ CV, Compose.StoredFastLockAt tr x' i' j' B' CV)
    (hi'b : tr.time i' ≤ b)
    (hi'c : OriginInCap sp.toParams sp.deepDepth g (tr.time i'))
    (hh' : Healing.Growing.HZ tr H g + 1 ≤ ((tr.state x' i').fg.σ B'.root).h) :
    Compatible (tr.HonestBlocksAt H) B B' :=
  (resetPremisesUpTo_of_premises_cap hβ hrun hp hr hab hac).origins_compatible_at
    ⟨hx, ho.1, ho.2, hh⟩ (le_originCapTime hib hic) ⟨hx', ho'.1, ho'.2, hh'⟩
    (le_originCapTime hi'b hi'c)

/-- `heal_after_reset` at the drain `2k + 5`: honest proposals from `2k + 5` slots after the
reset's slot are chained through the horizon, one slot on with the service reserve and two or
more slots on. -/
theorem goldilocks_heal_after_reset {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    {g ΔF a b hold : Time} (hβ : βK ≤ 1 / 2)
    (hrun : (goldilocksRunInterface sp sign G).Run cm proposer dg H tr)
    (hp : Premises tr H cm βK proposer dg (fun v => v.val) g ΔF b hold)
    (hr : Healing.Growing.IsReset tr H g a) (hab : a ≤ b)
    (hbudget : ResetInBudget sp.toParams sp.deepDepth (2 * sp.k + 5) g a) :
    HealedFrom tr H proposer (sp.toParams.slotOf a + (2 * sp.k + 5)) b := by
  have hq := resetPremisesUpTo_of_premises_budget hβ hrun hp hr hab hbudget
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hts (u : Nat) : sp.toParams.slotTime u = sp.ts u := by
    rw [sp.slotTime_eq]; simp [ACParams.ts]
  have hpr {u : Nat} {w : Fin sp.n} {kw : Nat} {Y : AC.Blk sp.n (List (FG.Att sp.n))}
      (hY : HonestProposal tr H proposer u w kw Y) :
      Healing.Growing.HonestProposalRun tr H proposer u Y :=
    Healing.Growing.honestProposalRun_of_proposesAt_at hq.run hq.noColl
      (by rw [← hts]; exact hY.honest) hY.designated hY.proposes hY.slot
  intro s s' z z' k k' X X' hs hss hb hX hX'
  have hs' : sp.slot a + 2 * sp.k + 5 ≤ s := by
    have : sp.toParams.slotOf a = sp.slot a := rfl
    omega
  have hR : Healing.drainTime sp a ≤ sp.ts s := by
    rw [Healing.drainTime_eq]
    exact (AC.ts_le_iff sp).2 (by exact_mod_cast hs')
  rw [hts] at hb
  rcases Nat.lt_or_ge (s + 1) s' with h | h
  · exact Obligations.Growing.honest_proposal_below_later_upTo_at hq (hpr hX) hR (hpr hX')
      (by omega) (by linarith)
  · obtain rfl : s' = s + 1 := by omega
    have hle : sp.ts s ≤ sp.ts (s + 1 : Nat) := (AC.ts_le_iff sp).2 (by push_cast; omega)
    exact Obligations.Growing.honest_proposal_below_next_upTo_at hq (hpr hX) hR (hpr hX')
      (by linarith)

end Consensus.Goldilocks.Generic

end

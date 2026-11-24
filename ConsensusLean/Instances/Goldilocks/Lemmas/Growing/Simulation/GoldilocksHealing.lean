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

open AC (ACParams ReplayOrder Payload)
open Healing (cutZ)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
  {sign : Fin sp.n → Time → Bool} {G : Nat}

/-- The bundled premises of an interface run with a reset by its horizon form the finite reset
record: the committee facts come from the run under collision freedom, the service fields are the
same, and restarts after `ḡ` are excluded at every cut, so also at those by the horizon. -/
theorem resetPremisesUpTo_of_premises {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    {g ΔF a b : Time} (hβ : βK ≤ 1 / 2)
    (hrun : (goldilocksRunInterface sp ro sign G).Run cm proposer dg H tr)
    (hp : Premises tr H cm βK proposer dg (fun v => v.val) g ΔF b)
    (hr : Healing.Growing.IsReset tr H g a) (hab : a ≤ b) :
    Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK :=
  have hrun := (goldilocksRunInterface_run_iff cm).mp hrun
  { beta_le := hβ
    run := hrun.1
    committee_pos := hrun.2.1
    committeeFacts := hrun.2.2.2.1 hp.noColl
    committeeFaults := hp.committee
    noColl := hp.noColl
    sync := ⟨hp.sync.deltaF, hp.sync.message, hp.sync.block, hp.sync.relay, hp.sync.signedRow⟩
    awake := hp.awake
    faults := hp.faults
    reset := hr
    reset_le := hab
    snapshot := hp.snapshot
    catchUp := hp.catchUp
    noRestart := fun y k hy hk _ => hp.noRestart y k hy hk
    timeoutDelay := hp.timeoutDelay
    nonempty := hp.nonempty }

/-- `report_in_frame`: an honest report lies in its reporter's tree above the fork-choice root. -/
theorem goldilocks_report_in_frame {cm : Time → Finset (Fin sp.n)}
    {y : Fin sp.n} {i : Nat} {R : AC.Blk sp.n (List (FG.Att sp.n))}
    (hrun : (goldilocksRunInterface sp ro sign G).Run cm proposer dg H tr)
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
theorem goldilocks_origins_comparable {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    {g ΔF a b : Time} {x x' : Fin sp.n} {i j i' j' : Nat}
    {B B' : AC.Blk sp.n (List (FG.Att sp.n))} (hβ : βK ≤ 1 / 2)
    (hrun : (goldilocksRunInterface sp ro sign G).Run cm proposer dg H tr)
    (hp : Premises tr H cm βK proposer dg (fun v => v.val) g ΔF b)
    (hr : Healing.Growing.IsReset tr H g a) (hab : a ≤ b)
    (hx : x ∈ H (max (cutZ sp.toParams g) (tr.time i)))
    (ho : tr.JoinedAt x (tr.time i) ∧ ∃ CV, Compose.StoredFastLockAt tr x i j B CV)
    (hib : tr.time i ≤ b) (hh : Healing.Growing.HZ tr H g + 1 ≤ ((tr.state x i).fg.σ B.root).h)
    (hx' : x' ∈ H (max (cutZ sp.toParams g) (tr.time i')))
    (ho' : tr.JoinedAt x' (tr.time i') ∧ ∃ CV, Compose.StoredFastLockAt tr x' i' j' B' CV)
    (hi'b : tr.time i' ≤ b)
    (hh' : Healing.Growing.HZ tr H g + 1 ≤ ((tr.state x' i').fg.σ B'.root).h) :
    Compatible (tr.HonestBlocksAt H) B B' :=
  (resetPremisesUpTo_of_premises hβ hrun hp hr hab).origins_compatible_at
    ⟨hx, ho.1, ho.2, hh⟩ hib ⟨hx', ho'.1, ho'.2, hh'⟩ hi'b

/-- `heal_after_reset` at the drain `2k + 5`: honest proposals from `2k + 5` slots after the
reset's slot are chained through the horizon, one slot on with the service reserve and two or
more slots on. -/
theorem goldilocks_heal_after_reset {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    {g ΔF a b : Time} (hβ : βK ≤ 1 / 2)
    (hrun : (goldilocksRunInterface sp ro sign G).Run cm proposer dg H tr)
    (hp : Premises tr H cm βK proposer dg (fun v => v.val) g ΔF b)
    (hr : Healing.Growing.IsReset tr H g a) (hab : a ≤ b) :
    HealedFrom tr H proposer (sp.toParams.slotOf a + (2 * sp.k + 5)) b := by
  have hq := resetPremisesUpTo_of_premises hβ hrun hp hr hab
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

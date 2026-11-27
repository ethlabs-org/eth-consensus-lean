module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Node.Reachable
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Model
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.SignCalendar
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.SignedTickCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreStock
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RunCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Handlers
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Driven
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.SignTick
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Signing ticks and their report calls in the P-U run -/

namespace Consensus.Goldilocks.Shadow.PU.Growing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- An awake honest node has a signing tick when its calendar signs. -/
theorem signTickAt_of_calendar_at {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {sign : Fin sp.n → Time → Bool} (hcal : tr.SignCalendarAt proposer dg H sign)
    {y : Fin sp.n} {t : Time} (hy : y ∈ H t) (ht : 0 ≤ t)
    (hpub : sp.toParams.IsPublic t) (hawake : tr.awake y t) (hsign : sign y t = true) :
    ∃ j, tr.SignTickAt proposer dg y j t := by
  obtain ⟨j, hj⟩ := hrun.tick_of_awake y t hy ht hpub hawake
  obtain ⟨x, f, hg⟩ := (RunTrace.tickAt_iff ..).1 hj
  have hf : f = true := ((RunTrace.signCalendarAt_iff tr).1 hcal y j t x f hy hg).trans hsign
  subst hf
  exact ⟨j, (RunTrace.signTickAt_iff ..).2 ⟨x, hg⟩⟩

/-- A shadow node joins after every preceding restart is at least one slot old. -/
theorem joined_of_restart_le_at {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {t : Time} {s : Nat} (hy : y ∈ H t)
    (ht : sp.ts s + 4 * sp.Δ ≤ t)
    (hres : ∀ r, tr.time r ≤ t → y ∈ H (tr.time r) → tr.RestartAt y r → tr.time r ≤ sp.ts s)
    {i : Nat} (htime : tr.time i = t) :
    AC.joined sp (tr.projAC.state y i) (tr.time i) :=
  Healing.Growing.Core.joined_of_restart_le_at hrun.toCore hnc hy ht hres htime

end Consensus.Goldilocks.Shadow.PU.Growing

namespace Consensus.Goldilocks.Shadow.PU.Growing

open AC (ACParams ReplayOrder Payload)
open Node

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- At an update deadline, a signing tick's report immediately follows its AC tick,
with the same frame because the AC tick leaves the finality store unchanged. -/
theorem signing_tick_toFG_cuts_at {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {sign : Fin sp.n → Time → Bool} (hcal : tr.SignCalendarAt proposer dg H sign) {T : Time}
    (hT : ∃ u : Nat, T = sp.ts (u + 1 : Nat) + 2 * sp.Δ) {y : Fin sp.n} (hy : y ∈ H T)
    (haw : tr.awake y T) (hsig : sign y T = true) :
    ∃ k ell ell', tr.projAC.CallAt y k ell ∧ ell.call = .tick ∧ tr.time k = T ∧
      tr.projAC.CallAt y (k + 1) ell' ∧ ell'.call = .toFG ∧ tr.time (k + 1) = T ∧
      ell'.frame = ell.frame := by
  obtain ⟨u, rfl⟩ := hT
  have hT : sp.ts (u + 1 : Nat) + 2 * sp.Δ = sp.ts u + 6 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  have ht0 : 0 ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ := by
    have hΔ := sp.toParams.hΔ
    simp only [ACParams.ts]; positivity
  obtain ⟨j, hj⟩ := signTickAt_of_calendar_at hrun hcal hy ht0
    ⟨4 * (u : Int) + 6, by rw [hT]; simp only [ACParams.ts]; ring⟩ haw hsig
  obtain ⟨x, hg⟩ := (RunTrace.signTickAt_iff ..).1 hj
  have hnP : ¬ Proposes proposer y (sp.ts (u + 1 : Nat) + 2 * sp.Δ) := by
    rw [hT]
    exact Healing.not_proposes_update_time y u
  obtain ⟨hcj, htj⟩ := Healing.tick_first_cut hg
  have h1 : (exec proposer dg y (tr.state y j) (sp.ts (u + 1 : Nat) + 2 * sp.Δ)
      (.tick x true)).2[1]? = some
      (acToFG (tickStep proposer dg y (tr.state y j)
        (sp.ts (u + 1 : Nat) + 2 * sp.Δ) x .acTick).1
        (sp.ts (u + 1 : Nat) + 2 * sp.Δ)).2.1 := by
    rw [exec_eq, Healing.onTick_cuts]
    simp only [tickStep_eq, hnP, ↓reduceIte]
    split <;> simp [acToFG_eq, acCall_eq]
  obtain ⟨hcj1, htj1⟩ := Compose.group_cut hg h1
  simp only [acToFG_eq] at hcj1
  simp only [acCall_eq] at hcj
  have hl0 := (cutStep_ac _ _ _ _ _).1
    (hrun.cutLaw y j _ hcj (by rw [htj]; exact hy))
  have hl1 := (cutStep_ac _ _ _ _ _).1
    (hrun.cutLaw y (j + 1) _ hcj1 (by rw [htj1]; exact hy))
  refine ⟨j, _, _, Compose.projAC_callAt.2 hcj, rfl, htj,
    Compose.projAC_callAt.2 hcj1, rfl, htj1, ?_⟩
  rw [hl1.1, hl0.1, tr.state_succ_of_call hcj, Node.frame_eq, hl0.2.2.1]
  exact (Node.frame_eq _).symm

end Consensus.Goldilocks.Shadow.PU.Growing

end

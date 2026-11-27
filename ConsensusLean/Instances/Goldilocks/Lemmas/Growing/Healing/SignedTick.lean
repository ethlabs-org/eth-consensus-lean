module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.SignedTickCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreStock
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.SignTick
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Projection
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Signing ticks of a growing run

The facts every growing report path reads from a signing tick:

* a node honest at a public signing time of its calendar, and awake then, has a signing tick there
  (`signTickAt_of_calendar_at`);
* a node honest at `t` whose restarts up to `t` all lie by `t_u`, with `t_{u+1} ≤ t`, is joined at
  every cut at `t` (`joined_of_restart_le_at`);
* a signing tick at an update deadline has the adjacent update and `ac_to_fg` cuts at the same
  frame (`update_toFG_of_signTick_at`, from `Healing.toFG_second_cut_of_signing_tick`).
-/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
  {ini : Fin sp.n → (goldilocksNode sp ro).State}

/-- A node honest and awake at a public time its calendar signs has a signing tick there. -/
theorem signTickAt_of_calendar_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {sign : Fin sp.n → Time → Bool} (hcal : tr.SignCalendarAt proposer dg H sign)
    {y : Fin sp.n} {t : Time} (hy : y ∈ H t) (ht : 0 ≤ t)
    (hpub : sp.toParams.IsPublic t) (hawake : tr.awake y t) (hsign : sign y t = true) :
    ∃ j, tr.SignTickAt proposer dg y j t := by
  obtain ⟨j, x, f, hg⟩ := hrun.tick_of_awake y t hy ht hpub hawake
  have hf : f = true := (hcal y j t x f hy hg).trans hsign
  subst hf
  exact ⟨j, x, hg⟩

/-- **Joined from a restart bound.** A node honest at `t ≥ t_{u+1}` whose restarts up to `t` are
all at times `≤ t_u` is joined at every cut at `t`. -/
theorem joined_of_restart_le_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {t : Time} {u : Nat} (hy : y ∈ H t)
    (ht : sp.ts u + 4 * sp.Δ ≤ t)
    (hres : ∀ r, tr.time r ≤ t → y ∈ H (tr.time r) → tr.RestartAt y r → tr.time r ≤ sp.ts u)
    {i : Nat} (htime : tr.time i = t) :
    AC.joined sp (tr.projAC.state y i) (tr.time i) :=
  Core.joined_of_restart_le_at hrun.toCore hnc hy ht hres htime

/-- A signing tick at the update deadline has adjacent update and report cuts. Only this
tick's signing evidence is required; other ticks need not sign. -/
theorem update_toFG_of_signTick_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} {u j : Nat} (hy : y ∈ H (sp.ts u + 6 * sp.Δ))
    (hsign : tr.SignTickAt proposer dg y j (sp.ts u + 6 * sp.Δ))
    (hjoin : ∀ i, tr.time i = sp.ts u + 6 * sp.Δ →
      AC.joined sp (tr.projAC.state y i) (tr.time i)) :
    ∃ ell ell', AC.UpdateAt tr.projAC y j u ell ∧
      tr.projAC.CallAt y (j + 1) ell' ∧ ell'.call = .toFG ∧
      tr.time (j + 1) = sp.ts u + 6 * sp.Δ ∧ ell'.frame = ell.frame ∧
      AC.joined sp (tr.projAC.state y (j + 1)) (tr.time (j + 1)) := by
  obtain ⟨x, hg⟩ := hsign
  obtain ⟨ell, ell', hc, hcall, htj, hc1, hcall', htj1, hfr⟩ :=
    Healing.toFG_second_cut_of_signing_tick hg (Healing.not_proposes_update_time y u)
      fun i c hci hti => hrun.cutLaw y i c hci (by rw [hti]; exact hy)
  exact ⟨ell, ell', ⟨hc, hcall, htj, hjoin j htj⟩, hc1, hcall', htj1, hfr, hjoin (j + 1) htj1⟩

end Consensus.Goldilocks.Healing.Growing

end

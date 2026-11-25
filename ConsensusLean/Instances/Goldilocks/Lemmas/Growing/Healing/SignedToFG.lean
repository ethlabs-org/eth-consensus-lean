module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.UpdateCalls
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.SignedTick
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.SignTick
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Joined report calls at signing times

A public signing time supplies the entire FG update, including when the tick also proposes.
The report call is located after the proposal cuts rather than at a fixed offset. The tick and cut
facts are the shared ones of `Healing/Projection/SignTick` and `Growing/Healing/SignedTick`.
-/

namespace Consensus.Goldilocks.RunTrace

variable {P : Params} {A : NodeAC P}

/-- Every tick of a node honest at its time runs the FG update. -/
def GrowingAllTicksSign (tr : RunTrace A) (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (H : Time → Set (Fin P.n)) : Prop :=
  ∀ y j t, y ∈ H t → tr.TickAt proposer dg y j t → tr.SignTickAt proposer dg y j t

theorem growingAllTicksSign_iff {tr : RunTrace A} {proposer : Nat → Fin P.n}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)} :
    tr.GrowingAllTicksSign proposer dg H ↔
      ∀ y j t, y ∈ H t → tr.TickAt proposer dg y j t → tr.SignTickAt proposer dg y j t := by
  exact Iff.rfl

end Consensus.Goldilocks.RunTrace

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload gbar)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}
variable {hold : Time}

/-- A node honest at a public signing time has a signing tick there
(`signTickAt_of_calendar_at` from the premises' run). -/
theorem signTickAt_of_calendar {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {sign : Fin sp.n → Time → Bool} (hcal : tr.SignCalendarAt proposer dg H sign)
    {y : Fin sp.n} {t : Time} (hy : y ∈ H t) (ht : 0 ≤ t)
    (hpub : sp.toParams.IsPublic t) (hawake : tr.awake y t) (hsign : sign y t = true) :
    ∃ j, tr.SignTickAt proposer dg y j t :=
  signTickAt_of_calendar_at hp.run hcal hy ht hpub hawake hsign

/-- **A node honest at a time after a ready slot's update deadline is joined at every cut then**:
its restarts are before `ḡ`, before the slot preceding that time (`joined_of_restart_le_at`). -/
theorem ResetPremisesUpTo.joined_at_of_ready
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {t : Time} {u : Nat} (hy : y ∈ H t)
    (hu : sp.ts (sp.slot (gbar g) + 1 : Nat) ≤ sp.ts u)
    (ht : sp.ts u + 6 * sp.Δ ≤ t) (htb : t ≤ b) {i : Nat} (htime : tr.time i = t) :
    AC.joined sp (tr.projAC.state y i) (tr.time i) :=
  joined_of_restart_le_at hp.run hp.noColl hy (by linarith [sp.toParams.hΔ])
    (fun _ hrt hyr hrs => (hp.restart_le_before_at hyr hrs (hrt.trans htb)).trans hu) htime

/-- At a public signing time after a ready slot's update deadline, a node honest then executes
a joined `ac_to_fg` call. Proposal cuts may occur before this call in the same tick. -/
theorem ResetPremisesUpTo.toFG_call_of_sign
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {sign : Fin sp.n → Time → Bool} (hcal : tr.SignCalendarAt proposer dg H sign)
    {y : Fin sp.n} {t : Time} {u : Nat} (hy : y ∈ H t)
    (hu : sp.ts (sp.slot (gbar g) + 1 : Nat) ≤ sp.ts u)
    (ht : sp.ts u + 6 * sp.Δ ≤ t) (htb : t ≤ b)
    (hpub : sp.toParams.IsPublic t) (hawake : tr.awake y t) (hsign : sign y t = true) :
    ∃ i ell, tr.projAC.CallAt y i ell ∧ ell.call = .toFG ∧ tr.time i = t ∧
      AC.joined sp (tr.projAC.state y i) (tr.time i) := by
  have hΔ := sp.toParams.hΔ
  have ht0 : 0 ≤ t := by
    have hu0 : 0 ≤ sp.ts u := by simp only [ACParams.ts]; positivity
    linarith
  obtain ⟨j, x, hg⟩ := signTickAt_of_calendar hp hcal hy ht0 hpub hawake hsign
  obtain ⟨k, ell, hc, hcall, htime⟩ := Healing.toFG_call_of_signing_tick hg
  exact ⟨j + k, ell, hc, hcall, htime, hp.joined_at_of_ready hy hu ht htb htime⟩

end Consensus.Goldilocks.Healing.Growing

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.SignCalendar
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.SignedTickCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RunCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Handlers

public section

/-! # Signing ticks and their report calls in the P-U run -/

namespace Consensus.Goldilocks.Shadow.PU.Growing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace' sp ro}

/-- An awake honest node has a signing tick when its calendar signs. -/
theorem signTickAt_of_calendar_at' {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    {sign : Fin sp.n → Time → Bool} (hcal : tr.SignCalendarAt' proposer dg H sign)
    {y : Fin sp.n} {t : Time} (hy : y ∈ H t) (ht : 0 ≤ t)
    (hpub : sp.toParams.IsPublic t) (hawake : tr.awake y t) (hsign : sign y t = true) :
    ∃ j, tr.SignTickAt' proposer dg y j t := by
  obtain ⟨j, hj⟩ := hrun.tick_of_awake y t hy ht hpub hawake
  obtain ⟨x, f, hg⟩ := (RunTrace.tickAt'_iff ..).1 hj
  have hf : f = true := ((RunTrace.signCalendarAt'_iff tr).1 hcal y j t x f hy hg).trans hsign
  subst hf
  exact ⟨j, (RunTrace.signTickAt'_iff ..).2 ⟨x, hg⟩⟩

/-- A shadow node joins after every preceding restart is at least one slot old. -/
theorem joined_of_restart_le_at' {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {t : Time} {s : Nat} (hy : y ∈ H t)
    (ht : sp.ts s + 4 * sp.Δ ≤ t)
    (hres : ∀ r, tr.time r ≤ t → y ∈ H (tr.time r) → tr.RestartAt y r → tr.time r ≤ sp.ts s)
    {i : Nat} (htime : tr.time i = t) :
    AC.joined sp (tr.projAC.state y i) (tr.time i) :=
  Healing.Growing.Core.joined_of_restart_le_at hrun.toCore hnc hy ht hres htime

end Consensus.Goldilocks.Shadow.PU.Growing

namespace Consensus.Goldilocks.Healing

open Node

variable {P : Params} {A : NodeAC P} {dg : Digest (List (FG.Att P.n)) A.Payload}
  {tr : RunTrace A} {proposer : Nat → Fin P.n}

/-- A shadow signing tick executes `ac_to_fg` at its own time. -/
theorem toFG_call_of_signing_tick' {y : Fin P.n} {j : Nat} {t : Time} {x : Nat}
    (hg : tr.GroupAt' proposer dg y j t (.tick x true)) :
    ∃ k ell, tr.projAC.CallAt y (j + k) ell ∧ ell.call = .toFG ∧ tr.time (j + k) = t := by
  let st₁ := (tickStep' proposer dg y (tr.state y j) t x .acTick).1
  let st₂ := (tickStep' proposer dg y st₁ t x .proposal).1
  have hcuts : (exec' proposer dg y (tr.state y j) t (.tick x true)).2 =
      (tickStep' proposer dg y (tr.state y j) t x .acTick).2 ++
      (tickStep' proposer dg y st₁ t x .proposal).2 ++
      (tickStep' proposer dg y st₂ t x .fgUpdate).2 := by
    simp only [exec'_eq, onTick'_eq, runSteps'_eq, tickSteps, ↓reduceIte,
      List.foldl_cons, List.foldl_nil, List.nil_append, st₁, st₂]
  have hmem : (acToFG' st₂ t).2.1 ∈ (tickStep' proposer dg y st₂ t x .fgUpdate).2 := by
    simp only [tickStep'_eq]
    split <;> simp
  obtain ⟨ell, he⟩ : ∃ ell : ACLabel A, (acToFG' st₂ t).2.1 = .ac ell := by
    rw [acToFG'_eq]
    exact ⟨_, rfl⟩
  rw [he] at hmem
  have hcall : ell.call = .toFG := by
    rw [acToFG'_eq] at he
    cases he
    rfl
  have hmem' : Cut.ac ell ∈ (exec' proposer dg y (tr.state y j) t (.tick x true)).2 := by
    rw [hcuts]
    exact List.mem_append_right _ hmem
  obtain ⟨k, hk, he⟩ := List.getElem_of_mem hmem'
  have hget : (exec' proposer dg y (tr.state y j) t (.tick x true)).2[k]? = some (.ac ell) :=
    List.getElem?_eq_some_iff.2 ⟨hk, he⟩
  obtain ⟨hc, ht⟩ := Compose.group_cut' hg hget
  exact ⟨k, ell, Compose.projAC_callAt.2 hc, hcall, ht⟩

end Consensus.Goldilocks.Healing

end

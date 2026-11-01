module
public import AvailableChainFGCompose.Proofs.Finality.Joined
public import AvailableChainFGCompose.Proofs.Finality.Forward

set_option linter.privateModule false

public section
namespace AvailableChain.FGCompose.Tests.P0d7bb
open AvailableChain.SimplexFG AvailableChain.KitFG

/-! P0d7b-b G0 (pure data). (A) the forward round from the recurrence: exact start and finite
horizon; (B) the joined kernel premise with an independent FG quorum and no recovery bound;
(C) the guarded opening premise on a run whose proposer joins after round 1.
Timing: Δ = 1, R = 4, ΔF = 1 (κ = 2, P = 16, β = 8), g = 1, so W_W = 57. -/

private abbrev xT : FGTiming where
  delta := 1
  roundSlots := 4
  proposal s := 4 * (s : Time) * 1
  vote s := 4 * (s : Time) * 1 + 1
  early s := 4 * (s : Time) * 1 + 2 * 1
  freeze s := 4 * (s : Time) * 1 + 3 * 1
  release s := 4 * (s : Time) * 1 + 5 * 1
  gate s := 4 * (s : Time) * 1 + 6 * 1
  action r := 4 * ((r * 4 : Nat) : Time) * 1 + 6 * 1

private theorem xL : FGTimingLaws xT where
  delta_pos := by decide
  rounds := by decide
  proposal_eq _ := rfl
  vote_eq _ := rfl
  early_eq _ := rfl
  freeze_eq _ := rfl
  release_eq _ := rfl
  gate_eq _ := rfl
  action_eq _ := rfl

private theorem xKappa : kappaF xT 1 = 2 := by decide

private theorem xValues : FGCompose.P xT = 16 ∧ betaF xT 1 = 8 ∧ W_W xT 1 1 = 57 ∧
    ∀ r : Nat, kernelDeadlineW xT 1 (r + 2) = ((r : Time) + 2) * 16 + 9 := by
  refine ⟨by decide, by decide, by decide, fun r => ?_⟩
  unfold kernelDeadlineW betaF FGCompose.P
  rw [xKappa]
  push_cast
  ring

private abbrev xH (s : Slot) : Prop := 0 < s

private theorem xGood (r : Nat) (hr : 1 ≤ r) :
    Gen.Pure.FGoodE_W xH xT.roundSlots (kappaF xT 1) r := by
  rw [Gen.Pure.FGoodE_W_def, xKappa]
  change 0 < r * 4 ∧ 0 < (r + 1) * 4 ∧
    (∃ c : Nat, (r + 1) * 4 + 2 ≤ c ∧ c ≤ (r + 2) * 4 ∧ 0 < c) ∧ 0 < (r + 2) * 4 + 2
  exact ⟨by omega, by omega, ⟨(r + 1) * 4 + 2, le_rfl, by omega, by omega⟩, by omega⟩

/-- The recurrence from start 0 with every positive slot honest. -/
private theorem xRecur (horizon : Time) : FE_W xT 1 xH 0 horizon 1 := by
  refine ⟨le_rfl, fun q hq _ _ => ⟨q, ?_, xGood q hq⟩⟩
  rw [Gen.Pure.InWindow_def]
  omega

/-- premises_sat for `forward_round_FE` at t = 20: recurrence from 0, 0 < t, start ≤ t and
the horizon exactly t + W_W = 77. -/
private theorem xForward_premises_sat :
    FE_W xT 1 xH 0 77 1 ∧ (0 : Time) < 20 ∧ (0 : Time) ≤ 20 ∧ 20 + W_W xT 1 1 ≤ (77 : Time) :=
  ⟨xRecur 77, by decide, by decide, by rw [xValues.2.2.1]; decide⟩

/-- POSITIVE: the generic forward round; the returned round is inspected: it is exactly
q = r = 2 (period start 32), with kernel deadline 73 < 77 inside the horizon. -/
private theorem xForward : ∃ q r : Nat, q = 2 ∧ r = 2 ∧
    Gen.Pure.FGoodE_W xH xT.roundSlots (kappaF xT 1) r ∧
    kernelDeadlineW xT 1 (r + 2) = 73 ∧ kernelDeadlineW xT 1 (r + 2) < 20 + W_W xT 1 1 ∧
    kernelDeadlineW xT 1 (r + 2) ≤ (77 : Time) := by
  obtain ⟨q, r, htq, hqt, hr, hgood, _, hD, hhor⟩ := forward_round_FE xT xL
    xForward_premises_sat.1 xForward_premises_sat.2.1 xForward_premises_sat.2.2.1
    xForward_premises_sat.2.2.2
  rw [xValues.1] at htq hqt
  rw [Gen.Pure.InWindow_def] at hr
  dsimp only [Time] at htq hqt
  have hq : q = 2 := by omega
  have hr2 : r = 2 := by omega
  subst hq hr2
  exact ⟨2, 2, rfl, rfl, hgood, by rw [xValues.2.2.2]; decide, hD, hhor⟩

private abbrev xLate (s : Slot) : Prop := 40 ≤ s

/-- NEGATIVE (recurrence start): honest slots only from slot 40 give the recurrence from
start 160, but at t = 20 < 160 the aligned window has no good round. -/
private theorem xStartNeeded : FE_W xT 1 xLate 160 1000 1 ∧
    ¬ ∃ q r : Nat, (20 : Time) ≤ (q : Time) * FGCompose.P xT ∧
      (q : Time) * FGCompose.P xT < 20 + FGCompose.P xT ∧ Gen.Pure.InWindow q 1 r ∧
      Gen.Pure.FGoodE_W xLate xT.roundSlots (kappaF xT 1) r := by
  refine ⟨⟨le_rfl, fun q _ hs _ => ⟨q, ?_, ?_⟩⟩, ?_⟩
  · rw [Gen.Pure.InWindow_def]
    omega
  · rw [xValues.1] at hs
    dsimp only [Time] at hs
    have hq : 10 ≤ q := by omega
    rw [Gen.Pure.FGoodE_W_def, xKappa]
    change 40 ≤ q * 4 ∧ 40 ≤ (q + 1) * 4 ∧
      (∃ c : Nat, (q + 1) * 4 + 2 ≤ c ∧ c ≤ (q + 2) * 4 ∧ 40 ≤ c) ∧ 40 ≤ (q + 2) * 4 + 2
    exact ⟨by omega, by omega, ⟨(q + 1) * 4 + 2, le_rfl, by omega, by omega⟩, by omega⟩
  · rintro ⟨q, r, htq, hqt, hr, hgood⟩
    rw [xValues.1] at htq hqt
    rw [Gen.Pure.InWindow_def] at hr
    rw [Gen.Pure.FGoodE_W_def] at hgood
    have h1 : 40 ≤ r * 4 := hgood.1
    dsimp only [Time] at htq hqt
    omega

/-- NEGATIVE (finite horizon): below the first guard (horizon 56 < 57) the recurrence holds
with no honest slot at all, and no time t > 0 has its window inside the horizon. -/
private theorem xHorizonNeeded : FE_W xT 1 (fun _ => False) 0 56 1 ∧
    ∀ t : Time, 0 < t → ¬ t + W_W xT 1 1 ≤ 56 := by
  refine ⟨⟨le_rfl, fun q hq _ hguard => ?_⟩, fun t ht h => ?_⟩
  · rw [xValues.1, xValues.2.1] at hguard
    dsimp only [Time] at hguard
    push_cast at hguard
    omega
  · rw [xValues.2.2.1] at h
    dsimp only [Time] at h ht
    omega

/-! (B) The joined kernel premise at round 1 (opening time 16), horizon 57 = its deadline. -/

private abbrev xSP : FGServicePoint := ⟨⟨0, 0, 0, 0, 0, .genesis⟩, 0, .genesis, 0⟩

/-- premises_sat: every field; the service predicate names exactly one point. The premise
has no recovery-bound field: only κ ≤ R, the window, the start, the deadline and the quorum. -/
private theorem xJoined_premises_sat :
    KernelJoinedPrem xT 1 57 1 xH 1 1 8 2 (· = xSP) where
  bound := ⟨by rw [xKappa]; decide⟩
  window := xGood 1 le_rfl
  start := ⟨xSP, rfl, by decide⟩
  hhor := by rw [xValues.2.2.2]; decide
  honest_quorum := le_rfl
  timeout_eq := rfl
  capacity_ge := le_rfl

/-- POSITIVE: the generic join returns the kernel premise at the same service point. -/
private theorem xJoined :
    KernelPrem_W xT 1 57 xSP ⟨1⟩ xH 1 1 8 2 := by
  obtain ⟨sp, hsp, hK⟩ := finality_kernel_prem_W_of_joined xJoined_premises_sat
  exact hsp ▸ hK

/-- NEGATIVE (independent live FG quorum): window, start, deadline, timeout and capacity
are as in the positive; honest FG weight 1 below quorum 2 alone refutes the premise. -/
private theorem xQuorumNeeded : ¬ KernelJoinedPrem xT 1 57 1 xH 2 1 8 2 (· = xSP) :=
  fun h => absurd h.honest_quorum (by decide)

/-- NEGATIVE (service start): a service point that starts after the opening period. -/
private theorem xLateService :
    ¬ KernelJoinedPrem xT 1 57 1 xH 1 1 8 2
      (· = ⟨⟨0, 0, 0, 0, 0, .genesis⟩, 0, .genesis, 17⟩) := by
  intro h
  obtain ⟨sp, rfl, hstart⟩ := h.start
  exact absurd hstart (by decide)

/-- NEGATIVE (finite horizon): one unit short of the kernel deadline 57. -/
private theorem xJoinedHorizonShort : ¬ KernelJoinedPrem xT 1 56 1 xH 1 1 8 2 (· = xSP) := by
  intro h
  have := h.hhor
  rw [xValues.2.2.2] at this
  exact absurd this (by decide)

/-! (C) The guarded opening premise. One honest node proposes only from slot 12 (time 48):
before that its duty emits nothing (a join cut after round 1). With t = 40 the guarded
premise (rounds with t ≤ r·P, here r = 3) holds on this run; the unguarded premise fails at
round 1. Interface model, not an ExecutionValid FG-SA or PC-SA run. -/

private abbrev oP : V2.ProtocolSpecD Unit where
  State := Unit
  Label := Nat
  Duty := Nat
  signLabel d := d / 4
  seats _ := 1
  Payload := Block
  Durable := Unit
  init := ()
  clock st _ := st
  actTime d := (d : Time)
  duties t := if 0 ≤ t then [t.toNat] else []
  duties_spec s t := by
    split
    · next ht =>
      simp only [List.mem_singleton]
      constructor
      · intro hs; subst s; exact Int.toNat_of_nonneg ht
      · intro hs; subst t; simp
    · next ht =>
      constructor
      · intro hm; cases hm
      · intro hs; exact False.elim (ht (hs ▸ Int.natCast_nonneg s))
  duties_nodup t := by split <;> simp
  act _ d _ := if 48 ≤ d then some .genesis else none
  gossip _ _ := []
  process st _ := st
  selfVisible _ := true
  recordOwn st _ := st
  durable st := st
  restore st _ := st
  wellFormed _ := true
  depsPresent _ _ := true
  processed _ _ := false
  excludes _ _ := false
  handles _ _ _ := False
  carries _ _ := False

private noncomputable abbrev oI : V2.D.Interface oP where
  confirmed _ := .genesis
  stable _ := .genesis
  block := some
  opening _ := True
  propLabel s := s
  propDuty s := 4 * s
  propDuty_label s := Nat.mul_div_cancel_left s (by decide)
  propLabel_single _ := rfl
  propLabel_injective := fun _ _ h => h

private noncomputable abbrev oEnv : Generic.Env Unit := ⟨1, by decide, 0, le_rfl, fun _ _ => true⟩

private noncomputable abbrev oRun : V2.D.Run Unit oP where
  honest := {()}
  horizon := 60
  events := [.tick () 16, .tick () 48]
  seatOf _ _ := ()
  input _ _ := ()

/-- The slot-12 duty emits one proposal object at the tick of time 48. -/
private theorem oEmits12 : ∃ o : oP.Object,
    V2.D.Run.emits oEnv oRun () o 48 ∧ oI.block o.payload = some .genesis :=
  ⟨⟨.seat 12 ⟨0, by decide⟩, .genesis⟩, ⟨1, rfl, by decide +kernel⟩, rfl⟩

/-- The slot-4 duty emits nothing at the tick of time 16. -/
private theorem oEmits4 : ∀ o : oP.Object, ¬ V2.D.Run.emits oEnv oRun () o 16 := by
  rintro o ⟨i, hi, ho⟩
  match i, hi, ho with
  | 0, _, ho =>
    have he : V2.D.Run.emitsAt oEnv oRun 0 = [] := by decide +kernel
    rw [he] at ho
    cases ho
  | 1, hi, _ => exact absurd hi (by decide)
  | (_ + 2), hi, _ => cases hi

/-- POSITIVE (premises_sat of the guarded premise): at t = 40 every honest round with
t ≤ r·P inside the horizon 60 (only r = 3) has an actual honest proposal. -/
private theorem oGuarded : ∀ r : Nat, xH (r * xT.roundSlots) →
    (40 : Time) ≤ (r : Time) * FGCompose.P xT → xT.proposal (r * xT.roundSlots) ≤ oRun.horizon →
    ∃ A, HonestProposal oEnv oRun oI (r * xT.roundSlots) A := by
  intro r _ htr hh
  rw [xValues.1] at htr
  change 4 * ((r * 4 : Nat) : Time) * 1 ≤ 60 at hh
  dsimp only [Time] at htr hh
  have hr : r = 3 := by push_cast at hh; omega
  subst hr
  obtain ⟨o, ho, hb⟩ := oEmits12
  exact ⟨.genesis, ⟨by decide, Finset.mem_singleton_self _⟩, o, ho, hb⟩

/-- NEGATIVE: the unguarded premise is false on the same run: round 1 (slot 4, time 16) is
honest and inside the horizon, but its duty emitted no proposal. -/
private theorem oUnguardedFails : ¬ ∀ r : Nat, xH (r * xT.roundSlots) →
    xT.proposal (r * xT.roundSlots) ≤ oRun.horizon →
    ∃ A, HonestProposal oEnv oRun oI (r * xT.roundSlots) A := by
  intro h
  obtain ⟨A, _, o, ho, _⟩ := h 1 (by decide) (by decide)
  exact oEmits4 o ho

#print axioms xForward
#print axioms xStartNeeded
#print axioms xHorizonNeeded
#print axioms xJoined_premises_sat
#print axioms xJoined
#print axioms xQuorumNeeded
#print axioms xLateService
#print axioms xJoinedHorizonShort
#print axioms oGuarded
#print axioms oUnguardedFails

end AvailableChain.FGCompose.Tests.P0d7bb
end

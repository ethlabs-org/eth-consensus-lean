module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Opponents
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Timing
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks: the view and the relay window of a proposal call

Two facts of an `ac_proposal` call at `t_s`, read off one AC state and one AC trace:

* `acProposal_pay_view`: the call's payload view of slot `s − 1` has the caller's slot-`(s−1)`
  pool votes with a finite stamp as its votes, and those also resolved in the frame as its
  support;
* `proposal_relay_deadline`: with the caller's restarts up to the call at or before `t_{s−1}`,
  the relay deadline of an acceptance by `t_{s−1} + 2Δ` is at most `t_{s−1} + 3Δ` at every cut up
  to the call, and the call is after it.

The proposal walk of `Service/PivotSteps` (constant faults) and of its growing-fault form use
both; the restarts are their users' (`proposal_call_restarts`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams Payload)

variable {sp : SAParams} {FGP : Type}

/-- **The payload view of a proposal call**: when `ac_proposal` at a time of slot `s + 1` returns
`(d, pay)`, the votes of `pay`'s view are the slot-`s` pool votes of `A` with a finite stamp, and
its support those of them resolved in `Φ`. -/
theorem acProposal_pay_view {A : SA.SAState sp.n} {Φ : SA.Frm sp.n FGP} {t : Time} {s : Nat}
    {d : DutyHead sp.n FGP (Payload sp.n)} {pay : Payload sp.n}
    (hd : (SA.acProposal sp A Φ t).2 = some (d, pay)) (hsl : sp.slot t = s + 1) :
    (∀ v, v ∈ (SA.View.ofLists pay).votes ↔ v ∈ A.pool s ∧ A.voteStamp v < ⊤) ∧
      ∀ v, v ∈ (SA.View.ofLists pay).support ↔
        (v ∈ A.pool s ∧ A.voteStamp v < ⊤) ∧ SA.resolutionTime A Φ v < ⊤ := by
  obtain ⟨-, hpay, -⟩ := SA.proposal_payload hd
  rw [hsl, show (((s + 1 : Nat) : Int) - 1) = (s : Int) by push_cast; ring] at hpay
  subst hpay
  refine ⟨fun v => ?_, fun v => ?_⟩
  · simp [SA.View.ofLists, SA.voteViewList, SA.SAState.poolAt]
  · simp [SA.View.ofLists, SA.voteViewList, SA.SAState.poolAt]
    tauto

/-- **The relay window before a proposal call**: let `p`'s call at cut `i` be at `t_s`, with
every restart of `p` up to `i` at or before `t_{slot(i)−1}`. Then the deadline of an acceptance
at `kx`, by `t_{s−1} + 2Δ`, is at most `t_{s−1} + 3Δ` at every cut up to `i`, and at most the
time of `i`. -/
theorem proposal_relay_deadline {A : ACInterface sp.toParams FGP} {T : ACTrace A}
    {p : Fin sp.n} {i kx s : Nat} (hti : T.time i = sp.ts s)
    (hrs : ∀ c ≤ i, T.RestartAt p c → T.time c ≤ sp.ts ((sp.slot (T.time i) : Int) - 1))
    (hkx : T.time kx ≤ sp.ts ((s : Int) - 1) + 2 * sp.Δ) :
    (∀ c ≤ i, T.deadline p c (T.time kx) ≤ sp.ts ((s : Int) - 1) + 3 * sp.Δ) ∧
      T.deadline p i (T.time kx) ≤ T.time i := by
  have hΔ := sp.toParams.hΔ
  have hsi : sp.slot (T.time i) = s := by
    rw [hti]; simpa using (SA.slot_arithmetic sp s).1 0 (by omega)
  have hts : sp.ts (s : Int) = sp.ts ((s : Int) - 1) + 4 * sp.Δ := by
    simp only [SAParams.ts]; ring
  rw [hsi] at hrs
  have hdl : ∀ c ≤ i, T.deadline p c (T.time kx) ≤ sp.ts ((s : Int) - 1) + 3 * sp.Δ :=
    fun c hc' => by
      have h1 := ac_deadline_le_of_restarts (T := T)
        (fun k hk hrk => hrs k (hk.trans hc') hrk) (T.time kx)
      have h2 := max_le hkx (show sp.ts ((s : Int) - 1) ≤ sp.ts ((s : Int) - 1) + 2 * sp.Δ from
        le_add_of_nonneg_right (mul_nonneg zero_le_two hΔ.le))
      linarith only [h1, h2]
  refine ⟨hdl, ?_⟩
  have := hdl i le_rfl
  linarith only [this, hti, hts, hΔ]

end Consensus.Goldilocks.Compose

end

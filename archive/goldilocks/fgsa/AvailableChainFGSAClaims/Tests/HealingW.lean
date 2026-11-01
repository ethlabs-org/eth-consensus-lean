module
public import AvailableChainFGSAClaims.Statements.Packages.Healing -- shake: keep (package examples)

-- Concrete regime inhabitants; production modules must not import Tests.
set_option linter.privateModule false
set_option linter.defProp false

@[expose] public section

/-! ROOT-DIGEST W3: explicit small roots for statement fixtures. -/

namespace AvailableChain.FGSA.Run.Tests.HealingW

-- A concrete FG-SA run. The time-zero tick is required by tick_total.
private abbrev smokeParams : Params :=
  ⟨⟨1, 1, 2, 0, by decide, by decide, by decide, by decide⟩, 3, 6, by decide, 2, by decide, fun d =>
      ⟨d.slot + 1⟩⟩
private abbrev smokeCodec : AppCodec Nat := ⟨id, some, fun _ => rfl⟩
private abbrev smokeEnv : Generic.Env (Fin 1) := ⟨1, by decide, 0, le_rfl, fun _ _ => true⟩
private abbrev smokeRun : V2.D.Run (Fin 1) (fgsa smokeParams smokeCodec) where
  honest := Finset.univ
  horizon := 0
  events := [.tick 0 0]
  seatOf := fun _ _ => 0
  input := fun _ _ => 0

private def smokeSchedule : V2.D.ScheduleWellFormed smokeEnv smokeRun where
  horizon_nonneg := le_rfl
  sorted := List.pairwise_singleton _ _
  nodup := List.nodup_singleton _
  in_horizon := by intro e he; simp only [List.mem_singleton] at he; subst e; exact ⟨le_rfl, le_rfl⟩
  honest_only := by intro e _; exact Finset.mem_univ _
  tick_public := by
    intro v t ht
    have he : V2.Event.tick v t = .tick 0 0 := List.mem_singleton.mp ht
    cases he
    exact ⟨0, rfl⟩
  tick_total := by
    intro v _ t _ ht hh _
    have he : t = 0 := le_antisymm hh ht
    subst t
    have hv : v = 0 := Subsingleton.elim _ _
    subst v
    exact List.mem_singleton_self _

private def smokeNoDelivery (i : Nat) (v : Fin 1) (o : (fgsa smokeParams smokeCodec).Object)
    (t : Time) : smokeRun.events[i]? ≠ some (.deliver v o t) := by
  cases i <;> simp

/-- Horizon zero with no faulty validator and GST zero. This is only a smoke test. -/
private def smoke_base : Base₂ smokeParams smokeCodec smokeEnv smokeRun where
  receiptIdealization := by
    have scope (B : NamedProposal smokeParams.n)
        (h : NamedProposalInRun smokeParams smokeCodec smokeEnv smokeRun B) :
        B = .genesis := by
      obtain ⟨C, hC, hBC⟩ := h
      have hc : C = .genesis := by
        rcases hC with ⟨v, o, t, hm, _⟩ | ⟨v, hv, i, hm⟩
        · simp at hm
        · have hi : ∀ i : Nat, ∀ v : Fin 1,
              (V2.D.Run.stateBefore smokeEnv smokeRun i v).st.namedBodies = [.genesis] := by
            intro i v
            have hv : v = 0 := Subsingleton.elim _ _
            subst v
            cases i <;> simp only [V2.D.Run.stateBefore, smokeRun, List.take_succ_cons,
              List.take_nil, List.foldl_cons, List.foldl_nil] <;> rfl
          rw [hi] at hm
          exact List.mem_singleton.mp hm
      rw [hc] at hBC
      exact of_decide_eq_true hBC
    have receiptScope (B : NamedProposal smokeParams.n)
        (h : NamedProposalReceiptScope smokeParams smokeCodec smokeEnv smokeRun B) :
        B = .genesis := by
      rcases h with h | ⟨v, _, o, t, N, ⟨i, hi, hem⟩, _, _⟩
      · exact scope B h
      · cases i with
        | zero =>
          have he : 0 = v ∧ 0 = t := by simpa using hi
          rcases he with ⟨rfl, rfl⟩
          change o ∈ [] at hem
          exact (List.not_mem_nil hem).elim
        | succ i => simp at hi
    intro A B hA hB _
    exact (receiptScope A hA).trans (receiptScope B hB).symm
  valid := {
    toScheduleWellFormed := smokeSchedule
    tick_awake := by intros; rfl
    deliver_awake := by intros; rfl
    restart_awake := by intros; rfl
    wake_restart := by intro v hv t ht hh hw; cases hw.2
    wire := by intro i v o t h; exact (smokeNoDelivery i v o t h).elim
    deps := by intro i v o t h; exact (smokeNoDelivery i v o t h).elim
    fresh := by intro i v o t h; exact (smokeNoDelivery i v o t h).elim
    unforgeable := by rintro v o t ⟨i, hi⟩; exact (smokeNoDelivery i v o t hi).elim
    carried := by rintro v o t ⟨i, hi⟩; exact (smokeNoDelivery i v o t hi).elim }
  linked := by
    refine ⟨1, Equiv.refl _, ?_⟩
    intro ℓ hℓ
    rcases ℓ with (_ | _) | _
    · exact hℓ.elim
    · exact ⟨rfl, fun i => Subsingleton.elim _ _⟩
    · exact hℓ.elim
  cstar := by
    intro ℓ hℓ
    rcases ℓ with (_ | _) | _
    · change Function.Bijective (fun _ : Fin 1 => (0 : Fin 1))
      exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun v => ⟨0, Subsingleton.elim _ _⟩⟩
    · exact hℓ.elim
    · exact hℓ.elim
  restartsAtWakes := by intro v t h; simp at h
  delta := rfl

/-- A concrete finite run, with all validators honest and awake.
This checks package consistency, not completion of a healing search. -/
private def healingSet (ΔF : Time) (hF : 1 ≤ ΔF) :
    HealingSet smokeParams smokeCodec smokeEnv smokeRun 4 ΔF where
  deltaF := hF
  sync := by
    refine { broadcast_emitted := ?_, relay_accepted := ?_ }
    · rintro v _ o t _ w _ a _ _ _ hd _ _ _
      have hdelay : 0 < fgsaDelay (p := smokeParams) smokeEnv.Δ ΔF o := by
        cases o with
        | mk a m =>
          cases m <;> simp only [fgsaDelay]
          all_goals first | exact (by decide) | exact lt_of_lt_of_le (by decide) hF
      change max a 0 + fgsaDelay smokeEnv.Δ ΔF o ≤ 0 at hd
      exact (not_le_of_gt
        (lt_add_of_le_of_pos (le_max_right a (0 : Time)) hdelay) hd).elim
    · rintro v _ i o t ⟨⟨o', hi, _⟩, _⟩
      exact (smokeNoDelivery i v o' t hi).elim
  gap := by
    intro t ht hh
    change 0 ≤ t at ht
    change t + 4 ≤ 0 at hh
    exact (not_le_of_gt (lt_add_of_le_of_pos ht (by decide)) hh).elim
  base := smoke_base
  fault := by rw [Gen.V2.Duty.faulty_def]; decide
  awake := by intros; rfl
  gapPos := le_rfl
  suffixNoRestart := by intro v hv i t hi; cases i <;> simp at hi
  joinedGap := by
    intro t ht hh
    change 0 + 6 ≤ t at ht
    change t + 4 ≤ 0 at hh
    dsimp [Time] at ht hh
    omega

example : 2 * smokeParams.Δ < (6 : Time) ∧ kappaF smokeParams 6 = 3 := by decide
example : kappaF smokeParams smokeEnv.Δ = 2 := by decide
example : LivenessBoundW smokeParams 6 := ⟨by decide⟩
example : LivenessBoundW smokeParams smokeEnv.Δ := ⟨by decide⟩
example : HealingSet smokeParams smokeCodec smokeEnv smokeRun 4 6 :=
  healingSet 6 (by decide)
example : HealingSet smokeParams smokeCodec smokeEnv smokeRun 4 smokeEnv.Δ :=
  healingSet smokeEnv.Δ (by decide)
example : HealingPrem smokeParams smokeCodec 4 6 smokeEnv smokeRun () :=
  ⟨healingSet 6 (by decide), ⟨by decide⟩⟩
example : HealingPrem smokeParams smokeCodec 4 smokeEnv.Δ smokeEnv smokeRun () :=
  ⟨healingSet smokeEnv.Δ (by decide), ⟨by decide⟩⟩

private theorem smoke_recoveryStart_ge {V : Type} (E : Generic.Env V) :
    E.t_GST ≤ recoveryStart smokeParams E := by
  simp only [recoveryStart, tauC, firstUpdateLabel, slotStartZ]
  dsimp [Time]
  omega

-- Apply a reset contract at ΔF = 6 > 2Δ to a package with the same delay.
-- This checks the statement interface. It does not prove the reset contract.
example {V In : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa smokeParams c))
    (h : ResetArrivalStatement smokeParams 4 6)
    (prem : ResetArrivalPrem smokeParams c 4 6 E rho ()) :
    ∃ w, H0Reset smokeParams c E rho w ∧
      smokeParams.actionTime w.rStar < recoveryStart smokeParams E + B'_resetF smokeParams 6 4 :=
  h (by decide) c E rho prem.set prem.bound prem.hhor

example {V In : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa smokeParams c))
    (h : ResetArrivalFullStatement smokeParams 4 6)
    (prem : ResetArrivalFullPrem smokeParams c 4 6 E rho ()) :
    ∃ w, H0 smokeParams c E rho w ∧
      smokeParams.actionTime w.rStar < recoveryStart smokeParams E + B'_resetF smokeParams 6 4 :=
  h (by decide) c E rho prem.set prem.bound prem.hhor

-- The attempt contract consumes the horizon after the actual start event.
example {V In : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa smokeParams c)) (pt : PtK)
    (h : ProgressAttemptStatement smokeParams 4 6)
    (prem : HealingAttemptPrem smokeParams c 4 6 E rho pt) :
    AttemptEndsBy smokeParams c E rho pt.k (attemptBudget smokeParams 4 pt.k) := by
  obtain ⟨ev, he, hhor⟩ := prem.hhor
  exact h (by decide) c E rho prem.set prem.bound pt.k ev prem.valid he hhor

-- Blueprint 21:1850–1863, third numeric point: Δ = 1, R = 3, k = 2.
private abbrev numericParams : Params :=
  ⟨⟨1, 1, 2, 0, by decide, by decide, by decide, by decide⟩, 3, 6, by decide, 2, by decide, fun d =>
      ⟨d.slot + 1⟩⟩
example : kappaF numericParams 6 = 3 ∧ E_jF numericParams 6 8 25 = 52 ∧
    B'_resetF numericParams 6 8 = 339 := by decide

#print axioms healingSet

end AvailableChain.FGSA.Run.Tests.HealingW
end

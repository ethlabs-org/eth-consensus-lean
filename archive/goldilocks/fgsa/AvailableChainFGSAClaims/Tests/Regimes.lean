module
public import AvailableChainFGSAClaims.Statements.Regimes

-- Test values are private; production code must not import Tests.
set_option linter.privateModule false

@[expose] public section

/-! ROOT-DIGEST W3: explicit small roots for statement fixtures. -/

-- These private structure values are smoke data, not Claims theorems (F-28).
set_option linter.defProp false

namespace AvailableChain.FGSA.Run.Tests.Regimes

-- A concrete FG-SA run. The time-zero tick is required by tick_total.
private abbrev smokeParams : Params :=
  ⟨⟨1, 1, 2, 0, by decide, by decide, by decide, by decide⟩, 2, 0, by decide, 2, by decide, fun d =>
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

private def smokeHealthy : V2.D.HealthyPrefixDelivery smokeEnv smokeRun 0 where
  broadcast_emitted := by
    rintro v _ o t ⟨i, hi, _⟩ w _ a _ ha _ hd _ _ _
    change a + 1 ≤ 0 at hd
    exact (not_le_of_gt (lt_add_of_le_of_pos ha (by decide)) hd).elim
  relay_accepted := by
    rintro v _ i o t ⟨⟨o', hi, _⟩, _⟩
    exact (smokeNoDelivery i v o' t hi).elim

private def smokeDelay : fgsaDelay (p := smokeParams) smokeEnv.Δ smokeEnv.Δ =
    fun _ => smokeEnv.Δ := by
  funext o
  cases o with | mk a m => cases m <;> rfl

private def smoke_healthyPrefix : HealthyPrefixSleep₂ smokeParams smokeCodec smokeEnv smokeRun 0 :=
  { toHealthyPrefix₂ :=
      ⟨smoke_base, ⟨le_rfl, le_rfl⟩, (by
        rw [smokeDelay]
        exact ⟨smokeHealthy.broadcast_emitted, smokeHealthy.relay_accepted⟩), le_rfl,
        fun _ ht hb => (not_lt_of_ge ht hb).elim⟩
    joinedPartBefore := fun _ ht hb => (not_lt_of_ge ht hb).elim }

private def smoke_cleanPrefix : CleanPrefixSleep₂ smokeParams smokeCodec smokeEnv smokeRun 0 := by
  refine ⟨⟨smoke_healthyPrefix.toHealthyPrefix₂, ?_⟩, smoke_healthyPrefix, ?_⟩
  · rw [Gen.V2.Duty.faulty_def, Gen.V2.Duty.awakeHonest_def]
    decide
  · classical
    simp [Gen.V2.Duty.faulty, joinedHonest, joinedAt, V2.D.Wakes]

private def smoke_cleanCut : CleanCut₂ smokeParams smokeCodec smokeEnv smokeRun 0 :=
  smoke_healthyPrefix.toHealthyPrefix₂

private def smoke_clean : CleanSleep₂ smokeParams smokeCodec smokeEnv smokeRun :=
  ⟨⟨smoke_cleanPrefix.toCleanPrefix₂, rfl⟩, smoke_cleanPrefix⟩

private def smoke_recovery : RecoverySleep₂ smokeParams smokeCodec smokeEnv smokeRun 4 where
  deltaF := le_rfl
  sync := by
    rw [smokeDelay]
    refine { broadcast_emitted := ?_, relay_accepted := ?_ }
    · rintro v _ o t _ w _ a _ _ _ hd _ _ _
      change max a 0 + 1 ≤ 0 at hd
      exact (not_le_of_gt (lt_add_of_le_of_pos (le_max_right a (0 : Time)) (by decide)) hd).elim
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

#print axioms smoke_base
#print axioms smoke_healthyPrefix
#print axioms smoke_cleanPrefix
#print axioms smoke_cleanCut
#print axioms smoke_clean
#print axioms smoke_recovery

end AvailableChain.FGSA.Run.Tests.Regimes
end

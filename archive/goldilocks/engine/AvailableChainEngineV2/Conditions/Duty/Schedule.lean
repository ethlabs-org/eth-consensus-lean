module
public import AvailableChainEngineV2.Conditions.Duty.Sleep
public import AvailableChainEngineV2.Conditions.Schedule

@[expose] public section

namespace AvailableChain.V2.D

open AvailableChain

variable {V : Type} {In : Type} {P : ProtocolSpecD In}

structure ScheduleWellFormed (E : Generic.Env V) (rho : Run V P) : Prop where
  horizon_nonneg : 0 ≤ rho.horizon
  sorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)
  nodup : rho.events.Nodup
  in_horizon : ∀ e ∈ rho.events, 0 ≤ e.time ∧ e.time ≤ rho.horizon
  honest_only : ∀ e ∈ rho.events, e.node ∈ rho.honest
  tick_public : ∀ v t, Event.tick v t ∈ rho.events → PublicTime E t
  tick_total : ∀ v ∈ rho.honest, ∀ t, PublicTime E t → 0 ≤ t → t ≤ rho.horizon →
    E.awake v t = true → Event.tick v t ∈ rho.events

def NoRestart (rho : Run V P) : Prop :=
  ∀ (i : Nat) (v : V) (t : Time), rho.events[i]? ≠ some (.restart v t)

def restartFree (rho : Run V P) (v : V) (i j : Nat) : Prop :=
  ∀ (k : Nat) (t : Time), i ≤ k → k < j → rho.events[k]? ≠ some (.restart v t)

variable [DecidableEq V]

structure DeliveryWellFormed (E : Generic.Env V) (rho : Run V P) : Prop where
  wire : ∀ (i : Nat) (v : V) (o : P.Object) (t : Time),
    rho.events[i]? = some (Event.deliver v o t) →
      P.wellFormed o = true
  deps : ∀ (i : Nat) (v : V) (o : P.Object) (t : Time),
    rho.events[i]? = some (Event.deliver v o t) →
      P.depsPresent (Run.stateBefore E rho i v) o = true
  fresh : ∀ (i : Nat) (v : V) (o : P.Object) (t : Time),
    rho.events[i]? = some (Event.deliver v o t) →
      P.processed (Run.stateBefore E rho i v) o = false

structure UnforgeableSignatures (E : Generic.Env V) (rho : Run V P) : Prop where
  unforgeable : ∀ v o t,
    Run.processes rho v o t →
      ∀ u ∈ rho.honest, Run.holder rho o.auth = some u →
        ∃ t', t' ≤ t ∧ Run.emits E rho u o t'
  carried : ∀ v o t,
    Run.processes rho v o t →
      ∀ o', P.carries o o' → ∀ u ∈ rho.honest,
        Run.holder rho o'.auth = some u →
        ∃ t', t' ≤ t ∧ Run.emits E rho u o' t'

structure ExecutionValid (E : Generic.Env V) (rho : Run V P) : Prop extends
  ScheduleWellFormed E rho, DeliveryWellFormed E rho, UnforgeableSignatures E rho,
  SleepWellFormed E rho

def SelfDelivery (E : Generic.Env V) (rho : Run V P) : Prop :=
  ∀ (i : Nat) (v : V) (t : Time), rho.events[i]? = some (.tick v t) →
    ∀ o ∈ Run.emitsAt E rho i, P.objSelfVisible o = true →
      ∃ j, i < j ∧ rho.events[j]? = some (.deliver v o t)

theorem ScheduleWellFormed.mem_emittedAt_iff_emits {E : Generic.Env V} {rho : Run V P}
    (h : ScheduleWellFormed E rho) {v : V} {o : P.Object} {t : Time} :
    o ∈ Run.emittedAt E rho v t ↔ Run.emits E rho v o t :=
  Run.mem_emittedAt_iff_emits E h.nodup

omit [DecidableEq V]

theorem restartFree_refl (rho : Run V P) (v : V) (i : Nat) : restartFree rho v i i :=
  fun _ _ hik hki => absurd (lt_of_le_of_lt hik hki) (lt_irrefl i)

theorem not_restartFree_succ_iff (rho : Run V P) (v : V) (i : Nat) :
    ¬ restartFree rho v i (i + 1) ↔ ∃ t, rho.events[i]? = some (.restart v t) := by
  constructor
  · intro h
    by_contra hne
    exact h fun k t hik hki heq =>
      hne ⟨t, by rwa [show k = i by omega] at heq⟩
  · rintro ⟨t, ht⟩ h
    exact h i t le_rfl (Nat.lt_succ_self i) ht

theorem restartFree.mono {rho : Run V P} {v : V} {i j i' j' : Nat}
    (h : restartFree rho v i j) (hi : i ≤ i') (hj : j' ≤ j) : restartFree rho v i' j' :=
  fun k t hik hkj => h k t (le_trans hi hik) (lt_of_lt_of_le hkj hj)

theorem restartFree.append {rho : Run V P} {v : V} {i j k : Nat}
    (h₁ : restartFree rho v i j) (h₂ : restartFree rho v j k) : restartFree rho v i k := by
  intro m t him hmk
  by_cases hmj : m < j
  · exact h₁ m t him hmj
  · exact h₂ m t (Nat.le_of_not_lt hmj) hmk

theorem NoRestart.restartFree {rho : Run V P} (h : NoRestart rho) (v : V) (i j : Nat) :
    restartFree rho v i j :=
  fun k t _ _ => h k v t

end AvailableChain.V2.D

end

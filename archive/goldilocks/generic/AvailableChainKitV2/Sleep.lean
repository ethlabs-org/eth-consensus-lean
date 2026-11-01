module
public import AvailableChainKitV2.Stable -- shake: keep (re-export)

public section

set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace AvailableChain.V2.Engine

open AvailableChain

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}

variable {E : Generic.Env V} {rho : Run V P} {v : V} {t a b : Time}
  {i j : Nat} {e : Event V P.Object}

/-- A restart has a lower phase than every local action at its time. -/
theorem restart_index_lt_event (hS : ScheduleWellFormed E rho)
    (hi : rho.events[i]? = some (.restart v t))
    (he : rho.events[j]? = some e) (ht : t ≤ e.time) (hp : 0 < e.phase) : i < j := by
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp he
  by_contra hn
  rcases lt_or_eq_of_le (Nat.le_of_not_gt hn) with hji | hji
  · have hk := (List.pairwise_iff_getElem.mp hS.sorted) j i hjl hil hji
    rw [hje, hie] at hk
    change toLex (e.time, e.phase) ≤ toLex (t, 0) at hk
    rcases Prod.Lex.toLex_le_toLex.mp hk with h | ⟨_, h⟩ <;> dsimp [Time] at * <;> omega
  · subst j
    have hh := Option.some.inj (hi.symm.trans he)
    rw [← hh] at hp
    cases hp

/-- The required wake restart occurs before a local action at that wake. -/
theorem wake_restart_before_event
    (hS : ScheduleWellFormed E rho) (hW : SleepWellFormed E rho)
    (hv : v ∈ rho.honest) (ht : 0 < t) (hh : t ≤ rho.horizon)
    (hw : Wakes E v t) (he : rho.events[j]? = some e)
    (hen : e.node = v) (het : e.time = t) (hep : 0 < e.phase) :
    ∃ i, i < j ∧ rho.events[i]? = some (.restart v t) := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (hW.wake_restart v hv t ht hh hw)
  exact ⟨i, restart_index_lt_event hS hi he (le_of_eq het.symm) hep, hi⟩

/-- The state just after restart uses the exact event time. -/
theorem state_after_restart (hi : rho.events[i]? = some (.restart v t)) :
    Run.stateBefore E rho (i + 1) v =
      P.restore (P.durable (Run.stateBefore E rho i v)) t := by
  rw [Run.stateBefore_succ E rho hi]
  simp only [World.step, Function.update_self]

/-- An asleep node has no local event that can change its state. -/
theorem asleep_state_frozen (hW : SleepWellFormed E rho) (hij : i ≤ j)
    (hSleep : ∀ k e, i ≤ k → k < j → rho.events[k]? = some e →
      e.node = v → E.awake v e.time = false) :
    Run.stateBefore E rho i v = Run.stateBefore E rho j v := by
  symm
  apply Run.stateBefore_eq_of_node_ne E rho hij
  intro k e hik hkj he hv
  have hf := hSleep k e hik hkj he hv
  have hm := List.mem_of_getElem? he
  cases e with
  | restart u t =>
      change u = v at hv
      subst v
      change E.awake u t = false at hf
      rw [hW.restart_awake u t hm] at hf
      cases hf
  | tick u t =>
      change u = v at hv
      subst v
      change E.awake u t = false at hf
      rw [hW.tick_awake u t hm] at hf
      cases hf
  | deliver u o t =>
      change u = v at hv
      subst v
      change E.awake u t = false at hf
      rw [hW.deliver_awake u o t hm] at hf
      cases hf

/-- An awake interval has no interior wake restart. -/
theorem noRestartOn_of_awakeOn
    (hR : RestartsAtWakes E rho) (hA : AwakeOn E v a b) : NoRestartOn rho v a b := by
  intro i t hi hat htb
  have hw := (hR v t (List.mem_of_getElem? hi)).2.2
  have ha := hA (t - 1) (by dsimp [Time] at *; omega) (by dsimp [Time] at *; omega)
  simp [ha] at hw

/-- An awake closed suffix has no later wake restart. -/
theorem noRestartAfter_of_awakeOnClosed
    (hS : ScheduleWellFormed E rho) (hR : RestartsAtWakes E rho)
    (hA : AwakeOnClosed E v a rho.horizon) : NoRestartAfter rho v a := by
  intro i t hi
  by_contra hn
  have hm := List.mem_of_getElem? hi
  have hw := (hR v t hm).2.2
  have ht := (hS.in_horizon _ hm).2
  have ha := hA (t - 1) (by dsimp [Time] at *; omega) (by
    change t ≤ rho.horizon at ht
    dsimp [Time] at *; omega)
  simp [ha] at hw

/-- An asleep time followed by an awake time has an intervening integer wake. -/
theorem wake_between {E : Generic.Env V} {v : V} {a t : Time}
    (hat : a ≤ t) (ha : E.awake v a = false) (ht : E.awake v t = true) :
    ∃ w, a < w ∧ w ≤ t ∧ Wakes E v w := by
  have hex : ∃ n : Nat, E.awake v (a + (n : Int)) = true := by
    refine ⟨(t - a).toNat, ?_⟩
    have he : a + ((t - a).toNat : Int) = t := by dsimp [Time] at *; omega
    rwa [he]
  let n := Nat.find hex
  have hn := Nat.find_spec hex
  have hn0 : 0 < n := by
    by_contra h
    have hz : n = 0 := by omega
    change E.awake v (a + (n : Int)) = true at hn
    simp [hz, ha] at hn
  have hnt : n ≤ (t - a).toNat := Nat.find_min' hex (by
    have he : a + ((t - a).toNat : Int) = t := by dsimp [Time] at *; omega
    rwa [he])
  refine ⟨a + (n : Int), ?_, ?_, hn, ?_⟩
  · dsimp [Time] at *; omega
  · dsimp [Time] at *; omega
  · have hprev := Nat.find_min hex (show n - 1 < n by omega)
    have he : a + (n : Int) - 1 = a + ((n - 1 : Nat) : Int) := by dsimp [Time] at *; omega
    rw [he]
    exact Bool.eq_false_iff.mpr hprev

end AvailableChain.V2.Engine

end

module
public import ConsensusModelProofs
public import Mathlib.Tactic
@[expose] public section

/-! # Layer-½ tests

A tiny protocol with two roles: `false` (every key, one duty per integer time)
and `true` (one key). Tests: relayed ingress and the cumulative mempool,
validity rules out a negative horizon, and credentials bind the role (a key
selected for one role cannot sign in another). -/

namespace Consensus.Shape.Tests.Model
open Consensus Model

/-- One output identifier, serving every capability. -/
abbrev schema : OutputSchema := ⟨Unit, fun _ => some ()⟩

/-- The test protocol: role `false` selects every key and has one duty per
integer time, signing empty data; role `true` selects one key and has no
duty. No state, no outputs, no conflicts. -/
def proto (pub : Public) : Protocol pub Unit where
  State := Unit
  Role := Bool
  Duty := Time
  Item := Unit
  Body := Unit
  Durable := Unit
  decRole := inferInstance
  decItem := inferInstance
  decBody := inferInstance
  encItem := inferInstance
  selSpec := fun r => if r then .sized 1 else .all
  role := fun _ => false
  actTime := id
  duties := fun t => [t]
  duties_spec := by intro d t; simp
  duties_nodup := fun t => List.nodup_singleton t
  init := fun _ => ()
  clock := fun _ _ _ => ()
  act := fun _ _ => some (.data (), [])
  gossip := fun _ _ => []
  process := fun _ _ _ => ()
  recordOwn := fun _ _ _ => ()
  durable := fun _ => ()
  restore := fun _ _ _ => ()
  out := fun _ _ => []
  conflicts := fun _ _ => false

/-- The test family. -/
def family : Family schema := proto

/-- Two validators, always awake, `Δ = 3`, `GST = 4`. -/
def env : Env (Fin 2) := ⟨3, by decide, 4, fun _ _ => true⟩

/-- The identity PKI. -/
def pki : Fin (Fintype.card (Fin 2)) ≃ Fin 2 := finCongr (Fintype.card_fin 2)

/-- An admissible selection: every key in role `false`, key `0` in role `true`. -/
def sel : Bool → Finset (Fin (Fintype.card (Fin 2))) :=
  fun r => if r then {0} else Finset.univ

theorem sel_valid (rho : Run family env) (h : rho.sel = sel) : rho.SelValid := by
  intro r
  rw [h]
  cases r
  · exact (rfl : sel false = Finset.univ)
  · change (sel true).card = min 1 (Fintype.card (Fin 2))
    decide

/-- Ingress can inject an unsubmitted transaction. The cumulative inbox
survives restarts and is available to the next clock. -/
def relayedRun : Run family env :=
  mkRun Finset.univ 5 pki sel (fun _ _ => []) (fun _ t => if t = 2 then [42] else [])
    (fun _ => 0) [.restart 0 3]

theorem injected_held : relayedRun.TxHeld 0 42 3 :=
  ⟨2, by decide, by decide, by simp [relayedRun, mkRun, Run.inbox]⟩

theorem held_strict_deadline : ¬ relayedRun.TxHeld 0 42 2 := by
  rintro ⟨τ, hτ, hτd, hx⟩
  have hne : τ ≠ 2 := ne_of_lt hτd
  simp [relayedRun, mkRun, Run.inbox, hne] at hx

theorem relayed_mempool_after_restart : 42 ∈ mempool relayedRun.inbox 0 5 :=
  relayedRun.txHeld_mem_mempool ⟨2, by decide, by decide, by simp [relayedRun, mkRun, Run.inbox]⟩

theorem injected_not_submitted : ¬ relayedRun.point.SubmittedToSome 42 5 := by
  rintro ⟨v, _, τ, _, _, _, hx⟩
  simp [relayedRun, mkRun, Run.point] at hx

/-- Validity rules out a negative horizon, for every protocol and
environment: the empty time window of such a point is never a valid run. -/
theorem negativeHorizon_not_valid {O : OutputSchema} (F : Family O) {V : Type} [Fintype V]
    [DecidableEq V] (E : Env V) (rho : Run F E) (h : rho.horizon < 0) :
    ¬ rho.ExecutionValid := by
  intro hv
  exact absurd hv.horizon_nonneg (not_le.mpr h)

/-- A forged role: key `1` is selected for role `false` but not for role
`true`; a run that delivers an object signed by key `1` in role `true` has an
admissible selection but violates `Credentials`. -/
def forgedRun : Run family env :=
  mkRun Finset.univ 5 pki sel (fun _ _ => []) (fun _ _ => []) (fun _ => 0)
    [.deliver 0 (.mk (.signed 1 true) (.data ()) []) 0]

theorem forged_role_invalid : forgedRun.SelValid ∧ ¬ forgedRun.Credentials := by
  refine ⟨sel_valid _ rfl, ?_⟩
  intro h
  have := h 0 0 _ 0 rfl _ (.refl _) 1 true rfl
  simp [forgedRun, mkRun, sel] at this

/-- Hence a forged role makes the run invalid. -/
theorem forged_role_not_valid : ¬ forgedRun.ExecutionValid :=
  fun hv => forged_role_invalid.2 hv.credentials

end Consensus.Shape.Tests.Model
end

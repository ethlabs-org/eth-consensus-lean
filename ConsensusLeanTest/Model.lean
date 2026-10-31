module
public import ConsensusLean.Lemmas.Model.Protocol
public import ConsensusLean.Lemmas.Model.Laws
public import ConsensusLean.Lemmas.Model.Objects
public import ConsensusLean.Lemmas.Model.View
public import ConsensusLean.Spec.Model.System
public import ConsensusLean.Lemmas.Problem.Facts.Transfer
public import ConsensusLean.Lemmas.Problem.Facts.Good
public import ConsensusLean.Lemmas.Model.Canonical.Construction
public import ConsensusLean.Lemmas.Model.Candidates
public import ConsensusLean.Lemmas.Model.Credentials
public import ConsensusLean.Lemmas.Model.Mempool
public import ConsensusLean.Lemmas.Model.Protection
public import ConsensusLean.Lemmas.Model.Causal
public import ConsensusLean.Proofs.Faithful.Main
public import ConsensusLean.Lemmas.Model.Truncate
public import ConsensusLean.Lemmas.Model.Adequate
public import ConsensusLeanTest.Common
public import Mathlib.Tactic
@[expose] public section

/-! # Model (L1) tests

A tiny protocol with two roles: `false` (every key, one duty per integer time)
and `true` (one key). Tests: relayed ingress and the cumulative mempool,
validity rules out a negative horizon, credentials bind the role (a key
selected for one role cannot sign in another), ticks happen at every
integer time, and slashing protection: with `conflicts` always true the engine
releases no signed object, so non-framing holds by construction, and
protection ignores candidates signed by other keys. Same-tick semantics
(`seqProto`): a later duty of a tick sees the `recordOwn` of an earlier
release, and `act`'s state is applied when the node is not selected. -/

namespace Consensus.Shape.Tests.Model
open Consensus Model

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
  cntItem := inferInstance
  selSpec := fun r => if r then .sized 1 else .fixed Finset.univ
  role := fun _ => false
  duties := fun t => [t]
  init := fun _ => ()
  clock := fun _ _ _ => ()
  act := fun _ _ => ((), some (.data (), []))
  gossip := fun _ _ => []
  process := fun _ _ _ => ()
  recordOwn := fun _ _ _ => ()
  durable := fun _ => ()
  restore := fun _ _ _ => ()
  out := fun _ _ => []
  conflicts := fun _ _ => false

/-- The test family. -/
def family : Family schema := proto

/-- Data depends on a previously held item; items have no dependency. -/
def dependentProto : Protocol ⟨1, 1, by decide⟩ Unit :=
  { proto ⟨1, 1, by decide⟩ with
    dependencies := {
      ready := fun held (o : Obj 1 Bool Unit Unit) => match o.msg with
        | .item _ => true
        | .data _ => held.any fun p => p.item?.isSome
      mono := by
        intro held held' o hsub h
        split at h
        · rfl
        · simp only [List.any_eq_true] at h ⊢
          obtain ⟨p, hp, hr⟩ := h
          exact ⟨p, hsub hp, hr⟩ } }

/-- Dependencies must precede a release; later candidates cannot retroactively enable it. -/
theorem release_dependency_order :
    let parent : dependentProto.Object := .mk .none (.item ()) []
    let child : dependentProto.Object := .mk .none (.data ()) []
    (releaseAll dependentProto (fun _ => 0) 0 ⟨(), []⟩ [child, parent]).2 = [parent] ∧
    (releaseAll dependentProto (fun _ => 0) 0 ⟨(), []⟩ [parent, child]).2 = [parent, child] := by
  decide

/-- Two validators, always awake, `Δ = 3`, `GST = 4`. -/
def env : Env (Fin 2) := ⟨3, by decide, fun _ _ => true⟩

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
  Run.mk Finset.univ 5 [.restart 0 3] (pkiFin 2) sel (fun _ _ => [])
      (fun _ t => if t = 2 then [42] else []) (fun _ => 0)

theorem injected_held : CommLog.TxHeld relayedRun.log 0 42 3 :=
  ⟨2, by decide, by decide, by simp [relayedRun, Run.log, Run.inbox]⟩

/-- Holding is inclusive: the transaction relayed at `2` is held at the
deadline `2` itself (L0 `TxHeld`, "received by that time"), … -/
theorem held_at_deadline : CommLog.TxHeld relayedRun.log 0 42 2 :=
  ⟨2, by decide, le_rfl, by simp [relayedRun, Run.log, Run.inbox]⟩

/-- … but not before it arrives. -/
theorem not_held_before_relay : ¬ CommLog.TxHeld relayedRun.log 0 42 1 := by
  rintro ⟨τ, hτ, hτd, hx⟩
  have hne : τ ≠ 2 := by intro h; subst h; exact absurd hτd (by decide)
  simp [relayedRun, Run.log, Run.inbox, hne] at hx

/-- … and it is processed at a later tick (the mempool at `5`, after the
restart at `3`). -/
theorem relayed_mempool_after_restart : 42 ∈ mempool relayedRun.inbox 0 5 :=
  relayedRun.txHeld_mem_mempool held_at_deadline (by decide)

theorem injected_not_submitted : ¬ relayedRun.point.SubmittedToSome 42 5 := by
  rintro ⟨v, _, τ, _, _, _, hx⟩
  simp [relayedRun, Run.point] at hx

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
  Run.mk Finset.univ 5 [.deliver 0 (.mk (.signed 1 true) (.data ()) []) 0] (pkiFin 2) sel
      (fun _ _ => []) (fun _ _ => []) (fun _ => 0)

theorem forged_role_invalid : forgedRun.SelValid ∧ ¬ forgedRun.Credentials := by
  refine ⟨sel_valid _ rfl, ?_⟩
  intro h
  have := h 0 0 _ 0 rfl _ (.refl _) 1 true rfl
  simp [forgedRun, sel] at this

/-- Hence a forged role makes the run invalid. -/
theorem forged_role_not_valid : ¬ forgedRun.ExecutionValid :=
  fun hv => forged_role_invalid.2 hv.credentials

/-- Unit ticks: with `Δ = 3`, every valid run of horizon at least `1` ticks
an awake honest node at time `1`, which is not a multiple of `Δ` (so a
`Δ`-grid schedule would not be valid). -/
theorem unit_ticks (rho : Run family env) (hv : rho.ExecutionValid) (h0 : (0 : Fin 2) ∈ rho.honest)
    (hh : 1 ≤ rho.horizon) : Event.tick (0 : Fin 2) 1 ∈ rho.events ∧ ¬ (3 : Time) ∣ 1 :=
  ⟨hv.tick_total 0 h0 1 (by decide) hh rfl, by decide⟩

/-- The test protocol with `conflicts` always true: every signed object would
convict its signer. -/
def protoC (pub : Public) : Protocol pub Unit := { proto pub with conflicts := fun _ _ => true }

/-- The test family with `conflicts` always true. -/
def familyC : Family schema := protoC

/-- With `conflicts` always true, slashing protection refuses every own-signed
candidate: every release of every run (valid or not) is unsigned. -/
theorem conflictsTrue_releases_unsigned_only {V : Type} [Fintype V] [DecidableEq V]
    (E : Env V) (rho : Run familyC E) (i : Nat) {o : (protoOf familyC E).Object}
    (ho : o ∈ rho.releasesAt i) : o.signer? = none := by
  have ho' := ho
  cases he : rho.events[i]? with
  | none => simp [Run.releasesAt, he] at ho
  | some e =>
    cases e with
    | tick v t =>
      simp only [Run.releasesAt, he] at ho
      rcases rho.tick_signer _ v t ho with h | h
      · exact h
      · have hf : (protoOf familyC E).conflicts o o = false :=
          rho.tick_noConflict he ho' ho' h h
        cases hf
    | deliver v p t =>
      simp only [Run.releasesAt, he] at ho
      rcases rho.deliver_signer _ v p t ho with h | h
      · exact h
      · have hf : (protoOf familyC E).conflicts o o = false :=
          rho.deliver_noConflict he ho' ho' h h
        cases hf
    | restart v t => simp [Run.releasesAt, he] at ho

/-- Hence non-framing, which a protocol convicting everything would violate
without protection, holds for it (an instance of `sysOf_nonFraming`). -/
theorem conflictsTrue_nonFraming :
    (sysOf schema familyC (Fin 2)).HoldsAlways (sysOf schema familyC (Fin 2)).NonFraming :=
  sysOf_nonFraming _ _ _

/-- Protection fires on own candidates only: a candidate signed by key `1`
passes `protects` for key `0`, even next to a key-`0` object it would conflict
with; the same candidate signed by key `0` is refused. -/
theorem protects_other_key :
    protects (familyC (pubOf env)) 0 [.mk (.signed 0 false) (.data ()) []]
        (.mk (.signed 1 false) (.data ()) []) = true ∧
      protects (familyC (pubOf env)) 0 [] (.mk (.signed 0 false) (.data ()) []) = false := by
  decide

/-! ## Same-tick semantics: duties run one after the other -/

/-- Duties `false` then `true` at every time, each in its own role (every key).
Each duty signs the current state; duty `false` also adds 1 to the state;
`recordOwn` adds 10. -/
def seqProto (pub : Public) : Protocol pub Unit where
  State := Nat
  Role := Bool
  Duty := Bool
  Item := Unit
  Body := Nat
  Durable := Unit
  decRole := inferInstance
  decItem := inferInstance
  decBody := inferInstance
  cntItem := inferInstance
  selSpec := fun _ => .fixed Finset.univ
  role := id
  duties := fun _ => [false, true]
  init := fun _ => 0
  clock := fun s _ _ => s
  act := fun s d => (if d then s else s + 1, some (.data s, []))
  gossip := fun _ _ => []
  process := fun s _ _ => s
  recordOwn := fun s _ _ => s + 10
  durable := fun _ => ()
  restore := fun _ _ _ => 0
  out := fun _ _ => []
  conflicts := fun _ _ => false

/-- The sequential test family. -/
def seqFamily : Family schema := seqProto

/-- A later duty reads the state the earlier one left, including the
`recordOwn` of its release: duty `true` signs `0 + 1 + 10 = 11`. -/
theorem later_duty_sees_recordOwn (rho : Run seqFamily env) (v : Fin 2)
    (hsel : rho.sel = fun _ => Finset.univ) :
    (rho.runDuties v ⟨(0 : Nat), []⟩ [false, true]).2 =
      [.mk (.signed (rho.ownKey v) false) (.data (0 : Nat)) [],
        .mk (.signed (rho.ownKey v) true) (.data (11 : Nat)) []] := by
  erw [Run.runDuties_cons, Run.runDuties_cons, Run.runDuties_nil]
  unfold Run.dutyStep Run.signedCandidate
  simp [hsel, releaseAll, releasable, protects, Obj.carried, protoOf, seqFamily, seqProto]
  rfl

/-- `act`'s state is applied when the node is not selected: duty `false` is
dropped, yet duty `true` signs `0 + 1 = 1`. -/
theorem state_applied_unselected (rho : Run seqFamily env) (v : Fin 2)
    (hsel : rho.sel = fun r => cond r Finset.univ ∅) :
    (rho.runDuties v ⟨(0 : Nat), []⟩ [false, true]).2 =
      [.mk (.signed (rho.ownKey v) true) (.data (1 : Nat)) []] := by
  erw [Run.runDuties_cons, Run.runDuties_cons, Run.runDuties_nil]
  unfold Run.dutyStep Run.signedCandidate
  simp [hsel, releaseAll, releasable, protects, Obj.carried, protoOf, seqFamily, seqProto]
  rfl

end Consensus.Shape.Tests.Model
end

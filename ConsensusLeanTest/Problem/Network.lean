module
public import ConsensusLeanTest.Model.Basic
public import ConsensusLeanTest.Fixtures.Common
import ConsensusLean.Lemmas.Tactic.Linarith
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
@[expose] public section

/-! # Network tests (L0 delivery, L1 faithfulness)

* `waker_within_bound`: `Δ = 2`, GST `0`; validator 1 is
  asleep at `0` and `1` and awake from `2`. An honest send at `0` must be
  re-served to validator 1 strictly before the bound of its wake: held at
  `3 = max 2 0 + Δ − 1` (the normal-delivery rule: awake over the
  delivery interval `[2, 3]`). `waker_within_bound_silent`: a log in which
  validator 1 never receives the message is not partially synchronous.
  `waker_not_instant`: receipt at `3` suffices; the rule does not demand
  receipt at the wake `2` (no instant re-delivery). `waker_late`: receipt at
  `4 = max 2 0 + Δ`, the bound itself, is too late. `waker_receipt_at_wake`:
  receipt at the wake `2` suffices.
* `receipt_at_deadline`: two always-awake validators, `Δ = 2`; receipt exactly
  at `t + Δ` does **not** meet `PSync 0` (held strictly before the bound).
  `receipt_before_deadline`: receipt at `t + Δ − 1` does.
* `held_restart`: a receipt before a wake is held until the wake, not after.
* `negative_send_covered`: sends at negative times are
  covered. Two always-awake honest validators, `Δ = 2`, GST `0`; validator 0
  sends at `-1` and nobody receives: not `PSync 0` (validator 1 must hold the
  message at `max (-1) 0 + 2 − 1 = 1`).
* `agreesUpTo_empty_messages`: with an empty message
  type, logs whose inboxes differ at `0` do not agree up to `0`.
* `faithful_relayedRun`: on the model test run, the system's log is the
  engine's (`sysOf_log_faithful`): inbox and sends. `faithful_receipt`: a run
  with a real delivery; its receipt is in the system's log, tagged with the
  run's environment, and a foreign tag is not.
* `silent_run_valid`: for every protocol and run
  data, the canonical run with GST past the horizon is a valid run with no
  receipts at all, and it violates `PSync g'` at every `g'` for which some
  honest send at `t` has a deadline `max t g' + Δ − 1` in the horizon and an honest
  node awake throughout `[t, max t g' + Δ − 1]` has not sent the message itself
  (`silent_not_psync`, an L0 fact about logs with no receipts). So
  `Adequate.covers` includes runs that no network premise admits.
* `truncate_relayedRun`: a concrete valid run (both validators tick
  at `0, 1, 2`; `42` relayed at `1`) truncated at `1` is valid, keeps exactly
  the four ticks at times `≤ 1`, is the L0 prefix of the full trace at `1`,
  and still holds the relayed transaction in its log. -/

/-! ## Explanatory network facts (moved from the library) -/

namespace Consensus.CommLog

variable {V M : Type} {p : EnvPoint V} {L : CommLog V M}

/-- A smaller cut is weaker. -/
theorem Delivers.mono_cut {dl dlF : Time → Time} {cut cut' : Time}
    (h : L.Delivers p dl dlF cut) (hc : cut' ≤ cut) : L.Delivers p dl dlF cut' :=
  h.reindex (f := id) (fun _ => le_rfl) (fun _ => rfl) (fun _ => rfl) hc

/-- A later GST is weaker. -/
theorem PSync.mono {g g' : Time} (hg : g ≤ g') (h : L.PSync p g) : L.PSync p g' := by
  apply h.reindex (f := fun a => max a g') (fun a => le_max_left a g') ?_ ?_ le_rfl
  · intro a
    show max a g' + p.env.ΔAC - 1 = max (max a g') g + p.env.ΔAC - 1
    rw [max_assoc, max_eq_left hg]
  · intro a
    show max a g' + p.env.ΔFG - 1 = max (max a g') g + p.env.ΔFG - 1
    rw [max_assoc, max_eq_left hg]

/-- Synchrony up to a cut is weaker at a smaller cut. -/
theorem SyncUntil.mono {b b' : Time} (hb : b' ≤ b) (h : L.SyncUntil p b) : L.SyncUntil p b' :=
  Delivers.mono_cut h hb

end Consensus.CommLog

namespace Consensus.Shape.Tests.Network
open Consensus

/-- `Δ = 2`; validator 0 always awake, validator 1 asleep before time `2`. -/
def envW : Env (Fin 2) := ⟨2, by decide, 2, by decide, fun v t => decide (v = 0 ∨ 2 ≤ t)⟩

/-- Both honest, horizon `5`, no submissions. -/
def ptW : EnvPoint (Fin 2) := ⟨envW, fun _ => ∅, monotone_const, 5, fun _ _ => []⟩

/-- Validator 0 sends one message at `0`; receipts as given. -/
def logW (recv : Fin 2 → Unit → Time → Prop) : CommLog (Fin 2) Unit :=
  ⟨fun v _ t => v = 0 ∧ t = 0, recv, fun _ _ => [], fun _ => False⟩

/-- The normal-delivery rule for a waker: validator 1, asleep at `0`–`1` and awake from
`2`, must hold the message sent at `0` strictly before `max 2 0 + Δ = 4`, i.e. by `3`. -/
theorem waker_within_bound (recv : Fin 2 → Unit → Time → Prop) (h : (logW recv).PSync ptW 0) :
    (logW recv).Held ptW 1 () 3 :=
  h.msgs 0 () 0 ⟨rfl, rfl⟩ (by simp [EnvPoint.HonestAt, ptW]) id 1 2 (by decide)
    (by decide) (by decide) (by simp [EnvPoint.HonestAt, ptW])
    (fun u hu _ => by simp [ptW, envW, hu])

/-- A log in which validator 1 never receives the message violates `PSync 0`. -/
theorem waker_within_bound_silent : ¬ (logW fun _ _ _ => False).PSync ptW 0 := by
  intro h
  obtain ⟨t', -, hs, -⟩ := waker_within_bound _ h
  rcases hs with ⟨h1, -⟩ | hs
  · exact absurd h1 (by decide)
  · exact hs

/-- The log with validator 1 receiving the message at `2`, its wake. -/
def recvAt2 : Fin 2 → Unit → Time → Prop := fun w _ t => w = 1 ∧ t = 2

theorem held0 (d : Time) (hd : 0 ≤ d) : (logW recvAt2).Held ptW 0 () d := by
  refine ⟨0, hd, Or.inl ⟨rfl, rfl⟩, fun u _ _ hwk => ?_⟩
  have := hwk.2
  simp [ptW, envW] at this

theorem held1 (d : Time) (hd : 2 ≤ d) : (logW recvAt2).Held ptW 1 () d := by
  refine ⟨2, hd, Or.inr ⟨rfl, rfl⟩, fun u hu _ hwk => ?_⟩
  have := hwk.2
  simp only [ptW, envW, decide_eq_false_iff_not, not_or] at this
  dsimp only [Time] at *
  omega

theorem held_all (w : Fin 2) (d : Time) (hd : 2 ≤ d) : (logW recvAt2).Held ptW w () d := by
  fin_cases w
  · exact held0 d (by dsimp only [Time] at *; omega)
  · exact held1 d hd

/-- Receipt by the waker at its wake `2` satisfies `PSync 0`: validator 1 is awake over
no delivery interval `[a, max a 0 + Δ − 1]` with `a < 2`, and every later one ends at `3` or
later. -/
theorem waker_receipt_at_wake : (logW recvAt2).PSync ptW 0 := by
  refine ⟨?_, fun _ _ _ _ _ h => h.elim, ?_⟩
  · rintro v m t ⟨-, rfl⟩ - - w a ha - - - haw
    have h0 := le_max_right a 0
    fin_cases w
    · exact held0 _ (by change 0 ≤ max a 0 + 2 - 1; dsimp only [Time] at *; omega)
    · refine held1 _ ?_
      change 2 ≤ max a 0 + 2 - 1
      by_contra hlt
      have h1 := haw (max a 0) (le_max_left a 0)
        (by change max a 0 ≤ max a 0 + 2 - 1; dsimp only [Time]; omega)
      simp only [ptW, envW, decide_eq_true_eq] at h1
      rcases h1 with h1 | h1
      · exact absurd h1 (by decide)
      · dsimp only [Time] at *; omega
  · intro u x τ _ _ _ hx
    exact absurd hx (List.not_mem_nil)

/-- The log with validator 1 receiving the message only at `3`, one unit after
its wake at `2`. -/
def recvAt3 : Fin 2 → Unit → Time → Prop := fun w _ t => w = 1 ∧ t = 3

/-- No instant re-delivery: receipt by the waker at `3 = max 2 0 + Δ − 1`, not at
its wake `2`, satisfies `PSync 0`. Validator 1 is awake over no delivery
interval `[a, max a 0 + 2 − 1]` with `a < 2`. -/
theorem waker_not_instant : (logW recvAt3).PSync ptW 0 ∧ ¬ (logW recvAt3).Held ptW 1 () 2 := by
  refine ⟨⟨?_, fun _ _ _ _ _ h => h.elim, ?_⟩, ?_⟩
  · rintro v m t ⟨-, rfl⟩ - - w a ha - hh - haw
    fin_cases w
    · refine ⟨0, ?_, Or.inl ⟨rfl, rfl⟩, fun u _ _ hwk => ?_⟩
      · change 0 ≤ max a 0 + 2 - 1
        have := le_max_right a 0
        dsimp only [Time] at *
        omega
      · have := hwk.2
        simp [ptW, envW] at this
    · have h2 : 2 ≤ a := by
        by_contra hlt
        have hle : max a 0 ≤ max a 0 + ptW.env.ΔAC - 1 := by
          change max a 0 ≤ max a 0 + 2 - 1
          dsimp only [Time]
          omega
        have h1 := haw (max a 0) (le_max_left a 0) hle
        have hm : max a 0 < 2 := max_lt (not_le.mp hlt) (by decide)
        simp only [ptW, envW, decide_eq_true_eq] at h1
        rcases h1 with h1 | h1
        · exact absurd h1 (by decide)
        · exact absurd h1 (not_le.mpr hm)
      refine ⟨3, ?_, Or.inr ⟨rfl, rfl⟩, fun u hu _ hwk => ?_⟩
      · change 3 ≤ max a 0 + 2 - 1
        have := le_max_left a 0
        dsimp only [Time] at *
        omega
      · have := hwk.2
        simp only [ptW, envW, decide_eq_false_iff_not, not_or] at this
        dsimp only [Time] at *
        omega
  · intro u x τ _ _ _ hx
    exact absurd hx (List.not_mem_nil)
  · rintro ⟨t', ht', hs, -⟩
    rcases hs with ⟨h1, -⟩ | ⟨-, rfl⟩
    · exact absurd h1 (by decide)
    · exact absurd ht' (by decide)

/-- The log with validator 1 receiving the message only at `4 = max 2 0 + Δ`, the bound of
its wake itself. -/
def recvAt4 : Fin 2 → Unit → Time → Prop := fun w _ t => w = 1 ∧ t = 4

/-- **Rejection**: receipt by the waker at `4 = max 2 0 + Δ` is too late for `PSync 0`; it
must hold the message strictly before the bound, at `3` (`waker_within_bound`). -/
theorem waker_late : ¬ (logW recvAt4).PSync ptW 0 := by
  intro h
  obtain ⟨t', ht', hs, -⟩ := waker_within_bound _ h
  rcases hs with ⟨h1, -⟩ | ⟨-, rfl⟩
  · exact absurd h1 (by decide)
  · exact absurd ht' (by decide)

/-- Validator 0 awake at `0`, asleep at `1`, awake again (a wake) at `2`. -/
def envR : Env (Fin 2) := ⟨1, by decide, 1, by decide, fun _ t => decide (t ≠ 1)⟩

/-- Validator 0 received one message at `0`. -/
def logR : CommLog (Fin 2) Unit :=
  ⟨fun _ _ _ => False, fun v _ t => v = 0 ∧ t = 0, fun _ _ => [], fun _ => False⟩

def ptR : EnvPoint (Fin 2) := ⟨envR, fun _ => ∅, monotone_const, 5, fun _ _ => []⟩

/-- A receipt is held until the next wake (holding is memory, not
awakeness: validator 0 holds at `1` while asleep) and lost at the wake at `2`. -/
theorem held_restart : logR.Held ptR 0 () 1 ∧ ¬ logR.Held ptR 0 () 2 := by
  refine ⟨⟨0, by decide, Or.inr ⟨rfl, rfl⟩, fun u hu hu1 hwk => ?_⟩, ?_⟩
  · have hu' : u = 1 := by dsimp only [Time] at *; omega
    subst hu'
    have := hwk.1
    simp [ptR, envR] at this
  · rintro ⟨t', -, hs, hn⟩
    rcases hs with hs | ⟨-, rfl⟩
    · exact hs
    · exact hn 2 (by decide) le_rfl ⟨by simp [ptR, envR], by simp [ptR, envR]⟩

/-- Both validators always awake, `Δ = 2`, GST `0`. -/
def envN : Env (Fin 2) := ⟨2, by decide, 2, by decide, fun _ _ => true⟩

def ptN : EnvPoint (Fin 2) := ⟨envN, fun _ => ∅, monotone_const, 5, fun _ _ => []⟩

/-- Validator 0 sends at `-1`; nobody receives. -/
def logN : CommLog (Fin 2) Unit :=
  ⟨fun v _ t => v = 0 ∧ t = -1, fun _ _ _ => False, fun _ _ => [], fun _ => False⟩

/-- A send at a negative time is covered by `PSync 0`: validator 1 must hold
it at `max (-1) 0 + Δ − 1 = 1`. -/
theorem negative_send_covered : ¬ logN.PSync ptN 0 := by
  intro h
  obtain ⟨t', -, hs, -⟩ := h.msgs 0 () (-1) ⟨rfl, rfl⟩
    (by simp [EnvPoint.HonestAt, ptN]) id 1 (-1) le_rfl (by decide) (by decide)
    (by simp [EnvPoint.HonestAt, ptN]) (fun _ _ _ => rfl)
  rcases hs with ⟨h1, -⟩ | hs
  · exact absurd h1 (by decide)
  · exact hs

/-- Both validators always awake, `Δ = 2`; validator 0 sends at `0`, validator 1 receives
at `R`. -/
def logD (R : Time) : CommLog (Fin 2) Unit :=
  ⟨fun v _ t => v = 0 ∧ t = 0, fun v _ t => v = 1 ∧ t = R, fun _ _ => [], fun _ => False⟩

/-- **Rejection at the bound**: receipt exactly at `t + Δ = 2` does not meet `PSync 0`; the
always-awake validator 1 must hold the message at `0 + Δ − 1 = 1`. -/
theorem receipt_at_deadline : ¬ (logD 2).PSync ptN 0 := by
  intro h
  obtain ⟨t', ht', hs, -⟩ := h.msgs 0 () 0 ⟨rfl, rfl⟩
    (by simp [EnvPoint.HonestAt, ptN]) id 1 0 le_rfl (by decide) (by decide)
    (by simp [EnvPoint.HonestAt, ptN]) (fun _ _ _ => rfl)
  rcases hs with ⟨h1, -⟩ | ⟨-, rfl⟩
  · exact absurd h1 (by decide)
  · exact absurd ht' (by decide)

/-- **Acceptance strictly before the bound**: receipt at `t + Δ − 1 = 1` meets `PSync 0`
("received by that time" at the last time before the bound). -/
theorem receipt_before_deadline : (logD 1).PSync ptN 0 := by
  refine ⟨?_, fun _ _ _ _ _ h => h.elim, ?_⟩
  · rintro v m t ⟨-, rfl⟩ - - w a ha - - - -
    have h1 : (1 : Time) ≤ max a 0 + ptN.env.ΔAC - 1 := by
      change (1 : Time) ≤ max a 0 + 2 - 1
      have := le_max_right a 0
      dsimp only [Time] at *
      omega
    fin_cases w
    · exact ⟨0, by dsimp only [Time] at *; omega, Or.inl ⟨rfl, rfl⟩,
        fun u _ _ hwk => by simp [Wakes, ptN, envN] at hwk⟩
    · exact ⟨1, h1, Or.inr ⟨rfl, rfl⟩, fun u _ _ hwk => by simp [Wakes, ptN, envN] at hwk⟩
  · intro u x τ _ _ _ hx
    exact absurd hx (List.not_mem_nil)

/-- Two logs over an empty message type whose inboxes differ at `0`. -/
def logE₁ : CommLog Unit Empty :=
  ⟨fun _ _ _ => False, fun _ _ _ => False, fun _ _ => [], fun _ => False⟩
def logE₂ : CommLog Unit Empty :=
  ⟨fun _ _ _ => False, fun _ _ _ => False, fun _ t => if t = 0 then [42] else [], fun _ => False⟩

/-- Prefix agreement is not vacuous for an empty message type. -/
theorem agreesUpTo_empty_messages : ¬ logE₁.AgreesUpTo logE₂ 0 := by
  rintro ⟨-, h, -⟩
  have := h () 0 le_rfl
  simp [logE₁, logE₂] at this

open Consensus.Model in
/-- On the model test run the system's log is the engine's communication: the
inbox (with the relayed transaction `42` at time `2`) and the sends. -/
theorem faithful_relayedRun :
    ((sysOf schema Model.family (Fin 2)).log ⟨Model.env, Model.relayedRun⟩).inbox =
      Model.relayedRun.inbox ∧
    42 ∈ ((sysOf schema Model.family (Fin 2)).log ⟨Model.env, Model.relayedRun⟩).inbox 0 2 ∧
    ∀ v o t, ((sysOf schema Model.family (Fin 2)).log ⟨Model.env, Model.relayedRun⟩).sent
      v ⟨Model.env, o⟩ t ↔ Model.relayedRun.releases v o t := by
  have hf := sysOf_log_faithful (O := schema) (F := Model.family) (V := Fin 2)
    ⟨Model.env, Model.relayedRun⟩
  refine ⟨hf.2.2.2, ?_, hf.1⟩
  rw [hf.2.2.2]
  simp [Model.relayedRun, Run.inbox]

open Consensus.Model in
/-- A model run with one real delivery: validator 1 receives `o` at `1`. -/
def deliveredRun (o : (protoOf Model.family Model.env).Object) : Run Model.family Model.env :=
  Run.mk (fun _ => ∅) monotone_const 5 [.deliver 1 o 1] (pkiFin 2) Model.sel
      (fun _ _ => []) (fun _ _ => [])
      (fun _ => 0)

open Consensus.Model in
/-- The delivery is a receipt in the system's log, tagged with the run's
environment, and no message tagged with another environment is in the log. -/
theorem faithful_receipt (o : (protoOf Model.family Model.env).Object) :
    ((sysOf schema Model.family (Fin 2)).log ⟨Model.env, deliveredRun o⟩).recv
      1 ⟨Model.env, o⟩ 1 ∧
    ∀ (E' : Env (Fin 2)) (o' : (protoOf Model.family E').Object) v t, E' ≠ Model.env →
      ¬ ((sysOf schema Model.family (Fin 2)).log ⟨Model.env, deliveredRun o⟩).recv
        v ⟨E', o'⟩ t := by
  have hf := sysOf_log_faithful (O := schema) (F := Model.family) (V := Fin 2)
    ⟨Model.env, deliveredRun o⟩
  refine ⟨(hf.2.1 1 o 1).mpr ⟨0, rfl⟩, ?_⟩
  intro E' o' v t hE hr
  obtain ⟨o'', he⟩ := hf.2.2.1 v _ t (Or.inr hr)
  exact hE (congrArg Sigma.fst he)

/-- A log with no receipts is not partially synchronous with GST `g'` once an
honest send at `t` has a deadline `d = max t g' + Δ − 1` in the horizon and an
honest node awake throughout `[t, d]` has not sent the message itself by `d`. -/
theorem silent_not_psync {V M : Type} (p : EnvPoint V) (L : CommLog V M)
    (hq : ∀ w m t, ¬ L.recv w m t) {g' t : Time} {v w : V} {m : M} (hv : p.HonestAt v t)
    (hs : L.sent v m t) (hr : ¬ L.fgAtt m)
    (hw : p.HonestAt w (max t g' + p.env.ΔAC - 1))
    (hd : max t g' + p.env.ΔAC - 1 ≤ p.horizon)
    (ha : p.AwakeOnClosed w t (max t g' + p.env.ΔAC - 1))
    (hns : ∀ t', t' ≤ max t g' + p.env.ΔAC - 1 → ¬ L.sent w m t') : ¬ L.PSync p g' := by
  intro h
  obtain ⟨t', ht', hs', -⟩ := h.msgs v m t hs hv hr w t le_rfl hd hd hw ha
  rcases hs' with hs' | hr
  · exact hns t' ht' hs'
  · exact hq _ _ _ hr

open Consensus.Model in
/-- Silent runs are valid: for every protocol and run data, there is a valid
run with no receipts (the canonical run with GST `horizon + 1`), and it
violates `PSync g'` whenever an honest send at `t` must reach, by the reachable
deadline `max t g' + Δ − 1`, an honest node awake throughout `[t, max t g' + Δ − 1]`
that did not send it itself. -/
theorem silent_run_valid (O : OutputSchema) (F : ProtocolFamily O) (V : Type) [Fintype V]
    [DecidableEq V] (E : Env V) (faultyAt : Time → Finset V) (hmono : Monotone faultyAt)
    (horizon : Time) (hh : 0 ≤ horizon)
    (key : Fin (Fintype.card V) ≃ V) (sel : (protoOf F E).Role → Finset (Fin (Fintype.card V)))
    (hsel : ∀ r, ((protoOf F E).selSpec r).Admits (sel r))
    (submit : V → Time → List Tx) (hash : (protoOf F E).Item → Nat) :
    ∃ (relay : V → Time → List Tx) (events : List (Event V (protoOf F E).Object)),
      let rho := Run.mk (F := F) (E := E) faultyAt hmono horizon events key sel submit relay hash
      rho.ExecutionValid ∧ (∀ w o t, ¬ rho.receives w o t) ∧
        ∀ g' v w o t, v ∉ faultyAt t → rho.releases v o t → ¬ (protoOf F E).isFGAtt o →
          w ∉ faultyAt (max t g' + E.ΔAC - 1) →
          max t g' + E.ΔAC - 1 ≤ horizon →
          (∀ u, t ≤ u → u ≤ max t g' + E.ΔAC - 1 → E.awake w u = true) →
          (∀ t', t' ≤ max t g' + E.ΔAC - 1 → ¬ rho.releases w o t') →
          ¬ CommLog.PSync rho.point rho.log g' := by
  obtain ⟨relay, events, hv, he⟩ :=
    canonical_run_from O F V E faultyAt hmono horizon hh key sel hsel submit hash (horizon + 1)
  refine ⟨relay, events, hv, ?_, ?_⟩
  · intro w o t hr
    have hq := he.quiet w o t hr
    obtain ⟨i, hi⟩ := hr
    have := (hv.in_horizon _ (List.mem_of_getElem? hi)).2
    change t ≤ horizon at this
    change horizon + 1 ≤ t at hq
    dsimp only [Time] at *
    omega
  · intro g' v w o t hvh hs hr hw hd ha hns
    refine silent_not_psync _ _ ?_ hvh hs hr hw hd ha hns
    intro w' o' t' hr
    have hq := he.quiet w' o' t' hr
    obtain ⟨i, hi⟩ := hr
    have := (hv.in_horizon _ (List.mem_of_getElem? hi)).2
    change t' ≤ horizon at this
    change horizon + 1 ≤ t' at hq
    dsimp only [Time] at *
    omega

open Consensus.Model in
/-- Both validators tick at `0, 1, 2`; `42` is relayed to both at `1`. -/
def tickedRun : Run Model.family Model.env :=
  Run.mk (fun _ => ∅) monotone_const 2
      [.tick 0 0, .tick 1 0, .tick 0 1, .tick 1 1, .tick 0 2, .tick 1 2] (pkiFin 2)
      Model.sel (fun _ _ => []) (fun _ t => if t = 1 then [42] else []) (fun _ => 0)

open Consensus.Model in
theorem tickedRun_valid : tickedRun.ExecutionValid := by
  have hnd : ∀ (i : Nat) (w : Fin 2) (o : (protoOf Model.family Model.env).Object) (t : Time),
      tickedRun.events[i]? ≠ some (Event.deliver w o t) := by
    intro i w o t h
    have := List.mem_of_getElem? h
    simp [tickedRun] at this
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Model.sel_valid _ rfl, ?_⟩
  · simp [tickedRun, Event.keyLe, Event.time, Event.phase]
  · simp [tickedRun]
  · intro e he
    simp only [tickedRun, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro e _
    simp [tickedRun]
  · intro v t ht0 ht2 _ _
    change t ≤ 2 at ht2
    fin_cases v <;> interval_cases t <;> simp [tickedRun]
  · intro v t _
    rfl
  · intro v o t _
    rfl
  · intro v t he
    simp [tickedRun] at he
  · intro v t _ _ _ hw
    exact absurd hw.2 (by simp [Model.env])
  · intro i w o t h
    exact absurd h (hnd i w o t)
  · intro i w o t h
    exact absurd h (hnd i w o t)

open Consensus.Model in
/-- Truncating the valid run at `1` keeps the four ticks at times `≤ 1` and
drops those at `2`; the truncation is valid, its trace is the L0 prefix of the
full trace at `1`, and its log still has the transaction relayed at `1`. -/
theorem truncate_relayedRun :
    (tickedRun.truncate 1).events = [.tick 0 0, .tick 1 0, .tick 0 1, .tick 1 1] ∧
    (tickedRun.truncate 1).ExecutionValid ∧
    ((sysOf schema Model.family (Fin 2)).trace ⟨Model.env, tickedRun.truncate 1⟩).PrefixOf
      ((sysOf schema Model.family (Fin 2)).trace ⟨Model.env, tickedRun⟩) 1 ∧
    42 ∈ ((sysOf schema Model.family (Fin 2)).log
      ⟨Model.env, tickedRun.truncate 1⟩).inbox 0 1 := by
  refine ⟨?_, Run.truncate_valid tickedRun_valid (by decide) (by decide),
    (Run.truncate_prefix tickedRun_valid 1).1, ?_⟩
  · simp [Run.truncate_eq, tickedRun, Event.time]
  · simp [sysOf, tagLog, Run.log, Run.truncate_eq, tickedRun, Run.inbox]

/-! ## Two bounds: rows strictly before `ΔF`, every other message strictly before `Δ`

Two honest validators, always awake, `Δ = 2`, horizon `10`; validator 0 sends one message at
`0`, validator 1 receives it at `R`; the message is a row exactly when `row`. Delivery is
strictly before the bound, so a row is due by `ΔF − 1` and any other message by `Δ − 1 = 1`.
Regression witnesses at `ΔF < Δ`, `ΔF = Δ` and `ΔF > Δ` (`two_bound_witnesses`), and two
controls (`row_held_to_row_bound`: a row is due by `ΔF − 1`, not by `Δ − 1`, when `ΔF < Δ`;
`nonrow_held_to_message_bound`: a non-row is due by `Δ − 1`, not by `ΔF − 1`, when `ΔF > Δ`;
the row witness at `ΔF = 5 > Δ` shows that `msgs` does not hold rows to `Δ`), so no order
between the two bounds is assumed in either direction. -/

/-- `Δ = 2`, row bound `ΔF`, everyone awake. -/
def envT (ΔF : Time) (h : 0 < ΔF) : Env (Fin 2) := ⟨2, by decide, ΔF, h, fun _ _ => true⟩

/-- Both honest, horizon `10`, no submissions. -/
def ptT (ΔF : Time) (h : 0 < ΔF) : EnvPoint (Fin 2) :=
  ⟨envT ΔF h, fun _ => ∅, monotone_const, 10, fun _ _ => []⟩

/-- Validator 0 sends at `0`, validator 1 receives at `R`; the message is a row iff `row`. -/
def logT (row : Prop) (R : Time) : CommLog (Fin 2) Unit :=
  ⟨fun v _ t => v = 0 ∧ t = 0, fun v _ t => v = 1 ∧ t = R, fun _ _ => [], fun _ => row⟩

theorem heldT {ΔF : Time} {h : 0 < ΔF} {row : Prop} {R : Time} (w : Fin 2) (d : Time)
    (h0 : 0 ≤ d) (hR : R ≤ d) : (logT row R).Held (ptT ΔF h) w () d := by
  fin_cases w
  · exact ⟨0, h0, Or.inl ⟨rfl, rfl⟩, fun u _ _ hwk => by simp [Wakes, ptT, envT] at hwk⟩
  · exact ⟨R, hR, Or.inr ⟨rfl, rfl⟩, fun u _ _ hwk => by simp [Wakes, ptT, envT] at hwk⟩

/-- A receipt by `ΔF − 1` (a row) or by `Δ − 1 = 1` (any other message) meets `PSync 0`. -/
theorem psyncT {ΔF : Time} {h : 0 < ΔF} {row : Prop} {R : Time}
    (hrow : row → R ≤ ΔF - 1) (hnr : ¬ row → R ≤ 1) : (logT row R).PSync (ptT ΔF h) 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rintro v m t ⟨-, rfl⟩ - hr w a ha - - - -
    have := hnr hr
    have := le_max_right a 0
    exact heldT w (max a 0 + 2 - 1) (by linarith) (by linarith)
  · rintro v m t ⟨-, rfl⟩ - hr w a ha - - - -
    have := hrow hr
    have := le_max_right a 0
    exact heldT w (max a 0 + ΔF - 1) (by dsimp only [Time] at *; omega) (by linarith)
  · intro u x τ _ _ _ hx
    exact absurd hx List.not_mem_nil

/-- **Regression witnesses** at `ΔF = 1 < Δ`, `ΔF = 2 = Δ` and `ΔF = 5 > Δ`: a row received
exactly at `ΔF − 1` and a non-row received exactly at `Δ − 1` meet `PSync 0` (at `ΔF = 1`
the row is due at its send time `0`). -/
theorem two_bound_witnesses :
    (logT True 0).PSync (ptT 1 one_pos) 0 ∧ (logT False 1).PSync (ptT 1 one_pos) 0 ∧
    (logT True 1).PSync (ptT 2 two_pos) 0 ∧ (logT False 1).PSync (ptT 2 two_pos) 0 ∧
    (logT True 4).PSync (ptT 5 (by decide)) 0 ∧ (logT False 1).PSync (ptT 5 (by decide)) 0 := by
  refine ⟨psyncT ?_ ?_, psyncT ?_ ?_, psyncT ?_ ?_, psyncT ?_ ?_, psyncT ?_ ?_, psyncT ?_ ?_⟩ <;>
    simp

/-- **Control at `ΔF < Δ`**: a row received only at `Δ − 1 = 1` misses its row deadline
`ΔF − 1 = 0` (rows are held to their own bound, not to `Δ`). -/
theorem row_held_to_row_bound : ¬ (logT True 1).PSync (ptT 1 one_pos) 0 := by
  intro hp
  obtain ⟨t', ht', hs, -⟩ := hp.fgAtts 0 () 0 ⟨rfl, rfl⟩
    (by simp [EnvPoint.HonestAt, ptT]) trivial 1 0 le_rfl (by decide) (by decide)
    (by simp [EnvPoint.HonestAt, ptT]) (fun _ _ _ => rfl)
  rcases hs with ⟨h1, -⟩ | ⟨-, rfl⟩
  · exact absurd h1 (by decide)
  · exact absurd ht' (by decide)

/-- **Control at `ΔF > Δ`**: a non-row received only at `ΔF − 1 = 4` misses its deadline
`Δ − 1 = 1` (the larger row bound does not extend to other messages). -/
theorem nonrow_held_to_message_bound : ¬ (logT False 4).PSync (ptT 5 (by decide)) 0 := by
  intro hp
  obtain ⟨t', ht', hs, -⟩ := hp.msgs 0 () 0 ⟨rfl, rfl⟩
    (by simp [EnvPoint.HonestAt, ptT]) id 1 0 le_rfl (by decide) (by decide)
    (by simp [EnvPoint.HonestAt, ptT]) (fun _ _ _ => rfl)
  rcases hs with ⟨h1, -⟩ | ⟨-, rfl⟩
  · exact absurd h1 (by decide)
  · exact absurd ht' (by decide)

/-- A receipt at `ΔF` or later (a row, with `ΔF ≤ 11` so the deadline `ΔF − 1` is within the
horizon `10`) or at `Δ = 2` or later (any other message) misses `PSync 0`: the always-awake
validator 1 must hold the message strictly before the bound. -/
theorem not_psyncT {ΔF : Time} {h : 0 < ΔF} {row : Prop} {R : Time}
    (hrow : row → ΔF ≤ R) (hnr : ¬ row → 2 ≤ R) (hF : ΔF ≤ 11) :
    ¬ (logT row R).PSync (ptT ΔF h) 0 := by
  intro hp
  have hd : max 0 0 + (ptT ΔF h).env.ΔFG - 1 ≤ (ptT ΔF h).horizon := by
    change max 0 0 + ΔF - 1 ≤ 10; rw [max_self]; dsimp only [Time] at *; omega
  by_cases hr : row
  · obtain ⟨t', ht', hs, -⟩ := hp.fgAtts 0 () 0 ⟨rfl, rfl⟩
      (by simp [EnvPoint.HonestAt, ptT]) hr 1 0 le_rfl hd hd
      (by simp [EnvPoint.HonestAt, ptT]) (fun _ _ _ => rfl)
    rcases hs with ⟨h1, -⟩ | ⟨-, rfl⟩
    · exact absurd h1 (by decide)
    · have := hrow hr
      change t' ≤ max 0 0 + ΔF - 1 at ht'
      rw [max_self] at ht'; dsimp only [Time] at *; omega
  · obtain ⟨t', ht', hs, -⟩ := hp.msgs 0 () 0 ⟨rfl, rfl⟩
      (by simp [EnvPoint.HonestAt, ptT]) hr 1 0 le_rfl
      (by change max (0 : Time) 0 + 2 - 1 ≤ 10; decide)
      (by change max (0 : Time) 0 + 2 - 1 ≤ 10; decide)
      (by simp [EnvPoint.HonestAt, ptT]) (fun _ _ _ => rfl)
    rcases hs with ⟨h1, -⟩ | ⟨-, rfl⟩
    · exact absurd h1 (by decide)
    · have := hnr hr
      change t' ≤ max 0 0 + 2 - 1 at ht'
      rw [max_self] at ht'; dsimp only [Time] at *; omega

/-- **Rejections at the bound**: the six former at-bound witnesses (a row received exactly at
`ΔF`, a non-row exactly at `Δ = 2`, at `ΔF = 1, 2, 5`) now miss `PSync 0` (delivery is strictly
before the bound). -/
theorem two_bound_at_bound_late :
    ¬ (logT True 1).PSync (ptT 1 one_pos) 0 ∧ ¬ (logT False 2).PSync (ptT 1 one_pos) 0 ∧
    ¬ (logT True 2).PSync (ptT 2 two_pos) 0 ∧ ¬ (logT False 2).PSync (ptT 2 two_pos) 0 ∧
    ¬ (logT True 5).PSync (ptT 5 (by decide)) 0 ∧ ¬ (logT False 2).PSync (ptT 5 (by decide)) 0 := by
  refine ⟨not_psyncT ?_ ?_ ?_, not_psyncT ?_ ?_ ?_, not_psyncT ?_ ?_ ?_, not_psyncT ?_ ?_ ?_,
    not_psyncT ?_ ?_ ?_, not_psyncT ?_ ?_ ?_⟩ <;> simp

namespace RawArrival
open Consensus.Model

/-- An honest proposal needs a faulty credentialed item before it may be released. -/
abbrev proto (pub : Public) : Protocol pub Unit :=
  { Model.proto pub with dependencies := (Model.batchProto pub).dependencies }

def env : Env (Fin 3) := ⟨2, by decide, 2, by decide, fun _ _ => true⟩
def poison : Obj 3 Bool Unit Unit := .mk (.signed 2 true) (.item ()) []
def child : Obj 3 Bool Unit Unit := .mk (.signed 0 false) (.data ()) []

/-- Only the sender receives the prerequisite; the recipient receives the proposal alone. -/
def run : Run (O := schema) proto env :=
  Run.mk (fun _ => {2}) monotone_const 2
    [.tick 0 0, .tick 1 0, .deliver 0 poison 0,
      .tick 0 1, .tick 1 1, .deliver 1 child 1, .tick 0 2, .tick 1 2]
    (pkiFin 3) (fun (r : Bool) => if r then {2} else Finset.univ)
    (fun _ _ => []) (fun _ _ => []) (fun _ => 0)

private theorem valid : run.ExecutionValid := by
  refine ⟨by decide, ?_, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [run, Event.keyLe, Event.time, Event.phase]
  · intro e he
    simp only [run, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro e he
    simp only [run, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro v t ht hh hv _
    change t ≤ 2 at hh
    fin_cases v <;> interval_cases t <;> simp_all [run]
  · intro v t _; rfl
  · intro v o t _; rfl
  · intro v t he
    simp [run] at he
  · intro v t _ _ _ h
    simp [Wakes, env] at h
  · intro i v o t he q hq u hu hs
    have hi : i < 8 := (List.getElem?_eq_some_iff.mp he).1
    interval_cases i <;> simp [run] at he
    · obtain ⟨rfl, rfl, rfl⟩ := he
      have hq' : q = poison := List.mem_singleton.mp hq
      subst q
      change some (2 : Fin 3) = some u at hu
      cases Option.some.inj hu
      exact False.elim (hs (by simp [run]))
    · obtain ⟨rfl, rfl, rfl⟩ := he
      have hq' : q = child := List.mem_singleton.mp hq
      subst q
      change some (0 : Fin 3) = some u at hu
      cases Option.some.inj hu
      exact ⟨3, 1, by decide, Or.inl rfl, List.mem_singleton_self _⟩
  · intro r
    cases r
    · rfl
    · change ({2} : Finset (Fin 3)).card = min 1 3
      decide
  · intro i v o t he q hq k r ha
    have hi : i < 8 := (List.getElem?_eq_some_iff.mp he).1
    interval_cases i <;> simp [run] at he
    · obtain ⟨rfl, rfl, rfl⟩ := he
      have hq' : q = poison := List.mem_singleton.mp hq
      subst q
      simp only [poison, Obj.auth] at ha
      obtain ⟨rfl, rfl⟩ := ha
      exact Finset.mem_singleton_self _
    · obtain ⟨rfl, rfl, rfl⟩ := he
      have hq' : q = child := List.mem_singleton.mp hq
      subst q
      simp only [child, Obj.auth] at ha
      obtain ⟨rfl, rfl⟩ := ha
      exact Finset.mem_univ _

private theorem releases_iff (v : Fin 3) (o : Obj 3 Bool Unit Unit) (t : Time) :
    run.releases v o t ↔ v = 0 ∧ o = child ∧ (t = 1 ∨ t = 2) := by
  constructor
  · rintro ⟨i, he, ho⟩
    have hi : i < 8 := by
      rcases he with he | ⟨p, he⟩ <;> exact (List.getElem?_eq_some_iff.mp he).1
    have hr : run.releasesAt i = if i = 3 ∨ i = 6 then [child] else [] := by
      interval_cases i <;> rfl
    rw [hr] at ho
    split at ho
    next h =>
      obtain rfl := List.mem_singleton.mp ho
      rcases h with rfl | rfl <;> simp [Run.SendsAt, run] at he <;> aesop
    next h => exact False.elim (List.not_mem_nil ho)
  · rintro ⟨rfl, rfl, rfl | rfl⟩
    · exact ⟨3, Or.inl rfl, List.mem_singleton_self _⟩
    · exact ⟨6, Or.inl rfl, List.mem_singleton_self _⟩

private theorem psync : run.log.PSync run.point 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro v o t hs _ _ w a ha _ _ hw _
    obtain ⟨rfl, rfl, ht⟩ := (releases_iff v o t).mp hs
    have hta : 1 ≤ a := by rcases ht with rfl | rfl <;> dsimp only [Time] at * <;> omega
    refine ⟨1, ?_, ?_, ?_⟩
    · change 1 ≤ max a 0 + 2 - 1; dsimp only [Time] at *; omega
    · fin_cases w
      · exact Or.inl ((releases_iff 0 child 1).mpr ⟨rfl, rfl, Or.inl rfl⟩)
      · exact Or.inr ⟨5, rfl⟩
      · simp [EnvPoint.HonestAt, Run.point, run] at hw
    · intro u _ _ h
      simp [Wakes, Run.point, run, env] at h
  · intro v o t hs hv hrow
    exact False.elim hrow
  · intro v x t ht hv ha hx
    exact False.elim (List.not_mem_nil hx)

/-- Withholding a prerequisite no longer removes an honest proposal's timely raw arrival
from valid synchronous executions. Its deadline is in the horizon; the recipient remains
unready and never receives the prerequisite. No protocol admission is asserted. -/
theorem poisoned_arrival : run.ExecutionValid ∧ run.log.PSync run.point 0 ∧
    run.releases 0 child 1 ∧ run.receives 1 child 1 ∧
    (proto (pubOf env)).dependencies.ready
      (closure (P := proto (pubOf env)) (run.stateBefore 5 1).seen) child = false ∧
    poison ∉ run.ViewIdx 1 run.events.length := by
  exact ⟨valid, psync, ⟨3, Or.inl rfl, List.mem_singleton_self _⟩,
    ⟨5, rfl⟩, rfl, by change poison ∉ [child]; decide⟩

end RawArrival

section Compromise

/-- The only transaction source is honest at submission, then compromised at one. -/
def sourcePoint : EnvPoint (Fin 2) where
  env := ⟨2, by decide, 2, by decide, fun _ _ => true⟩
  faultyAt := fun t => if 1 ≤ t then {0} else ∅
  faultyAt_mono := by
    intro a b hab
    dsimp only
    split_ifs with ha hb
    · exact Finset.Subset.refl _
    · exact False.elim (hb (ha.trans hab))
    · exact Finset.empty_subset _
    · exact Finset.Subset.refl _
  horizon := 4
  submit := fun v t => if v = 0 ∧ t = 0 then [42] else []

/-- A transaction submitted honestly stays owed after the source's compromise. -/
theorem compromised_source_still_owed (L : CommLog (Fin 2) Unit)
    (h : L.PSync sourcePoint 0) : L.TxHeld 1 42 1 := by
  exact h.txs 0 42 0 (by decide) (by simp [EnvPoint.HonestAt, sourcePoint])
    rfl (by simp [sourcePoint]) 1 0 le_rfl (by decide)
    (by decide)
    (by simp [EnvPoint.HonestAt, sourcePoint]) (fun _ _ _ => rfl)

/-- Withholding all inbox copies is rejected even though the sole source is now faulty. -/
theorem compromised_source_no_inbox_rejected :
    ¬ (⟨fun _ _ _ => False, fun _ _ _ => False, fun _ _ => [], fun _ => False⟩ :
      CommLog (Fin 2) Unit).PSync sourcePoint 0 := by
  intro h
  obtain ⟨t, _, ht⟩ := compromised_source_still_owed _ h
  exact List.not_mem_nil ht.2

/-- The weakened source-through-receipt rule admits a completely empty inbox: the only
source is compromised before the first deadline. This is why ingress uses
submission-time honesty. -/
theorem source_through_receipt_vacuous :
    ∀ u x τ, 0 ≤ τ → sourcePoint.HonestAt u τ →
      x ∈ sourcePoint.submit u τ → ∀ a, τ ≤ a →
      sourcePoint.HonestAt u (max a 0 + sourcePoint.env.ΔAC - 1) →
      (⟨fun _ _ _ => False, fun _ _ _ => False, fun _ _ => [], fun _ => False⟩ :
        CommLog (Fin 2) Unit).TxHeld 1 x (max a 0 + sourcePoint.env.ΔAC - 1) := by
  intro u x τ _ _ hx a _ hu
  have huτ : u = 0 ∧ τ = 0 := by
    by_contra h
    simp [sourcePoint, h] at hx
  rcases huτ with ⟨rfl, rfl⟩
  apply False.elim
  apply hu
  have hd : (1 : Time) ≤ max a 0 + 2 - 1 := by linarith [le_max_right a 0]
  simp [sourcePoint, hd]

/-- A receiver already compromised at the deadline is intentionally outside delivery's scope. -/
theorem compromised_recipient_excluded :
    sourcePoint.HonestAt 0 0 ∧ ¬ sourcePoint.HonestAt 0 1 := by
  simp [EnvPoint.HonestAt, sourcePoint]

/-- An honest pre-exposure message stays owed after its sender is compromised. -/
theorem compromised_sender_message_owed (L : CommLog (Fin 2) Unit)
    (h : L.PSync sourcePoint 0) (hs : L.sent 0 () 0) (hf : ¬ L.fgAtt ()) :
    L.Held sourcePoint 1 () 1 := by
  exact h.msgs 0 () 0 hs (by simp [EnvPoint.HonestAt, sourcePoint]) hf
    1 0 le_rfl (by decide) (by decide)
    (by simp [EnvPoint.HonestAt, sourcePoint]) (fun _ _ _ => rfl)

/-- Key one wakes at two while the source is already compromised. -/
def wakingPoint : EnvPoint (Fin 2) :=
  { sourcePoint with env := ⟨2, by decide, 2, by decide,
      fun v t => decide (v = 0 ∨ 2 ≤ t)⟩ }

/-- A waking recipient is re-served by its own delay bound, not the original send's bound. -/
theorem compromised_sender_waking_service (L : CommLog (Fin 2) Unit)
    (h : L.PSync wakingPoint 0) (hs : L.sent 0 () 0) (hf : ¬ L.fgAtt ()) :
    Wakes wakingPoint.env 1 2 ∧ L.Held wakingPoint 1 () 3 := by
  refine ⟨by norm_num [Wakes, wakingPoint], ?_⟩
  apply h.msgs 0 () 0 hs (by simp [EnvPoint.HonestAt, wakingPoint, sourcePoint]) hf
    1 2 (by decide) (by decide) (by decide)
    (by simp [EnvPoint.HonestAt, wakingPoint, sourcePoint])
  intro u hu _
  simp [wakingPoint, hu]

end Compromise

end Consensus.Shape.Tests.Network

end

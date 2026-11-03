module
public import ConsensusLeanTest.Model
public import ConsensusLeanTest.Common
public import Mathlib.Tactic
@[expose] public section

/-! # Network tests (L0 delivery, L1 faithfulness)

* `waker_within_bound`: `Δ = 2`, GST `0`; validator 1 is
  asleep at `0` and `1` and awake from `2`. An honest send at `0` must be
  re-served to validator 1 strictly before the bound of its wake: held at
  `3 = max 2 0 + Δ − 1` (Francesco's rule, normal delivery: awake over the
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
    show max a g' + p.env.Δ - 1 = max (max a g') g + p.env.Δ - 1
    rw [max_assoc, max_eq_left hg]
  · intro a
    show max a g' + p.env.ΔF - 1 = max (max a g') g + p.env.ΔF - 1
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
def ptW : EnvPoint (Fin 2) := ⟨envW, Finset.univ, 5, fun _ _ => []⟩

/-- Validator 0 sends one message at `0`; receipts as given. -/
def logW (recv : Fin 2 → Unit → Time → Prop) : CommLog (Fin 2) Unit :=
  ⟨fun v _ t => v = 0 ∧ t = 0, recv, fun _ _ => [], fun _ => False⟩

/-- Francesco's rule for a waker: validator 1, asleep at `0`–`1` and awake from
`2`, must hold the message sent at `0` strictly before `max 2 0 + Δ = 4`, i.e. by `3`. -/
theorem waker_within_bound (recv : Fin 2 → Unit → Time → Prop) (h : (logW recv).PSync ptW 0) :
    (logW recv).Held ptW 1 () 3 :=
  h.msgs 0 (Finset.mem_univ _) () 0 ⟨rfl, rfl⟩ id 1 (Finset.mem_univ _) 2 (by decide)
    (by decide) (by decide) (fun u hu _ => by simp [ptW, envW, hu])

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
  · rintro v - m t ⟨-, rfl⟩ - w - a ha - - haw
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
  · intro u _ x τ _ _ hx
    exact absurd hx (List.not_mem_nil)

/-- The log with validator 1 receiving the message only at `3`, one unit after
its wake at `2`. -/
def recvAt3 : Fin 2 → Unit → Time → Prop := fun w _ t => w = 1 ∧ t = 3

/-- No instant re-delivery: receipt by the waker at `3 = max 2 0 + Δ − 1`, not at
its wake `2`, satisfies `PSync 0`. Validator 1 is awake over no delivery
interval `[a, max a 0 + 2 − 1]` with `a < 2`. -/
theorem waker_not_instant : (logW recvAt3).PSync ptW 0 ∧ ¬ (logW recvAt3).Held ptW 1 () 2 := by
  refine ⟨⟨?_, fun _ _ _ _ _ h => h.elim, ?_⟩, ?_⟩
  · rintro v - m t ⟨-, rfl⟩ - w - a ha - hh haw
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
        have hle : max a 0 ≤ max a 0 + ptW.env.Δ - 1 := by
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
  · intro u _ x τ _ _ hx
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

def ptR : EnvPoint (Fin 2) := ⟨envR, Finset.univ, 5, fun _ _ => []⟩

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

def ptN : EnvPoint (Fin 2) := ⟨envN, Finset.univ, 5, fun _ _ => []⟩

/-- Validator 0 sends at `-1`; nobody receives. -/
def logN : CommLog (Fin 2) Unit :=
  ⟨fun v _ t => v = 0 ∧ t = -1, fun _ _ _ => False, fun _ _ => [], fun _ => False⟩

/-- A send at a negative time is covered by `PSync 0`: validator 1 must hold
it at `max (-1) 0 + Δ − 1 = 1`. -/
theorem negative_send_covered : ¬ logN.PSync ptN 0 := by
  intro h
  obtain ⟨t', -, hs, -⟩ := h.msgs 0 (Finset.mem_univ _) () (-1) ⟨rfl, rfl⟩ id 1
    (Finset.mem_univ _) (-1) le_rfl (by decide) (by decide) (fun _ _ _ => rfl)
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
  obtain ⟨t', ht', hs, -⟩ := h.msgs 0 (Finset.mem_univ _) () 0 ⟨rfl, rfl⟩ id 1
    (Finset.mem_univ _) 0 le_rfl (by decide) (by decide) (fun _ _ _ => rfl)
  rcases hs with ⟨h1, -⟩ | ⟨-, rfl⟩
  · exact absurd h1 (by decide)
  · exact absurd ht' (by decide)

/-- **Acceptance strictly before the bound**: receipt at `t + Δ − 1 = 1` meets `PSync 0`
("received by that time" at the last time before the bound). -/
theorem receipt_before_deadline : (logD 1).PSync ptN 0 := by
  refine ⟨?_, fun _ _ _ _ _ h => h.elim, ?_⟩
  · rintro v - m t ⟨-, rfl⟩ - w - a ha - - -
    have h1 : (1 : Time) ≤ max a 0 + ptN.env.Δ - 1 := by
      change (1 : Time) ≤ max a 0 + 2 - 1
      have := le_max_right a 0
      dsimp only [Time] at *
      omega
    fin_cases w
    · exact ⟨0, by dsimp only [Time] at *; omega, Or.inl ⟨rfl, rfl⟩,
        fun u _ _ hwk => by simp [Wakes, ptN, envN] at hwk⟩
    · exact ⟨1, h1, Or.inr ⟨rfl, rfl⟩, fun u _ _ hwk => by simp [Wakes, ptN, envN] at hwk⟩
  · intro u _ x τ _ _ hx
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
  Run.mk Finset.univ 5 [.deliver 1 o 1] (pkiFin 2) Model.sel (fun _ _ => []) (fun _ _ => [])
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
    (hq : ∀ w m t, ¬ L.recv w m t) {g' t : Time} {v w : V} {m : M} (hv : v ∈ p.honest)
    (hs : L.sent v m t) (hr : ¬ L.row m) (hw : w ∈ p.honest)
    (hd : max t g' + p.env.Δ - 1 ≤ p.horizon)
    (ha : p.AwakeOnClosed w t (max t g' + p.env.Δ - 1))
    (hns : ∀ t', t' ≤ max t g' + p.env.Δ - 1 → ¬ L.sent w m t') : ¬ L.PSync p g' := by
  intro h
  obtain ⟨t', ht', hs', -⟩ := h.msgs v hv m t hs hr w hw t le_rfl hd hd ha
  rcases hs' with hs' | hr
  · exact hns t' ht' hs'
  · exact hq _ _ _ hr

open Consensus.Model in
/-- Silent runs are valid: for every protocol and run data, there is a valid
run with no receipts (the canonical run with GST `horizon + 1`), and it
violates `PSync g'` whenever an honest send at `t` must reach, by the reachable
deadline `max t g' + Δ − 1`, an honest node awake throughout `[t, max t g' + Δ − 1]`
that did not send it itself. -/
theorem silent_run_valid (O : OutputSchema) (F : Family O) (V : Type) [Fintype V]
    [DecidableEq V] (E : Env V) (honest : Finset V) (horizon : Time) (hh : 0 ≤ horizon)
    (key : Fin (Fintype.card V) ≃ V) (sel : (protoOf F E).Role → Finset (Fin (Fintype.card V)))
    (hsel : ∀ r, ((protoOf F E).selSpec r).Admits (sel r))
    (submit : V → Time → List Tx) (hash : (protoOf F E).Item → Nat) :
    ∃ (relay : V → Time → List Tx) (events : List (Event V (protoOf F E).Object)),
      let rho := Run.mk (F := F) (E := E) honest horizon events key sel submit relay hash
      rho.ExecutionValid ∧ (∀ w o t, ¬ rho.receives w o t) ∧
        ∀ g' v w o t, v ∈ honest → rho.releases v o t → ¬ (protoOf F E).isRow o → w ∈ honest →
          max t g' + E.Δ - 1 ≤ horizon →
          (∀ u, t ≤ u → u ≤ max t g' + E.Δ - 1 → E.awake w u = true) →
          (∀ t', t' ≤ max t g' + E.Δ - 1 → ¬ rho.releases w o t') →
          ¬ CommLog.PSync rho.point rho.log g' := by
  obtain ⟨relay, events, hv, he⟩ :=
    canonical_run_from O F V E honest horizon hh key sel hsel submit hash (horizon + 1)
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
  Run.mk Finset.univ 2 [.tick 0 0, .tick 1 0, .tick 0 1, .tick 1 1, .tick 0 2, .tick 1 2] (pkiFin 2)
      Model.sel (fun _ _ => []) (fun _ t => if t = 1 then [42] else []) (fun _ => 0)

open Consensus.Model in
theorem tickedRun_valid : tickedRun.ExecutionValid := by
  have hnd : ∀ (i : Nat) (w : Fin 2) (o : (protoOf Model.family Model.env).Object) (t : Time),
      tickedRun.events[i]? ≠ some (Event.deliver w o t) := by
    intro i w o t h
    have := List.mem_of_getElem? h
    simp [tickedRun] at this
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Model.sel_valid _ rfl, ?_⟩
  · simp [tickedRun, Event.keyLe, Event.time, Event.phase]
  · simp [tickedRun]
  · intro e he
    simp only [tickedRun, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro e _
    exact Finset.mem_univ _
  · intro v _ t ht0 ht2 _
    change t ≤ 2 at ht2
    fin_cases v <;> interval_cases t <;> simp [tickedRun]
  · intro v t _
    rfl
  · intro v o t _
    rfl
  · intro i v o t he
    exact False.elim (hnd i v o t he)
  · intro v t he
    simp [tickedRun] at he
  · intro v _ t _ _ hw
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

/-! ## Two bounds: rows within `ΔF`, every other message within `Δ`

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
def ptT (ΔF : Time) (h : 0 < ΔF) : EnvPoint (Fin 2) := ⟨envT ΔF h, Finset.univ, 10, fun _ _ => []⟩

/-- Validator 0 sends at `0`, validator 1 receives at `R`; the message is a row iff `row`. -/
def logT (row : Prop) (R : Time) : CommLog (Fin 2) Unit :=
  ⟨fun v _ t => v = 0 ∧ t = 0, fun v _ t => v = 1 ∧ t = R, fun _ _ => [], fun _ => row⟩

theorem heldT {ΔF : Time} {h : 0 < ΔF} {row : Prop} {R : Time} (w : Fin 2) (d : Time)
    (h0 : 0 ≤ d) (hR : R ≤ d) : (logT row R).Held (ptT ΔF h) w () d := by
  fin_cases w
  · exact ⟨0, h0, Or.inl ⟨rfl, rfl⟩, fun u _ _ hwk => by simp [Wakes, ptT, envT] at hwk⟩
  · exact ⟨R, hR, Or.inr ⟨rfl, rfl⟩, fun u _ _ hwk => by simp [Wakes, ptT, envT] at hwk⟩

/-- A receipt by `ΔF − 1` (a row) or by `Δ − 1 = 1` (any other message), at a time `R ≥ 0`,
meets `PSync 0`. -/
theorem psyncT {ΔF : Time} {h : 0 < ΔF} {row : Prop} {R : Time}
    (hrow : row → R ≤ ΔF - 1) (hnr : ¬ row → R ≤ 1) : (logT row R).PSync (ptT ΔF h) 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rintro v - m t ⟨-, rfl⟩ hr w - a ha - - -
    have := hnr hr
    have := le_max_right a 0
    exact heldT w (max a 0 + 2 - 1) (by linarith) (by linarith)
  · rintro v - m t ⟨-, rfl⟩ hr w - a ha - - -
    have := hrow hr
    have := le_max_right a 0
    exact heldT w (max a 0 + ΔF - 1) (by dsimp only [Time] at *; omega) (by linarith)
  · intro u _ x τ _ _ hx
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
  obtain ⟨t', ht', hs, -⟩ := hp.rows 0 (Finset.mem_univ _) () 0 ⟨rfl, rfl⟩ trivial 1
    (Finset.mem_univ _) 0 le_rfl (by decide) (by decide) (fun _ _ _ => rfl)
  rcases hs with ⟨h1, -⟩ | ⟨-, rfl⟩
  · exact absurd h1 (by decide)
  · exact absurd ht' (by decide)

/-- **Control at `ΔF > Δ`**: a non-row received only at `ΔF − 1 = 4` misses its deadline
`Δ − 1 = 1` (the larger row bound does not extend to other messages). -/
theorem nonrow_held_to_message_bound : ¬ (logT False 4).PSync (ptT 5 (by decide)) 0 := by
  intro hp
  obtain ⟨t', ht', hs, -⟩ := hp.msgs 0 (Finset.mem_univ _) () 0 ⟨rfl, rfl⟩ id 1
    (Finset.mem_univ _) 0 le_rfl (by decide) (by decide) (fun _ _ _ => rfl)
  rcases hs with ⟨h1, -⟩ | ⟨-, rfl⟩
  · exact absurd h1 (by decide)
  · exact absurd ht' (by decide)

end Consensus.Shape.Tests.Network

end

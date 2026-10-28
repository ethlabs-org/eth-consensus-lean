module
public import ConsensusModelProofs
public import Mathlib.Tactic

@[expose] public section

/-! # Injective-hash lifting (meta-result, moved from the library)

A valid run with no hash collision has a rehashed twin with an injective hash
and the same trace, log and validity (`Run.injective_twin`). So a
trace-invariant property holds on all runs up to the collision excuse iff it
holds on all valid runs with an injective hash (`holds_of_injective`,
`injective_of_holds`). No library proof uses it; it is checked here. -/
namespace Consensus.Model
variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : Family O} {E : Env V}

namespace Run

/-- A finite pool of all released or delivered roots. -/
def roots (rho : Run F E) : List (protoOf F E).Object :=
  (List.range rho.events.length).flatMap fun i =>
    rho.releasesAt i ++ (match rho.events[i]? with
      | some (.deliver _ o _) => [o]
      | _ => [])

theorem observed_mem_roots {rho : Run F E} {o : (protoOf F E).Object}
    (ho : o ∈ rho.Observed) : o ∈ closure rho.roots := by
  obtain ⟨v, hv, hov⟩ := ho
  obtain ⟨k, r, hk, he, hc⟩ := rho.mem_viewIdx_iff.mp hov
  apply List.mem_flatMap.mpr
  refine ⟨r, ?_, hc⟩
  apply List.mem_flatMap.mpr
  refine ⟨k, List.mem_range.mpr hk, ?_⟩
  rcases he with ⟨t, ht, hr⟩ | ⟨t, ht⟩
  · exact List.mem_append_left _ hr
  · exact List.mem_append_right _ (by simp [ht])

theorem observedItems_finite (rho : Run F E) : {x | rho.ObservedItem x}.Finite := by
  classical
  apply Set.Finite.subset (s := ↑((closure rho.roots).filterMap Obj.item?).toFinset)
    (Finset.finite_toSet _)
  intro x ⟨o, ho, hx⟩
  simp only [Finset.mem_coe, List.mem_toFinset, List.mem_filterMap]
  exact ⟨o, observed_mem_roots ho, hx⟩

/-- Extend the observed collision-free hash to an injective hash. -/
theorem extend_hash (rho : Run F E) (hn : ¬ rho.HashCollision) :
    ∃ hash' : (protoOf F E).Item → Nat, Function.Injective hash' ∧
      ∀ x, rho.ObservedItem x → hash' x = rho.hash x := by
  classical
  let S := rho.observedItems_finite.toFinset
  let M := S.sup rho.hash
  have bound : ∀ x, rho.ObservedItem x → rho.hash x ≤ M := by
    intro x hx
    exact Finset.le_sup (f := rho.hash) (by simpa [S] using hx)
  have inj : ∀ a, rho.ObservedItem a → ∀ b, rho.ObservedItem b →
      rho.hash a = rho.hash b → a = b := by
    intro a ha b hb he
    by_contra hab
    exact hn ⟨a, b, hab, ha, hb, he⟩
  obtain ⟨enc, henc⟩ := Countable.exists_injective_nat (protoOf F E).Item
  let f := fun x => if rho.ObservedItem x then rho.hash x else M + 1 + enc x
  refine ⟨f, ?_, ?_⟩
  · intro a b he
    by_cases ha : rho.ObservedItem a <;> by_cases hb : rho.ObservedItem b
    · exact inj a ha b hb (by simpa [f, ha, hb] using he)
    · have := bound a ha
      simp only [f, ite_eq_left ha, ite_eq_right hb] at he
      omega
    · have := bound b hb
      simp only [f, ite_eq_right ha, ite_eq_left hb] at he
      omega
    · apply henc
      simpa [f, ha, hb] using he
  · intro x hx; simp [f, hx]

theorem digests_eq_of_observed (rho : Run F E) (hash' : (protoOf F E).Item → Nat)
    (ha : ∀ x, rho.ObservedItem x → hash' x = rho.hash x)
    {o : (protoOf F E).Object} (ho : o ∈ rho.Observed) :
    digests hash' o = digests rho.hash o := by
  unfold digests
  apply List.map_congr_left
  intro x hx
  obtain ⟨d, hd, he⟩ := List.mem_filterMap.mp hx
  have obs : d ∈ rho.Observed := by
    obtain ⟨v, hv, hov⟩ := ho
    obtain ⟨k, r, hk, hr, hc⟩ := rho.mem_viewIdx_iff.mp hov
    exact ⟨v, hv, rho.mem_viewIdx_iff.mpr ⟨k, r, hk, hr, hc.trans hd⟩⟩
  exact Prod.ext rfl (ha x ⟨d, obs, he⟩)

end Run

theorem releaseAll_eq_of_digests {pub : Public} {Out : Type} {P : Protocol pub Out}
    (hash hash' : P.Item → Nat) (k : Key pub) (nd : Node P) (cs : List P.Object)
    (ha : ∀ o ∈ (releaseAll P hash k nd cs).2, digests hash' o = digests hash o) :
    releaseAll P hash' k nd cs = releaseAll P hash k nd cs := by
  induction cs generalizing nd with
  | nil => rfl
  | cons c cs ih =>
    unfold releaseAll at ha ⊢
    split at ha
    next hf =>
      simp only [hf, ↓reduceIte]
      have hc := ha c List.mem_cons_self
      rw [hc]
      rw [ih _ (fun o ho => ha o (List.mem_cons_of_mem c ho))]
    next hf =>
      simp only [hf]
      exact ih nd ha

namespace Run
/-- Replacing the hash while preserving observed digests preserves the trace. -/
theorem rehash_trace (rho : Run F E) (hv : rho.ExecutionValid) (hash' : (protoOf F E).Item → Nat)
    (ha : ∀ h, rho.ObservedItem h → hash' h = rho.hash h) :
    let r := {rho with hash := hash'}
    (∀ i, r.stateBefore i = rho.stateBefore i) ∧
      (∀ i, r.releasesAt i = rho.releasesAt i) := by
  let r := {rho with hash := hash'}
  have tick_eq : ∀ i v t, rho.events[i]? = some (.tick v t) →
      r.tick (rho.stateBefore i v) v t = rho.tick (rho.stateBefore i v) v t := by
    intro i v t he
    unfold tick
    change (if E.awake v t then releaseAll _ hash' _ _ _ else _) = _
    split
    · apply releaseAll_eq_of_digests
      intro o ho
      apply rho.digests_eq_of_observed hash' ha
      refine ⟨v, hv.honest_only _ (List.mem_of_getElem? he), rho.mem_viewIdx_iff.mpr ⟨i, o,
        (List.getElem?_eq_some_iff.mp he).1, Or.inl ⟨t, he, ?_⟩, .refl _⟩⟩
      simpa only [releasesAt, he, tick, ‹E.awake v t = true›, ↓reduceIte, r,
        show r.inbox = rho.inbox from rfl, show r.candidates = rho.candidates from rfl,
        show r.ownKey = rho.ownKey from rfl] using ho
    · rfl
  have states : ∀ i, r.stateBefore i = rho.stateBefore i := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih =>
      cases he : rho.events[i]? with
      | none => simpa [stateBefore, List.take_add_one, r, he] using ih
      | some e =>
        rw [r.stateBefore_succ he, rho.stateBefore_succ he, ih]
        cases e with
        | tick v t => simp only [step, tick_eq i v t he]
        | restart v t => rfl
        | deliver v o t =>
          have ho : o ∈ rho.Observed :=
            ⟨v, hv.honest_only _ (List.mem_of_getElem? he), rho.mem_viewIdx_iff.mpr ⟨i, o,
              (List.getElem?_eq_some_iff.mp he).1, Or.inr ⟨t, he⟩, .refl _⟩⟩
          simp only [step]
          simp only [show r.hash = hash' from rfl, rho.digests_eq_of_observed hash' ha ho]
  refine ⟨states, ?_⟩
  intro i
  change r.releasesAt i = rho.releasesAt i
  unfold releasesAt
  change (match rho.events[i]? with | some (.tick v t) => _ | _ => _) = _
  cases he : rho.events[i]? with
  | none => rfl
  | some e =>
    cases e with
    | tick v t =>
      change (r.tick (r.stateBefore i v) v t).2 = _
      rw [states i]
      exact congrArg Prod.snd (tick_eq i v t he)
    | deliver => rfl
    | restart => rfl

/-- Runs in one environment differ only in their hash, which agrees on all
items observed by the first run (same honest set, horizon, events, PKI,
selection, submissions and relay). -/
structure SameTrace (rho r : Run F E) : Prop where
  honest : r.honest = rho.honest
  horizon : r.horizon = rho.horizon
  events : r.events = rho.events
  key : r.key = rho.key
  sel : r.sel = rho.sel
  submit : r.submit = rho.submit
  relay : r.relay = rho.relay
  hash : ∀ x, rho.ObservedItem x → r.hash x = rho.hash x

namespace SameTrace
variable {rho r : Run F E} (h : SameTrace rho r)
include h

theorem trace (hv : rho.ExecutionValid) :
    (∀ i, r.stateBefore i = rho.stateBefore i) ∧
    (∀ i, r.releasesAt i = rho.releasesAt i) := by
  have hr : r = {rho with hash := r.hash} := by
    cases rho; cases r
    simp only [Run.mk.injEq]
    exact ⟨h.honest, h.horizon, h.events, h.key, h.sel, h.submit, h.relay, trivial⟩
  rw [hr]
  exact rho.rehash_trace hv r.hash h.hash

theorem viewIdx_eq (hv : rho.ExecutionValid) : r.ViewIdx = rho.ViewIdx := by
  obtain ⟨hs, -⟩ := h.trace hv
  funext v i
  simp only [Run.ViewIdx, hs]

theorem observed_eq (hv : rho.ExecutionValid) : r.Observed = rho.Observed := by
  simp only [Run.Observed, h.honest, h.events, h.viewIdx_eq hv]

theorem readIdx_eq (hv : rho.ExecutionValid) : r.readIdx = rho.readIdx := by
  obtain ⟨hs, _⟩ := h.trace hv
  funext g v i
  simp only [Run.readIdx, hs]

theorem releases_eq (hv : rho.ExecutionValid) : r.releases = rho.releases := by
  obtain ⟨_, hr⟩ := h.trace hv
  funext v o t
  simp only [Run.releases, h.events, hr]

theorem receives_eq : r.receives = rho.receives := by
  funext v o t
  simp only [Run.receives, h.events]

theorem inbox_eq : r.inbox = rho.inbox := by
  funext v t
  simp only [Run.inbox, h.submit, h.relay]

/-- The communication log is preserved (derived from the events, submissions
and relay; no field of its own). -/
theorem log_eq (hv : rho.ExecutionValid) : r.log = rho.log := by
  simp only [Run.log, h.releases_eq hv, h.receives_eq, h.inbox_eq]

/-- Rehashing a valid source preserves execution validity as well as its reads. -/
theorem executionValid (hv : rho.ExecutionValid) : r.ExecutionValid := by
  obtain ⟨_, hr⟩ := h.trace hv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [h.horizon] using hv.horizon_nonneg
  · simpa only [h.events] using hv.sorted
  · simpa only [h.events] using hv.nodup
  · simpa only [h.events, h.horizon] using hv.in_horizon
  · simpa only [h.events, h.honest] using hv.honest_only
  · simpa only [h.events, h.honest, h.horizon] using hv.tick_total
  · simpa only [h.events] using hv.tick_awake
  · simpa only [h.events] using hv.deliver_awake
  · simpa only [h.events] using hv.restart_at_wake
  · simpa only [h.events, h.honest, h.horizon] using hv.wake_restart
  · simpa only [Unforgeable, signerOf, h.events, h.honest, h.key, hr] using hv.unforgeable
  · simpa only [SelValid, h.sel] using hv.selValid
  · simpa only [Credentials, h.events, h.sel] using hv.credentials

end SameTrace

theorem rehash_sameTrace (rho : Run F E) (hash' : (protoOf F E).Item → Nat)
    (ha : ∀ x, rho.ObservedItem x → hash' x = rho.hash x) :
    rho.SameTrace {rho with hash := hash'} := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ha⟩

/-- Every collision-free run has an injective-hash trace twin. -/
theorem injective_twin (rho : Run F E) (hn : ¬ rho.HashCollision) :
    ∃ r : Run F E, rho.SameTrace r ∧ r.InjectiveHash := by
  obtain ⟨hash', hi, ha⟩ := rho.extend_hash hn
  exact ⟨{rho with hash := hash'}, rho.rehash_sameTrace hash' ha, hi⟩

end Run

/-- Trace-invariant properties lift from injective hashes to collision-escaped claims.
Only transport from a valid source satisfying `A` is required: assumptions move
forward to its rehashed twin, and the conclusion moves back to the source. -/
theorem holds_of_injective (O : OutputSchema) (F : Family O) (V : Type) [Fintype V] [DecidableEq V]
    (A P : (sysOf O F V).Run → Prop)
    (ha : ∀ E (r s : Run F E), r.ExecutionValid → A ⟨E, r⟩ →
      r.SameTrace s → A ⟨E, s⟩)
    (hp : ∀ E (r s : Run F E), r.ExecutionValid → A ⟨E, r⟩ →
      r.SameTrace s → (P ⟨E, s⟩ → P ⟨E, r⟩))
    (hi : ∀ r, (sysOf O F V).Valid r → A r → r.2.InjectiveHash → P r) :
    (sysOf O F V).Holds A P := by
  rintro ⟨E, r⟩ hv ar
  by_cases hc : r.HashCollision
  · exact Or.inr hc
  · obtain ⟨s, hs, hinj⟩ := r.injective_twin hc
    exact Or.inl (hp E r s hv ar hs (hi ⟨E, s⟩ (hs.executionValid hv) (ha E r s hv ar hs) hinj))

/-- The converse direction of injective-hash lifting, on valid runs. -/
theorem injective_of_holds (O : OutputSchema) (F : Family O) (V : Type) [Fintype V] [DecidableEq V]
    (A P : (sysOf O F V).Run → Prop) (h : (sysOf O F V).Holds A P) :
    ∀ r, (sysOf O F V).Valid r → A r → r.2.InjectiveHash → P r := by
  intro r hv ha hi
  exact (h r hv ha).resolve_right (Run.not_hashCollision_of_injective hi)
end Consensus.Model
end

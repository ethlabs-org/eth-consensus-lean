module
public import ConsensusModel.System

@[expose] public section
namespace Consensus.Model
variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : Family O} {E : Env V}
namespace Obj
variable {n : Nat} {Role Item Body : Type}

theorem partsList_eq (cs : List (Obj n Role Item Body)) :
    parts.partsList cs = cs.flatMap parts := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [parts.partsList, ih]

theorem parts_eq (o : Obj n Role Item Body) : o.parts = o :: o.carried.flatMap parts := by
  cases o
  simp [parts, partsList_eq, carried]

theorem carried_size_lt (o : Obj n Role Item Body) : sizeOf o.carried < sizeOf o := by
  cases o
  simp [carried]

theorem contains_of_mem_parts (o d : Obj n Role Item Body) (h : d ∈ o.parts) : Contains o d := by
  rw [parts_eq, List.mem_cons] at h
  rcases h with rfl | h
  · exact .refl _
  · obtain ⟨c, hc, hd⟩ := List.mem_flatMap.mp h
    exact .step hc (contains_of_mem_parts c d hd)
termination_by sizeOf o
decreasing_by exact lt_trans (List.sizeOf_lt_of_mem hc) (carried_size_lt _)

theorem mem_parts_of_contains {o d : Obj n Role Item Body} (h : Contains o d) : d ∈ o.parts := by
  induction h with
  | refl o => rw [parts_eq]; exact List.mem_cons_self
  | step hc _ ih =>
    rw [parts_eq]
    exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨_, hc, ih⟩)

theorem mem_parts_iff (o d : Obj n Role Item Body) : d ∈ o.parts ↔ Contains o d :=
  ⟨contains_of_mem_parts o d, mem_parts_of_contains⟩

end Obj

namespace Run

theorem not_hashCollision_of_injective {rho : Run F E} (hi : rho.InjectiveHash) :
    ¬ rho.HashCollision := by
  rintro ⟨x, y, hne, _, _, he⟩
  exact hne (hi he)

/-- A finite pool of all released or delivered roots. -/
def roots (rho : Run F E) : List (protoOf F E).Object :=
  (List.range rho.events.length).flatMap fun i =>
    rho.releasesAt i ++ (match rho.events[i]? with
      | some (.deliver _ o _) => [o]
      | _ => [])

theorem observed_mem_roots {rho : Run F E} {o : (protoOf F E).Object}
    (ho : o ∈ rho.Observed) : o ∈ closure rho.roots := by
  obtain ⟨v, hv, k, r, hk, he, hc⟩ := ho
  apply List.mem_flatMap.mpr
  refine ⟨r, ?_, (Obj.mem_parts_iff _ _).mpr hc⟩
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
  let f := fun x => if rho.ObservedItem x then rho.hash x else M + 1 + Encodable.encode x
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
    · apply Encodable.encode_injective
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
    obtain ⟨v, hv, k, r, hk, hr, hc⟩ := ho
    exact ⟨v, hv, k, r, hk, hr, hc.trans ((Obj.mem_parts_iff _ _).mp hd)⟩
  exact Prod.ext rfl (ha x ⟨d, obs, he⟩)

theorem stateBefore_succ (rho : Run F E) {i : Nat} {e : Event V (protoOf F E).Object}
    (hi : rho.events[i]? = some e) :
    rho.stateBefore (i + 1) = rho.step (rho.stateBefore i) e := by
  simp only [stateBefore, List.take_add_one, hi, Option.toList_some, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

end Run

theorem releaseAll_eq_of_digests {pub : Public} {Out : Type} {P : Protocol pub Out}
    (hash hash' : P.Item → Nat) (nd : Node P) (cs : List P.Object)
    (ha : ∀ o ∈ (releaseAll hash nd cs).2, digests hash' o = digests hash o) :
    releaseAll hash' nd cs = releaseAll hash nd cs := by
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
    change (if E.awake v t then releaseAll hash' _ _ else _) = _
    split
    · apply releaseAll_eq_of_digests
      intro o ho
      apply rho.digests_eq_of_observed hash' ha
      refine ⟨v, hv.honest_only _ (List.mem_of_getElem? he), i, o,
        (List.getElem?_eq_some_iff.mp he).1, Or.inl ⟨t, he, ?_⟩, .refl _⟩
      simpa only [releasesAt, he, tick, ‹E.awake v t = true›, ↓reduceIte, r,
        show r.inbox = rho.inbox from rfl, show r.candidates = rho.candidates from rfl] using ho
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
            ⟨v, hv.honest_only _ (List.mem_of_getElem? he), i, o,
              (List.getElem?_eq_some_iff.mp he).1, Or.inr ⟨t, he⟩, .refl _⟩
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
  obtain ⟨_, hr⟩ := h.trace hv
  funext v i
  simp only [Run.ViewIdx, h.events, hr]

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

/-- Rehashing a valid source preserves execution validity as well as its reads. -/
theorem executionValid (hv : rho.ExecutionValid) : r.ExecutionValid := by
  obtain ⟨_, hr⟩ := h.trace hv
  have hs : r.ScheduleWellFormed := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [h.horizon] using hv.horizon_nonneg
    · simpa only [h.events] using hv.sorted
    · simpa only [h.events] using hv.nodup
    · simpa only [h.events, h.horizon] using hv.in_horizon
    · simpa only [h.events, h.honest] using hv.honest_only
    · simpa only [h.events] using hv.tick_public
    · simpa only [h.events, h.honest, h.horizon] using hv.tick_total
  have hw : r.SleepWellFormed := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [h.events] using hv.tick_awake
    · simpa only [h.events] using hv.deliver_awake
    · simpa only [h.events] using hv.restart_at_wake
    · simpa only [h.events, h.honest, h.horizon] using hv.wake_restart
  refine ⟨hs, hw, ?_, ?_, ?_⟩
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

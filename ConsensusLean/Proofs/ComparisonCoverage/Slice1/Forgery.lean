module
public import ConsensusLean.Comparison.Activity
public import ConsensusLean.Lemmas.Model.Canonical.Parts
public import ConsensusLean.Lemmas.Model.Objects

public section

/-! # Slice 1 coverage: forged objects and the exact activity count

A witness with positive activity delivers forged objects to one honest node `u₀`. A forged object
`forged k r m tag` is signed by key `k` in role `r` and says `m`; with `tag` it carries one unsigned
copy of `m`, so that two forgeries of one key in one role are distinct objects. A forgery plan
`fs` lists entries `Forgery` (key, role, message, tag, time): the forged object is injected to
`u₀` at the entry's time (`forgeInj`).

* `parts_forged`: the only signed part of a forged object is itself.
* `activeIn_iff_of_forgeries`: in the scheduled run with these injections, constant faults and a
  valid schedule, a key is active on `[a, b)` exactly when the plan forges it at a time of
  `[a, b)`, provided every planned key is compromised, `u₀` is honest and always awake, every
  planned time is within `[0, horizon]` and at or after its role's floor, and the plan injects each
  forged object at one time only.
* `activeFaulty_of_forgeries`: the active set on `[a, b)` is the set of validators of the keys the
  plan forges in `[a, b)`. -/

namespace Consensus.Comparison

open Consensus.Model

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : ProtocolFamily O}
  {E : Env V}

/-- A forged object: signed by `k` in role `r`, saying `m`, carrying one unsigned copy of `m` when
`tag`. -/
def forged (k : Fin (Fintype.card V)) (r : (protoOf F E).Role)
    (m : Msg (protoOf F E).Item (protoOf F E).Body) (tag : Bool) : (protoOf F E).Object :=
  .mk (.signed k r) m (if tag then [.mk .none m []] else [])

omit [DecidableEq V] in
/-- The only signed part of a forged object is itself. -/
theorem parts_forged {k : Fin (Fintype.card V)} {r : (protoOf F E).Role}
    {m : Msg (protoOf F E).Item (protoOf F E).Body} {tag : Bool} {d : (protoOf F E).Object}
    (hd : Obj.Contains (forged k r m tag) d) : d = forged k r m tag ∨ d.auth = .none := by
  unfold Obj.Contains at hd
  rw [Obj.parts_eq] at hd
  rcases List.mem_cons.mp hd with h | h
  · exact Or.inl h
  · right
    cases tag <;> simp [forged, Obj.carried, Obj.parts_eq] at h
    subst h
    rfl

omit [DecidableEq V] in
theorem forged_auth (k : Fin (Fintype.card V)) (r : (protoOf F E).Role)
    (m : Msg (protoOf F E).Item (protoOf F E).Body) (tag : Bool) :
    (forged k r m tag).auth = .signed k r := by rfl

omit [DecidableEq V] in
theorem forged_inj {k k' : Fin (Fintype.card V)} {r r' : (protoOf F E).Role}
    {m m' : Msg (protoOf F E).Item (protoOf F E).Body} {tag tag' : Bool}
    (h : (forged k r m tag : (protoOf F E).Object) = forged k' r' m' tag') :
    k = k' ∧ r = r' ∧ m = m' ∧ tag = tag' := by
  unfold forged at h
  injection h with ha hm hc
  injection ha with hk hr
  refine ⟨hk, hr, hm, ?_⟩
  cases tag <;> cases tag' <;> simp_all

variable (F E) in
/-- A forgery plan entry: the key, role, message and tag of the forged object, and its injection
time. -/
structure Forgery where
  key : Fin (Fintype.card V)
  role : (protoOf F E).Role
  msg : Msg (protoOf F E).Item (protoOf F E).Body
  tag : Bool
  time : Time

/-- The forged object of a plan entry. -/
abbrev Forgery.obj (x : Forgery F E) : (protoOf F E).Object := forged x.key x.role x.msg x.tag

/-- The injections of a forgery plan: at `t`, to `u₀`, the forged objects the plan schedules at
`t`. -/
def forgeInj (u₀ : V) (fs : List (Forgery F E)) (t : Time) (v : V) : List (protoOf F E).Object :=
  if v = u₀ then (fs.filter fun x => x.time = t).map Forgery.obj else []

theorem mem_forgeInj {u₀ : V} {fs : List (Forgery F E)} {t : Time} {v : V}
    {o : (protoOf F E).Object} :
    o ∈ forgeInj u₀ fs t v ↔ v = u₀ ∧ ∃ x ∈ fs, x.time = t ∧ o = x.obj := by
  unfold forgeInj
  split_ifs with h
  · simp only [List.mem_map, List.mem_filter, decide_eq_true_eq, h, true_and]
    constructor
    · rintro ⟨x, ⟨hx, ht⟩, rfl⟩; exact ⟨x, hx, ht, rfl⟩
    · rintro ⟨x, hx, ht, rfl⟩; exact ⟨x, ⟨hx, ht⟩, rfl⟩
  · simp [h]

/-- The premises of the exact activity count. -/
structure ForgeryPremises (rho : Model.Run F E) (fl : (protoOf F E).Role → Option Time)
    (u₀ : V) (fs : List (Forgery F E))
    (pol : List (Event V (protoOf F E).Object) → V → (protoOf F E).Object → Time → Bool) :
    Prop where
  valid : (rho.injectRun (fun _ => 0) (forgeInj u₀ fs) pol).ExecutionValid
  constFaults : ∀ t, rho.faultyAt t = rho.faultyAt 0
  key_faulty : ∀ x ∈ fs, rho.key x.key ∈ rho.faultyAt 0
  u₀_honest : u₀ ∉ rho.faultyAt 0
  u₀_awake : ∀ t, E.awake u₀ t = true
  time_range : ∀ x ∈ fs, 0 ≤ x.time ∧ x.time ≤ rho.horizon
  floor_le : ∀ x ∈ fs, ∀ s, fl x.role = some s → s ≤ x.time
  unique : ∀ x ∈ fs, ∀ y ∈ fs, x.key = y.key → x.role = y.role → x.msg = y.msg →
    x.tag = y.tag → x.time = y.time

variable {rho : Model.Run F E} {fl : (protoOf F E).Role → Option Time}
  {u₀ : V} {fs : List (Forgery F E)}
  {pol : List (Event V (protoOf F E).Object) → V → (protoOf F E).Object → Time → Bool}

/-- A planned forgery is received by `u₀` at its time. -/
theorem forgery_received (h : ForgeryPremises rho fl u₀ fs pol) {x : Forgery F E}
    (hx : x ∈ fs) :
    (rho.injectRun (fun _ => 0) (forgeInj u₀ fs) pol).receives u₀
      (x.obj) x.time := by
  obtain ⟨h0, hh⟩ := h.time_range x hx
  have hmem : Event.deliver u₀ (x.obj) x.time ∈
      rho.injectEvents (fun _ => 0) (forgeInj u₀ fs) pol := by
    apply rho.injectEvents_layer _ _ _ x.time h0 hh
    rw [Model.Run.mem_injectLayer]
    refine Or.inr (Or.inr ⟨u₀, ?_, h.u₀_awake _, _,
      Or.inl (mem_forgeInj.mpr ⟨rfl, x, hx, rfl, rfl⟩), rfl⟩)
    rw [h.constFaults]
    exact h.u₀_honest
  rw [← Model.Run.withEvents_events rho (rho.injectEvents _ _ _)] at hmem
  exact List.mem_iff_getElem?.mp hmem

/-- The charging time of a planned forgery is its injection time. -/
private theorem chargeTime_eq {x : Forgery F E} (h : ForgeryPremises rho fl u₀ fs pol)
    (hx : x ∈ fs) : chargeTime fl x.role x.time = x.time := by
  unfold chargeTime
  cases hf : fl x.role with
  | none => simp
  | some s => simpa using h.floor_le x hx s hf

/-- A part signed by a compromised key of an honest receipt is a planned forgery injected no
later. -/
private theorem forged_of_receipt (h : ForgeryPremises rho fl u₀ fs pol)
    {k : Fin (Fintype.card V)} (hk : rho.key k ∈ rho.faultyAt 0) {w : V}
    {o : (protoOf F E).Object} {t : Time}
    (hr : (rho.injectRun (fun _ => 0) (forgeInj u₀ fs) pol).receives w o t)
    {d : (protoOf F E).Object} (hd : Obj.Contains o d) {r : (protoOf F E).Role}
    (hs : d.auth = .signed k r) :
    ∃ y ∈ fs, y.time ≤ t ∧ d = y.obj := by
  obtain ⟨t', v, o', ht', ho', hc, -⟩ := rho.injectRun_part_injected (fun _ => 0) _ pol
    (fun _ => le_rfl) (k := k) (fun t => by rw [h.constFaults]; exact hk) hr hd hs
  obtain ⟨-, y, hy, rfl, rfl⟩ := mem_forgeInj.mp ho'
  rcases parts_forged hc with rfl | hn
  · exact ⟨y, hy, ht', rfl⟩
  · rw [hs] at hn; cases hn

/-- **Activity of a key under a forgery plan**: a key is active on `[a, b)` exactly when the plan
forges it at a time of `[a, b)`. -/
theorem activeIn_iff_of_forgeries (h : ForgeryPremises rho fl u₀ fs pol)
    (k : Fin (Fintype.card V)) (a b : Time) :
    ActiveIn (rho.injectRun (fun _ => 0) (forgeInj u₀ fs) pol) fl k a b ↔
      ∃ x ∈ fs, x.key = k ∧ a ≤ x.time ∧ x.time < b := by
  set W := rho.injectRun (fun _ => 0) (forgeInj u₀ fs) pol
  have hkey : W.key = rho.key := Model.Run.withEvents_key _ _
  have hhon : ∀ v t, W.point.HonestAt v t ↔ v ∉ rho.faultyAt 0 := fun v t => by
    simp only [W, Model.Run.withEvents_point]
    change v ∉ rho.faultyAt t ↔ _
    rw [h.constFaults]
  constructor
  · rintro ⟨d, r, t₀, hs, hnot, ⟨⟨v, o, hrec, hvh, hcont⟩, hmin⟩, ha, hb⟩
    by_cases hk : rho.key k ∈ rho.faultyAt 0
    · obtain ⟨y, hy, hyt, rfl⟩ := forged_of_receipt h hk hrec hcont hs
      obtain ⟨hk', hr'⟩ : y.key = k ∧ y.role = r := by
        have := hs; rw [forged_auth] at this; injection this with h1 h2; exact ⟨h1, h2⟩
      have hle : t₀ ≤ y.time := hmin _ ⟨u₀, _, forgery_received h hy,
        (hhon u₀ _).mpr h.u₀_honest, Obj.Contains.refl _⟩
      have heq : t₀ = y.time := le_antisymm hle hyt
      subst heq
      rw [← hr', chargeTime_eq h hy] at ha hb
      exact ⟨y, hy, hk', ha, hb⟩
    · obtain ⟨t', -, hrel⟩ := W.part_released_of_receives h.valid hrec hcont hs
        (by rw [hhon, hkey]; exact hk)
      refine absurd ⟨t', ?_, d, ?_, Obj.Contains.refl d⟩ hnot
      · rw [hhon, hkey]; exact hk
      · exact hrel
  · rintro ⟨x, hx, rfl, ha, hb⟩
    refine ⟨x.obj, x.role, x.time, forged_auth _ _ _ _, ?_, ⟨⟨u₀, _,
      forgery_received h hx, (hhon u₀ _).mpr h.u₀_honest, Obj.Contains.refl _⟩, ?_⟩, ?_, ?_⟩
    · rintro ⟨t, ht, -⟩
      rw [hhon, hkey] at ht
      exact ht (h.key_faulty x hx)
    · rintro t ⟨w, o, hrec, -, hcont⟩
      obtain ⟨y, hy, hyt, hfe⟩ := forged_of_receipt h (h.key_faulty x hx) hrec hcont
        (forged_auth _ _ _ _)
      obtain ⟨h1, h2, h3, h4⟩ := forged_inj hfe
      rw [h.unique x hx y hy h1 h2 h3 h4]
      exact hyt
    · rw [chargeTime_eq h hx]; exact ha
    · rw [chargeTime_eq h hx]; exact hb

/-- **The active set under a forgery plan**: the validators of the keys the plan forges in
`[a, b)`. -/
theorem activeFaulty_of_forgeries (h : ForgeryPremises rho fl u₀ fs pol) (a b : Time) :
    activeFaulty (rho.injectRun (fun _ => 0) (forgeInj u₀ fs) pol) fl a b =
      ((fs.filter fun x => decide (a ≤ x.time ∧ x.time < b)).map
        fun x => rho.key x.key).toFinset := by
  ext v
  simp only [activeFaulty, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset,
    List.mem_map, List.mem_filter, decide_eq_true_eq]
  rw [activeIn_iff_of_forgeries h]
  have hkey : (rho.injectRun (fun _ => 0) (forgeInj u₀ fs) pol).key = rho.key :=
    Model.Run.withEvents_key _ _
  simp only [Model.Run.ownKey, hkey]
  constructor
  · rintro ⟨x, hx, hk, ha, hb⟩
    exact ⟨x, ⟨hx, ha, hb⟩, by rw [hk, Equiv.apply_symm_apply]⟩
  · rintro ⟨x, ⟨hx, ha, hb⟩, rfl⟩
    exact ⟨x, hx, by rw [Equiv.symm_apply_apply], ha, hb⟩

end Consensus.Comparison

end

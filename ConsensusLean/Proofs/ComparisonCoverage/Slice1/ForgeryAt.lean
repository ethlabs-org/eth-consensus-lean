module
public import ConsensusLean.Proofs.ComparisonCoverage.Slice1.Forgery

public section

/-! # Slice 1 coverage: the exact activity count, recipient awake at the planned times

The exact activity count of `Forgery` (`activeFaulty_of_forgeries`) for injections `inj` that
deliver the forged objects of a plan `fs` to `u₀` at their times (`inj t v` holds exactly the forged
objects of the entries timed `t` when `v = u₀`, nothing otherwise), with `u₀` awake at the planned
times only (the late witness point keeps everyone asleep before its start).

* `activeFaulty_of_forgeriesAt`: the active set on `[a, b)` is the set of validators of the keys
  the plan forges in `[a, b)`. -/

namespace Consensus.Comparison

open Consensus.Model

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : ProtocolFamily O}
  {E : Env V}

/-- The premises of the exact activity count, with injections `inj` of the plan `fs` to `u₀`,
batches delayed by `delay ≥ 0`, and `u₀` awake at the planned times. -/
structure ForgeryPremisesAt (rho : Model.Run F E) (fl : (protoOf F E).Role → Option Time)
    (u₀ : V) (fs : List (Forgery F E)) (inj : Time → V → List (protoOf F E).Object)
    (delay : Event V (protoOf F E).Object → Time)
    (pol : List (Event V (protoOf F E).Object) → V → (protoOf F E).Object → Time → Bool) :
    Prop where
  inj_iff : ∀ t v o, o ∈ inj t v ↔ v = u₀ ∧ ∃ x ∈ fs, x.time = t ∧ o = x.obj
  delay_nonneg : ∀ e, 0 ≤ delay e
  valid : (rho.injectRun delay inj pol).ExecutionValid
  constFaults : ∀ t, rho.faultyAt t = rho.faultyAt 0
  key_faulty : ∀ x ∈ fs, rho.key x.key ∈ rho.faultyAt 0
  u₀_honest : u₀ ∉ rho.faultyAt 0
  u₀_awake : ∀ x ∈ fs, E.awake u₀ x.time = true
  time_range : ∀ x ∈ fs, 0 ≤ x.time ∧ x.time ≤ rho.horizon
  floor_le : ∀ x ∈ fs, ∀ s, fl x.role = some s → s ≤ x.time
  unique : ∀ x ∈ fs, ∀ y ∈ fs, x.key = y.key → x.role = y.role → x.msg = y.msg →
    x.tag = y.tag → x.time = y.time

variable {rho : Model.Run F E} {fl : (protoOf F E).Role → Option Time}
  {u₀ : V} {fs : List (Forgery F E)} {inj : Time → V → List (protoOf F E).Object}
  {delay : Event V (protoOf F E).Object → Time}
  {pol : List (Event V (protoOf F E).Object) → V → (protoOf F E).Object → Time → Bool}

/-- A planned forgery is received by `u₀` at its time. -/
private theorem forgery_receivedAt (h : ForgeryPremisesAt rho fl u₀ fs inj delay pol)
    {x : Forgery F E} (hx : x ∈ fs) :
    (rho.injectRun delay inj pol).receives u₀ x.obj x.time := by
  obtain ⟨h0, hh⟩ := h.time_range x hx
  have hmem : Event.deliver u₀ x.obj x.time ∈ rho.injectEvents delay inj pol := by
    apply rho.injectEvents_layer _ _ _ x.time h0 hh
    rw [Model.Run.mem_injectLayer]
    refine Or.inr (Or.inr ⟨u₀, ?_, h.u₀_awake x hx, _,
      Or.inl ((h.inj_iff _ _ _).mpr ⟨rfl, x, hx, rfl, rfl⟩), rfl⟩)
    rw [h.constFaults]
    exact h.u₀_honest
  rw [← Model.Run.withEvents_events rho (rho.injectEvents _ _ _)] at hmem
  exact List.mem_iff_getElem?.mp hmem

/-- The charging time of a planned forgery is its injection time. -/
private theorem chargeTime_eqAt {x : Forgery F E}
    (h : ForgeryPremisesAt rho fl u₀ fs inj delay pol)
    (hx : x ∈ fs) : chargeTime fl x.role x.time = x.time := by
  unfold chargeTime
  cases hf : fl x.role with
  | none => simp
  | some s => simpa using h.floor_le x hx s hf

/-- A part signed by a compromised key of an honest receipt is a planned forgery injected no
later. -/
private theorem forged_of_receiptAt (h : ForgeryPremisesAt rho fl u₀ fs inj delay pol)
    {k : Fin (Fintype.card V)} (hk : rho.key k ∈ rho.faultyAt 0) {w : V}
    {o : (protoOf F E).Object} {t : Time}
    (hr : (rho.injectRun delay inj pol).receives w o t)
    {d : (protoOf F E).Object} (hd : Obj.Contains o d) {r : (protoOf F E).Role}
    (hs : d.auth = .signed k r) :
    ∃ y ∈ fs, y.time ≤ t ∧ d = y.obj := by
  obtain ⟨t', v, o', ht', ho', hc, -⟩ := rho.injectRun_part_injected delay _ pol
    h.delay_nonneg (k := k) (fun t => by rw [h.constFaults]; exact hk) hr hd hs
  obtain ⟨-, y, hy, rfl, rfl⟩ := (h.inj_iff _ _ _).mp ho'
  rcases parts_forged hc with rfl | hn
  · exact ⟨y, hy, ht', rfl⟩
  · rw [hs] at hn; cases hn

/-- **Activity of a key under a forgery plan**: a key is active on `[a, b)` exactly when the plan
forges it at a time of `[a, b)`. -/
theorem activeIn_iff_of_forgeriesAt (h : ForgeryPremisesAt rho fl u₀ fs inj delay pol)
    (k : Fin (Fintype.card V)) (a b : Time) :
    ActiveIn (rho.injectRun delay inj pol) fl k a b ↔
      ∃ x ∈ fs, x.key = k ∧ a ≤ x.time ∧ x.time < b := by
  set W := rho.injectRun delay inj pol
  have hkey : W.key = rho.key := Model.Run.withEvents_key _ _
  have hhon : ∀ v t, W.point.HonestAt v t ↔ v ∉ rho.faultyAt 0 := fun v t => by
    simp only [W, Model.Run.withEvents_point]
    change v ∉ rho.faultyAt t ↔ _
    rw [h.constFaults]
  constructor
  · rintro ⟨d, r, t₀, hs, hnot, ⟨⟨v, o, hrec, hvh, hcont⟩, hmin⟩, ha, hb⟩
    by_cases hk : rho.key k ∈ rho.faultyAt 0
    · obtain ⟨y, hy, hyt, rfl⟩ := forged_of_receiptAt h hk hrec hcont hs
      obtain ⟨hk', hr'⟩ : y.key = k ∧ y.role = r := by
        have := hs; rw [forged_auth] at this; injection this with h1 h2; exact ⟨h1, h2⟩
      have hle : t₀ ≤ y.time := hmin _ ⟨u₀, _, forgery_receivedAt h hy,
        (hhon u₀ _).mpr h.u₀_honest, Obj.Contains.refl _⟩
      have heq : t₀ = y.time := le_antisymm hle hyt
      subst heq
      rw [← hr', chargeTime_eqAt h hy] at ha hb
      exact ⟨y, hy, hk', ha, hb⟩
    · obtain ⟨t', -, hrel⟩ := W.part_released_of_receives h.valid hrec hcont hs
        (by rw [hhon, hkey]; exact hk)
      refine absurd ⟨t', ?_, d, ?_, Obj.Contains.refl d⟩ hnot
      · rw [hhon, hkey]; exact hk
      · exact hrel
  · rintro ⟨x, hx, rfl, ha, hb⟩
    refine ⟨x.obj, x.role, x.time, forged_auth _ _ _ _, ?_, ⟨⟨u₀, _,
      forgery_receivedAt h hx, (hhon u₀ _).mpr h.u₀_honest, Obj.Contains.refl _⟩, ?_⟩, ?_, ?_⟩
    · rintro ⟨t, ht, -⟩
      rw [hhon, hkey] at ht
      exact ht (h.key_faulty x hx)
    · rintro t ⟨w, o, hrec, -, hcont⟩
      obtain ⟨y, hy, hyt, hfe⟩ := forged_of_receiptAt h (h.key_faulty x hx) hrec hcont
        (forged_auth _ _ _ _)
      obtain ⟨h1, h2, h3, h4⟩ := forged_inj hfe
      rw [h.unique x hx y hy h1 h2 h3 h4]
      exact hyt
    · rw [chargeTime_eqAt h hx]; exact ha
    · rw [chargeTime_eqAt h hx]; exact hb

/-- **The active set under a forgery plan**: the validators of the keys the plan forges in
`[a, b)`. -/
theorem activeFaulty_of_forgeriesAt (h : ForgeryPremisesAt rho fl u₀ fs inj delay pol)
    (a b : Time) :
    activeFaulty (rho.injectRun delay inj pol) fl a b =
      ((fs.filter fun x => decide (a ≤ x.time ∧ x.time < b)).map
        fun x => rho.key x.key).toFinset := by
  ext v
  simp only [activeFaulty, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset,
    List.mem_map, List.mem_filter, decide_eq_true_eq]
  rw [activeIn_iff_of_forgeriesAt h]
  have hkey : (rho.injectRun delay inj pol).key = rho.key :=
    Model.Run.withEvents_key _ _
  simp only [Model.Run.ownKey, hkey]
  constructor
  · rintro ⟨x, hx, hk, ha, hb⟩
    exact ⟨x, ⟨hx, ha, hb⟩, by rw [hk, Equiv.apply_symm_apply]⟩
  · rintro ⟨x, ⟨hx, ha, hb⟩, rfl⟩
    exact ⟨x, hx, by rw [Equiv.symm_apply_apply], ha, hb⟩

end Consensus.Comparison

end

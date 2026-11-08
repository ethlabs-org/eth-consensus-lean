module
public import ConsensusLean.Proofs.ComparisonCoverage.Slice1.Hold

public section

/-! # Slice 1 coverage: the held split with a one-step delivery delay

The held split's run of `Hold` with every batch delivered one time step after its release
(`holdRun1`: the scheduler with injections with delay `1` and the filter `holdPol`). With
`ΔAC = 2` the delay is within the synchrony deadline, and at the start `b₀` of the incident the due
batch holds only releases from before `b₀`, which the filter serves (`hold1_serves`): the run at
`b₀` delivers what a run that serves everything delivers.

* `hold1_syncUntil`, `hold1_psync`, `hold1_groupSync`: the filtered run is synchronous for
  deadlines up to `b₀`, partially synchronous from `b₁`, and synchronous inside each group before
  `b₁`.
* `hold1_contentOriginHold`: the filtered run holds content by origin (`ContentOriginHold`). -/

namespace Consensus.Comparison

open Consensus.Model

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : ProtocolFamily O}
  {E : Env V}

variable (rho : Model.Run F E) (G : V → Bool) (b₀ b₁ : Time)
  (inj : Time → V → List (protoOf F E).Object)

/-- The filtered run with a one-step delay: injections `inj`, the filter `holdPol`. -/
noncomputable abbrev holdRun1 : Model.Run F E :=
  rho.injectRun (fun _ => 1) inj (holdPol rho G b₀ b₁)

/-- The premises of the delayed filtered run's lemmas (as `HoldPremises`). -/
structure HoldPremises1 : Prop where
  horizon_nonneg : 0 ≤ rho.horizon
  selValid : rho.SelValid
  ΔAC_gt : 1 < E.ΔAC
  ΔFG_eq : E.ΔFG = E.ΔAC
  eagerTx : (holdRun1 rho G b₀ b₁ inj).EagerTxDelivery
  constFaults : ∀ t, rho.faultyAt t = rho.faultyAt 0
  injFaulty : ∀ t v o, o ∈ inj t v → ∀ d, Obj.Contains o d → ∀ u, rho.signerOf d = some u →
    u ∈ rho.faultyAt t
  injSel : ∀ t v o, o ∈ inj t v → ∀ d, Obj.Contains o d → ∀ k r, d.auth = .signed k r →
    k ∈ rho.sel r

variable {rho G b₀ b₁ inj}

/-- `omega` on integer times. -/
local macro "tomega" : tactic => `(tactic| (try dsimp only [Time] at *) <;> omega)

/-! ### The filter's prefix and the provenance of signed parts -/

variable (rho G b₀ b₁ inj) in
/-- The schedule prefix the filter reads at time `a`. -/
private noncomputable abbrev holdFront1 (a : Time) : List (Event V (protoOf F E).Object) :=
  rho.front (rho.injectStages (fun _ => 1) inj (holdPol rho G b₀ b₁) a.toNat) (a.toNat : Time)

omit [DecidableEq V] in
private theorem signerOf_signed (rho' : Model.Run F E) {d : (protoOf F E).Object}
    {k : Fin (Fintype.card V)} {r : (protoOf F E).Role} (hs : d.auth = .signed k r) :
    rho'.signerOf d = some (rho'.key k) := by
  simp [Model.Run.signerOf, Obj.signer?, hs]

/-- A signed object released at event `i` is released by the validator of its key. -/
private theorem sendsAt_of_signed (rho' : Model.Run F E) {i : Nat} {o : (protoOf F E).Object}
    (ho : o ∈ rho'.releasesAt i) {k : Fin (Fintype.card V)} {r : (protoOf F E).Role}
    (hs : o.auth = .signed k r) : ∃ t, rho'.SendsAt (rho'.key k) i t := by
  have hk := signerOf_signed rho' hs
  cases he : rho'.events[i]? with
  | none => simp [Model.Run.releasesAt, he] at ho
  | some e =>
    cases e with
    | tick v τ =>
      simp only [Model.Run.releasesAt, he] at ho
      rcases rho'.tick_signerOf _ v τ ho with hn | hv
      · rw [hn] at hk; cases hk
      · obtain rfl := Option.some.inj (hk.symm.trans hv)
        exact ⟨τ, Or.inl he⟩
    | deliver v p τ =>
      simp only [Model.Run.releasesAt, he] at ho
      rcases rho'.deliver_signerOf _ v p τ ho with hn | hv
      · rw [hn] at hk; cases hk
      · obtain rfl := Option.some.inj (hk.symm.trans hv)
        exact ⟨τ, Or.inr ⟨p, he⟩⟩
    | restart v τ => simp [Model.Run.releasesAt, he] at ho

private theorem holdRun1_events : (holdRun1 rho G b₀ b₁ inj).events =
    rho.injectStages (fun _ => 1) inj (holdPol rho G b₀ b₁) (rho.horizon.toNat + 1) := by
  rw [Model.Run.withEvents_events, Model.Run.injectEvents_eq]

/-- Up to the horizon, the filter's prefix is a prefix of the filtered run. -/
private theorem holdRun1_eq_front {a : Time} (hah : a ≤ rho.horizon) :
    ∃ tail, holdRun1 rho G b₀ b₁ inj =
      rho.withEvents (holdFront1 rho G b₀ b₁ inj a ++ tail) := by
  have han : a.toNat < rho.horizon.toNat + 1 := by
    have := Int.toNat_le_toNat hah
    omega
  obtain ⟨tail, htail⟩ := rho.injectFront_prefix (fun _ => 1) inj (holdPol rho G b₀ b₁) han
  exact ⟨tail, by rw [← htail, ← Model.Run.injectEvents_eq]⟩

/-- The releases of the filter's prefix are the releases of the filtered run at its indices. -/
private theorem front1_releases_iff {a : Time} (hah : a ≤ rho.horizon) {u : V}
    {d : (protoOf F E).Object} {t : Time} :
    (rho.withEvents (holdFront1 rho G b₀ b₁ inj a)).releases u d t ↔
      ∃ i < (holdFront1 rho G b₀ b₁ inj a).length, (holdRun1 rho G b₀ b₁ inj).SendsAt u i t ∧
        d ∈ (holdRun1 rho G b₀ b₁ inj).releasesAt i := by
  obtain ⟨tail, hR⟩ := holdRun1_eq_front (G := G) (b₀ := b₀) (b₁ := b₁) (inj := inj) hah
  rw [hR]
  generalize holdFront1 rho G b₀ b₁ inj a = xs
  constructor
  · rintro ⟨i, hs, hd⟩
    have hil : i < xs.length := by
      obtain ⟨e, he, -, -⟩ := hs.exists_event
      rw [Model.Run.withEvents_events] at he
      exact (List.getElem?_eq_some_iff.mp he).1
    exact ⟨i, hil, rho.sendsAt_append xs tail hs,
      by rw [rho.releasesAt_append xs tail hil]; exact hd⟩
  · rintro ⟨i, hil, hs, hd⟩
    refine ⟨i, ?_, by rwa [rho.releasesAt_append xs tail hil] at hd⟩
    have hget : (rho.withEvents (xs ++ tail)).events[i]? = (rho.withEvents xs).events[i]? := by
      rw [Model.Run.withEvents_events, Model.Run.withEvents_events,
        List.getElem?_append_left hil]
    rcases hs with hs | ⟨p, hs⟩
    · exact Or.inl (hget ▸ hs)
    · exact Or.inr ⟨p, hget ▸ hs⟩

/-- An event of the filtered run before `a` lies in the filter's prefix at `a`. -/
private theorem idx_lt_holdFront1 {a : Time} (hah : a ≤ rho.horizon) {j : Nat}
    {e : Event V (protoOf F E).Object} (hj : (holdRun1 rho G b₀ b₁ inj).events[j]? = some e)
    (hlt : e.time < a) : j < (holdFront1 rho G b₀ b₁ inj a).length := by
  have hem := List.mem_of_getElem? hj
  rw [holdRun1_events] at hem
  have hmem : e ∈ holdFront1 rho G b₀ b₁ inj a := by
    simp only [holdFront1, Model.Run.front_eq]
    exact List.mem_append_left _
      (List.mem_append_left _ (rho.mem_injectStages_of_time_lt _ inj _ hem hlt))
  obtain ⟨j', hj'⟩ := List.mem_iff_getElem?.mp hmem
  have hj'l := (List.getElem?_eq_some_iff.mp hj').1
  have hn : (holdRun1 rho G b₀ b₁ inj).events.Nodup := by
    rw [holdRun1_events]
    exact rho.injectStages_nodup _ inj _ _
  obtain ⟨tail, hR⟩ := holdRun1_eq_front (G := G) (b₀ := b₀) (b₁ := b₁) (inj := inj) hah
  rw [hR, Model.Run.withEvents_events] at hj hn
  have : j' = j := (hn.getElem?_inj (by rw [List.length_append]; omega)).mp
    ((List.getElem?_append_left hj'l).trans (hj'.trans hj.symm))
  omega

private theorem release_of_front1 {a : Time} (hah : a ≤ rho.horizon) {u : V}
    {d : (protoOf F E).Object} {t : Time}
    (hr : (rho.withEvents (holdFront1 rho G b₀ b₁ inj a)).releases u d t) :
    (holdRun1 rho G b₀ b₁ inj).releases u d t := by
  obtain ⟨i, -, hs, hd⟩ := (front1_releases_iff hah).mp hr
  exact ⟨i, hs, hd⟩

private theorem front1_of_release {a : Time} (hah : a ≤ rho.horizon) {u : V}
    {d : (protoOf F E).Object} {t : Time} (hr : (holdRun1 rho G b₀ b₁ inj).releases u d t)
    (hlt : t < a) : (rho.withEvents (holdFront1 rho G b₀ b₁ inj a)).releases u d t := by
  obtain ⟨i, hs, hd⟩ := hr
  obtain ⟨e, he, -, het⟩ := hs.exists_event
  exact (front1_releases_iff hah).mpr ⟨i, idx_lt_holdFront1 hah he (het ▸ hlt), hs, hd⟩

/-- Every delivery of the filtered run is an injection, or a release of the filter's prefix that
the filter serves. -/
private theorem hold1_source {i : Nat} {w : V} {o : (protoOf F E).Object} {τ : Time}
    (hi : (holdRun1 rho G b₀ b₁ inj).events[i]? = some (.deliver w o τ)) :
    o ∈ inj τ w ∨ (holdPol rho G b₀ b₁ (holdFront1 rho G b₀ b₁ inj τ) w o τ = true ∧
      ∃ j < (holdFront1 rho G b₀ b₁ inj τ).length,
        o ∈ (holdRun1 rho G b₀ b₁ inj).releasesAt j) := by
  have hm := List.mem_of_getElem? hi
  rw [holdRun1_events] at hm
  obtain ⟨k, hk, he⟩ := (rho.mem_injectStages _ inj _ _ _).mp hm
  have htk : τ = (k : Time) := rho.injectLayer_time _ inj _ _ _ he
  subst htk
  rcases (rho.mem_injectLayer _ inj _ _ _ _).mp he with
    ⟨v, _, _, _, h⟩ | ⟨v, _, _, h⟩ | ⟨v, _, _, p, hp, h⟩
  · cases h
  · cases h
  · cases h
    simp only [holdFront1, Int.toNat_natCast]
    rcases hp with hp | ⟨hpool, hpol⟩
    · exact Or.inl hp
    · refine Or.inr ⟨hpol, ?_⟩
      obtain ⟨tail, htail⟩ := rho.injectFront_prefix _ inj _ hk
      obtain ⟨j, e, hje, -, ho⟩ := (rho.mem_duePool _ _ _ _).mp hpool
      have hjl := (List.getElem?_eq_some_iff.mp hje).1
      refine ⟨j, hjl, ?_⟩
      have hR : holdRun1 rho G b₀ b₁ inj = rho.withEvents
          (rho.front (rho.injectStages (fun _ => 1) inj (holdPol rho G b₀ b₁) k) (k : Time) ++
            tail) := by
        rw [← htail, ← Model.Run.injectEvents_eq]
      rw [hR, rho.releasesAt_append _ _ hjl]
      exact ho

/-- The delayed filtered run is a valid execution. -/
theorem hold1_valid (h : HoldPremises1 rho G b₀ b₁ inj) :
    (holdRun1 rho G b₀ b₁ inj).ExecutionValid :=
  rho.injectEvents_valid _ inj _ h.horizon_nonneg h.selValid (fun _ => zero_le_one) h.injFaulty
    h.injSel

/-- A validator with an event is never compromised (faults do not grow). -/
private theorem honest_of_sendsAt (h : HoldPremises1 rho G b₀ b₁ inj) {u : V} {i : Nat}
    {t : Time} (hs : (holdRun1 rho G b₀ b₁ inj).SendsAt u i t) (t' : Time) :
    u ∉ rho.faultyAt t' := by
  obtain ⟨e, he, hn, ht⟩ := hs.exists_event
  have := (hold1_valid h).honest_only e (List.mem_of_getElem? he)
  rw [Model.Run.withEvents_faultyAt, hn, ht, h.constFaults] at this
  rw [h.constFaults]
  exact this

private theorem sendsAt_time_le (h : HoldPremises1 rho G b₀ b₁ inj) {u v : V} {i j : Nat}
    {t t' : Time} (hij : i ≤ j) (hi : (holdRun1 rho G b₀ b₁ inj).SendsAt u i t')
    (hj : (holdRun1 rho G b₀ b₁ inj).SendsAt v j t) : t' ≤ t := by
  obtain ⟨ei, hei, -, hti⟩ := hi.exists_event
  obtain ⟨ej, hej, -, htj⟩ := hj.exists_event
  rcases hij.lt_or_eq with hlt | rfl
  · rw [← hti, ← htj]
    exact (holdRun1 rho G b₀ b₁ inj).time_le_of_lt (hold1_valid h).sorted hlt hej hei
  · rw [hei] at hej
    cases hej
    rw [← hti, ← htj]

/-- A part signed by a never-compromised key was released at top level by its validator, at an
event no later than the event releasing the object. -/
private theorem part_idx (h : HoldPremises1 rho G b₀ b₁ inj) {i : Nat}
    {o : (protoOf F E).Object} (ho : o ∈ (holdRun1 rho G b₀ b₁ inj).releasesAt i)
    {d : (protoOf F E).Object} (hd : Obj.Contains o d) {k : Fin (Fintype.card V)}
    {r : (protoOf F E).Role} (hs : d.auth = .signed k r) (hk : ∀ t, rho.key k ∉ rho.faultyAt t) :
    ∃ j ≤ i, ∃ t', (holdRun1 rho G b₀ b₁ inj).SendsAt (rho.key k) j t' ∧
      d ∈ (holdRun1 rho G b₀ b₁ inj).releasesAt j := by
  have hcl := (holdRun1 rho G b₀ b₁ inj).closed_of_sources
    (fun i d => ∀ (k : Fin (Fintype.card V)) (r : (protoOf F E).Role), d.auth = .signed k r →
      (∀ t, rho.key k ∉ rho.faultyAt t) → ∃ j < i, ∃ t',
        (holdRun1 rho G b₀ b₁ inj).SendsAt (rho.key k) j t' ∧
          d ∈ (holdRun1 rho G b₀ b₁ inj).releasesAt j)
    (fun _ => True)
    (fun hle h k r hs hk => let ⟨j, hj, t', h'⟩ := h k r hs hk; ⟨j, by omega, t', h'⟩)
    (fun _ _ _ _ _ => trivial)
    (by
      rintro i - o ho k r hs -
      obtain ⟨t, ht⟩ := sendsAt_of_signed _ ho hs
      rw [Model.Run.withEvents_key] at ht
      exact ⟨i, Nat.lt_succ_self i, t, ht, ho⟩)
    (by
      rintro i w p τ - hi
      rcases rho.injectEvents_source _ inj _ hi with hp | ⟨j, hj, -, -, -, hjr⟩
      · exact Or.inl fun d hd k r hs hk =>
          absurd (h.injFaulty τ w p hp d hd _ (signerOf_signed rho hs)) (hk τ)
      · exact Or.inr ⟨j, hj, trivial, hjr⟩)
  obtain ⟨j, hj, t', h'⟩ := hcl i trivial o ho d hd k r hs hk
  exact ⟨j, by omega, t', h'⟩

/-! ### Delivery -/

/-- A release at `t` is held at every `a > t` up to the horizon by every awake honest node that the
filter serves it to at `a`. -/
private theorem hold1_held (h : HoldPremises1 rho G b₀ b₁ inj) {v : V}
    {m : (protoOf F E).Object} {t : Time} (hr : (holdRun1 rho G b₀ b₁ inj).releases v m t)
    {w : V} {a : Time} (hta : t < a) (hah : a ≤ rho.horizon) (hw : w ∉ rho.faultyAt a)
    (haw : E.awake w a = true)
    (hpol : holdPol rho G b₀ b₁ (holdFront1 rho G b₀ b₁ inj a) w m a = true) :
    (holdRun1 rho G b₀ b₁ inj).log.Held rho.point w m a := by
  obtain ⟨j, hs, hm⟩ := hr
  obtain ⟨e, he, -, het⟩ := hs.exists_event
  apply CommLog.held_of_recv
  exact rho.injectEvents_receives _ inj _ h.horizon_nonneg he hm
    (by simp only [het]; exact Int.add_one_le_of_lt hta) (Or.inl (het ▸ hta)) hah hw haw hpol

/-- **The filter serves a due release**: a release at `t` is served at every later `a` up to the
horizon from `b₁` on, and at every later `a` when its deadline `t + ΔAC − 1` is at most `b₀`. -/
theorem hold1_serves (h : HoldPremises1 rho G b₀ b₁ inj) {v : V}
    {m : (protoOf F E).Object} {t : Time} (hr : (holdRun1 rho G b₀ b₁ inj).releases v m t)
    {w : V} {a : Time} (hta : t < a) (hah : a ≤ rho.horizon)
    (hb : b₁ ≤ a ∨ t + E.ΔAC - 1 ≤ b₀) :
    holdPol rho G b₀ b₁
      (rho.front (rho.injectStages (fun _ => 1) inj (holdPol rho G b₀ b₁) a.toNat)
        (a.toNat : Time)) w m a = true := by
  change holdPol rho G b₀ b₁ (holdFront1 rho G b₀ b₁ inj a) w m a = true
  rw [holdPol_eq_true]
  rintro ⟨ha, d, hd, k, r, hs, -, hheld⟩
  obtain ⟨-, ⟨t₀, h0⟩, hall⟩ := heldIn_iff.mp hheld
  rcases hb with hb | hb
  · exact absurd ha (not_lt.mpr hb)
  obtain ⟨i₀, -, hs₀, -⟩ := (front1_releases_iff hah).mp h0
  obtain ⟨j, hsj, hmj⟩ := hr
  obtain ⟨j', hj', t', hs', hd'⟩ := part_idx h hmj hd hs (honest_of_sendsAt h hs₀)
  have ht' := sendsAt_time_le h hj' hs' hsj
  have := hall t' (front1_of_release hah ⟨j', hs', hd'⟩ (lt_of_le_of_lt ht' hta))
  tomega

/-- **Before `b₁`, what a node of group `g` releases carries no part signed by the other group
that is held**. -/
private theorem group1_closed (h : HoldPremises1 rho G b₀ b₁ inj) (g : Bool) :
    ∀ i, (∃ e, (holdRun1 rho G b₀ b₁ inj).events[i]? = some e ∧ G e.node = g ∧ e.time < b₁) →
      ∀ o ∈ (holdRun1 rho G b₀ b₁ inj).releasesAt i, ∀ d, Obj.Contains o d →
        ∀ (k : Fin (Fintype.card V)) (r : (protoOf F E).Role), d.auth = .signed k r →
          G (rho.key k) ≠ g → (∀ t, rho.key k ∉ rho.faultyAt t) → ¬ (protoOf F E).isFGAtt d →
            ∃ t₀, (holdRun1 rho G b₀ b₁ inj).releases (rho.key k) d t₀ ∧
              t₀ + E.ΔAC - 1 ≤ b₀ := by
  have hv := hold1_valid h
  exact (holdRun1 rho G b₀ b₁ inj).closed_of_sources
    (fun _ d => ∀ (k : Fin (Fintype.card V)) (r : (protoOf F E).Role), d.auth = .signed k r →
      G (rho.key k) ≠ g → (∀ t, rho.key k ∉ rho.faultyAt t) → ¬ (protoOf F E).isFGAtt d →
        ∃ t₀, (holdRun1 rho G b₀ b₁ inj).releases (rho.key k) d t₀ ∧ t₀ + E.ΔAC - 1 ≤ b₀)
    (fun i => ∃ e, (holdRun1 rho G b₀ b₁ inj).events[i]? = some e ∧ G e.node = g ∧
      e.time < b₁)
    (fun _ h => h)
    (by
      rintro i j ei ej ⟨e, he, hg, ht⟩ hji hi hj hn
      rw [he] at hi
      cases hi
      exact ⟨ej, hj, hn ▸ hg,
        lt_of_le_of_lt ((holdRun1 rho G b₀ b₁ inj).time_le_of_lt hv.sorted hji he hj) ht⟩)
    (by
      rintro i ⟨e, he, hg, -⟩ o ho k r hs hGk
      obtain ⟨t, ht⟩ := sendsAt_of_signed _ ho hs
      obtain ⟨e', he', hn, -⟩ := ht.exists_event
      rw [he] at he'
      cases he'
      rw [Model.Run.withEvents_key] at hn
      exact absurd (hn ▸ hg) hGk)
    (by
      rintro i w p τ ⟨e, he, hg, ht⟩ hi
      rw [hi] at he
      cases he
      simp only [Event.node, Event.time] at hg ht
      left
      intro d hd k r hs hGk hk hfg
      rcases hold1_source hi with hp | ⟨hpol, j, hj, hjr⟩
      · exact absurd (h.injFaulty τ w p hp d hd _ (signerOf_signed rho hs)) (hk τ)
      · have hah : τ ≤ rho.horizon := by
          have := (hv.in_horizon _ (List.mem_of_getElem? hi)).2
          rwa [Model.Run.withEvents_horizon] at this
        obtain ⟨j', hj', t', hs', hd'⟩ := part_idx h hjr hd hs hk
        have hfr := (front1_releases_iff hah).mpr ⟨j', by tomega, hs', hd'⟩
        rw [holdPol_eq_true] at hpol
        by_contra hno
        push Not at hno
        exact hpol ⟨ht, d, hd, k, r, hs, fun hc => hGk (hc.trans hg),
          heldIn_iff.mpr ⟨hfg, ⟨t', hfr⟩, fun t₀ h0 => hno t₀ (release_of_front1 hah h0)⟩⟩)

/-- In-group delivery before `b₁` with deadline `a + ΔAC − 1`. -/
private theorem hold1_group_held (h : HoldPremises1 rho G b₀ b₁ inj) {v : V}
    {m : (protoOf F E).Object} {t : Time} (hr : (holdRun1 rho G b₀ b₁ inj).releases v m t)
    (ht : t < b₁) {w : V} (hG : G w = G v) {a : Time} (hta : t ≤ a)
    (hah : a + E.ΔAC - 1 ≤ rho.horizon) (hw : w ∉ rho.faultyAt (a + E.ΔAC - 1))
    (haw : E.awake w (a + E.ΔAC - 1) = true) :
    (holdRun1 rho G b₀ b₁ inj).log.Held rho.point w m (a + E.ΔAC - 1) := by
  have hΔ := h.ΔAC_gt
  refine hold1_held h hr (by tomega) hah hw haw ?_
  rw [holdPol_eq_true]
  rintro ⟨-, d, hd, k, r, hs, hGk, hheld⟩
  obtain ⟨hfg, ⟨t₀, h0⟩, hall⟩ := heldIn_iff.mp hheld
  obtain ⟨i₀, -, hs₀, -⟩ := (front1_releases_iff hah).mp h0
  have hk := honest_of_sendsAt h hs₀
  obtain ⟨j, hsj, hmj⟩ := hr
  obtain ⟨j', hj', t', hs', hd'⟩ := part_idx h hmj hd hs hk
  have ht' := sendsAt_time_le h hj' hs' hsj
  have h1 := hall t' (front1_of_release hah ⟨j', hs', hd'⟩ (by tomega))
  obtain ⟨e, he, hn, het⟩ := hsj.exists_event
  obtain ⟨t₁, hr₁, ht₁⟩ := group1_closed h (G v) j ⟨e, he, hn ▸ rfl, het ▸ ht⟩ m hmj d hd k r
    hs (hG ▸ hGk) hk hfg
  by_cases hlt : t₁ < a + E.ΔAC - 1
  · have := hall t₁ (front1_of_release hah hr₁ hlt)
    tomega
  · tomega

/-- The delayed filtered run is synchronous for deadlines up to `b₀`. -/
theorem hold1_syncUntil (h : HoldPremises1 rho G b₀ b₁ inj) :
    (holdRun1 rho G b₀ b₁ inj).log.SyncUntil (holdRun1 rho G b₀ b₁ inj).point b₀ := by
  rw [show (holdRun1 rho G b₀ b₁ inj).point = rho.point from Model.Run.withEvents_point _ _]
  have hΔ := h.ΔAC_gt
  have key : ∀ v m t, (holdRun1 rho G b₀ b₁ inj).releases v m t → ∀ w a, t ≤ a →
      a + E.ΔAC - 1 ≤ b₀ → a + E.ΔAC - 1 ≤ rho.horizon → w ∉ rho.faultyAt (a + E.ΔAC - 1) →
        E.awake w (a + E.ΔAC - 1) = true →
          (holdRun1 rho G b₀ b₁ inj).log.Held rho.point w m (a + E.ΔAC - 1) :=
    fun v m t hr w a hta hdc hdh hw haw => hold1_held h hr (by tomega) hdh hw haw
      (hold1_serves h hr (by tomega) hdh (Or.inr (by tomega)))
  have htx' := Model.Run.eagerTxDelivery_iff.mp h.eagerTx
  rw [Model.Run.withEvents_faultyAt, show (holdRun1 rho G b₀ b₁ inj).submit = rho.submit from
    congrArg EnvPoint.submit (Model.Run.withEvents_point _ _)] at htx'
  constructor
  · intro v m t hs _ _ w a hta hdc hdh hw haw
    exact key v m t hs w a hta hdc hdh hw (haw _ (by tomega) le_rfl)
  · intro v m t hs _ _ w a hta hdc hdh hw haw
    have e : rho.point.env.ΔFG = E.ΔAC := h.ΔFG_eq
    simp only [e] at hdc hdh hw haw ⊢
    exact key v m t hs w a hta hdc hdh hw (haw _ (by tomega) le_rfl)
  · intro u x τ hτ hu hua hx w a hτa _ _ hw haw
    have hle : τ ≤ a + E.ΔAC - 1 := by tomega
    exact ⟨_, hτ.trans hle, le_rfl, htx' u x τ hτ hu hua hx w _ hle hw
      (haw _ (by tomega) le_rfl)⟩

/-- The delayed filtered run is partially synchronous with GST `b₁`. -/
theorem hold1_psync (h : HoldPremises1 rho G b₀ b₁ inj) :
    (holdRun1 rho G b₀ b₁ inj).log.PSync (holdRun1 rho G b₀ b₁ inj).point b₁ := by
  rw [show (holdRun1 rho G b₀ b₁ inj).point = rho.point from Model.Run.withEvents_point _ _]
  have hΔ := h.ΔAC_gt
  have key : ∀ v m t, (holdRun1 rho G b₀ b₁ inj).releases v m t → ∀ w a, t ≤ a →
      max a b₁ + E.ΔAC - 1 ≤ rho.horizon → w ∉ rho.faultyAt (max a b₁ + E.ΔAC - 1) →
        E.awake w (max a b₁ + E.ΔAC - 1) = true →
          (holdRun1 rho G b₀ b₁ inj).log.Held rho.point w m (max a b₁ + E.ΔAC - 1) := by
    intro v m t hr w a hta hdh hw haw
    have h1 := le_max_left a b₁
    have h2 := le_max_right a b₁
    exact hold1_held h hr (by tomega) hdh hw haw
      (hold1_serves h hr (by tomega) hdh (Or.inl (by tomega)))
  have htx' := Model.Run.eagerTxDelivery_iff.mp h.eagerTx
  rw [Model.Run.withEvents_faultyAt, show (holdRun1 rho G b₀ b₁ inj).submit = rho.submit from
    congrArg EnvPoint.submit (Model.Run.withEvents_point _ _)] at htx'
  constructor
  · intro v m t hs _ _ w a hta _ hdh hw haw
    exact key v m t hs w a hta hdh hw
      (haw _ (by have := le_max_left a b₁; tomega) le_rfl)
  · intro v m t hs _ _ w a hta _ hdh hw haw
    have e : rho.point.env.ΔFG = E.ΔAC := h.ΔFG_eq
    simp only [e] at hdh hw haw ⊢
    exact key v m t hs w a hta hdh hw
      (haw _ (by have := le_max_left a b₁; tomega) le_rfl)
  · intro u x τ hτ hu hua hx w a hτa _ _ hw haw
    have hle : τ ≤ max a b₁ + E.ΔAC - 1 := by have := le_max_left a b₁; tomega
    exact ⟨_, hτ.trans hle, le_rfl, htx' u x τ hτ hu hua hx w _ hle hw
      (haw _ (by have := le_max_left a b₁; tomega) le_rfl)⟩

/-- The delayed filtered run is synchronous inside each group of `G` before `b₁`. -/
theorem hold1_groupSync (h : HoldPremises1 rho G b₀ b₁ inj) :
    GroupSync (holdRun1 rho G b₀ b₁ inj).point (holdRun1 rho G b₀ b₁ inj).log G b₁ := by
  rw [show (holdRun1 rho G b₀ b₁ inj).point = rho.point from Model.Run.withEvents_point _ _]
  have hΔ := h.ΔAC_gt
  have htx' := Model.Run.eagerTxDelivery_iff.mp h.eagerTx
  rw [Model.Run.withEvents_faultyAt, show (holdRun1 rho G b₀ b₁ inj).submit = rho.submit from
    congrArg EnvPoint.submit (Model.Run.withEvents_point _ _)] at htx'
  constructor
  · intro v m t hs _ _ ht w hG a hta hdh hw haw
    exact hold1_group_held h hs ht hG hta hdh hw (haw _ (by tomega) le_rfl)
  · intro v m t hs _ _ ht w hG a hta hdh hw haw
    have e : rho.point.env.ΔFG = E.ΔAC := h.ΔFG_eq
    simp only [e] at hdh hw haw ⊢
    exact hold1_group_held h hs ht hG hta hdh hw (haw _ (by tomega) le_rfl)
  · intro u x τ hτ _ hu hua hx w _ a hτa _ hw haw
    have hle : τ ≤ a + E.ΔAC - 1 := by tomega
    exact ⟨_, hτ.trans hle, le_rfl, htx' u x τ hτ hu hua hx w _ hle hw
      (haw _ (by tomega) le_rfl)⟩

/-- **The delayed filtered run holds content by origin**. -/
theorem hold1_contentOriginHold (h : HoldPremises1 rho G b₀ b₁ inj) :
    ContentOriginHold (holdRun1 rho G b₀ b₁ inj) G b₀ b₁ := by
  rintro w o t hr - ht d hd k r hs hG ⟨hfg, t₀, ⟨⟨hk0, -⟩, hfirst⟩, -, hb⟩
  simp only [Model.Run.withEvents_key] at hG hk0
  rw [Model.Run.withEvents_point] at hk0
  have hk : ∀ t, rho.key k ∉ rho.faultyAt t := fun t => by
    rw [h.constFaults]
    rw [← h.constFaults t₀]
    exact hk0
  obtain ⟨i, hi⟩ := hr
  rcases hold1_source hi with hp | ⟨hpol, j, hj, hjr⟩
  · exact hk t (h.injFaulty t w o hp d hd _ (signerOf_signed rho hs))
  · have hah : t ≤ rho.horizon := by
      have := ((hold1_valid h).in_horizon _ (List.mem_of_getElem? hi)).2
      rwa [Model.Run.withEvents_horizon] at this
    obtain ⟨j', hj', t', hs', hd'⟩ := part_idx h hjr hd hs hk
    have hfr := (front1_releases_iff hah).mpr ⟨j', by tomega, hs', hd'⟩
    rw [holdPol_eq_true] at hpol
    refine hpol ⟨ht, d, hd, k, r, hs, hG, heldIn_iff.mpr ⟨hfg, ⟨t', hfr⟩, fun t₁ h1 => ?_⟩⟩
    have hh : (holdRun1 rho G b₀ b₁ inj).point.HonestAt
        ((holdRun1 rho G b₀ b₁ inj).key k) t₁ := by
      rw [Model.Run.withEvents_point, Model.Run.withEvents_key]
      exact hk t₁
    have hr₁ : (holdRun1 rho G b₀ b₁ inj).releases ((holdRun1 rho G b₀ b₁ inj).key k) d t₁ := by
      rw [Model.Run.withEvents_key]
      exact release_of_front1 hah h1
    have h2 := hfirst t₁ ⟨hh, d, hr₁, Obj.Contains.refl d⟩
    tomega

end Consensus.Comparison

end

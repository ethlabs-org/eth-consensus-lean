module
public import ConsensusLean.Lemmas.Model.Canonical.Construction

public section

/-! # The canonical scheduler under a delivery policy

The canonical scheduler (`Run.stages`) delivers, at every integer time from its GST on, every
released object to every awake honest node. Here the delivery layer of time `t` keeps only the
receipts that a **delivery policy** `pol` allows: object `o` is delivered to `v` at `t` exactly when
`pol es v o t`, where `es` is the schedule so far (wakes and ticks of `t` included), so the policy
can read who released `o` and when. Wakes and ticks are those of the canonical scheduler.

* `policyStages pol n` and `policyEvents pol`: the schedule of times `0, …, n − 1`, and through the
  inclusive horizon; each layer is a sublist of the canonical one on the same prefix, so it is
  sorted and duplicate-free, and only removes deliveries.
* `policy_valid`: the schedule is a valid execution; its network is causal (`policy_causal`).
* `policy_receives`: a release at `t` by a node honest at `t` is received at every `a` with
  `t < a ≤ horizon` by every node honest and awake at `a` that the policy serves it to at `a`.
* `policy_receives_inv`: every receipt is one the policy allows, of an object released by then.
* `policyStages_eq_stages`: a policy that serves everything before `s` gives the synchronous
  canonical schedule (`stages 0`) on the times before `s`. -/

namespace Consensus.Model

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : ProtocolFamily O}
    {E : Env V}

namespace Run
variable (rho : Run F E)
variable (pol : List (Event V (protoOf F E).Object) → V → (protoOf F E).Object → Time → Bool)

/-- The deliveries of time `t` after the prefix `es` under the policy: to every awake honest node,
the released objects the policy serves it. -/
noncomputable def policyDeliveries (es : List (Event V (protoOf F E).Object)) (t : Time) :
    List (Event V (protoOf F E).Object) := by
  classical
  exact (((Finset.univ \ rho.faultyAt t).filter (fun v => E.awake v t = true)).toList).flatMap
    (fun v => ((rho.pool es).filter (fun o => pol es v o t)).map (fun o => .deliver v o t))

/-- The layer of time `t`: wake restarts, ticks, then the policy's deliveries. -/
noncomputable def policyLayer (es : List (Event V (protoOf F E).Object)) (t : Time) :=
  rho.wakeEvents t ++ rho.tickEvents t ++ rho.policyDeliveries pol (rho.front es t) t

/-- The first `n` integer times, starting at zero. -/
noncomputable def policyStages : Nat → List (Event V (protoOf F E).Object)
  | 0 => []
  | n + 1 => policyStages n ++ rho.policyLayer pol (policyStages n) (n : Time)

/-- The run through the inclusive horizon under the policy. -/
noncomputable def policyEvents := rho.policyStages pol (rho.horizon.toNat + 1)

theorem policyLayer_eq (es : List (Event V (protoOf F E).Object)) (t : Time) :
    rho.policyLayer pol es t =
      rho.wakeEvents t ++ rho.tickEvents t ++ rho.policyDeliveries pol (rho.front es t) t := by
  rfl

@[simp] theorem policyStages_zero : rho.policyStages pol 0 = [] := by rfl

theorem policyStages_succ (n : Nat) :
    rho.policyStages pol (n + 1) =
      rho.policyStages pol n ++ rho.policyLayer pol (rho.policyStages pol n) (n : Time) := by rfl

theorem policyEvents_eq : rho.policyEvents pol = rho.policyStages pol (rho.horizon.toNat + 1) := by
  rfl

@[simp] theorem mem_policyDeliveries (es : List (Event V (protoOf F E).Object)) (t : Time)
    (e : Event V (protoOf F E).Object) :
    e ∈ rho.policyDeliveries pol es t ↔
      ∃ v, v ∉ rho.faultyAt t ∧ E.awake v t = true ∧
        ∃ o ∈ rho.pool es, pol es v o t = true ∧ e = .deliver v o t := by
  classical
  delta policyDeliveries
  simp only [List.mem_flatMap, List.mem_map, List.mem_filter, Finset.mem_toList,
    Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨v, ⟨hv, hw⟩, o, ⟨ho, hp⟩, rfl⟩
    exact ⟨v, hv, hw, o, ho, hp, rfl⟩
  · rintro ⟨v, hv, hw, o, ho, hp, rfl⟩
    exact ⟨v, ⟨hv, hw⟩, o, ⟨ho, hp⟩, rfl⟩

/-- At a nonnegative time the policy's deliveries are a sublist of the canonical ones. -/
theorem policyDeliveries_sublist (es : List (Event V (protoOf F E).Object)) {t : Time}
    (ht : 0 ≤ t) : List.Sublist (rho.policyDeliveries pol es t) (rho.deliveryEvents 0 es t) := by
  classical
  simp only [deliveryEvents_eq, ht, ↓reduceIte]
  delta policyDeliveries
  generalize (((Finset.univ \ rho.faultyAt t).filter (fun v => E.awake v t = true)).toList) = vs
  induction vs with
  | nil => exact List.Sublist.refl _
  | cons v vs ih =>
    simp only [List.flatMap_cons]
    exact List.Sublist.append (List.Sublist.map _ List.filter_sublist) ih

theorem policyLayer_sublist (es : List (Event V (protoOf F E).Object)) {t : Time} (ht : 0 ≤ t) :
    List.Sublist (rho.policyLayer pol es t) (rho.layer 0 es t) := by
  rw [policyLayer_eq, layer_eq]
  exact List.Sublist.append (List.Sublist.refl _) (rho.policyDeliveries_sublist pol _ ht)

theorem policyLayer_time (es : List (Event V (protoOf F E).Object)) (t : Time)
    {e : Event V (protoOf F E).Object} (he : e ∈ rho.policyLayer pol es t) : e.time = t := by
  simp only [policyLayer_eq, List.mem_append, mem_wakeEvents, mem_tickEvents,
    mem_policyDeliveries] at he
  rcases he with (⟨v, _, _, _, rfl⟩ | ⟨v, _, _, rfl⟩) | ⟨v, _, _, o, _, _, rfl⟩ <;> rfl

theorem policyLayer_honest (es : List (Event V (protoOf F E).Object)) (t : Time)
    {e : Event V (protoOf F E).Object} (he : e ∈ rho.policyLayer pol es t) :
    e.node ∉ rho.faultyAt e.time := by
  simp only [policyLayer_eq, List.mem_append, mem_wakeEvents, mem_tickEvents,
    mem_policyDeliveries] at he
  rcases he with (⟨v, hv, _, _, rfl⟩ | ⟨v, hv, _, rfl⟩) | ⟨v, hv, _, o, _, _, rfl⟩ <;> exact hv

theorem policyStages_time (n : Nat) {e : Event V (protoOf F E).Object}
    (he : e ∈ rho.policyStages pol n) : 0 ≤ e.time ∧ e.time < (n : Time) := by
  induction n with
  | zero => simp at he
  | succ n ih =>
    rcases List.mem_append.mp he with he | he
    · have := ih he
      exact ⟨this.1, lt_trans this.2 (by exact_mod_cast Nat.lt_succ_self n)⟩
    · rw [rho.policyLayer_time pol _ _ he]
      exact ⟨Int.natCast_nonneg n, by exact_mod_cast Nat.lt_succ_self n⟩

theorem policyStages_sorted (n : Nat) : (rho.policyStages pol n).Pairwise Event.keyLe := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [policyStages_succ, List.pairwise_append]
    refine ⟨ih, (rho.layer_sorted 0 _ _).sublist
      (rho.policyLayer_sublist pol _ (Int.natCast_nonneg n)), ?_⟩
    intro e he f hf
    exact Or.inl (by rw [rho.policyLayer_time pol _ _ hf]; exact (rho.policyStages_time pol n he).2)

theorem policyStages_nodup (n : Nat) : (rho.policyStages pol n).Nodup := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [policyStages_succ, List.nodup_append]
    refine ⟨ih, (rho.layer_nodup 0 _ _).sublist
      (rho.policyLayer_sublist pol _ (Int.natCast_nonneg n)), ?_⟩
    intro e he f hf hef
    subst f
    have := (rho.policyStages_time pol n he).2
    rw [rho.policyLayer_time pol _ _ hf] at this
    exact lt_irrefl _ this

theorem mem_policyStages (n : Nat) (e : Event V (protoOf F E).Object) :
    e ∈ rho.policyStages pol n ↔
      ∃ k < n, e ∈ rho.policyLayer pol (rho.policyStages pol k) (k : Time) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [policyStages_succ, List.mem_append, ih]
    constructor
    · rintro (⟨k, hk, he⟩ | he)
      · exact ⟨k, by omega, he⟩
      · exact ⟨n, by omega, he⟩
    · rintro ⟨k, hk, he⟩
      by_cases hkn : k < n
      · exact Or.inl ⟨k, hkn, he⟩
      · have : k = n := by omega
        subst k
        exact Or.inr he

theorem policyStages_prefix {m n : Nat} (hmn : m ≤ n) :
    ∃ tail, rho.policyStages pol n = rho.policyStages pol m ++ tail := by
  induction n with
  | zero =>
    have : m = 0 := by omega
    subst m
    exact ⟨[], (List.append_nil _).symm⟩
  | succ n ih =>
    by_cases hm : m ≤ n
    · obtain ⟨tail, ht⟩ := ih hm
      refine ⟨tail ++ rho.policyLayer pol (rho.policyStages pol n) (n : Time), ?_⟩
      rw [policyStages_succ, ht, List.append_assoc]
    · have : m = n + 1 := by omega
      subst m
      exact ⟨[], (List.append_nil _).symm⟩

theorem policy_front_prefix {k n : Nat} (hk : k < n) :
    ∃ tail, rho.policyStages pol n = rho.front (rho.policyStages pol k) (k : Time) ++ tail := by
  obtain ⟨tail, ht⟩ := rho.policyStages_prefix pol (show k + 1 ≤ n by omega)
  refine ⟨rho.policyDeliveries pol (rho.front (rho.policyStages pol k) (k : Time)) (k : Time) ++
    tail, ?_⟩
  rw [ht, policyStages_succ, policyLayer_eq, front_eq]
  simp only [List.append_assoc]

theorem policy_in_horizon (h0 : 0 ≤ rho.horizon) {e : Event V (protoOf F E).Object}
    (he : e ∈ rho.policyEvents pol) : 0 ≤ e.time ∧ e.time ≤ rho.horizon := by
  have h := rho.policyStages_time pol _ he
  have hn : (rho.horizon.toNat : Int) = rho.horizon := Int.toNat_of_nonneg h0
  change 0 ≤ (e.time : Int) ∧ (e.time : Int) ≤ rho.horizon
  change 0 ≤ (e.time : Int) ∧ (e.time : Int) < ((rho.horizon.toNat + 1 : Nat) : Int) at h
  push_cast at h
  dsimp [Time] at *
  omega

theorem policy_layer_mem (t : Time) (h0 : 0 ≤ t) (hh : t ≤ rho.horizon)
    {e : Event V (protoOf F E).Object}
    (he : e ∈ rho.policyLayer pol (rho.policyStages pol t.toNat) t) :
    e ∈ rho.policyEvents pol := by
  apply (rho.mem_policyStages pol _ e).mpr
  refine ⟨t.toNat, ?_, ?_⟩
  · have := Int.toNat_le_toNat hh
    omega
  · simpa only [Int.toNat_of_nonneg h0] using he

/-- The policy's schedule meets every schedule and sleep condition; with the three bindings it is
a valid execution. -/
theorem policy_valid_of (h0 : 0 ≤ rho.horizon)
    (hu : (rho.withEvents (rho.policyEvents pol)).Unforgeable)
    (hsel : (rho.withEvents (rho.policyEvents pol)).SelValid)
    (hc : (rho.withEvents (rho.policyEvents pol)).Credentials) :
    (rho.withEvents (rho.policyEvents pol)).ExecutionValid := by
  rw [withEvents_eq] at hu hsel hc ⊢
  have event_layer {e : Event V (protoOf F E).Object} (he : e ∈ rho.policyEvents pol) :
      ∃ k, e ∈ rho.policyLayer pol (rho.policyStages pol k) (k : Time) := by
    obtain ⟨k, _, hk⟩ := (rho.mem_policyStages pol _ e).mp he
    exact ⟨k, hk⟩
  refine ⟨h0, rho.policyStages_sorted pol _, rho.policyStages_nodup pol _, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, hu, hsel, hc⟩
  · exact fun e he => rho.policy_in_horizon pol h0 he
  · intro e he
    obtain ⟨k, hk⟩ := event_layer he
    exact rho.policyLayer_honest pol _ _ hk
  · intro v t ht0 hh hv ha
    apply rho.policy_layer_mem pol t ht0 hh
    simp only [policyLayer_eq, List.mem_append]
    exact Or.inl (Or.inr ((rho.mem_tickEvents t _).mpr ⟨v, hv, ha, rfl⟩))
  · intro v t he
    obtain ⟨k, hk⟩ := event_layer he
    simp only [policyLayer_eq, List.mem_append, mem_wakeEvents, mem_tickEvents,
      mem_policyDeliveries] at hk
    rcases hk with (⟨w, _, _, _, h⟩ | ⟨w, _, ha, h⟩) | ⟨w, _, _, o, _, _, h⟩
    · cases h
    · cases h; exact ha
    · cases h
  · intro v o t he
    obtain ⟨k, hk⟩ := event_layer he
    simp only [policyLayer_eq, List.mem_append, mem_wakeEvents, mem_tickEvents,
      mem_policyDeliveries] at hk
    rcases hk with (⟨w, _, _, _, h⟩ | ⟨w, _, _, h⟩) | ⟨w, _, ha, p, _, _, h⟩
    · cases h
    · cases h
    · cases h; exact ha
  · intro v t he
    obtain ⟨k, hk⟩ := event_layer he
    simp only [policyLayer_eq, List.mem_append, mem_wakeEvents, mem_tickEvents,
      mem_policyDeliveries] at hk
    rcases hk with (⟨w, _, hp, ha, h⟩ | ⟨w, _, _, h⟩) | ⟨w, _, _, o, _, _, h⟩
    · cases h; exact ⟨hp, ha⟩
    · cases h
    · cases h
  · intro v t hp hh hv hw
    apply rho.policy_layer_mem pol t hp.le hh
    simp only [policyLayer_eq, List.mem_append]
    exact Or.inl (Or.inl ((rho.mem_wakeEvents t _).mpr ⟨v, hv, hp, hw, rfl⟩))

/-- The policy's network is causal: every delivery is of an object released earlier. -/
theorem policy_causal : (rho.withEvents (rho.policyEvents pol)).Causal := by
  rw [causal_iff]
  intro i w o t hi
  rw [withEvents_events] at hi
  have hm := List.mem_of_getElem? hi
  rw [policyEvents_eq] at hm
  obtain ⟨k, hk, he⟩ := (rho.mem_policyStages pol _ _).mp hm
  have htk : t = (k : Time) := rho.policyLayer_time pol _ _ he
  subst t
  have hp : o ∈ rho.pool (rho.front (rho.policyStages pol k) (k : Time)) := by
    simp only [policyLayer_eq, List.mem_append, mem_wakeEvents, mem_tickEvents,
      mem_policyDeliveries] at he
    rcases he with (⟨v, _, _, _, h⟩ | ⟨v, _, _, h⟩) | ⟨v, _, _, p, hp, _, h⟩
    · cases h
    · cases h
    · cases h; exact hp
  obtain ⟨tail, htail⟩ := rho.policy_front_prefix pol hk
  obtain ⟨v, t', j, hj, ho⟩ := (rho.mem_pool _ _).mp hp
  obtain ⟨e, hje, _, _⟩ := hj.exists_event
  rw [withEvents_events] at hje
  have hjl : j < (rho.front (rho.policyStages pol k) (k : Time)).length :=
    (List.getElem?_eq_some_iff.mp hje).1
  have hni : ¬ Event.deliver w o (k : Time) ∈ rho.front (rho.policyStages pol k) (k : Time) := by
    intro h
    simp only [front_eq, List.mem_append] at h
    rcases h with (h | h) | h
    · exact lt_irrefl _ (rho.policyStages_time pol k h).2
    · simp at h
    · simp at h
  have hile : (rho.front (rho.policyStages pol k) (k : Time)).length ≤ i := by
    by_contra h
    have hil : i < (rho.front (rho.policyStages pol k) (k : Time)).length := by omega
    apply hni
    apply List.mem_of_getElem?
    rw [show (rho.front (rho.policyStages pol k) (k : Time))[i]? =
      (rho.policyEvents pol)[i]? by rw [(rho.policyEvents_eq pol).trans htail,
        List.getElem?_append_left hil]]
    exact hi
  refine ⟨j, v, t', lt_of_lt_of_le hjl hile, ?_, ?_⟩
  · rw [(rho.policyEvents_eq pol).trans htail]
    exact rho.sendsAt_append _ tail hj
  · change (rho.withEvents (rho.policyEvents pol)).releasesAt j |> fun l => o ∈ l
    rw [(rho.policyEvents_eq pol).trans htail, rho.releasesAt_append _ _ hjl]
    exact ho

/-- The policy's schedule is a valid execution. -/
theorem policy_valid (h0 : 0 ≤ rho.horizon) (hsel : rho.SelValid) :
    (rho.withEvents (rho.policyEvents pol)).ExecutionValid :=
  rho.policy_valid_of pol h0
    ((rho.withEvents (rho.policyEvents pol)).unforgeable_of_causal (rho.policy_causal pol))
    (by rw [withEvents_eq]; exact hsel)
    ((rho.withEvents (rho.policyEvents pol)).credentials_of_causal (rho.policy_causal pol))

/-- A policy event whose time is below `a` lies in the stages before `a`. -/
theorem mem_policyStages_of_time_lt {n : Nat} {e : Event V (protoOf F E).Object}
    (he : e ∈ rho.policyStages pol n) {a : Time} (ha : e.time < a) :
    e ∈ rho.policyStages pol a.toNat := by
  obtain ⟨k, _, hk⟩ := (rho.mem_policyStages pol n e).mp he
  have htk : e.time = (k : Time) := rho.policyLayer_time pol _ _ hk
  refine (rho.mem_policyStages pol _ e).mpr ⟨k, ?_, hk⟩
  rw [htk] at ha
  have h := (Int.toNat_lt_toNat (lt_of_le_of_lt (Int.natCast_nonneg k) ha)).mpr ha
  simpa using h

/-- A release before `a` is a release of the front of time `a` (the schedule before `a`, with the
wakes and ticks of `a`). -/
theorem policy_releases_front {v : V} {o : (protoOf F E).Object}
    {t a : Time} (hr : (rho.withEvents (rho.policyEvents pol)).releases v o t) (hta : t < a)
    (hah : a ≤ rho.horizon) :
    (rho.withEvents (rho.front (rho.policyStages pol a.toNat) (a.toNat : Time))).releases v o
      t := by
  have han : a.toNat < rho.horizon.toNat + 1 := by
    have := Int.toNat_le_toNat hah
    omega
  obtain ⟨tail, htail⟩ := rho.policy_front_prefix pol han
  have hr0 := hr
  rw [policyEvents_eq] at hr0
  apply rho.releases_restrict _ tail
  · rw [← htail]; exact rho.policyStages_nodup pol _
  · intro e' he' _ het'
    rw [← htail] at he'
    rw [front_eq]
    apply List.mem_append_left
    apply List.mem_append_left
    exact rho.mem_policyStages_of_time_lt pol he' (het' ▸ hta)
  · rw [← htail]
    exact hr0

/-- **Receipt under the policy**: a release at `t` is received at every `a` with
`t < a ≤ horizon` by every node honest and awake at `a` that the policy serves it to at `a`. -/
theorem policy_receives (h0 : 0 ≤ rho.horizon) {v : V} {o : (protoOf F E).Object} {t : Time}
    (hr : (rho.withEvents (rho.policyEvents pol)).releases v o t) {w : V} {a : Time}
    (hta : t < a) (hah : a ≤ rho.horizon) (hw : w ∉ rho.faultyAt a) (haw : E.awake w a = true)
    (hp : pol (rho.front (rho.policyStages pol a.toNat) (a.toNat : Time)) w o a = true) :
    (rho.withEvents (rho.policyEvents pol)).receives w o a := by
  obtain ⟨i, hi, _⟩ := id hr
  obtain ⟨e, hie, _, het⟩ := hi.exists_event
  have htm := List.mem_of_getElem? hie
  rw [withEvents_events] at htm
  have ht0 : 0 ≤ t := het ▸ (rho.policy_in_horizon pol h0 htm).1
  have ha0 : 0 ≤ a := le_trans ht0 (le_of_lt hta)
  have hr' := rho.policy_releases_front pol hr hta hah
  have hpool := (rho.mem_pool _ o).mpr ⟨v, t, hr'⟩
  have hdel : Event.deliver w o a ∈ rho.policyEvents pol := by
    apply rho.policy_layer_mem pol a ha0 hah
    simp only [policyLayer_eq, List.mem_append]
    apply Or.inr
    apply (rho.mem_policyDeliveries pol _ a _).mpr
    refine ⟨w, hw, haw, o, by simpa only [Int.toNat_of_nonneg ha0] using hpool, ?_, rfl⟩
    simpa only [Int.toNat_of_nonneg ha0] using hp
  rw [← withEvents_events rho (rho.policyEvents pol)] at hdel
  exact List.mem_iff_getElem?.mp hdel

/-- **Every receipt is one the policy allows**, at a nonnegative time, of an object released by
then (in the front of its time). -/
theorem policy_receives_inv {w : V} {o : (protoOf F E).Object} {a : Time}
    (hr : (rho.withEvents (rho.policyEvents pol)).receives w o a) :
    0 ≤ a ∧ o ∈ rho.pool (rho.front (rho.policyStages pol a.toNat) (a.toNat : Time)) ∧
      pol (rho.front (rho.policyStages pol a.toNat) (a.toNat : Time)) w o a = true := by
  obtain ⟨i, hi⟩ := hr
  rw [withEvents_events, policyEvents_eq] at hi
  obtain ⟨k, _, he⟩ := (rho.mem_policyStages pol _ _).mp (List.mem_of_getElem? hi)
  simp only [policyLayer_eq, List.mem_append, mem_wakeEvents, mem_tickEvents,
    mem_policyDeliveries] at he
  rcases he with (⟨v, _, _, _, h⟩ | ⟨v, _, _, h⟩) | ⟨v, _, _, p, hp, hpol, h⟩
  · cases h
  · cases h
  · cases h
    simp only [Int.toNat_natCast]
    exact ⟨Int.natCast_nonneg k, hp, hpol⟩

/-- **A policy that serves everything before `s` is synchronous there**: its stages before `s`
are those of the synchronous canonical schedule. -/
theorem policyStages_eq_stages {s : Time}
    (hpol : ∀ es v o (t : Time), 0 ≤ t → t < s → pol es v o t = true) :
    ∀ n : Nat, (n : Time) ≤ s → rho.policyStages pol n = rho.stages 0 n := by
  intro n
  induction n with
  | zero => intro _; rw [policyStages_zero, stages_zero]
  | succ n ih =>
    intro hn
    have hn' : (n : Time) < s := lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) hn
    rw [policyStages_succ, stages_succ, ih hn'.le, policyLayer_eq, layer_eq]
    congr 1
    have hf : ∀ v, (rho.pool (rho.front (rho.stages 0 n) (n : Time))).filter
        (fun o => pol (rho.front (rho.stages 0 n) (n : Time)) v o (n : Time)) =
        rho.pool (rho.front (rho.stages 0 n) (n : Time)) := fun v =>
      List.filter_eq_self.mpr fun o _ => hpol _ v o _ (Int.natCast_nonneg n) hn'
    classical
    simp only [deliveryEvents_eq, Int.natCast_nonneg n, ↓reduceIte]
    delta policyDeliveries
    simp only [hf]

/-- A release of a prefix is a release of the longer schedule. -/
theorem releases_append (xs ys : List (Event V (protoOf F E).Object)) {v : V}
    {o : (protoOf F E).Object} {t : Time} (hr : (rho.withEvents xs).releases v o t) :
    (rho.withEvents (xs ++ ys)).releases v o t := by
  obtain ⟨i, hi, ho⟩ := hr
  have hil : i < xs.length := by
    rcases hi with hi | ⟨_, hi⟩ <;>
      (rw [withEvents_events] at hi; exact (List.getElem?_eq_some_iff.mp hi).1)
  exact ⟨i, rho.sendsAt_append xs ys hi, by rw [rho.releasesAt_append xs ys hil]; exact ho⟩

/-- A signed object is released only by the validator of its key. -/
theorem releases_key_of_signer {u : V} {o : (protoOf F E).Object} {t : Time}
    {k : Fin (Fintype.card V)} (hr : rho.releases u o t) (hk : o.signer? = some k) :
    rho.key k = u := by
  obtain ⟨i, hi, ho⟩ := hr
  have hs : o.signer? = none ∨ o.signer? = some (rho.ownKey u) := by
    rcases hi with he | ⟨p, he⟩
    · simp only [releasesAt, he] at ho
      exact rho.tick_signer _ u t ho
    · simp only [releasesAt, he] at ho
      exact rho.deliver_signer _ u p t ho
  rcases hs with hs | hs
  · rw [hk] at hs; cases hs
  · have hko : k = rho.ownKey u := Option.some.inj (hk.symm.trans hs)
    rw [hko, ownKey, Equiv.apply_symm_apply]

/-- A release in the front of time `a` (a prefix of events before `a`, then the wakes and ticks of
`a`) is at a time `≤ a`. -/
theorem front_releases_le (es : List (Event V (protoOf F E).Object)) (a : Time)
    (hes : ∀ e ∈ es, e.time < a) {u : V} {o : (protoOf F E).Object} {t : Time}
    (hr : (rho.withEvents (rho.front es a)).releases u o t) : t ≤ a := by
  obtain ⟨i, hi, -⟩ := hr
  obtain ⟨e, he, -, het⟩ := hi.exists_event
  have hm := List.mem_of_getElem? he
  rw [withEvents_events, front_eq] at hm
  subst het
  simp only [List.mem_append, mem_wakeEvents, mem_tickEvents] at hm
  rcases hm with (hm | ⟨v, _, _, _, rfl⟩) | ⟨v, _, _, rfl⟩
  · exact (hes e hm).le
  · exact le_rfl
  · exact le_rfl

/-- **Releases before `s` agree** between a policy that serves everything before `s` and the
synchronous canonical schedule: at a time `t` with `t + 1 ≤ s` (all of whose events precede `s`). -/
theorem policy_releases_iff {s : Time}
    (hpol : ∀ es v o (t : Time), 0 ≤ t → t < s → pol es v o t = true) (h0 : 0 ≤ rho.horizon)
    {u : V} {o : (protoOf F E).Object} {t : Time} (hts : t + 1 ≤ s) (hth : t ≤ rho.horizon) :
    (rho.withEvents (rho.policyEvents pol)).releases u o t ↔
      (rho.withEvents (rho.canonicalEvents 0)).releases u o t := by
  have time0 : ∀ (l : List (Event V (protoOf F E).Object)), (∀ e ∈ l, 0 ≤ e.time) →
      (rho.withEvents l).releases u o t → 0 ≤ t := by
    rintro l hl ⟨i, hi, -⟩
    obtain ⟨e, he, -, het⟩ := hi.exists_event
    rw [withEvents_events] at he
    exact het ▸ hl e (List.mem_of_getElem? he)
  have hn : t.toNat + 1 ≤ rho.horizon.toNat + 1 := by
    have := Int.toNat_le_toNat hth; omega
  have hsucc : 0 ≤ t → (t + 1).toNat = t.toNat + 1 := fun ht0 => by
    rw [Int.toNat_add ht0 zero_le_one]; rfl
  have restrict : ∀ (l tail : List (Event V (protoOf F E).Object)),
      (l ++ tail).Nodup → (∀ e ∈ l ++ tail, e.time = t → e ∈ l) →
      (rho.withEvents (l ++ tail)).releases u o t → (rho.withEvents l).releases u o t :=
    fun l tail hnd hin hr => rho.releases_restrict l tail hnd (fun e he _ ht => hin e he ht) hr
  constructor
  · intro hr
    have ht0 := time0 _ (fun e he => (rho.policy_in_horizon pol h0 he).1) hr
    have hP : rho.policyStages pol (t.toNat + 1) = rho.stages 0 (t.toNat + 1) :=
      rho.policyStages_eq_stages pol hpol _ (by push_cast; rw [Int.toNat_of_nonneg ht0]; exact hts)
    obtain ⟨tail, htail⟩ := rho.policyStages_prefix pol hn
    obtain ⟨tail', htail'⟩ := rho.stages_prefix 0 hn
    rw [canonicalEvents_eq, htail', ← hP]
    apply rho.releases_append
    rw [policyEvents_eq, htail] at hr
    refine restrict _ tail (htail ▸ rho.policyStages_nodup pol _) (fun e he het => ?_) hr
    rw [← htail] at he
    have h := rho.mem_policyStages_of_time_lt pol he (a := t + 1) (by rw [het]; exact lt_add_one t)
    rwa [hsucc ht0] at h
  · intro hr
    have ht0 := time0 _ (fun e he => (rho.canonical_in_horizon 0 h0 he).1) hr
    have hP : rho.policyStages pol (t.toNat + 1) = rho.stages 0 (t.toNat + 1) :=
      rho.policyStages_eq_stages pol hpol _ (by push_cast; rw [Int.toNat_of_nonneg ht0]; exact hts)
    obtain ⟨tail, htail⟩ := rho.policyStages_prefix pol hn
    obtain ⟨tail', htail'⟩ := rho.stages_prefix 0 hn
    rw [policyEvents_eq, htail, hP]
    apply rho.releases_append
    rw [canonicalEvents_eq, htail'] at hr
    refine restrict _ tail' (htail' ▸ rho.stages_nodup 0 _) (fun e he het => ?_) hr
    rw [← htail'] at he
    have h := rho.mem_stages_of_time_lt 0 he (a := t + 1) (by rw [het]; exact lt_add_one t)
    rwa [hsucc ht0] at h

end Run

end Consensus.Model
end

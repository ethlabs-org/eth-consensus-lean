module
public import ConsensusLean.Lemmas.Model.Canonical.Inject
public import ConsensusLean.Lemmas.Model.Canonical.Policy
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Runs in two environments that differ only in who is awake (L1)

Two environments `⟨d₁, h₁, d₂, h₂, a⟩` and `⟨d₁, h₁, d₂, h₂, a'⟩` that differ only in the awake
profile have the same public parameters, so a family runs the same protocol in both. Two runs
`ρ`, `ρ'` in them with the same compromise schedule, PKI, selection, submissions and hash are
*twins* (`Run.Twins`).

* `step_twins`: an event steps the world of both runs alike, given (for a tick) the same awake bit
  and mempool of its node at its time.
* `releasesAt_twins_local`: the releases of an event of `v` depend only on `v`'s own earlier events:
  twins release the same at the same event when `v`'s events before it are the same.
* `injectStages_twins`: twin scheduled runs with injections have the same stages while the awake
  profiles, the relays, the injections and the filters agree. -/

namespace Consensus.Model

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : ProtocolFamily O}
  {d₁ d₂ : Time} {h₁ : 0 < d₁} {h₂ : 0 < d₂} {a a' : V → Time → Bool}

namespace Run

/-- **Twin runs**: runs in two environments that differ only in the awake profile, with the same
compromise schedule, PKI, selection, submissions and hash (horizon, events and relay may
differ). -/
structure Twins (ρ : Run F ⟨d₁, h₁, d₂, h₂, a⟩) (ρ' : Run F ⟨d₁, h₁, d₂, h₂, a'⟩) : Prop where
  faultyAt : ρ'.faultyAt = ρ.faultyAt
  key : ρ'.key = ρ.key
  sel : ρ'.sel = ρ.sel
  submit : ρ'.submit = ρ.submit
  hash : ρ'.hash = ρ.hash

variable {ρ : Run F ⟨d₁, h₁, d₂, h₂, a⟩} {ρ' : Run F ⟨d₁, h₁, d₂, h₂, a'⟩}

omit [DecidableEq V] in
theorem Twins.withEvents (tw : Twins ρ ρ')
    (es : List (Event V (protoOf F ⟨d₁, h₁, d₂, h₂, a⟩).Object))
    (es' : List (Event V (protoOf F ⟨d₁, h₁, d₂, h₂, a'⟩).Object)) :
    Twins (ρ.withEvents es) (ρ'.withEvents es') :=
  ⟨by simp only [withEvents_faultyAt]; exact tw.faultyAt,
    by simp only [withEvents_key]; exact tw.key,
    by simp only [withEvents_sel]; exact tw.sel,
    by rw [withEvents_eq, withEvents_eq]; exact tw.submit,
    by rw [withEvents_eq, withEvents_eq]; exact tw.hash⟩

omit [DecidableEq V] in
theorem initWorld_twins (tw : Twins ρ ρ') : ρ'.initWorld = ρ.initWorld := by
  obtain ⟨fa, fm, hz, ev, k, s, sb, rl, hs⟩ := ρ
  obtain ⟨fa', fm', hz', ev', k', s', sb', rl', hs'⟩ := ρ'
  obtain ⟨e1, e2, e3, e4, e5⟩ := tw
  dsimp only at e1 e2 e3 e4 e5
  subst e1 e2 e3 e4 e5
  rfl

omit [DecidableEq V] in
theorem deliver_twins (tw : Twins ρ ρ') (nd : Node (protoOf F ⟨d₁, h₁, d₂, h₂, a⟩)) (v : V)
    (o : (protoOf F ⟨d₁, h₁, d₂, h₂, a⟩).Object) (t : Time) :
    ρ'.deliver nd v o t = ρ.deliver nd v o t := by
  obtain ⟨fa, fm, hz, ev, k, s, sb, rl, hs⟩ := ρ
  obtain ⟨fa', fm', hz', ev', k', s', sb', rl', hs'⟩ := ρ'
  obtain ⟨e1, e2, e3, e4, e5⟩ := tw
  dsimp only at e1 e2 e3 e4 e5
  subst e1 e2 e3 e4 e5
  rfl

omit [DecidableEq V] in
theorem tick_twins (tw : Twins ρ ρ') (nd : Node (protoOf F ⟨d₁, h₁, d₂, h₂, a⟩)) {v : V}
    {t : Time} (ha : a' v t = a v t) (hm : mempool ρ'.inbox v t = mempool ρ.inbox v t) :
    ρ'.tick nd v t = ρ.tick nd v t := by
  obtain ⟨fa, fm, hz, ev, k, s, sb, rl, hs⟩ := ρ
  obtain ⟨fa', fm', hz', ev', k', s', sb', rl', hs'⟩ := ρ'
  obtain ⟨e1, e2, e3, e4, e5⟩ := tw
  dsimp only at e1 e2 e3 e4 e5
  subst e1 e2 e3 e4 e5
  unfold tick
  rw [hm]
  dsimp only
  by_cases hb : a v t = true
  · have hb' : a' v t = true := ha.trans hb
    simp only [hb, hb', ↓reduceIte]
    rfl
  · have hb' : ¬ a' v t = true := fun h => hb (ha.symm.trans h)
    simp only [hb, hb']
    rfl

omit [DecidableEq V] in
theorem ownKey_twins (tw : Twins ρ ρ') : ρ'.ownKey = ρ.ownKey := by
  funext v
  simp only [ownKey, tw.key]

/-- A tick of `v` at `t` that sees the same awake bit and mempool in both runs. -/
abbrev TickAgrees (ρ : Run F ⟨d₁, h₁, d₂, h₂, a⟩) (ρ' : Run F ⟨d₁, h₁, d₂, h₂, a'⟩)
    (e : Event V (protoOf F ⟨d₁, h₁, d₂, h₂, a⟩).Object) : Prop :=
  ∀ v t, e = .tick v t → a' v t = a v t ∧ mempool ρ'.inbox v t = mempool ρ.inbox v t

/-- **An event steps twin worlds alike** (a tick given the same awake bit and mempool). -/
theorem step_twins (tw : Twins ρ ρ') (w : V → Node (protoOf F ⟨d₁, h₁, d₂, h₂, a⟩))
    (e : Event V (protoOf F ⟨d₁, h₁, d₂, h₂, a⟩).Object) (he : TickAgrees ρ ρ' e) :
    ρ'.step w e = ρ.step w e := by
  cases e with
  | tick v t =>
    obtain ⟨ha, hm⟩ := he v t rfl
    simp only [step]
    rw [tick_twins tw _ ha hm]
  | deliver v o t =>
    simp only [step]
    rw [deliver_twins tw]
  | restart v t =>
    simp only [step]
    rw [ownKey_twins tw]

theorem foldl_step_twins (tw : Twins ρ ρ') :
    ∀ (l : List (Event V (protoOf F ⟨d₁, h₁, d₂, h₂, a⟩).Object))
      (w : V → Node (protoOf F ⟨d₁, h₁, d₂, h₂, a⟩)), (∀ e ∈ l, TickAgrees ρ ρ' e) →
      l.foldl ρ'.step w = l.foldl ρ.step w
  | [], _, _ => rfl
  | e :: l, w, h => by
    simp only [List.foldl_cons]
    rw [step_twins tw w e (h e List.mem_cons_self)]
    exact foldl_step_twins tw l _ (fun e' he' => h e' (List.mem_cons_of_mem _ he'))

omit [DecidableEq V] in
theorem mempool_twins {ρ : Run F ⟨d₁, h₁, d₂, h₂, a⟩} {ρ' : Run F ⟨d₁, h₁, d₂, h₂, a'⟩}
    {v : V} {t : Time} (h : ∀ k : Time, k ≤ t → ρ'.inbox v k = ρ.inbox v k) :
    mempool ρ'.inbox v t = mempool ρ.inbox v t := by
  unfold mempool
  split_ifs with ht
  · rfl
  · refine List.flatMap_congr fun k hk => h k ?_
    obtain ⟨j, hj, rfl⟩ : ∃ j < t.toNat + 1, k = (j : Time) := by simpa using hk
    have h0 : (0 : Int) ≤ t := le_of_not_gt ht
    change ((j : ℕ) : ℤ) ≤ (t : ℤ)
    omega

/-- Twin runs with the same events and every tick agreeing have the same worlds. -/
theorem stateBefore_twins (tw : Twins ρ ρ') (hev : ρ'.events = ρ.events)
    (hag : ∀ e ∈ ρ.events, TickAgrees ρ ρ' e) (i : Nat) :
    ρ'.stateBefore i = ρ.stateBefore i := by
  unfold stateBefore
  rw [hev, initWorld_twins tw]
  exact foldl_step_twins tw _ _ fun e he => hag e (List.mem_of_mem_take he)

/-- Twin runs with the same events and every tick agreeing release the same at every event. -/
theorem releasesAt_twins (tw : Twins ρ ρ') (hev : ρ'.events = ρ.events)
    (hag : ∀ e ∈ ρ.events, TickAgrees ρ ρ' e) (i : Nat) :
    ρ'.releasesAt i = ρ.releasesAt i := by
  unfold releasesAt
  rw [hev, stateBefore_twins tw hev hag]
  cases he : ρ.events[i]? with
  | none => rfl
  | some e =>
    cases e with
    | tick v t =>
      obtain ⟨ha, hm⟩ := hag _ (List.mem_of_getElem? he) v t rfl
      dsimp only
      rw [tick_twins tw _ ha hm]
    | deliver v o t =>
      dsimp only
      rw [deliver_twins tw]
    | restart v t => rfl

/-! ### A node's state depends only on its own events -/

variable {E : Env V}

/-- The transition of node `v` at an event (the identity at another node's event). -/
private def nodeStep (σ : Run F E) (v : V) (nd : Node (protoOf F E))
    (e : Event V (protoOf F E).Object) : Node (protoOf F E) :=
  σ.step (fun _ => nd) e v

private theorem step_apply (σ : Run F E) (w : V → Node (protoOf F E))
    (e : Event V (protoOf F E).Object) (v : V) : σ.step w e v = nodeStep σ v (w v) e := by
  unfold nodeStep
  cases e with
  | tick u t =>
    by_cases h : u = v
    · subst h; simp [step]
    · simp [step, Ne.symm h]
  | deliver u o t =>
    by_cases h : u = v
    · subst h; simp [step]
    · simp [step, Ne.symm h]
  | restart u t =>
    by_cases h : u = v
    · subst h; simp [step]
    · simp [step, Ne.symm h]

private theorem nodeStep_of_ne (σ : Run F E) {v : V} (nd : Node (protoOf F E))
    {e : Event V (protoOf F E).Object} (h : e.node ≠ v) : nodeStep σ v nd e = nd := by
  unfold nodeStep
  cases e with
  | tick u t => simp only [step]; exact Function.update_of_ne (Ne.symm h) _ _
  | deliver u o t => simp only [step]; exact Function.update_of_ne (Ne.symm h) _ _
  | restart u t => simp only [step]; exact Function.update_of_ne (Ne.symm h) _ _

private theorem foldl_step_apply (σ : Run F E) (v : V) :
    ∀ (l : List (Event V (protoOf F E).Object)) (w : V → Node (protoOf F E)),
      l.foldl σ.step w v = (l.filter fun e => e.node = v).foldl (nodeStep σ v) (w v)
  | [], _ => rfl
  | e :: l, w => by
    simp only [List.foldl_cons, List.filter_cons]
    rw [foldl_step_apply σ v l, step_apply]
    split_ifs with h
    · rfl
    · rw [nodeStep_of_ne σ _ (by simpa using h)]

private theorem foldl_nodeStep_twins (tw : Twins ρ ρ') (v : V) :
    ∀ (l : List (Event V (protoOf F ⟨d₁, h₁, d₂, h₂, a⟩).Object))
      (nd : Node (protoOf F ⟨d₁, h₁, d₂, h₂, a⟩)), (∀ e ∈ l, TickAgrees ρ ρ' e) →
      l.foldl (nodeStep ρ' v) nd = l.foldl (nodeStep ρ v) nd
  | [], _, _ => rfl
  | e :: l, nd, h => by
    simp only [List.foldl_cons]
    have : nodeStep ρ' v nd e = nodeStep ρ v nd e := by
      unfold nodeStep
      rw [step_twins tw _ e (h e List.mem_cons_self)]
    rw [this]
    exact foldl_nodeStep_twins tw v l _ (fun e' he' => h e' (List.mem_cons_of_mem _ he'))

/-- **Locality**: twin runs release the same at an event `e` of `v` (at index `i` of `ρ` and `i'`
of `ρ'`) when `v`'s events before it are the same in both and they, and `e`, agree as ticks. -/
theorem releasesAt_twins_local (tw : Twins ρ ρ') {i i' : Nat}
    {e : Event V (protoOf F ⟨d₁, h₁, d₂, h₂, a⟩).Object} (he : ρ.events[i]? = some e)
    (he' : ρ'.events[i']? = some e)
    (hpre : (ρ'.events.take i').filter (fun x => x.node = e.node) =
      (ρ.events.take i).filter (fun x => x.node = e.node))
    (hag : ∀ x ∈ (ρ.events.take i).filter (fun x => x.node = e.node), TickAgrees ρ ρ' x)
    (hage : TickAgrees ρ ρ' e) :
    ρ'.releasesAt i' = ρ.releasesAt i := by
  have hst : ρ'.stateBefore i' e.node = ρ.stateBefore i e.node := by
    unfold stateBefore
    rw [foldl_step_apply, foldl_step_apply, hpre, initWorld_twins tw]
    exact foldl_nodeStep_twins tw _ _ _ hag
  unfold releasesAt
  rw [he, he']
  cases e with
  | tick v t =>
    obtain ⟨ha, hm⟩ := hage v t rfl
    dsimp only
    change ρ'.stateBefore i' v = ρ.stateBefore i v at hst
    rw [hst, tick_twins tw _ ha hm]
  | deliver v o t =>
    dsimp only
    change ρ'.stateBefore i' v = ρ.stateBefore i v at hst
    rw [hst, deliver_twins tw]
  | restart v t => rfl

/-! ### Twin schedules -/

omit [DecidableEq V] in
theorem withEvents_inbox (σ : Run F E) (es : List (Event V (protoOf F E).Object)) :
    (σ.withEvents es).inbox = σ.inbox := by
  rw [withEvents_eq]
  rfl

/-- Twin runs on the same events, every tick agreeing: the same releases. -/
theorem releases_twins (tw : Twins ρ ρ')
    (es : List (Event V (protoOf F ⟨d₁, h₁, d₂, h₂, a⟩).Object))
    (hag : ∀ e ∈ es, TickAgrees ρ ρ' e) {u : V} {o : (protoOf F ⟨d₁, h₁, d₂, h₂, a⟩).Object}
    {t : Time} : (ρ'.withEvents es).releases u o t ↔ (ρ.withEvents es).releases u o t := by
  have hag' : ∀ e ∈ (ρ.withEvents es).events,
      TickAgrees (ρ.withEvents es) (ρ'.withEvents es) e := by
    intro e he v τ hv
    rw [withEvents_inbox, withEvents_inbox]
    exact hag e (by simpa using he) v τ hv
  have hr := releasesAt_twins (tw.withEvents es es) (by simp) hag'
  unfold releases SendsAt
  simp only [withEvents_events, hr]

theorem tickEvents_twins (tw : Twins ρ ρ') {t : Time} (ha : ∀ v, a' v t = a v t) :
    ρ'.tickEvents t = ρ.tickEvents t := by
  rw [tickEvents_eq, tickEvents_eq, tw.faultyAt]
  rw [Finset.filter_congr (q := fun v => a v t = true) fun v _ => by
    change a' v t = true ↔ a v t = true
    rw [ha]]

theorem wakeEvents_twins (tw : Twins ρ ρ') {t : Time} (ha : ∀ v, a' v t = a v t)
    (ha' : ∀ v, a' v (t - 1) = a v (t - 1)) : ρ'.wakeEvents t = ρ.wakeEvents t := by
  classical
  rw [wakeEvents_eq, wakeEvents_eq, tw.faultyAt]
  have hS : (Finset.univ \ ρ.faultyAt t).filter
        (fun v => 0 < t ∧ Wakes (⟨d₁, h₁, d₂, h₂, a'⟩ : Env V) v t) =
      (Finset.univ \ ρ.faultyAt t).filter
        (fun v => 0 < t ∧ Wakes (⟨d₁, h₁, d₂, h₂, a⟩ : Env V) v t) :=
    Finset.filter_congr fun v _ => by
      unfold Wakes
      change 0 < t ∧ a' v t = true ∧ a' v (t - 1) = false ↔
        0 < t ∧ a v t = true ∧ a v (t - 1) = false
      rw [ha, ha']
  rw [hS]

/-- Twin runs on the same events, every tick agreeing: the same due batch. -/
theorem duePool_twins (tw : Twins ρ ρ')
    (delay : Event V (protoOf F ⟨d₁, h₁, d₂, h₂, a⟩).Object → Time)
    (es : List (Event V (protoOf F ⟨d₁, h₁, d₂, h₂, a⟩).Object)) (t : Time)
    (hag : ∀ e ∈ es, TickAgrees ρ ρ' e) : ρ'.duePool delay es t = ρ.duePool delay es t := by
  have hag' : ∀ e ∈ (ρ.withEvents es).events,
      TickAgrees (ρ.withEvents es) (ρ'.withEvents es) e := by
    intro e he v τ hv
    rw [withEvents_inbox, withEvents_inbox]
    exact hag e (by simpa using he) v τ hv
  have hr := releasesAt_twins (tw.withEvents es es) (by simp) hag'
  rw [duePool_eq, duePool_eq]
  congr 1
  refine List.flatMap_congr fun j _ => ?_
  rw [hr j]

/-- **Twin schedules agree**: twin scheduled runs with injections have the same first `N` stages
while the awake profiles and the relays agree at the times below `N`, and the injections and the
filter values agree there. -/
theorem injectStages_twins (tw : Twins ρ ρ')
    (delay : Event V (protoOf F ⟨d₁, h₁, d₂, h₂, a⟩).Object → Time)
    (inj : Time → V → List (protoOf F ⟨d₁, h₁, d₂, h₂, a⟩).Object)
    (inj' : Time → V → List (protoOf F ⟨d₁, h₁, d₂, h₂, a'⟩).Object)
    (pol : List (Event V (protoOf F ⟨d₁, h₁, d₂, h₂, a⟩).Object) → V →
      (protoOf F ⟨d₁, h₁, d₂, h₂, a⟩).Object → Time → Bool)
    (pol' : List (Event V (protoOf F ⟨d₁, h₁, d₂, h₂, a'⟩).Object) → V →
      (protoOf F ⟨d₁, h₁, d₂, h₂, a'⟩).Object → Time → Bool) {N : Nat}
    (hawake : ∀ v (t : Time), t < N → a' v t = a v t)
    (hrelay : ∀ v (t : Time), t < N → ρ'.relay v t = ρ.relay v t)
    (hinj : ∀ n < N, inj' (n : Time) = inj (n : Time))
    (hpol : ∀ n < N, ∀ v o,
      pol' (ρ.front (ρ.injectStages delay inj pol n) (n : Time)) v o (n : Time) =
        pol (ρ.front (ρ.injectStages delay inj pol n) (n : Time)) v o (n : Time)) :
    ∀ n ≤ N, ρ'.injectStages delay inj' pol' n = ρ.injectStages delay inj pol n := by
  intro n
  induction n with
  | zero => intro _; rw [injectStages_zero, injectStages_zero]
  | succ n ih =>
    intro hn
    have hnN : (n : Time) < N := by exact_mod_cast hn
    have hw : ρ'.wakeEvents (n : Time) = ρ.wakeEvents (n : Time) :=
      wakeEvents_twins tw (fun v => hawake v _ hnN) (fun v => hawake v _ (by linarith))
    have ht : ρ'.tickEvents (n : Time) = ρ.tickEvents (n : Time) :=
      tickEvents_twins tw (fun v => hawake v _ hnN)
    have hfront : ∀ es, ρ'.front es (n : Time) = ρ.front es (n : Time) := fun es => by
      rw [front_eq, front_eq, hw, ht]
    have hag : ∀ e ∈ ρ.front (ρ.injectStages delay inj pol n) (n : Time), TickAgrees ρ ρ' e := by
      intro e he v τ hv
      subst hv
      have hτ : τ ≤ (n : Time) := by
        rw [front_eq] at he
        rcases List.mem_append.mp he with he | he
        · rcases List.mem_append.mp he with he | he
          · exact (ρ.injectStages_time delay inj pol n he).2.le
          · obtain ⟨_, _, _, _, h⟩ := (ρ.mem_wakeEvents _ _).mp he
            cases h
        · obtain ⟨_, _, _, h⟩ := (ρ.mem_tickEvents _ _).mp he
          cases h
          exact le_rfl
      refine ⟨hawake v τ (by linarith), mempool_twins fun k hk => ?_⟩
      change ρ'.submit v k ++ ρ'.relay v k = ρ.submit v k ++ ρ.relay v k
      rw [tw.submit, hrelay v k (by linarith)]
    rw [injectStages_succ, injectStages_succ, ih (by omega), injectLayer_eq, injectLayer_eq, hw, ht,
      hfront]
    congr 1
    rw [injectDeliveries_eq, injectDeliveries_eq, tw.faultyAt,
      duePool_twins tw delay _ _ hag, hinj n (by omega)]
    rw [Finset.filter_congr (q := fun v => a v (n : Time) = true) fun v _ => by
      change a' v (n : Time) = true ↔ a v (n : Time) = true
      rw [hawake v _ hnN]]
    have hf : ∀ v, (ρ.duePool delay (ρ.front (ρ.injectStages delay inj pol n) (n : Time))
        (n : Time)).filter (fun o => pol' (ρ.front (ρ.injectStages delay inj pol n) (n : Time))
          v o (n : Time)) =
        (ρ.duePool delay (ρ.front (ρ.injectStages delay inj pol n) (n : Time))
          (n : Time)).filter (fun o => pol (ρ.front (ρ.injectStages delay inj pol n)
            (n : Time)) v o (n : Time)) := fun v =>
      List.filter_congr fun o _ => by rw [hpol n (by omega) v o]
    simp only [hf]

/-! ### One node across a layer -/

omit [Fintype V] [DecidableEq V] in
private theorem prefix_unique {α : Type} {e : α} :
    ∀ {A A' B B' : List α}, e ∉ A → e ∉ A' → A ++ e :: B = A' ++ e :: B' → A = A'
  | [], [], _, _, _, _, _ => rfl
  | [], x :: A', _, _, _, h', h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) h'
  | x :: A, [], _, _, h, _, h' => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h'
    exact absurd (h'.1 ▸ List.mem_cons_self) h
  | x :: A, y :: A', B, B', h, h', heq => by
    simp only [List.cons_append, List.cons.injEq] at heq
    obtain ⟨rfl, heq⟩ := heq
    rw [prefix_unique (fun hm => h (List.mem_cons_of_mem _ hm))
      (fun hm => h' (List.mem_cons_of_mem _ hm)) heq]

omit [Fintype V] [DecidableEq V] in
private theorem filter_split {α : Type} (p : α → Bool) {l : List α} (hl : l.Nodup) {i : Nat}
    {e : α} (he : l[i]? = some e) (hp : p e = true) :
    l.filter p = (l.take i).filter p ++ e :: (l.drop (i + 1)).filter p ∧
      e ∉ (l.take i).filter p := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp he
  have hl' : l = l.take i ++ l[i] :: l.drop (i + 1) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  refine ⟨?_, fun hm => ?_⟩
  · conv_lhs => rw [hl']
    rw [List.filter_append, List.filter_cons_of_pos hp]
  · have hm' := (List.mem_filter.mp hm).1
    rw [hl'] at hl
    exact (List.nodup_append.mp hl).2.2 _ hm' _ List.mem_cons_self rfl

omit [Fintype V] [DecidableEq V] in
/-- In two duplicate-free lists that agree on the elements satisfying `p`, the elements satisfying
`p` before a common such element are the same. -/
theorem take_filter_eq {α : Type} (p : α → Bool) {l l' : List α} (hl : l.Nodup)
    (hl' : l'.Nodup) (h : l'.filter p = l.filter p) {i i' : Nat} {e : α} (he : l[i]? = some e)
    (he' : l'[i']? = some e) (hp : p e = true) :
    (l'.take i').filter p = (l.take i).filter p := by
  obtain ⟨h1, h2⟩ := filter_split p hl he hp
  obtain ⟨h1', h2'⟩ := filter_split p hl' he' hp
  rw [h1, h1'] at h
  exact prefix_unique h2' h2 h

omit [Fintype V] in
private theorem filter_node_flatMap {Ob : Type} (l : List V) (hl : l.Nodup)
    (f : V → List (Event V Ob)) (hf : ∀ x, ∀ e ∈ f x, e.node = x) (v : V) :
    (l.flatMap f).filter (fun e => e.node = v) = if v ∈ l then f v else [] := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.flatMap_cons, List.filter_append, ih (List.nodup_cons.mp hl).2]
    by_cases hx : x = v
    · subst hx
      have hn := (List.nodup_cons.mp hl).1
      rw [List.filter_eq_self.mpr fun e he => by simp [hf _ e he]]
      simp only [hn, List.mem_cons_self, ↓reduceIte, List.append_nil]
    · rw [List.filter_eq_nil_iff.mpr fun e he => by simp [hf _ e he, hx], List.nil_append]
      have hv : v ∈ x :: l ↔ v ∈ l := by simp [Ne.symm hx]
      by_cases hvl : v ∈ l
      · simp only [hvl, hv, ↓reduceIte]
      · simp only [hvl, hv, ↓reduceIte]

omit [Fintype V] [DecidableEq V] in
private theorem flatMap_singleton_eq_map {α β : Type} (f : α → β) :
    ∀ l : List α, l.flatMap (fun x => [f x]) = l.map f
  | [] => rfl
  | x :: l => by rw [List.flatMap_cons, flatMap_singleton_eq_map f l]; rfl

omit [Fintype V] in
private theorem filter_node_map {Ob : Type} (l : List V) (hl : l.Nodup) (f : V → Event V Ob)
    (hf : ∀ x, (f x).node = x) (v : V) :
    (l.map f).filter (fun e => e.node = v) = if v ∈ l then [f v] else [] := by
  have h := filter_node_flatMap l hl (fun x => [f x]) (fun x e he => by
    rw [List.mem_singleton.mp he, hf]) v
  rwa [flatMap_singleton_eq_map] at h

/-- **One node across a layer**: twin layers have the same events of `v` when `v` has the same
awake bits at `t` and `t - 1` and the same delivery batch. -/
theorem injectLayer_filter_twins (tw : Twins ρ ρ')
    (delay : Event V (protoOf F ⟨d₁, h₁, d₂, h₂, a⟩).Object → Time)
    (inj : Time → V → List (protoOf F ⟨d₁, h₁, d₂, h₂, a⟩).Object)
    (inj' : Time → V → List (protoOf F ⟨d₁, h₁, d₂, h₂, a'⟩).Object)
    (pol : List (Event V (protoOf F ⟨d₁, h₁, d₂, h₂, a⟩).Object) → V →
      (protoOf F ⟨d₁, h₁, d₂, h₂, a⟩).Object → Time → Bool)
    (pol' : List (Event V (protoOf F ⟨d₁, h₁, d₂, h₂, a'⟩).Object) → V →
      (protoOf F ⟨d₁, h₁, d₂, h₂, a'⟩).Object → Time → Bool)
    (es : List (Event V (protoOf F ⟨d₁, h₁, d₂, h₂, a⟩).Object)) (t : Time) (v : V)
    (hav : a' v t = a v t) (hav' : a' v (t - 1) = a v (t - 1))
    (hbatch : (inj' t v ++ (ρ'.duePool delay (ρ'.front es t) t).filter
        (fun o => pol' (ρ'.front es t) v o t)).dedup =
      (inj t v ++ (ρ.duePool delay (ρ.front es t) t).filter
        (fun o => pol (ρ.front es t) v o t)).dedup) :
    (ρ'.injectLayer delay inj' pol' es t).filter (fun e => e.node = v) =
      (ρ.injectLayer delay inj pol es t).filter (fun e => e.node = v) := by
  classical
  have hw : (ρ'.wakeEvents t).filter (fun e => e.node = v) =
      (ρ.wakeEvents t).filter (fun e => e.node = v) := by
    rw [wakeEvents_eq, wakeEvents_eq, tw.faultyAt, filter_node_map _ (Finset.nodup_toList _) _
      (fun _ => rfl), filter_node_map _ (Finset.nodup_toList _) _ (fun _ => rfl)]
    split_ifs with h1 h2 h2
    · rfl
    · exfalso
      apply h2
      rw [Finset.mem_toList, Finset.mem_filter] at h1 ⊢
      obtain ⟨hm, h0, hw1, hw2⟩ := h1
      refine ⟨hm, h0, ?_, ?_⟩
      · change a v t = true; rw [← hav]; exact hw1
      · change a v (t - 1) = false; rw [← hav']; exact hw2
    · exfalso
      apply h1
      rw [Finset.mem_toList, Finset.mem_filter] at h2 ⊢
      obtain ⟨hm, h0, hw1, hw2⟩ := h2
      refine ⟨hm, h0, ?_, ?_⟩
      · change a' v t = true; rw [hav]; exact hw1
      · change a' v (t - 1) = false; rw [hav']; exact hw2
    · rfl
  have ht : (ρ'.tickEvents t).filter (fun e => e.node = v) =
      (ρ.tickEvents t).filter (fun e => e.node = v) := by
    rw [tickEvents_eq, tickEvents_eq, tw.faultyAt, filter_node_map _ (Finset.nodup_toList _) _
      (fun _ => rfl), filter_node_map _ (Finset.nodup_toList _) _ (fun _ => rfl)]
    split_ifs with h1 h2 h2
    · rfl
    · exfalso
      apply h2
      rw [Finset.mem_toList, Finset.mem_filter] at h1 ⊢
      exact ⟨h1.1, by change a v t = true; rw [← hav]; exact h1.2⟩
    · exfalso
      apply h1
      rw [Finset.mem_toList, Finset.mem_filter] at h2 ⊢
      exact ⟨h2.1, by change a' v t = true; rw [hav]; exact h2.2⟩
    · rfl
  have hd : (ρ'.injectDeliveries delay inj' pol' (ρ'.front es t) t).filter
        (fun e => e.node = v) =
      (ρ.injectDeliveries delay inj pol (ρ.front es t) t).filter (fun e => e.node = v) := by
    rw [injectDeliveries_eq, injectDeliveries_eq, tw.faultyAt,
      filter_node_flatMap _ (Finset.nodup_toList _) _ (fun x e he => by
        obtain ⟨o, -, rfl⟩ := List.mem_map.mp he; rfl),
      filter_node_flatMap _ (Finset.nodup_toList _) _ (fun x e he => by
        obtain ⟨o, -, rfl⟩ := List.mem_map.mp he; rfl)]
    split_ifs with h1 h2 h2
    · rw [hbatch]
    · exfalso
      apply h2
      rw [Finset.mem_toList, Finset.mem_filter] at h1 ⊢
      exact ⟨h1.1, by change a v t = true; rw [← hav]; exact h1.2⟩
    · exfalso
      apply h1
      rw [Finset.mem_toList, Finset.mem_filter] at h2 ⊢
      exact ⟨h2.1, by change a' v t = true; rw [hav]; exact h2.2⟩
    · rfl
  rw [injectLayer_eq, injectLayer_eq, List.filter_append, List.filter_append, List.filter_append,
    List.filter_append, hw, ht, hd]

/-- A batch that is not due at `t` adds nothing to the due batch at `t`. -/
theorem duePool_append_of_not_due (σ : Run F E) (delay : Event V (protoOf F E).Object → Time)
    (es X : List (Event V (protoOf F E).Object)) (t : Time)
    (hX : ∀ e ∈ X, t < e.time + delay e) : σ.duePool delay (es ++ X) t = σ.duePool delay es t := by
  classical
  rw [duePool_eq, duePool_eq, List.length_append, List.range_add, List.flatMap_append]
  have h2 : ((List.range X.length).map (es.length + ·)).flatMap (fun j =>
      if ∃ e, (es ++ X)[j]? = some e ∧ e.time + delay e ≤ t then
        (σ.withEvents (es ++ X)).releasesAt j else []) = [] := by
    refine List.flatMap_eq_nil_iff.mpr fun j hj => ?_
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hj
    split_ifs with hP
    · exfalso
      obtain ⟨e, he, hle⟩ := hP
      rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left] at he
      exact absurd hle (not_le.mpr (hX e (List.mem_of_getElem? he)))
    · rfl
  rw [h2, List.append_nil]
  congr 1
  refine List.flatMap_congr fun j hj => ?_
  have hjl := List.mem_range.mp hj
  rw [List.getElem?_append_left hjl, σ.releasesAt_append es X hjl]

/-- **A release of a node across a layer**: twin scheduled runs (with the same horizon) whose
first `n` stages agree release the same objects of `v` at `n` when `v` has the same awake bits and
inbox throughout and the same delivery batch at `n`. -/
theorem releases_twins_layer (tw : Twins ρ ρ')
    (delay : Event V (protoOf F ⟨d₁, h₁, d₂, h₂, a⟩).Object → Time)
    (inj : Time → V → List (protoOf F ⟨d₁, h₁, d₂, h₂, a⟩).Object)
    (inj' : Time → V → List (protoOf F ⟨d₁, h₁, d₂, h₂, a'⟩).Object)
    (pol : List (Event V (protoOf F ⟨d₁, h₁, d₂, h₂, a⟩).Object) → V →
      (protoOf F ⟨d₁, h₁, d₂, h₂, a⟩).Object → Time → Bool)
    (pol' : List (Event V (protoOf F ⟨d₁, h₁, d₂, h₂, a'⟩).Object) → V →
      (protoOf F ⟨d₁, h₁, d₂, h₂, a'⟩).Object → Time → Bool)
    {n : Nat} {v : V} (hhor : ρ'.horizon = ρ.horizon) (hn : (n : Time) ≤ ρ.horizon)
    (hst : ρ'.injectStages delay inj' pol' n = ρ.injectStages delay inj pol n)
    (hav : ∀ t, a' v t = a v t) (hinbox : ∀ t, ρ'.inbox v t = ρ.inbox v t)
    (hbatch : (inj' n v ++ (ρ'.duePool delay (ρ'.front (ρ.injectStages delay inj pol n) n) n).filter
        (fun o => pol' (ρ'.front (ρ.injectStages delay inj pol n) n) v o n)).dedup =
      (inj n v ++ (ρ.duePool delay (ρ.front (ρ.injectStages delay inj pol n) n) n).filter
        (fun o => pol (ρ.front (ρ.injectStages delay inj pol n) n) v o n)).dedup)
    {o : (protoOf F ⟨d₁, h₁, d₂, h₂, a⟩).Object} (hr : (ρ.injectRun delay inj pol).releases v o n) :
    (ρ'.injectRun delay inj' pol').releases v o n := by
  set S := ρ.injectStages delay inj pol (n + 1) with hS
  set S' := ρ'.injectStages delay inj' pol' (n + 1) with hS'
  have hN : n + 1 ≤ ρ.horizon.toNat + 1 := by
    have := Int.toNat_le_toNat hn
    simp only [Int.toNat_natCast] at this
    omega
  obtain ⟨tail, htail⟩ := ρ.injectStages_prefix delay inj pol hN
  obtain ⟨tail', htail'⟩ := ρ'.injectStages_prefix delay inj' pol'
    (show n + 1 ≤ ρ'.horizon.toNat + 1 by rw [hhor]; exact hN)
  have hfilt : S'.filter (fun e => e.node = v) = S.filter (fun e => e.node = v) := by
    rw [hS, hS', injectStages_succ, injectStages_succ, hst, List.filter_append,
      List.filter_append,
      injectLayer_filter_twins tw delay inj inj' pol pol' _ _ v (hav _) (hav _) hbatch]
  -- restrict the release to `S`
  change (ρ.withEvents (ρ.injectEvents delay inj pol)).releases v o n at hr
  rw [injectEvents_eq, htail] at hr
  have hin : ∀ e ∈ S ++ tail, e.node = v → e.time = (n : Time) → e ∈ S := by
    intro e he _ het
    rw [← htail] at he
    have h := ρ.mem_injectStages_of_time_lt _ inj pol he (a := (n : Time) + 1)
      (by rw [het]; exact lt_add_one _)
    rwa [show ((n : Time) + 1).toNat = n + 1 by omega] at h
  obtain ⟨i, hs, ho⟩ := ρ.releases_restrict _ tail (htail ▸ ρ.injectStages_nodup _ inj pol _) hin hr
  obtain ⟨e, he, hev, het⟩ := hs.exists_event
  rw [withEvents_events] at he
  have heS' : e ∈ S'.filter (fun e => e.node = v) := by
    rw [hfilt]
    exact List.mem_filter.mpr ⟨List.mem_of_getElem? he, by simp [hev]⟩
  obtain ⟨i', he'⟩ := List.mem_iff_getElem?.mp (List.mem_filter.mp heS').1
  have hpre := take_filter_eq (fun x => decide (x.node = v)) (ρ.injectStages_nodup _ inj pol _)
    (ρ'.injectStages_nodup _ inj' pol' _) hfilt he he' (by simp [hev])
  have hag : ∀ x, x.node = v → TickAgrees (ρ.withEvents S) (ρ'.withEvents S') x := by
    intro x hx u τ hxu
    subst hxu
    change u = v at hx
    subst hx
    refine ⟨hav τ, ?_⟩
    rw [withEvents_inbox, withEvents_inbox]
    exact mempool_twins fun k _ => hinbox k
  have hrel := releasesAt_twins_local (tw.withEvents S S') (i := i) (i' := i')
    (by rw [withEvents_events]; exact he) (by rw [withEvents_events]; exact he')
    (by rw [withEvents_events, withEvents_events, hev]; exact hpre)
    (fun x hx => hag x (by have := (List.mem_filter.mp hx).2; simpa [hev] using this))
    (hag e hev)
  have hs' : (ρ'.withEvents S').SendsAt v i' n := by
    rcases hs with h | ⟨p, h⟩
    · rw [withEvents_events] at h
      rw [he] at h
      exact Or.inl (by rw [withEvents_events, he', h])
    · rw [withEvents_events] at h
      rw [he] at h
      exact Or.inr ⟨p, by rw [withEvents_events, he', h]⟩
  change (ρ'.withEvents (ρ'.injectEvents delay inj' pol')).releases v o n
  rw [injectEvents_eq, htail']
  exact ρ'.releases_append _ tail' ⟨i', hs', by rw [hrel]; exact ho⟩

end Run

end Consensus.Model

end

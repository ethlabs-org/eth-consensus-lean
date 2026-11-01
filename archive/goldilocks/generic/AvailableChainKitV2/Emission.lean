module
public import AvailableChainKitV2.Stable

@[expose] public section

/-! Generic emission lemmas over engine v2 (plan 2a, Task 4; DC N7). They
replace the unfolding of `tick` in each protocol: the signed objects of a
tick (`mem_tick_seat_iff`), under a bijective seat map (`emits_bijSeat`),
seat indices under `Linked` (`linked_index_stable`), and the own record as a
fold over the released self-visible objects (`ownRecord_fold`). -/

namespace AvailableChain.V2.Engine

open AvailableChain

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}

/-! ### The signed objects of a tick -/

/-- The tick of `v` at time `t` from state `st` releases seat `i` of label
`ℓ` with payload `p` exactly when `v` is awake, `ℓ` is due at `t`, `v` holds
that seat, and `act` gives `p` in the post-clock state for the input of `v`
at `t`. -/
theorem mem_tick_seat_iff (E : Generic.Env V) (rho : Run V P) (st : P.State) (v : V)
    (t : Time) (ℓ : P.Label) (i : Fin (P.seats ℓ)) (p : P.Payload) :
    (⟨.seat ℓ i, p⟩ : P.Object) ∈ (tick E rho st v t).2 ↔
      E.awake v t = true ∧ P.actTime ℓ = t ∧ rho.seatOf ℓ i = v ∧
        P.act (P.clock st t) ℓ (rho.input v t) = some p := by
  simp only [tick]
  by_cases hw : E.awake v t = true
  · simp only [hw, ite_true, List.mem_append, List.mem_flatMap, List.mem_filterMap,
      Option.map_eq_some_iff, List.mem_map, true_and]
    constructor
    · rintro (⟨ℓ', hℓ', i', hi', p', hp', heq⟩ | ⟨p', -, heq⟩)
      · simp only [Signed.mk.injEq, Auth.seat.injEq] at heq
        obtain ⟨⟨rfl, hii⟩, rfl⟩ := heq
        cases eq_of_heq hii
        simp only [Run.ownSeats, List.mem_filter, decide_eq_true_eq] at hi'
        exact ⟨(P.duties_spec _ t).mp hℓ', hi'.2, hp'⟩
      · simp at heq
    · rintro ⟨hℓ, hi, hp⟩
      left
      refine ⟨ℓ, (P.duties_spec ℓ t).mpr hℓ, i, ?_, p, hp, rfl⟩
      simp [Run.ownSeats, hi]
  · simp [hw]

/-- Under a bijective seat map `e` of label `ℓ`, `v` holds exactly one seat of
`ℓ`, the seat `e.symm v`. -/
theorem ownSeats_bijSeat (rho : Run V P) {ℓ : P.Label} (e : Fin (P.seats ℓ) ≃ V)
    (he : ∀ i, rho.seatOf ℓ i = e i) (v : V) : rho.ownSeats ℓ v = [e.symm v] := by
  have hp : (fun i => decide (rho.seatOf ℓ i = v)) = (fun i => decide (i = e.symm v)) := by
    funext i
    simp only [he, ← e.eq_symm_apply]
  rw [Run.ownSeats, hp, List.filter_eq,
    List.count_eq_one_of_mem (List.nodup_finRange _) (List.mem_finRange _)]
  rfl

/-- Emission under a bijective seat map `e` of label `ℓ` (DC N7): the
label-`ℓ` objects that the tick of `v` releases are exactly `⟨.seat ℓ (e.symm
v), p⟩`, with `p` the payload of `act` in the post-clock state, when `v` is
awake and `ℓ` is due. `ownSeats_bijSeat` gives one such object per tick. -/
theorem emits_bijSeat (E : Generic.Env V) (rho : Run V P) {ℓ : P.Label}
    (e : Fin (P.seats ℓ) ≃ V) (he : ∀ i, rho.seatOf ℓ i = e i) (st : P.State) (v : V)
    (t : Time) (i : Fin (P.seats ℓ)) (p : P.Payload) :
    (⟨.seat ℓ i, p⟩ : P.Object) ∈ (tick E rho st v t).2 ↔
      i = e.symm v ∧ E.awake v t = true ∧ P.actTime ℓ = t ∧
        P.act (P.clock st t) ℓ (rho.input v t) = some p := by
  rw [mem_tick_seat_iff, he, ← e.eq_symm_apply]
  tauto

omit [DecidableEq V] in
/-- `Linked` index stability (DC N7): in a `Linked` family, equal seat
indices name one validator across labels. It replaces v1 `LinkedFG`. -/
theorem linked_index_stable {F : P.Label → Prop} {rho : Run V P} (hL : Linked F rho)
    {ℓ ℓ' : P.Label} (hℓ : F ℓ) (hℓ' : F ℓ') (i : Fin (P.seats ℓ)) (j : Fin (P.seats ℓ'))
    (hij : (i : Nat) = j) : rho.seatOf ℓ i = rho.seatOf ℓ' j := by
  obtain ⟨N, e, hF⟩ := hL
  obtain ⟨h, hs⟩ := hF ℓ hℓ
  obtain ⟨h', hs'⟩ := hF ℓ' hℓ'
  rw [hs, hs']
  congr 1
  exact Fin.ext hij

/-! ### The own record as a fold -/

/-- The self-visible objects that the event at index `k` releases, if it is
an event of `v` (only a tick releases objects). -/
def ownReleasedAt (E : Generic.Env V) (rho : Run V P) (v : V) (k : Nat) : List P.Object :=
  if (rho.events[k]?).map Event.node = some v then
    (Run.emitsAt E rho k).filter P.objSelfVisible
  else []

/-- The self-visible objects that `v` releases at the indices in `[i, j)`, in
event order and release order. -/
def ownReleased (E : Generic.Env V) (rho : Run V P) (v : V) (i j : Nat) : List P.Object :=
  (List.range' i (j - i)).flatMap (ownReleasedAt E rho v)

theorem ownReleased_self (E : Generic.Env V) (rho : Run V P) (v : V) (i : Nat) :
    ownReleased E rho v i i = [] := by
  simp [ownReleased]

theorem ownReleased_succ (E : Generic.Env V) (rho : Run V P) (v : V) {i j : Nat}
    (hij : i ≤ j) :
    ownReleased E rho v i (j + 1) = ownReleased E rho v i j ++ ownReleasedAt E rho v j := by
  have hr : List.range' i (j + 1 - i) = List.range' i (j - i) ++ [j] := by
    rw [show j + 1 - i = (j - i) + 1 by omega, List.range'_concat]
    congr 2
    omega
  simp [ownReleased, hr]

private theorem proj_foldl_recordOwn {β : Type} (proj : P.State → β)
    (g : β → P.Object → β) (hrecord : ∀ st o, proj (P.recordOwn st o) = g (proj st) o) :
    ∀ (l : List P.Object) (s : P.State), proj (l.foldl P.recordOwn s) = l.foldl g (proj s) := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons o rest ih =>
      intro s
      rw [List.foldl_cons, List.foldl_cons, ih, hrecord]

/-- The own record on a restart-free interval (DC N7, per epoch): for a
projection that `clock` and `process` keep and that `recordOwn` updates by
`g`, the value before `j` is the `g`-fold, from the value before `i`, over
the self-visible objects that `v` releases in `[i, j)`. -/
theorem ownRecord_fold_interval {β : Type} (proj : P.State → β) (g : β → P.Object → β)
    (hclock : ∀ st t, proj (P.clock st t) = proj st)
    (hprocess : ∀ st o, proj (P.process st o) = proj st)
    (hrecord : ∀ st o, proj (P.recordOwn st o) = g (proj st) o)
    (E : Generic.Env V) (rho : Run V P) {i j : Nat} (hij : i ≤ j) (v : V)
    (hrf : restartFree rho v i j) :
    proj (Run.stateBefore E rho j v) =
      (ownReleased E rho v i j).foldl g (proj (Run.stateBefore E rho i v)) := by
  induction j, hij using Nat.le_induction with
  | base => rw [ownReleased_self]; rfl
  | succ j hij ih =>
      rw [ownReleased_succ E rho v hij, List.foldl_append,
        ← ih (hrf.mono le_rfl (Nat.le_succ j))]
      cases he : rho.events[j]? with
      | none => simp [Run.stateBefore, List.take_add_one, he, ownReleasedAt]
      | some e =>
          rw [Run.stateBefore_succ E rho he]
          by_cases hv : e.node = v
          · cases e with
            | restart u t =>
                simp only [Event.node] at hv; subst u
                exact absurd he (hrf j t hij (Nat.lt_succ_self j))
            | tick u t =>
                simp only [Event.node] at hv; subst u
                have hemit := (Run.step_tick_eq E rho he).2
                simp only [ownReleasedAt, he, Option.map_some, Event.node, ite_true, hemit,
                  World.step, Function.update_self, tick_decomp]
                rw [proj_foldl_recordOwn proj g hrecord, hclock]
            | deliver u o t =>
                simp only [Event.node] at hv; subst u
                simp [ownReleasedAt, he, Run.emitsAt, World.step, hprocess]
          · rw [World.step_apply_of_node_ne E rho _ hv]
            simp [ownReleasedAt, he, hv]

/-- The own record as a fold (DC N7): without restarts, for a projection that
`clock` and `process` keep and that `recordOwn` updates by `g`, the value at
`stateBefore E rho i v` is the `g`-fold, from the initial value, over the
self-visible objects that `v` released before `i`. -/
theorem ownRecord_fold {β : Type} (proj : P.State → β) (g : β → P.Object → β)
    (hclock : ∀ st t, proj (P.clock st t) = proj st)
    (hprocess : ∀ st o, proj (P.process st o) = proj st)
    (hrecord : ∀ st o, proj (P.recordOwn st o) = g (proj st) o)
    (E : Generic.Env V) (rho : Run V P) (hnr : NoRestart rho) (i : Nat) (v : V) :
    proj (Run.stateBefore E rho i v) = (ownReleased E rho v 0 i).foldl g (proj P.init) := by
  rw [ownRecord_fold_interval proj g hclock hprocess hrecord E rho (Nat.zero_le i) v
    (hnr.restartFree v 0 i)]
  simp [Run.stateBefore, World.init]

/-- The own-record fold with an explicit restore preservation law. -/
theorem ownRecord_fold_interval_restart {β : Type} (proj : P.State → β) (g : β → P.Object → β)
    (hclock : ∀ st t, proj (P.clock st t) = proj st)
    (hprocess : ∀ st o, proj (P.process st o) = proj st)
    (hrecord : ∀ st o, proj (P.recordOwn st o) = g (proj st) o)
    (E : Generic.Env V) (rho : Run V P) {i j : Nat} (hij : i ≤ j) (v : V)
    (hrestart : ∀ k t, i ≤ k → k < j → rho.events[k]? = some (.restart v t) →
      proj (P.restore (P.durable (Run.stateBefore E rho k v)) t) =
        proj (Run.stateBefore E rho k v)) :
    proj (Run.stateBefore E rho j v) =
      (ownReleased E rho v i j).foldl g (proj (Run.stateBefore E rho i v)) := by
  induction j, hij using Nat.le_induction with
  | base => rw [ownReleased_self]; rfl
  | succ j hij ih =>
      rw [ownReleased_succ E rho v hij, List.foldl_append,
        ← ih (fun k t hik hkj => hrestart k t hik (Nat.lt_succ_of_lt hkj))]
      -- A step that is not a restart of `v`: the frozen core on `[j, j + 1)`.
      have hcore : restartFree rho v j (j + 1) →
          proj (Run.stateBefore E rho (j + 1) v) =
            (ownReleasedAt E rho v j).foldl g (proj (Run.stateBefore E rho j v)) := by
        intro hrf
        have h1 := ownRecord_fold_interval proj g hclock hprocess hrecord E rho
          (Nat.le_succ j) v hrf
        rwa [ownReleased_succ E rho v le_rfl, ownReleased_self, List.nil_append] at h1
      have hne : ∀ e : Event V P.Object, rho.events[j]? = some e →
          (∀ t, e ≠ .restart v t) → restartFree rho v j (j + 1) :=
        fun e he hnr k t hjk hkj heq => by
          rw [show k = j by omega, he] at heq
          exact hnr t (Option.some.inj heq)
      cases he : rho.events[j]? with
      | none =>
          exact hcore fun k t hjk hkj heq => by
            rw [show k = j by omega, he] at heq
            cases heq
      | some e =>
          cases e with
          | restart u t =>
              by_cases hu : u = v
              · subst hu
                rw [Run.stateBefore_succ E rho he]
                simp only [ownReleasedAt, he, Option.map_some]
                dsimp only [Event.node]
                simp only [ite_true, Run.emitsAt, he, List.filter_nil, List.foldl_nil,
                  World.step, Function.update_self]
                exact hrestart j t hij (Nat.lt_succ_self j) he
              · exact hcore (hne _ he fun t' h => hu (Event.restart.inj h).1)
          | tick u t => exact hcore (hne _ he fun t' h => by cases h)
          | deliver u o t => exact hcore (hne _ he fun t' h => by cases h)

/-- A durable record is the fold of all self-visible releases, even with
restarts. Sleep adds no releases and does not change this law. -/
theorem ownRecord_fold_restore {β : Type} (proj : P.State → β) (g : β → P.Object → β)
    (hclock : ∀ st t, proj (P.clock st t) = proj st)
    (hprocess : ∀ st o, proj (P.process st o) = proj st)
    (hrecord : ∀ st o, proj (P.recordOwn st o) = g (proj st) o)
    (hrestore : ∀ st t, proj (P.restore (P.durable st) t) = proj st)
    (E : Generic.Env V) (rho : Run V P) (i : Nat) (v : V) :
    proj (Run.stateBefore E rho i v) = (ownReleased E rho v 0 i).foldl g (proj P.init) := by
  rw [ownRecord_fold_interval_restart proj g hclock hprocess hrecord E rho
    (Nat.zero_le i) v (fun _ t _ _ _ => hrestore _ t)]
  rfl

end AvailableChain.V2.Engine

end

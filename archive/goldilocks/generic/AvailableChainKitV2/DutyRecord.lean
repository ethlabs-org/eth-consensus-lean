module
public import AvailableChainKitV2.DutyStable -- shake: keep (re-export)

public section

/-! Own-record folds for duty runs, including sleep and restart. -/

namespace AvailableChain.V2.D.Engine

open AvailableChain

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}

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

/-- The public equation for one event's self-visible releases. -/
theorem ownReleasedAt_def (E : Generic.Env V) (rho : Run V P) (v : V) (k : Nat) :
    ownReleasedAt E rho v k =
      if (rho.events[k]?).map Event.node = some v then
        (Run.emitsAt E rho k).filter P.objSelfVisible else [] := by
  rfl

/-- The public equation for releases on an index interval. -/
theorem ownReleased_def (E : Generic.Env V) (rho : Run V P) (v : V) (i j : Nat) :
    ownReleased E rho v i j =
      (List.range' i (j - i)).flatMap (ownReleasedAt E rho v) := by
  rfl

theorem ownReleased_self (E : Generic.Env V) (rho : Run V P) (v : V) (i : Nat) :
    ownReleased E rho v i i = [] := by
  simp [ownReleased_def]

theorem ownReleased_succ (E : Generic.Env V) (rho : Run V P) (v : V) {i j : Nat}
    (hij : i ≤ j) :
    ownReleased E rho v i (j + 1) = ownReleased E rho v i j ++ ownReleasedAt E rho v j := by
  have hr : List.range' i (j + 1 - i) = List.range' i (j - i) ++ [j] := by
    rw [show j + 1 - i = (j - i) + 1 by omega, List.range'_concat]
    congr 2
    omega
  simp [ownReleased_def, hr]

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
      | none => simp [Run.stateBefore, List.take_add_one, he, ownReleasedAt_def]
      | some e =>
          rw [Run.stateBefore_succ E rho he]
          by_cases hv : e.node = v
          · cases e with
            | restart u t =>
                dsimp only [Event.node] at hv; subst u
                exact absurd he (hrf j t hij (Nat.lt_succ_self j))
            | tick u t =>
                dsimp only [Event.node] at hv; subst u
                have hemit := (Run.step_tick_eq E rho he).2
                simp only [ownReleasedAt_def, he, Option.map_some]
                dsimp only [Event.node]
                simp only [ite_true, hemit, World.step, Function.update_self, tick_decomp]
                rw [proj_foldl_recordOwn proj g hrecord, hclock]
            | deliver u o t =>
                dsimp only [Event.node] at hv; subst u
                simp [ownReleasedAt_def, he, Run.emitsAt, World.step, hprocess]
          · rw [World.step_apply_of_node_ne E rho _ hv]
            simp [ownReleasedAt_def, he, hv]

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
  rfl

/-- The own-record fold on an interval that can contain restarts of `v`.
Each restart must keep the record projection. -/
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
                simp only [ownReleasedAt_def, he, Option.map_some]
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

end AvailableChain.V2.D.Engine

end

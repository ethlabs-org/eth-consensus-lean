module
public import AvailableChainKitV2.Emission

public section

namespace AvailableChain.Gen.V2

open AvailableChain AvailableChain.V2 AvailableChain.V2.Engine

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}

/-- L33 route R1: the own-record fold on an interval that may contain
restarts of `v`. -/
theorem ownRecord_fold_restart {β : Type} (proj : P.State → β) (g : β → P.Object → β)
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
                simp only [ownReleasedAt, he, Option.map_some, Event.node, ite_true,
                  Run.emitsAt, List.filter_nil, List.foldl_nil, World.step,
                  Function.update_self]
                exact hrestart j t hij (Nat.lt_succ_self j) he
              · exact hcore (hne _ he fun t' h => hu (Event.restart.inj h).1)
          | tick u t => exact hcore (hne _ he fun t' h => by cases h)
          | deliver u o t => exact hcore (hne _ he fun t' h => by cases h)

end AvailableChain.Gen.V2

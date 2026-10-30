module
public import ConsensusLean.Lemmas.Model.Objects
public import ConsensusLean.Lemmas.Model.Candidates

public section

/-! # Views (L1 proof support)

`seen` is append-only (`seen_succ`, `seen_mono`), and everything in it came
from a tick release or a delivery of that node before the cut
(`seen_source`). So `ViewIdx` (the closure of `seen`) is the event-index
formula: every object released or received before the cut, with everything
it carries (`mem_viewIdx_iff`). -/

namespace Consensus.Model

section Engine

variable {pub : Public} {Out : Type} {P : Protocol pub Out}

/-- `releaseAll` appends exactly what it releases to `seen`. -/
theorem releaseAll_seen (hash : P.Item → Nat) (k : Key pub) (nd : Node P)
    (cs : List P.Object) :
    (releaseAll P hash k nd cs).1.seen = nd.seen ++ (releaseAll P hash k nd cs).2 := by
  induction cs generalizing nd with
  | nil => simp [releaseAll]
  | cons c cs ih =>
    unfold releaseAll
    split
    · dsimp only
      rw [ih]
      simp
    · exact ih nd

end Engine

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : Family O} {E : Env V}

namespace Run

variable (rho : Run F E)

omit [DecidableEq V] in
/-- A tick appends exactly what it releases to `seen`. -/
theorem tick_seen (nd : Node (protoOf F E)) (v : V) (t : Time) :
    (rho.tick nd v t).1.seen = nd.seen ++ (rho.tick nd v t).2 := by
  obtain ⟨cs, -, h2, h1⟩ := rho.tick_flat nd v t
  rw [h1, h2]
  exact releaseAll_seen _ _ _ _

/-- What a tick releases is in the node's `seen` right after it. -/
theorem releasesAt_seen {i : Nat} {v : V} {t : Time} (he : rho.events[i]? = some (.tick v t))
    {o : (protoOf F E).Object} (ho : o ∈ rho.releasesAt i) :
    o ∈ (rho.stateBefore (i + 1) v).seen := by
  rw [rho.stateBefore_succ he]
  simp only [releasesAt, he] at ho
  simp only [step, Function.update_self]
  rw [tick_seen]
  exact List.mem_append_right _ ho

/-- `seen` is append-only: it grows by one event. -/
theorem seen_succ (i : Nat) (v : V) {o : (protoOf F E).Object}
    (ho : o ∈ (rho.stateBefore i v).seen) : o ∈ (rho.stateBefore (i + 1) v).seen := by
  cases he : rho.events[i]? with
  | none =>
    have hworld : rho.stateBefore (i + 1) = rho.stateBefore i := by
      simp [stateBefore, List.take_add_one, he]
    rw [hworld]
    exact ho
  | some e =>
    rw [rho.stateBefore_succ he]
    by_cases hw : e.node = v
    · cases e with
      | tick w t =>
        simp only [Event.node] at hw
        subst hw
        simp only [step, Function.update_self]
        rw [tick_seen]
        exact List.mem_append_left _ ho
      | deliver w p t =>
        simp only [Event.node] at hw
        subst hw
        simp only [step, Function.update_self]
        exact List.mem_append_left _ ho
      | restart w t =>
        simp only [Event.node] at hw
        subst hw
        simpa only [step, Function.update_self] using ho
    · cases e with
      | tick w t =>
        simp only [Event.node] at hw
        simpa only [step, Function.update_of_ne (Ne.symm hw)] using ho
      | deliver w p t =>
        simp only [Event.node] at hw
        simpa only [step, Function.update_of_ne (Ne.symm hw)] using ho
      | restart w t =>
        simp only [Event.node] at hw
        simpa only [step, Function.update_of_ne (Ne.symm hw)] using ho

/-- `seen` is append-only. -/
theorem seen_mono {i j : Nat} (hij : i ≤ j) (v : V) {o : (protoOf F E).Object}
    (ho : o ∈ (rho.stateBefore i v).seen) : o ∈ (rho.stateBefore j v).seen := by
  induction j, hij using Nat.le_induction with
  | base => exact ho
  | succ j _ ih => exact rho.seen_succ j v ih

/-- Everything in node `v`'s `seen` before cut `i` was released by `v` at a
tick, or delivered to `v`, at an event with index `< i`. -/
theorem seen_source {i : Nat} {v : V} {o : (protoOf F E).Object}
    (ho : o ∈ (rho.stateBefore i v).seen) :
    ∃ k, k < i ∧ ((∃ t, rho.events[k]? = some (Event.tick v t) ∧ o ∈ rho.releasesAt k) ∨
      ∃ t, rho.events[k]? = some (Event.deliver v o t)) := by
  induction i with
  | zero => simp [stateBefore, initWorld] at ho
  | succ i ih =>
    cases he : rho.events[i]? with
    | none =>
      have hworld : rho.stateBefore (i + 1) = rho.stateBefore i := by
        simp [stateBefore, List.take_add_one, he]
      rw [hworld] at ho
      obtain ⟨k, hk, h⟩ := ih ho
      exact ⟨k, by omega, h⟩
    | some e =>
      rw [rho.stateBefore_succ he] at ho
      have hold : o ∈ (rho.stateBefore i v).seen →
          ∃ k, k < i + 1 ∧ ((∃ t, rho.events[k]? = some (Event.tick v t) ∧
            o ∈ rho.releasesAt k) ∨ ∃ t, rho.events[k]? = some (Event.deliver v o t)) := by
        intro h
        obtain ⟨k, hk, h⟩ := ih h
        exact ⟨k, by omega, h⟩
      by_cases hw : e.node = v
      · cases e with
        | tick w t =>
          simp only [Event.node] at hw
          subst hw
          simp only [step, Function.update_self] at ho
          rw [tick_seen] at ho
          rcases List.mem_append.mp ho with h | h
          · exact hold h
          · exact ⟨i, by omega, Or.inl ⟨t, he, by simpa [releasesAt, he] using h⟩⟩
        | deliver w p t =>
          simp only [Event.node] at hw
          subst hw
          simp only [step, Function.update_self] at ho
          rcases List.mem_append.mp ho with h | h
          · exact hold h
          · rw [List.mem_singleton.mp h]
            exact ⟨i, by omega, Or.inr ⟨t, he⟩⟩
        | restart w t =>
          simp only [Event.node] at hw
          subst hw
          simp only [step, Function.update_self] at ho
          exact hold ho
      · cases e with
        | tick w t =>
          simp only [Event.node] at hw
          exact hold (by simpa only [step, Function.update_of_ne (Ne.symm hw)] using ho)
        | deliver w p t =>
          simp only [Event.node] at hw
          exact hold (by simpa only [step, Function.update_of_ne (Ne.symm hw)] using ho)
        | restart w t =>
          simp only [Event.node] at hw
          exact hold (by simpa only [step, Function.update_of_ne (Ne.symm hw)] using ho)

/-- `ViewIdx` (the closure of `seen`) is the event-index formula: every object
released or received by `v` at an event with index `< i`, with everything it
carries. -/
theorem mem_viewIdx_iff {v : V} {i : Nat} {o : (protoOf F E).Object} :
    o ∈ rho.ViewIdx v i ↔ ∃ k o₀, k < i ∧
      ((∃ t, rho.events[k]? = some (Event.tick v t) ∧ o₀ ∈ rho.releasesAt k) ∨
        ∃ t, rho.events[k]? = some (Event.deliver v o₀ t)) ∧ Obj.Contains o₀ o := by
  change o ∈ closure (rho.stateBefore i v).seen ↔ _
  simp only [closure, List.mem_flatMap]
  constructor
  · rintro ⟨o₀, h₀, hc⟩
    obtain ⟨k, hk, h⟩ := rho.seen_source h₀
    exact ⟨k, o₀, hk, h, hc⟩
  · rintro ⟨k, o₀, hk, hev, hc⟩
    have h₀ : o₀ ∈ (rho.stateBefore (k + 1) v).seen := by
      rcases hev with ⟨t, he, hr⟩ | ⟨t, he⟩
      · exact rho.releasesAt_seen he hr
      · rw [rho.stateBefore_succ he]
        simp only [step, Function.update_self]
        exact List.mem_append_right _ (List.mem_singleton_self _)
    exact ⟨o₀, rho.seen_mono hk v h₀, hc⟩

/-- Views only grow. -/
theorem viewIdx_mono {i j : Nat} (hij : i ≤ j) (v : V) : rho.ViewIdx v i ⊆ rho.ViewIdx v j := by
  intro o ho
  change o ∈ closure _ at ho ⊢
  simp only [closure, List.mem_flatMap] at ho ⊢
  obtain ⟨o₀, h₀, hc⟩ := ho
  exact ⟨o₀, rho.seen_mono hij v h₀, hc⟩

end Run

end Consensus.Model

end

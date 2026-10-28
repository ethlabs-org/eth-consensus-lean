module
public import ConsensusModelProofs.Canonical.Events

@[expose] public section

/-! A general engine invariant: causal receipt of released roots implies
unforgeability of every nested authentication. The seen filter makes this
independent of all protocol state transitions, including restart and restore. -/

namespace Consensus.Model

/-- The seen filter preserves any predicate on all structural descendants,
provided the roots of the objects actually released satisfy it. -/
theorem releaseAll_preserves {pub : Public} {P : Protocol pub}
    (hash : P.Item → Nat) (Q : P.Object → Prop) (nd : Node P) (cs : List P.Object)
    (hs : ∀ o ∈ nd.seen, ∀ d, Obj.Contains o d → Q d)
    (hr : ∀ o ∈ (releaseAll hash nd cs).2, Q o) :
    (∀ o ∈ (releaseAll hash nd cs).1.seen, ∀ d, Obj.Contains o d → Q d) ∧
    (∀ o ∈ (releaseAll hash nd cs).2, ∀ d, Obj.Contains o d → Q d) := by
  induction cs generalizing nd with
  | nil => exact ⟨hs, by simp [releaseAll]⟩
  | cons c cs ih =>
    unfold releaseAll at hr ⊢
    split at hr
    next hf =>
      simp only [hf, ↓reduceIte]
      have hc : ∀ d, Obj.Contains c d → Q d := by
        intro d hd
        cases hd with
        | refl => exact hr c List.mem_cons_self
        | step hm hc =>
          have hm' := List.all_eq_true.mp hf _ hm
          have hmem : _ ∈ closure nd.seen := of_decide_eq_true hm'
          obtain ⟨o, ho, hoc⟩ := (mem_closure_iff _ _).mp hmem
          exact hs o ho d (hoc.trans hc)
      have hs' : ∀ o ∈ (nd.seen ++ [c]), ∀ d, Obj.Contains o d → Q d := by
        intro o ho
        rcases List.mem_append.mp ho with ho | ho
        · exact hs o ho
        · rcases List.mem_singleton.mp ho with rfl
          exact hc
      have hrec := ih ⟨P.recordOwn nd.st c (digests hash c), nd.seen ++ [c]⟩ hs'
        (fun o ho => hr o (List.mem_cons_of_mem c ho))
      refine ⟨hrec.1, ?_⟩
      intro o ho
      rcases List.mem_cons.mp ho with rfl | ho
      · exact hc
      · exact hrec.2 o ho
    next hf =>
      simp only [hf]
      exact ih nd hs hr

theorem releaseAll_subset {pub : Public} {P : Protocol pub} (hash : P.Item → Nat) (nd : Node P)
    (cs : List P.Object) : ∀ o ∈ (releaseAll hash nd cs).2, o ∈ cs := by
  induction cs generalizing nd with
  | nil => simp [releaseAll]
  | cons c cs ih =>
    unfold releaseAll
    split
    · intro o ho
      rcases List.mem_cons.mp ho with rfl | ho
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem c (ih _ o ho)
    · exact fun o ho => List.mem_cons_of_mem c (ih _ o ho)

variable {V : Type} [Fintype V] [DecidableEq V] {F : Family} {E : Env V}
namespace Run
variable (rho : Run F E)

/-- Root receipts are causal. The engine's seen filter strengthens this to
causality for every carried authentication. -/
def Causal : Prop :=
  ∀ i w o t, rho.events[i]? = some (.deliver w o t) →
    ∃ j v t', j < i ∧ rho.events[j]? = some (.tick v t') ∧ o ∈ rho.releasesAt j

def SignedBefore (i : Nat) (o : (protoOf F E).Object) : Prop :=
  ∀ u ∈ rho.honest, rho.holderOf o.auth = some u →
    ∃ j t, j < i ∧ rho.events[j]? = some (.tick u t) ∧ o ∈ rho.releasesAt j

def SafeBefore (i : Nat) (o : (protoOf F E).Object) : Prop :=
  ∀ d, Obj.Contains o d → rho.SignedBefore i d

theorem signedBefore_mono {i j : Nat} (hij : i ≤ j) {o : (protoOf F E).Object}
    (h : rho.SignedBefore i o) : rho.SignedBefore j o := by
  intro u hu hh
  obtain ⟨k, t, hk, he, ho⟩ := h u hu hh
  exact ⟨k, t, lt_of_lt_of_le hk hij, he, ho⟩

theorem safeBefore_mono {i j : Nat} (hij : i ≤ j) {o : (protoOf F E).Object}
    (h : rho.SafeBefore i o) : rho.SafeBefore j o :=
  fun d hd => rho.signedBefore_mono hij (h d hd)

/-- Every signed candidate is signed by the node running the tick. -/
theorem candidates_holder (st : (protoOf F E).State) (v : V) (t : Time)
    {o : (protoOf F E).Object} (ho : o ∈ rho.candidates st v t) :
    rho.holderOf o.auth = none ∨ rho.holderOf o.auth = some v := by
  unfold candidates at ho
  rcases List.mem_append.mp ho with hs | hg
  · obtain ⟨d, _, hd⟩ := List.mem_flatMap.mp hs
    cases ha : (protoOf F E).act st d with
    | none => simp [ha] at hd
    | some mc =>
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (by simpa [ha] using hd)
      have hi' : rho.holder ((protoOf F E).label d) i = v := by
        simpa [ownSeats] using (List.mem_filter.mp hi).2
      exact Or.inr (by simp [holderOf, Obj.auth, hi'])
  · obtain ⟨bc, _, rfl⟩ := List.mem_map.mp hg
    exact Or.inl rfl

theorem stateBefore_succ {i : Nat} {e : Event V (protoOf F E).Object}
    (hi : rho.events[i]? = some e) :
    rho.stateBefore (i + 1) = rho.step (rho.stateBefore i) e := by
  simp only [stateBefore, List.take_add_one, hi, Option.toList_some, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

theorem tick_safe {i : Nat} {v : V} {t : Time}
    (hi : rho.events[i]? = some (.tick v t))
    (hs : ∀ o ∈ (rho.stateBefore i v).seen, rho.SafeBefore i o) :
    (∀ o ∈ (rho.tick (rho.stateBefore i v) v t).1.seen, rho.SafeBefore (i + 1) o) ∧
    (∀ o ∈ rho.releasesAt i, rho.SafeBefore (i + 1) o) := by
  have hr : ∀ o ∈ (rho.tick (rho.stateBefore i v) v t).2,
      rho.SignedBefore (i + 1) o := by
    intro o ho u hu hholder
    have hc : o ∈ rho.candidates
        ((protoOf F E).clock (rho.stateBefore i v).st t (mempool rho.submit v t)) v t := by
      unfold tick at ho
      split at ho
      · exact releaseAll_subset _ _ _ o ho
      · simp at ho
    rcases rho.candidates_holder _ v t hc with hn | hv
    · rw [hn] at hholder; cases hholder
    · have huv : u = v := Option.some.inj (hholder.symm.trans hv)
      subst u
      exact ⟨i, t, Nat.lt_succ_self i, hi, by simpa only [releasesAt, hi] using ho⟩
  change _ ∧ ∀ o ∈ rho.releasesAt i, _
  simp only [releasesAt, hi]
  unfold tick at hr ⊢
  split at hr
  · simp only [‹E.awake v t = true›, ↓reduceIte]
    exact releaseAll_preserves rho.hash (rho.SignedBefore (i + 1)) _ _
      (fun o ho d hd => rho.signedBefore_mono (Nat.le_succ i) (hs o ho d hd)) hr
  · simp only [‹¬ E.awake v t = true›, Bool.not_eq_true] at *
    exact ⟨fun o ho => rho.safeBefore_mono (Nat.le_succ i) (hs o ho), by simp⟩

/-- Causal delivery of roots is enough for full structural unforgeability. -/
theorem unforgeable_of_causal (hc : rho.Causal) : rho.Unforgeable := by
  have inv : ∀ i, (∀ v o, o ∈ (rho.stateBefore i v).seen → rho.SafeBefore i o) ∧
      (∀ o ∈ rho.releasesAt i, rho.SafeBefore (i + 1) o) := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      have hseen : ∀ v o, o ∈ (rho.stateBefore i v).seen → rho.SafeBefore i o := by
        cases i with
        | zero => simp [stateBefore, initWorld]
        | succ k =>
          have old := (ih k (Nat.lt_succ_self k)).1
          cases he : rho.events[k]? with
          | none =>
            have hworld : rho.stateBefore (k + 1) = rho.stateBefore k := by
              simp [stateBefore, List.take_add_one, he]
            rw [hworld]
            exact fun v o ho => rho.safeBefore_mono (Nat.le_succ k) (old v o ho)
          | some e =>
            rw [rho.stateBefore_succ he]
            cases e with
            | tick v t =>
              have hsafe := (rho.tick_safe he (old v)).1
              intro w o ho
              by_cases hw : w = v
              · subst w; exact hsafe o (by simpa [step] using ho)
              · exact rho.safeBefore_mono (Nat.le_succ k) (old w o (by simpa [step, hw] using ho))
            | restart v t =>
              intro w o ho
              by_cases hw : w = v
              · subst w
                exact rho.safeBefore_mono (Nat.le_succ k) (old v o (by simpa [step] using ho))
              · exact rho.safeBefore_mono (Nat.le_succ k) (old w o (by simpa [step, hw] using ho))
            | deliver v p t =>
              obtain ⟨j, u, t', hj, hjt, hp⟩ := hc k v p t he
              have hsafe : rho.SafeBefore (k + 1) p :=
                rho.safeBefore_mono (by omega) ((ih j (by omega)).2 p hp)
              intro w o ho
              by_cases hw : w = v
              · subst w
                have hm : o ∈ (rho.stateBefore k v).seen ++ [p] := by simpa [step] using ho
                rcases List.mem_append.mp hm with hm | hm
                · exact rho.safeBefore_mono (Nat.le_succ k) (old v o hm)
                · rcases List.mem_singleton.mp hm with rfl
                  exact hsafe
              · exact rho.safeBefore_mono (Nat.le_succ k) (old w o (by simpa [step, hw] using ho))
      refine ⟨hseen, ?_⟩
      cases he : rho.events[i]? with
      | none => simp [releasesAt, he]
      | some e =>
        cases e with
        | tick v t => exact (rho.tick_safe he (hseen v)).2
        | deliver v p t => simp [releasesAt, he]
        | restart v t => simp [releasesAt, he]
  intro i w o t hi d hd u hu hh
  obtain ⟨j, v, t', hj, he, ho⟩ := hc i w o t hi
  have hs := (inv j).2 o ho d hd u hu hh
  obtain ⟨k, t'', hk, hkt, hko⟩ := hs
  exact ⟨k, t'', by omega, hkt, hko⟩

end Run
end Consensus.Model
end

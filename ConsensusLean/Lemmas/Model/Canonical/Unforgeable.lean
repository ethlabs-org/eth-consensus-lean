module
public import ConsensusLean.Lemmas.Model.Canonical.Events
public import ConsensusLean.Lemmas.Model.Candidates

public section

/-! A general engine invariant: causal receipt of released roots implies
unforgeability of every nested authentication. The seen filter makes this
independent of all protocol state transitions, including restart and restore. -/

namespace Consensus.Model

/-- The seen filter preserves any predicate on all structural descendants,
provided the roots of the objects actually released satisfy it. -/
theorem releaseAll_preserves {pub : Public} {Out : Type} {P : Protocol pub Out}
    (hash : P.Item → Nat) (k : Key pub) (Q : P.Object → Prop) (nd : Node P) (cs : List P.Object)
    (hs : ∀ o ∈ nd.seen, ∀ d, Obj.Contains o d → Q d)
    (hr : ∀ o ∈ (releaseAll P hash k nd cs).2, Q o) :
    (∀ o ∈ (releaseAll P hash k nd cs).1.seen, ∀ d, Obj.Contains o d → Q d) ∧
    (∀ o ∈ (releaseAll P hash k nd cs).2, ∀ d, Obj.Contains o d → Q d) := by
  induction cs generalizing nd with
  | nil => exact ⟨hs, by simp [releaseAll]⟩
  | cons c cs ih =>
    unfold releaseAll at hr ⊢
    split at hr
    next hf =>
      simp only [hf, ↓reduceIte]
      have hc : ∀ d, Obj.Contains c d → Q d := by
        intro d hd
        rcases hd.cases with rfl | ⟨_, hm, hc⟩
        · exact hr d List.mem_cons_self
        · have hm' := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hf).1 _ hm
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

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : Family O} {E : Env V}
namespace Run
variable (rho : Run F E)

/-- Root receipts are causal. The engine's seen filter strengthens this to
causality for every carried authentication. -/
def Causal : Prop :=
  ∀ i w o t, rho.events[i]? = some (.deliver w o t) →
    ∃ j v t', j < i ∧ rho.events[j]? = some (.tick v t') ∧ o ∈ rho.releasesAt j

def SignedBefore (i : Nat) (o : (protoOf F E).Object) : Prop :=
  ∀ u ∈ rho.honest, rho.signerOf o = some u →
    ∃ j t, j < i ∧ rho.events[j]? = some (.tick u t) ∧ o ∈ rho.releasesAt j

def SafeBefore (i : Nat) (o : (protoOf F E).Object) : Prop :=
  ∀ d, Obj.Contains o d → rho.SignedBefore i d

variable {rho} in
theorem causal_iff : rho.Causal ↔ ∀ i w o t, rho.events[i]? = some (.deliver w o t) →
    ∃ j v t', j < i ∧ rho.events[j]? = some (.tick v t') ∧ o ∈ rho.releasesAt j := Iff.rfl

variable {rho} in
theorem signedBefore_iff {i : Nat} {o : (protoOf F E).Object} : rho.SignedBefore i o ↔
    ∀ u ∈ rho.honest, rho.signerOf o = some u →
      ∃ j t, j < i ∧ rho.events[j]? = some (.tick u t) ∧ o ∈ rho.releasesAt j := Iff.rfl

variable {rho} in
theorem safeBefore_iff {i : Nat} {o : (protoOf F E).Object} :
    rho.SafeBefore i o ↔ ∀ d, Obj.Contains o d → rho.SignedBefore i d := Iff.rfl

theorem signedBefore_mono {i j : Nat} (hij : i ≤ j) {o : (protoOf F E).Object}
    (h : rho.SignedBefore i o) : rho.SignedBefore j o := by
  intro u hu hh
  obtain ⟨k, t, hk, he, ho⟩ := h u hu hh
  exact ⟨k, t, lt_of_lt_of_le hk hij, he, ho⟩

theorem safeBefore_mono {i j : Nat} (hij : i ≤ j) {o : (protoOf F E).Object}
    (h : rho.SafeBefore i o) : rho.SafeBefore j o :=
  fun d hd => rho.signedBefore_mono hij (h d hd)

theorem tick_safe {i : Nat} {v : V} {t : Time}
    (hi : rho.events[i]? = some (.tick v t))
    (hs : ∀ o ∈ (rho.stateBefore i v).seen, rho.SafeBefore i o) :
    (∀ o ∈ (rho.tick (rho.stateBefore i v) v t).1.seen, rho.SafeBefore (i + 1) o) ∧
    (∀ o ∈ rho.releasesAt i, rho.SafeBefore (i + 1) o) := by
  have hr : ∀ o ∈ (rho.tick (rho.stateBefore i v) v t).2,
      rho.SignedBefore (i + 1) o := by
    intro o ho u hu hsigner
    rcases rho.tick_signerOf _ v t ho with hn | hv
    · rw [hn] at hsigner; cases hsigner
    · have huv : u = v := Option.some.inj (hsigner.symm.trans hv)
      subst u
      exact ⟨i, t, Nat.lt_succ_self i, hi, by simpa only [releasesAt, hi] using ho⟩
  change _ ∧ ∀ o ∈ rho.releasesAt i, _
  simp only [releasesAt, hi]
  obtain ⟨cs, -, h2, h1⟩ := rho.tick_flat (rho.stateBefore i v) v t
  rw [h2] at hr ⊢
  rw [h1]
  exact releaseAll_preserves rho.hash _ (rho.SignedBefore (i + 1)) _ _
    (fun o ho d hd => rho.signedBefore_mono (Nat.le_succ i) (hs o ho d hd)) hr

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

/-- A released object comes from the releasing tick (event `i`, from node
`rho.stateBefore i u`): it is a signed duty candidate at a state the tick
reaches from its post-clock state, whose mempool is the node's mempool at the
tick, or gossip at the state after the tick's duties. -/
theorem releases_provenance {u : V} {o : (protoOf F E).Object} {τ : Time}
    (h : rho.releases u o τ) :
    ∃ i, rho.events[i]? = some (.tick u τ) ∧
      (rho.DutyCandidate
          ((protoOf F E).clock (rho.stateBefore i u).st τ (mempool rho.inbox u τ)) u τ o ∨
        o ∈ gossipCandidates (protoOf F E)
          (rho.runDuties u
            ⟨(protoOf F E).clock (rho.stateBefore i u).st τ (mempool rho.inbox u τ),
              (rho.stateBefore i u).seen⟩ ((protoOf F E).duties τ)).1.st τ) := by
  obtain ⟨i, hi, ho⟩ := h
  simp only [releasesAt, hi] at ho
  obtain ⟨cs, hcs, h2, -⟩ := rho.tick_flat (rho.stateBefore i u) u τ
  rw [h2] at ho
  exact ⟨i, hi, hcs o (releaseAll_subset _ _ _ _ o ho)⟩

end Run
end Consensus.Model
end

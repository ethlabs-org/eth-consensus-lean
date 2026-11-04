module
public import ConsensusLean.Lemmas.Model.Canonical.Events
public import ConsensusLean.Lemmas.Model.Candidates
public import ConsensusLean.Lemmas.Model.View

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
        · have hm' := List.all_eq_true.mp
            (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hf).1).1 _ hm
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

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : ProtocolFamily O}
    {E : Env V}
namespace Run
variable (rho : Run F E)

/-- Root receipts are causal. The engine's seen filter strengthens this to
causality for every carried authentication. -/
def Causal : Prop :=
  ∀ i w o t, rho.events[i]? = some (.deliver w o t) →
    ∃ j v t', j < i ∧ rho.SendsAt v j t' ∧ o ∈ rho.releasesAt j

/-- Causality restricts to an event prefix. -/
theorem causal_prefix (xs ys : List (Event V (protoOf F E).Object))
    (hc : (rho.withEvents (xs ++ ys)).Causal) : (rho.withEvents xs).Causal := by
  rw [withEvents_eq] at hc ⊢
  intro i v o t hi
  have hil : i < xs.length := (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨j, w, s, hj, hs, hr⟩ := hc i v o t
    ((List.getElem?_append_left hil).trans hi)
  refine ⟨j, w, s, hj, ?_, ?_⟩
  · rcases hs with hs | ⟨q, hs⟩
    · exact Or.inl ((List.getElem?_append_left (lt_trans hj hil)).symm.trans hs)
    · exact Or.inr ⟨q, (List.getElem?_append_left (lt_trans hj hil)).symm.trans hs⟩
  · have he := rho.releasesAt_append xs ys (lt_trans hj hil)
    rw [withEvents_eq, withEvents_eq] at he
    rwa [he] at hr

/-- In a causal run every held root has an earlier release, including roots
received at the current sender from a different validator. -/
theorem seen_released_before (hc : rho.Causal) {i : Nat} {v : V}
    {o : (protoOf F E).Object} (ho : o ∈ (rho.stateBefore i v).seen) :
    ∃ j < i, o ∈ rho.releasesAt j := by
  obtain ⟨j, hj, hs | ⟨t, ht⟩⟩ := rho.seen_source ho
  · obtain ⟨_, _, hr⟩ := hs
    exact ⟨j, hj, hr⟩
  · obtain ⟨k, _, _, hk, _, hr⟩ := hc j v o t ht
    exact ⟨k, lt_trans hk hj, hr⟩

/-- A causal release depends only on roots released earlier, including earlier
positions in the same engine event. No extra tick is needed for a dependency. -/
theorem release_ready_of_prefix (hc : rho.Causal) (i p : Nat)
    (o : (protoOf F E).Object) (ho : (rho.releasesAt i)[p]? = some o)
    (held : List (protoOf F E).Object)
    (hprev : ∀ j < i, ∀ a ∈ rho.releasesAt j, a ∈ held)
    (hsame : ∀ a ∈ (rho.releasesAt i).take p, a ∈ held) :
    (protoOf F E).dependencies.ready (closure held) o = true := by
  have hseen (v : V) : (rho.stateBefore i v).seen ⊆ held := by
    intro a ha
    obtain ⟨j, hj, hr⟩ := rho.seen_released_before hc ha
    exact hprev j hj a hr
  have hclosure {xs : List (protoOf F E).Object} (hx : xs ⊆ held) :
      closure xs ⊆ closure held := by
    intro a ha
    obtain ⟨root, hr, hd⟩ := (mem_closure_iff xs a).mp ha
    exact (mem_closure_iff held a).mpr ⟨root, hx hr, hd⟩
  cases he : rho.events[i]? with
  | none => simp [releasesAt, he] at ho
  | some e =>
    cases e with
    | restart v t => simp [releasesAt, he] at ho
    | tick v t =>
      have hr := rho.tick_ready (rho.stateBefore i v) v t p o
        (by simpa only [releasesAt, he] using ho)
      apply (protoOf F E).dependencies.mono _ _ _ (hclosure ?_) hr
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hseen v ha
      · apply hsame a
        simpa only [releasesAt, he] using ha
    | deliver v q t =>
      have hr := rho.deliver_ready (rho.stateBefore i v) v q t p o
        (by simpa only [releasesAt, he] using ho)
      apply (protoOf F E).dependencies.mono _ _ _ (hclosure ?_) hr
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · rcases List.mem_append.mp ha with ha | ha
        · exact hseen v ha
        · have haq := List.mem_singleton.mp ha
          obtain ⟨j, _, _, hj, _, hq⟩ := hc i v q t he
          exact haq ▸ hprev j hj q hq
      · apply hsame a
        simpa only [releasesAt, he] using ha

/-- Flattening event-local release lists preserves the causal dependency order. -/
theorem release_ready_flat (hc : rho.Causal) (n p : Nat)
    (o : (protoOf F E).Object)
    (ho : ((List.range n).flatMap rho.releasesAt)[p]? = some o) :
    (protoOf F E).dependencies.ready
      (closure (((List.range n).flatMap rho.releasesAt).take p)) o = true := by
  induction n with
  | zero => simp at ho
  | succ n ih =>
    let xs := (List.range n).flatMap rho.releasesAt
    have he : (List.range (n + 1)).flatMap rho.releasesAt = xs ++ rho.releasesAt n := by
      simp [List.range_succ, xs]
    rw [he] at ho ⊢
    by_cases hp : p < xs.length
    · rw [List.getElem?_append_left hp] at ho
      rw [List.take_append_of_le_length hp.le]
      exact ih ho
    · have hp' : xs.length ≤ p := Nat.le_of_not_gt hp
      rw [List.getElem?_append_right hp'] at ho
      rw [List.take_append, List.take_of_length_le hp']
      apply rho.release_ready_of_prefix hc n (p - xs.length) o ho
      · intro j hj a ha
        exact List.mem_append_left _ (List.mem_flatMap.mpr
          ⟨j, List.mem_range.mpr hj, ha⟩)
      · intro a ha
        exact List.mem_append_right _ ha

/-- Deduplicating by first occurrence keeps every release dependency in the
earlier pool prefix. -/
theorem pool_ready (hc : rho.Causal) (p : Nat) (o : (protoOf F E).Object)
    (ho : (rho.pool rho.events)[p]? = some o) :
    (protoOf F E).dependencies.ready
      (closure ((rho.pool rho.events).take p)) o = true := by
  have he : rho.withEvents rho.events = rho := by rw [withEvents_eq]
  rw [pool_eq, he] at ho ⊢
  obtain ⟨i, hi, hsub⟩ := firstRelease_prefix _ p o ho
  apply (protoOf F E).dependencies.mono _ _ _ ?_ (rho.release_ready_flat hc _ i o hi)
  intro a ha
  obtain ⟨r, hr, hd⟩ := (mem_closure_iff _ a).mp ha
  exact (mem_closure_iff _ a).mpr ⟨r, hsub hr, hd⟩

def SignedBefore (i : Nat) (o : (protoOf F E).Object) : Prop :=
  ∀ u ∈ rho.honest, rho.signerOf o = some u →
    ∃ j t, j < i ∧ rho.SendsAt u j t ∧ o ∈ rho.releasesAt j

def SafeBefore (i : Nat) (o : (protoOf F E).Object) : Prop :=
  ∀ d, Obj.Contains o d → rho.SignedBefore i d

variable {rho} in
theorem causal_iff : rho.Causal ↔ ∀ i w o t, rho.events[i]? = some (.deliver w o t) →
    ∃ j v t', j < i ∧ rho.SendsAt v j t' ∧ o ∈ rho.releasesAt j := Iff.rfl

variable {rho} in
theorem signedBefore_iff {i : Nat} {o : (protoOf F E).Object} : rho.SignedBefore i o ↔
    ∀ u ∈ rho.honest, rho.signerOf o = some u →
      ∃ j t, j < i ∧ rho.SendsAt u j t ∧ o ∈ rho.releasesAt j := Iff.rfl

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
      exact ⟨i, t, Nat.lt_succ_self i, Or.inl hi, by simpa only [releasesAt, hi] using ho⟩
  change _ ∧ ∀ o ∈ rho.releasesAt i, _
  simp only [releasesAt, hi]
  obtain ⟨cs, -, h2, h1⟩ := rho.tick_flat (rho.stateBefore i v) v t
  rw [h2] at hr ⊢
  rw [h1]
  exact releaseAll_preserves rho.hash _ (rho.SignedBefore (i + 1)) _ _
    (fun o ho d hd => rho.signedBefore_mono (Nat.le_succ i) (hs o ho d hd)) hr

/-- A delivery of an object safe before it keeps `seen` safe and releases only
safe objects: the twin of `tick_safe`, from the processed `seen ++ [p]`. -/
theorem deliver_safe {i : Nat} {v : V} {p : (protoOf F E).Object} {t : Time}
    (hi : rho.events[i]? = some (.deliver v p t))
    (hs : ∀ o ∈ (rho.stateBefore i v).seen, rho.SafeBefore i o) (hp : rho.SafeBefore i p) :
    (∀ o ∈ (rho.deliver (rho.stateBefore i v) v p t).1.seen, rho.SafeBefore (i + 1) o) ∧
    (∀ o ∈ rho.releasesAt i, rho.SafeBefore (i + 1) o) := by
  have hr : ∀ o ∈ (rho.deliver (rho.stateBefore i v) v p t).2,
      rho.SignedBefore (i + 1) o := by
    intro o ho u hu hsigner
    rcases rho.deliver_signerOf _ v p t ho with hn | hv
    · rw [hn] at hsigner; cases hsigner
    · have huv : u = v := Option.some.inj (hsigner.symm.trans hv)
      subst u
      exact ⟨i, t, Nat.lt_succ_self i, Or.inr ⟨p, hi⟩, by simpa only [releasesAt, hi] using ho⟩
  have hs' : ∀ o ∈ (rho.stateBefore i v).seen ++ [p], rho.SafeBefore i o := by
    intro o ho
    rcases List.mem_append.mp ho with ho | ho
    · exact hs o ho
    · rw [List.mem_singleton.mp ho]; exact hp
  change _ ∧ ∀ o ∈ rho.releasesAt i, _
  simp only [releasesAt, hi]
  obtain ⟨cs, -, h2, h1⟩ := rho.deliver_flat (rho.stateBefore i v) v p t
  rw [h2] at hr ⊢
  rw [h1]
  exact releaseAll_preserves rho.hash _ (rho.SignedBefore (i + 1)) _ _
    (fun o ho d hd => rho.signedBefore_mono (Nat.le_succ i) (hs' o ho d hd)) hr

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
              have hsafe := (rho.deliver_safe he (old v)
                (rho.safeBefore_mono (by omega) ((ih j (by omega)).2 p hp))).1
              intro w o ho
              by_cases hw : w = v
              · subst w; exact hsafe o (by simpa [step] using ho)
              · exact rho.safeBefore_mono (Nat.le_succ k) (old w o (by simpa [step, hw] using ho))
      refine ⟨hseen, ?_⟩
      cases he : rho.events[i]? with
      | none => simp [releasesAt, he]
      | some e =>
        cases e with
        | tick v t => exact (rho.tick_safe he (hseen v)).2
        | deliver v p t =>
          obtain ⟨j, u, t', hj, hjt, hp⟩ := hc i v p t he
          exact (rho.deliver_safe he (hseen v)
            (rho.safeBefore_mono (by omega) ((ih j hj).2 p hp))).2
        | restart v t => simp [releasesAt, he]
  intro i w o t hi d hd u hu hh
  obtain ⟨j, v, t', hj, he, ho⟩ := hc i w o t hi
  have hs := (inv j).2 o ho d hd u hu hh
  obtain ⟨k, t'', hk, hkt, hko⟩ := hs
  exact ⟨k, t'', by omega, hkt, hko⟩

/-- A released object comes from the releasing event `i`, from node
`rho.stateBefore i u`. At a tick: a signed duty candidate at a state the tick
reaches from its post-clock state, whose mempool is the node's mempool at the
tick, or gossip at the state after the tick's duties. At a delivery of `p`: a
signed delivery-duty candidate at a state the delivery reaches from the
processed state, or gossip at the state after the delivery duties. -/
theorem releases_provenance {u : V} {o : (protoOf F E).Object} {τ : Time}
    (h : rho.releases u o τ) :
    (∃ i, rho.events[i]? = some (.tick u τ) ∧
      (rho.DutyCandidate
          ((protoOf F E).clock (rho.stateBefore i u).st τ (mempool rho.inbox u τ)) u τ o ∨
        o ∈ gossipCandidates (protoOf F E)
          (rho.runDuties u
            ⟨(protoOf F E).clock (rho.stateBefore i u).st τ (mempool rho.inbox u τ),
              (rho.stateBefore i u).seen⟩ ((protoOf F E).duties τ)).1.st τ)) ∨
    ∃ i p, rho.events[i]? = some (.deliver u p τ) ∧
      (rho.DeliverCandidate
          ((protoOf F E).process (rho.stateBefore i u).st p (digests rho.hash p)) u τ o ∨
        o ∈ gossipCandidates (protoOf F E)
          (rho.runDuties u
            ⟨(protoOf F E).process (rho.stateBefore i u).st p (digests rho.hash p),
              (rho.stateBefore i u).seen ++ [p]⟩ ((protoOf F E).deliverDuties τ)).1.st τ) := by
  obtain ⟨i, hi | ⟨p, hi⟩, ho⟩ := h
  · simp only [releasesAt, hi] at ho
    obtain ⟨cs, hcs, h2, -⟩ := rho.tick_flat (rho.stateBefore i u) u τ
    rw [h2] at ho
    exact Or.inl ⟨i, hi, hcs o (releaseAll_subset _ _ _ _ o ho)⟩
  · simp only [releasesAt, hi] at ho
    obtain ⟨cs, hcs, h2, -⟩ := rho.deliver_flat (rho.stateBefore i u) u p τ
    rw [h2] at ho
    exact Or.inr ⟨i, p, hi, hcs o (releaseAll_subset _ _ _ _ o ho)⟩

end Run
end Consensus.Model
end

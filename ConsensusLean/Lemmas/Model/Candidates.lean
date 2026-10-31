module
public import ConsensusLean.Spec.Model.System
public import ConsensusLean.Lemmas.Problem.Facts.Transfer
public import ConsensusLean.Lemmas.Problem.Facts.Good
public import ConsensusLean.Lemmas.Model.Protocol

public section

/-! # Engine candidates

What the engine releases at a tick, and where it comes from.

`releaseAll`'s decisions and the `seen` it leaves depend only on `seen`
(`releaseAll_seen_only`), and releasing a concatenation is releasing its parts
in turn (`releaseAll_append`). So a tick, whose duties apply `act`'s state and
release their candidates one after the other and whose gossip comes last,
releases what one `releaseAll` call from its starting `seen` releases on the
tick's candidates (`Run.tick_flat`): signed duty candidates at states the tick
reaches (`TickReach`, `Run.DutyCandidate`), and gossip at the state after the
tick's duties (`Run.runDuties`). Every released object is unsigned, or signed
with the node's own key in a role that selects that key (`Run.tick_auth`). A
property of states that the duties and the records of released objects keep
holds after the tick
(`Run.tick_invariant`); the tick ends in a reached state (`Run.tick_reach`). -/

namespace Consensus.Model

section Engine

variable {pub : Public} {Out : Type} {P : Protocol pub Out}

/-- `releaseAll` releases only candidates. -/
theorem releaseAll_subset (hash : P.Item → Nat) (k : Key pub) (nd : Node P)
    (cs : List P.Object) : ∀ o ∈ (releaseAll P hash k nd cs).2, o ∈ cs := by
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

/-- A release is ready at any receiver holding the sender's initial objects
and all preceding releases of this call. This includes same-event release order. -/
theorem releaseAll_ready (hash : P.Item → Nat) (k : Key pub) (nd : Node P)
    (cs : List P.Object) :
    ∀ i o, (releaseAll P hash k nd cs).2[i]? = some o →
      P.dependencies.ready
        (closure (nd.seen ++ (releaseAll P hash k nd cs).2.take i)) o = true := by
  induction cs generalizing nd with
  | nil => simp [releaseAll]
  | cons c cs ih =>
    simp only [releaseAll]
    split
    next hf =>
      intro i o ho
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at ho
        subst o
        simpa using (Bool.and_eq_true_iff.mp hf).2
      | succ i =>
        simp only [List.getElem?_cons_succ] at ho
        have h := ih ⟨P.recordOwn nd.st c (digests hash c), nd.seen ++ [c]⟩ i o ho
        simpa only [List.take_succ_cons, List.append_assoc, List.singleton_append] using h
    next hf => exact ih nd

/-- What `releaseAll` releases and the `seen` it leaves depend only on `seen`,
not on the state. -/
theorem releaseAll_seen_only (hash : P.Item → Nat) (k : Key pub) {nd nd' : Node P}
    (h : nd.seen = nd'.seen) (cs : List P.Object) :
    (releaseAll P hash k nd cs).2 = (releaseAll P hash k nd' cs).2 ∧
      (releaseAll P hash k nd cs).1.seen = (releaseAll P hash k nd' cs).1.seen := by
  induction cs generalizing nd nd' with
  | nil => simp [releaseAll, h]
  | cons c cs ih =>
    simp only [releaseAll, h]
    by_cases hf : (releasable nd'.seen c && protects P k nd'.seen c &&
      P.dependencies.ready (closure nd'.seen) c) = true
    · simp only [hf, ↓reduceIte]
      have h' := ih (nd := ⟨P.recordOwn nd.st c (digests hash c), nd'.seen ++ [c]⟩)
        (nd' := ⟨P.recordOwn nd'.st c (digests hash c), nd'.seen ++ [c]⟩) rfl
      exact ⟨by rw [h'.1], h'.2⟩
    · simp only [hf, Bool.false_eq_true, ↓reduceIte]
      exact ih h

/-- Releasing `cs ++ cs'` is releasing `cs`, then `cs'` from the node it left. -/
theorem releaseAll_append (hash : P.Item → Nat) (k : Key pub) (nd : Node P)
    (cs cs' : List P.Object) :
    releaseAll P hash k nd (cs ++ cs') =
      ((releaseAll P hash k (releaseAll P hash k nd cs).1 cs').1,
        (releaseAll P hash k nd cs).2 ++
          (releaseAll P hash k (releaseAll P hash k nd cs).1 cs').2) := by
  induction cs generalizing nd with
  | nil => simp [releaseAll]
  | cons c cs ih =>
    simp only [List.cons_append, releaseAll]
    by_cases hf : (releasable nd.seen c && protects P k nd.seen c &&
      P.dependencies.ready (closure nd.seen) c) = true
    · simp only [hf, ↓reduceIte, ih, List.cons_append]
    · simp only [hf, Bool.false_eq_true, ↓reduceIte, ih]

/-- The states a tick may reach from `st` with the duties `ds`: the closure of
`st` under `(P.act · d).1` for `d ∈ ds` and under `recordOwn`. An
over-approximation of a tick's intermediate states: it allows any order and
any repetition of the due duties and any `recordOwn` argument. -/
inductive TickReach (P : Protocol pub Out) (ds : List P.Duty) (st : P.State) : P.State → Prop
  | refl : TickReach P ds st st
  | act {s : P.State} {d : P.Duty} :
      d ∈ ds → TickReach P ds st s → TickReach P ds st (P.act s d).1
  | recordOwn {s : P.State} (o : P.Object) (hs : List (P.Item × Nat)) :
      TickReach P ds st s → TickReach P ds st (P.recordOwn s o hs)

/-- A property of states that holds at `st` and is kept by the duties of `ds`
and by `recordOwn` holds at every state a tick reaches from `st`. -/
theorem TickReach.invariant {ds : List P.Duty} {st : P.State} (Q : P.State → Prop)
    (h₀ : Q st) (ha : ∀ s, ∀ d ∈ ds, Q s → Q (P.act s d).1)
    (hr : ∀ s o hs, Q s → Q (P.recordOwn s o hs)) {s : P.State} (h : TickReach P ds st s) :
    Q s := by
  induction h with
  | refl => exact h₀
  | act hd _ ih => exact ha _ _ hd ih
  | recordOwn o hs _ ih => exact hr _ o hs ih

/-- `releaseAll` from a reached state leaves a reached state. -/
theorem releaseAll_reach {ds : List P.Duty} {st : P.State} (hash : P.Item → Nat)
    (k : Key pub) (nd : Node P) (cs : List P.Object) (h : TickReach P ds st nd.st) :
    TickReach P ds st (releaseAll P hash k nd cs).1.st := by
  induction cs generalizing nd with
  | nil => simpa [releaseAll] using h
  | cons c cs ih =>
    simp only [releaseAll]
    split
    · exact ih _ (.recordOwn _ _ h)
    · exact ih _ h

/-- A property of states kept by `recordOwn` of every released object holds
after `releaseAll`. -/
theorem releaseAll_invariant (Q : P.State → Prop) (hash : P.Item → Nat) (k : Key pub)
    (nd : Node P) (cs : List P.Object)
    (hrec : ∀ s o hs, o ∈ (releaseAll P hash k nd cs).2 → Q s → Q (P.recordOwn s o hs))
    (h : Q nd.st) : Q (releaseAll P hash k nd cs).1.st := by
  induction cs generalizing nd with
  | nil => exact h
  | cons c cs ih =>
    simp only [releaseAll] at hrec ⊢
    by_cases hf : (releasable nd.seen c && protects P k nd.seen c &&
      P.dependencies.ready (closure nd.seen) c) = true
    · simp only [hf, ↓reduceIte] at hrec ⊢
      exact ih _ (fun s o hs ho => hrec s o hs (List.mem_cons_of_mem _ ho))
        (hrec _ c _ List.mem_cons_self h)
    · simp only [hf, Bool.false_eq_true, ↓reduceIte] at hrec ⊢
      exact ih _ hrec h

/-- What `gossipCandidates` gives: the gossip messages, unsigned. -/
theorem mem_gossipCandidates {st : P.State} {t : Time} {o : P.Object} :
    o ∈ gossipCandidates P st t ↔ ∃ mc ∈ P.gossip st t, o = .mk .none mc.1 mc.2 := by
  simp [gossipCandidates, eq_comm]

end Engine

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : Family O} {E : Env V}

namespace Run
variable (rho : Run F E)

omit [DecidableEq V] in
/-- What `signedCandidate` gives: `act`'s message, signed with the own key in
the duty's role, if that role selects the key. -/
theorem mem_signedCandidate {v : V} {d : (protoOf F E).Duty}
    {a : List (Msg (protoOf F E).Item (protoOf F E).Body × List (protoOf F E).Object)}
    {o : (protoOf F E).Object} :
    o ∈ rho.signedCandidate v d a ↔
      ∃ m cs, (m, cs) ∈ a ∧ rho.ownKey v ∈ rho.sel ((protoOf F E).role d) ∧
        o = .mk (.signed (rho.ownKey v) ((protoOf F E).role d)) m cs := by
  by_cases hk : rho.ownKey v ∈ rho.sel ((protoOf F E).role d)
  · simp [signedCandidate, hk, eq_comm]
  · simp [signedCandidate, hk]

omit [DecidableEq V] in
private theorem foldl_duties_acc (v : V) (ds : List (protoOf F E).Duty)
    (nd : Node (protoOf F E)) (rel : List (protoOf F E).Object) :
    ds.foldl (fun r d => let s := rho.dutyStep v r.1 d; (s.1, r.2 ++ s.2)) (nd, rel) =
      ((rho.runDuties v nd ds).1, rel ++ (rho.runDuties v nd ds).2) := by
  induction ds generalizing nd rel with
  | nil => simp [runDuties]
  | cons d ds ih =>
    change ds.foldl (fun r d => let s := rho.dutyStep v r.1 d; (s.1, r.2 ++ s.2))
        ((rho.dutyStep v nd d).1, rel ++ (rho.dutyStep v nd d).2) =
      ((ds.foldl (fun r d => let s := rho.dutyStep v r.1 d; (s.1, r.2 ++ s.2))
          ((rho.dutyStep v nd d).1, [] ++ (rho.dutyStep v nd d).2)).1,
        rel ++ (ds.foldl (fun r d => let s := rho.dutyStep v r.1 d; (s.1, r.2 ++ s.2))
          ((rho.dutyStep v nd d).1, [] ++ (rho.dutyStep v nd d).2)).2)
    rw [List.nil_append, ih, ih, List.append_assoc]

omit [DecidableEq V] in
theorem runDuties_nil (v : V) (nd : Node (protoOf F E)) : rho.runDuties v nd [] = (nd, []) := by
  rfl

omit [DecidableEq V] in
/-- The first duty, then the rest from the node it left. -/
theorem runDuties_cons (v : V) (nd : Node (protoOf F E)) (d : (protoOf F E).Duty)
    (ds : List (protoOf F E).Duty) :
    rho.runDuties v nd (d :: ds) =
      ((rho.runDuties v (rho.dutyStep v nd d).1 ds).1,
        (rho.dutyStep v nd d).2 ++ (rho.runDuties v (rho.dutyStep v nd d).1 ds).2) := by
  change ds.foldl (fun r d => let s := rho.dutyStep v r.1 d; (s.1, r.2 ++ s.2))
    ((rho.dutyStep v nd d).1, [] ++ (rho.dutyStep v nd d).2) = _
  rw [List.nil_append]
  exact foldl_duties_acc rho v ds _ _

omit [DecidableEq V] in
theorem dutyStep_eq (v : V) (nd : Node (protoOf F E)) (d : (protoOf F E).Duty) :
    rho.dutyStep v nd d =
      if rho.ownKey v ∈ rho.sel ((protoOf F E).role d) then
        releaseAll (protoOf F E) rho.hash (rho.ownKey v) ⟨((protoOf F E).act nd.st d).1, nd.seen⟩
          (rho.signedCandidate v d ((protoOf F E).act nd.st d).2)
      else (nd, []) := by
  rfl

omit [DecidableEq V] in
/-- A tick at an awake time: the duties from the post-clock state, then gossip. -/
theorem tick_of_awake (nd : Node (protoOf F E)) (v : V) (t : Time)
    (hw : E.awake v t = true) :
    rho.tick nd v t =
      ((releaseAll (protoOf F E) rho.hash (rho.ownKey v)
          (rho.runDuties v ⟨(protoOf F E).clock nd.st t (mempool rho.inbox v t), nd.seen⟩
            ((protoOf F E).duties t)).1
          (gossipCandidates (protoOf F E)
            (rho.runDuties v ⟨(protoOf F E).clock nd.st t (mempool rho.inbox v t), nd.seen⟩
              ((protoOf F E).duties t)).1.st t)).1,
        (rho.runDuties v ⟨(protoOf F E).clock nd.st t (mempool rho.inbox v t), nd.seen⟩
          ((protoOf F E).duties t)).2 ++
        (releaseAll (protoOf F E) rho.hash (rho.ownKey v)
          (rho.runDuties v ⟨(protoOf F E).clock nd.st t (mempool rho.inbox v t), nd.seen⟩
            ((protoOf F E).duties t)).1
          (gossipCandidates (protoOf F E)
            (rho.runDuties v ⟨(protoOf F E).clock nd.st t (mempool rho.inbox v t), nd.seen⟩
              ((protoOf F E).duties t)).1.st t)).2) := by
  change (if E.awake v t = true then _ else _) = _
  simp only [hw, ↓reduceIte]

omit [DecidableEq V] in
/-- A tick at an asleep time: the clock only. -/
theorem tick_of_asleep (nd : Node (protoOf F E)) (v : V) (t : Time)
    (hw : E.awake v t = false) :
    rho.tick nd v t = (⟨(protoOf F E).clock nd.st t (mempool rho.inbox v t), nd.seen⟩, []) := by
  change (if E.awake v t = true then _ else _) = _
  simp only [hw, Bool.false_eq_true, ↓reduceIte]

omit [DecidableEq V] in
/-- A property of states kept by the duties and by `recordOwn` of every
released object holds after the duties. -/
theorem runDuties_invariant (Q : (protoOf F E).State → Prop) (v : V)
    (ds : List (protoOf F E).Duty) (nd : Node (protoOf F E))
    (hact : ∀ s, ∀ d ∈ ds, Q s → Q ((protoOf F E).act s d).1)
    (hrec : ∀ s o hs, o ∈ (rho.runDuties v nd ds).2 → Q s → Q ((protoOf F E).recordOwn s o hs))
    (h : Q nd.st) : Q (rho.runDuties v nd ds).1.st := by
  induction ds generalizing nd with
  | nil => exact h
  | cons d ds ih =>
    rw [runDuties_cons] at hrec ⊢
    apply ih _ (fun s d' hd' => hact s d' (List.mem_cons_of_mem _ hd'))
      (fun s o hs ho => hrec s o hs (List.mem_append_right _ ho))
    by_cases hk : rho.ownKey v ∈ rho.sel ((protoOf F E).role d)
    · simp only [dutyStep, hk, ↓reduceIte] at hrec ⊢
      exact releaseAll_invariant Q _ _ _ _
        (fun s o hs ho => hrec s o hs (List.mem_append_left _ ho))
        (hact _ d List.mem_cons_self h)
    · simpa [dutyStep, hk] using h

omit [DecidableEq V] in
/-- A property of states that holds after the clock and is kept by the due
duties and by `recordOwn` of every object the tick releases holds after the
tick. -/
theorem tick_invariant (Q : (protoOf F E).State → Prop) (nd : Node (protoOf F E)) (v : V)
    (t : Time) (hact : ∀ s, ∀ d ∈ (protoOf F E).duties t, Q s → Q ((protoOf F E).act s d).1)
    (hrec : ∀ s o hs, o ∈ (rho.tick nd v t).2 → Q s → Q ((protoOf F E).recordOwn s o hs))
    (h₁ : Q ((protoOf F E).clock nd.st t (mempool rho.inbox v t))) :
    Q (rho.tick nd v t).1.st := by
  cases hw : E.awake v t
  · rw [rho.tick_of_asleep nd v t hw]
    exact h₁
  · rw [rho.tick_of_awake nd v t hw] at hrec ⊢
    exact releaseAll_invariant Q _ _ _ _
      (fun s o hs ho => hrec s o hs (List.mem_append_right _ ho))
      (rho.runDuties_invariant Q v _ _ hact
        (fun s o hs ho => hrec s o hs (List.mem_append_left _ ho)) h₁)

omit [DecidableEq V] in
/-- The tick ends in a state it reaches from the post-clock state. -/
theorem tick_reach (nd : Node (protoOf F E)) (v : V) (t : Time) :
    TickReach (protoOf F E) ((protoOf F E).duties t)
      ((protoOf F E).clock nd.st t (mempool rho.inbox v t)) (rho.tick nd v t).1.st :=
  rho.tick_invariant _ nd v t (fun _ _ hd hs => .act hd hs) (fun _ o hs _ h => .recordOwn o hs h)
    .refl

/-- A signed duty candidate of node `v`'s tick at `t` whose post-clock state
is `st₁`: the candidate of a due duty at a state the tick reaches. -/
def DutyCandidate (st₁ : (protoOf F E).State) (v : V) (t : Time)
    (o : (protoOf F E).Object) : Prop :=
  ∃ d ∈ (protoOf F E).duties t, ∃ st,
    TickReach (protoOf F E) ((protoOf F E).duties t) st₁ st ∧
      o ∈ rho.signedCandidate v d ((protoOf F E).act st d).2

omit [DecidableEq V] in
theorem dutyCandidate_iff {st₁ : (protoOf F E).State} {v : V} {t : Time}
    {o : (protoOf F E).Object} : rho.DutyCandidate st₁ v t o ↔
      ∃ d ∈ (protoOf F E).duties t, ∃ st,
        TickReach (protoOf F E) ((protoOf F E).duties t) st₁ st ∧
          o ∈ rho.signedCandidate v d ((protoOf F E).act st d).2 := Iff.rfl

omit [DecidableEq V] in
private theorem foldl_duties_flat (v : V) (ds dsAll : List (protoOf F E).Duty)
    (hds : ∀ d ∈ ds, d ∈ dsAll) (st₁ : (protoOf F E).State) (nd : Node (protoOf F E))
    (rel : List (protoOf F E).Object) (h : TickReach (protoOf F E) dsAll st₁ nd.st) :
    ∃ cs : List (protoOf F E).Object,
      (∀ c ∈ cs, ∃ d ∈ dsAll, ∃ st, TickReach (protoOf F E) dsAll st₁ st ∧
        c ∈ rho.signedCandidate v d ((protoOf F E).act st d).2) ∧
      (ds.foldl (fun r d => let s := rho.dutyStep v r.1 d; (s.1, r.2 ++ s.2)) (nd, rel)).2 =
        rel ++ (releaseAll (protoOf F E) rho.hash (rho.ownKey v) nd cs).2 ∧
      (ds.foldl (fun r d => let s := rho.dutyStep v r.1 d; (s.1, r.2 ++ s.2))
          (nd, rel)).1.seen =
        (releaseAll (protoOf F E) rho.hash (rho.ownKey v) nd cs).1.seen ∧
      TickReach (protoOf F E) dsAll st₁
        (ds.foldl (fun r d => let s := rho.dutyStep v r.1 d; (s.1, r.2 ++ s.2))
          (nd, rel)).1.st := by
  induction ds generalizing nd rel with
  | nil => exact ⟨[], by simp, by simp [releaseAll], by simp [releaseAll], h⟩
  | cons d ds ih =>
    by_cases hk : rho.ownKey v ∈ rho.sel ((protoOf F E).role d)
    case neg =>
      simpa only [List.foldl_cons, dutyStep, hk, ↓reduceIte, List.append_nil] using
        ih (fun d hd => hds d (List.mem_cons_of_mem _ hd)) nd rel h
    simp only [List.foldl_cons]
    have hstep : rho.dutyStep v nd d = releaseAll (protoOf F E) rho.hash (rho.ownKey v)
        ⟨((protoOf F E).act nd.st d).1, nd.seen⟩
        (rho.signedCandidate v d ((protoOf F E).act nd.st d).2) := by
      simp only [dutyStep, hk, ↓reduceIte]
    have hreach : TickReach (protoOf F E) dsAll st₁ (rho.dutyStep v nd d).1.st := by
      rw [hstep]
      exact releaseAll_reach _ _ _ _ (.act (hds d List.mem_cons_self) h)
    obtain ⟨cs, hcs, h2, h1, h3⟩ := ih (fun d hd => hds d (List.mem_cons_of_mem _ hd))
      (rho.dutyStep v nd d).1 (rel ++ (rho.dutyStep v nd d).2) hreach
    have hso := releaseAll_seen_only rho.hash (rho.ownKey v)
      (nd := ⟨((protoOf F E).act nd.st d).1, nd.seen⟩) (nd' := nd) rfl
      (rho.signedCandidate v d ((protoOf F E).act nd.st d).2)
    have hso' := releaseAll_seen_only rho.hash (rho.ownKey v) hso.2 cs
    refine ⟨rho.signedCandidate v d ((protoOf F E).act nd.st d).2 ++ cs, ?_, ?_, ?_, h3⟩
    · intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact ⟨d, hds d List.mem_cons_self, nd.st, h, hc⟩
      · exact hcs c hc
    · rw [h2, releaseAll_append, List.append_assoc, hstep, hso.1, hso'.1]
    · rw [h1, releaseAll_append, hstep, hso'.2]

omit [DecidableEq V] in
/-- The tick releases what one `releaseAll` call from its starting `seen`
releases on the tick's candidates, and leaves the same `seen`: the candidates
are signed duty candidates at states the tick reaches from the post-clock
state, and gossip at the state after the tick's duties
(`runDuties` from the post-clock node). The protocol states are not related:
flattening drops the duties' local updates between releases. -/
theorem tick_flat (nd : Node (protoOf F E)) (v : V) (t : Time) :
    ∃ cs : List (protoOf F E).Object,
      (∀ c ∈ cs,
        rho.DutyCandidate ((protoOf F E).clock nd.st t (mempool rho.inbox v t)) v t c ∨
          c ∈ gossipCandidates (protoOf F E)
            (rho.runDuties v ⟨(protoOf F E).clock nd.st t (mempool rho.inbox v t), nd.seen⟩
              ((protoOf F E).duties t)).1.st t) ∧
      (rho.tick nd v t).2 = (releaseAll (protoOf F E) rho.hash (rho.ownKey v) nd cs).2 ∧
      (rho.tick nd v t).1.seen =
        (releaseAll (protoOf F E) rho.hash (rho.ownKey v) nd cs).1.seen := by
  by_cases hw : E.awake v t = true
  · obtain ⟨cs, hcs, h2, h1, -⟩ := foldl_duties_flat rho v ((protoOf F E).duties t)
      ((protoOf F E).duties t) (fun _ hd => hd)
      ((protoOf F E).clock nd.st t (mempool rho.inbox v t))
      ⟨(protoOf F E).clock nd.st t (mempool rho.inbox v t), nd.seen⟩ [] .refl
    generalize hR : rho.runDuties v
      ⟨(protoOf F E).clock nd.st t (mempool rho.inbox v t), nd.seen⟩ ((protoOf F E).duties t) = R
    have hR' := hR
    unfold runDuties at hR'
    rw [hR'] at h1 h2
    have htick : rho.tick nd v t =
        ((releaseAll (protoOf F E) rho.hash (rho.ownKey v) R.1
            (gossipCandidates (protoOf F E) R.1.st t)).1,
          R.2 ++ (releaseAll (protoOf F E) rho.hash (rho.ownKey v) R.1
            (gossipCandidates (protoOf F E) R.1.st t)).2) := by
      rw [← hR]
      change (if E.awake v t = true then _ else _) = _
      simp only [hw, ↓reduceIte]
    have hso := releaseAll_seen_only rho.hash (rho.ownKey v)
      (nd := ⟨(protoOf F E).clock nd.st t (mempool rho.inbox v t), nd.seen⟩) (nd' := nd) rfl cs
    have hseen : R.1.seen = (releaseAll (protoOf F E) rho.hash (rho.ownKey v) nd cs).1.seen :=
      h1.trans hso.2
    have hgo := releaseAll_seen_only rho.hash (rho.ownKey v) hseen
      (gossipCandidates (protoOf F E) R.1.st t)
    refine ⟨cs ++ gossipCandidates (protoOf F E) R.1.st t, ?_, ?_, ?_⟩
    · intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact Or.inl (hcs c hc)
      · exact Or.inr hc
    · rw [htick, releaseAll_append, h2, List.nil_append, hso.1, hgo.1]
    · rw [htick, releaseAll_append, hgo.2]
  · have htick : rho.tick nd v t =
        (⟨(protoOf F E).clock nd.st t (mempool rho.inbox v t), nd.seen⟩, []) := by
      change (if E.awake v t = true then _ else _) = _
      simp only [hw, Bool.false_eq_true, ↓reduceIte]
    exact ⟨[], by simp, by simp [htick, releaseAll], by simp [htick, releaseAll]⟩

omit [DecidableEq V] in
/-- Tick releases satisfy dependencies using only holdings and earlier releases. -/
theorem tick_ready (nd : Node (protoOf F E)) (v : V) (t : Time) (i : Nat)
    (o : (protoOf F E).Object) (ho : (rho.tick nd v t).2[i]? = some o) :
    (protoOf F E).dependencies.ready
      (closure (nd.seen ++ (rho.tick nd v t).2.take i)) o = true := by
  obtain ⟨cs, _, h2, _⟩ := rho.tick_flat nd v t
  rw [h2] at ho ⊢
  exact releaseAll_ready rho.hash (rho.ownKey v) nd cs i o ho

omit [DecidableEq V] in
/-- Every object a tick of `v` releases is unsigned, or signed with `v`'s own
key in a role whose selection contains that key. -/
theorem tick_auth (nd : Node (protoOf F E)) (v : V) (t : Time) {o : (protoOf F E).Object}
    (ho : o ∈ (rho.tick nd v t).2) :
    o.auth = .none ∨ ∃ r, o.auth = .signed (rho.ownKey v) r ∧ rho.ownKey v ∈ rho.sel r := by
  obtain ⟨cs, hcs, h2, -⟩ := rho.tick_flat nd v t
  rw [h2] at ho
  rcases hcs o (releaseAll_subset _ _ _ _ o ho) with ⟨d, -, st, -, hc⟩ | hc
  · obtain ⟨m, cs, -, hk, rfl⟩ := (rho.mem_signedCandidate).mp hc
    exact Or.inr ⟨_, rfl, hk⟩
  · obtain ⟨mc, -, rfl⟩ := mem_gossipCandidates.mp hc
    exact Or.inl rfl

omit [DecidableEq V] in
/-- Every object a tick of `v` releases is unsigned or signed by `v`'s own
key. -/
theorem tick_signer (nd : Node (protoOf F E)) (v : V) (t : Time) {o : (protoOf F E).Object}
    (ho : o ∈ (rho.tick nd v t).2) :
    o.signer? = none ∨ o.signer? = some (rho.ownKey v) := by
  rcases rho.tick_auth nd v t ho with h | ⟨r, h, _⟩
  · exact Or.inl (by simp [Obj.signer?, h])
  · exact Or.inr (by simp [Obj.signer?, h])

omit [DecidableEq V] in
/-- Every signed object a tick releases is signed by a key selected for its
role. -/
theorem tick_selected (nd : Node (protoOf F E)) (v : V) (t : Time)
    {o : (protoOf F E).Object} (ho : o ∈ (rho.tick nd v t).2) {k r}
    (ha : o.auth = .signed k r) : k ∈ rho.sel r := by
  rcases rho.tick_auth nd v t ho with h | ⟨r', h, hk⟩
  · rw [h] at ha; cases ha
  · rw [h] at ha; cases ha; exact hk

omit [DecidableEq V] in
/-- Through the PKI, every signed object a tick of `v` releases is signed by
`v`. -/
theorem tick_signerOf (nd : Node (protoOf F E)) (v : V) (t : Time)
    {o : (protoOf F E).Object} (ho : o ∈ (rho.tick nd v t).2) :
    rho.signerOf o = none ∨ rho.signerOf o = some v := by
  rcases rho.tick_auth nd v t ho with h | ⟨r, h, _⟩
  · exact Or.inl (by simp [signerOf, Obj.signer?, h])
  · exact Or.inr (by simp [signerOf, Obj.signer?, ownKey, h])

omit [DecidableEq V] in
/-- A signed object a tick releases is the candidate of a due duty of its role
at a state the tick reaches from the post-clock state: `act`'s message and
carried objects there. -/
theorem tick_duty (nd : Node (protoOf F E)) (v : V) (t : Time)
    {a : Model.Auth (Fintype.card V) (protoOf F E).Role} {m cs}
    (ho : Obj.mk a m cs ∈ (rho.tick nd v t).2) {k r} (ha : a = .signed k r) :
    ∃ d ∈ (protoOf F E).duties t, (protoOf F E).role d = r ∧ ∃ st,
      TickReach (protoOf F E) ((protoOf F E).duties t)
        ((protoOf F E).clock nd.st t (mempool rho.inbox v t)) st ∧
      (m, cs) ∈ ((protoOf F E).act st d).2 := by
  subst ha
  obtain ⟨cs', hcs, h2, -⟩ := rho.tick_flat nd v t
  rw [h2] at ho
  rcases hcs _ (releaseAll_subset _ _ _ _ _ ho) with ⟨d, hd, st, hst, hc⟩ | hc
  · obtain ⟨m', cs'', hact, -, he⟩ := (rho.mem_signedCandidate).mp hc
    injection he with h₁ h₂ h₃
    injection h₁ with _ hr
    subst h₂ h₃
    exact ⟨d, hd, hr.symm, st, hst, hact⟩
  · obtain ⟨mc, -, he⟩ := mem_gossipCandidates.mp hc
    injection he with h₁
    cases h₁

/-! ## Deliveries

A delivery runs `process`, adds the object to `seen`, then the delivery duties
and gossip exactly as an awake tick runs its duties and gossip, from the
processed node (`Run.deliver_eq`). The tick lemmas above transfer: the
delivery releases what one `releaseAll` call from the processed `seen`
releases on its candidates (`Run.deliver_flat`), every released object is
unsigned or signed with the own key in a selecting role (`Run.deliver_auth`),
and an invariant kept by the delivery duties and the records holds after the
delivery (`Run.deliver_invariant`). -/

omit [DecidableEq V] in
/-- A delivery, unfolded: the processed node, its delivery duties, then gossip. -/
theorem deliver_eq (nd : Node (protoOf F E)) (v : V) (o : (protoOf F E).Object) (t : Time) :
    rho.deliver nd v o t =
      ((releaseAll (protoOf F E) rho.hash (rho.ownKey v)
          (rho.runDuties v ⟨(protoOf F E).process nd.st o (digests rho.hash o), nd.seen ++ [o]⟩
            ((protoOf F E).deliverDuties t)).1
          (gossipCandidates (protoOf F E)
            (rho.runDuties v
              ⟨(protoOf F E).process nd.st o (digests rho.hash o), nd.seen ++ [o]⟩
              ((protoOf F E).deliverDuties t)).1.st t)).1,
        (rho.runDuties v ⟨(protoOf F E).process nd.st o (digests rho.hash o), nd.seen ++ [o]⟩
          ((protoOf F E).deliverDuties t)).2 ++
        (releaseAll (protoOf F E) rho.hash (rho.ownKey v)
          (rho.runDuties v ⟨(protoOf F E).process nd.st o (digests rho.hash o), nd.seen ++ [o]⟩
            ((protoOf F E).deliverDuties t)).1
          (gossipCandidates (protoOf F E)
            (rho.runDuties v
              ⟨(protoOf F E).process nd.st o (digests rho.hash o), nd.seen ++ [o]⟩
              ((protoOf F E).deliverDuties t)).1.st t)).2) := rfl

omit [DecidableEq V] in
/-- A property of states that holds after `process` and is kept by the
delivery duties and by `recordOwn` of every object the delivery releases holds
after the delivery. -/
theorem deliver_invariant (Q : (protoOf F E).State → Prop) (nd : Node (protoOf F E)) (v : V)
    (o : (protoOf F E).Object) (t : Time)
    (hact : ∀ s, ∀ d ∈ (protoOf F E).deliverDuties t, Q s → Q ((protoOf F E).act s d).1)
    (hrec : ∀ s o' hs, o' ∈ (rho.deliver nd v o t).2 → Q s → Q ((protoOf F E).recordOwn s o' hs))
    (h₁ : Q ((protoOf F E).process nd.st o (digests rho.hash o))) :
    Q (rho.deliver nd v o t).1.st := by
  rw [rho.deliver_eq nd v o t] at hrec ⊢
  exact releaseAll_invariant Q _ _ _ _
    (fun s o' hs ho => hrec s o' hs (List.mem_append_right _ ho))
    (rho.runDuties_invariant Q v _ _ hact
      (fun s o' hs ho => hrec s o' hs (List.mem_append_left _ ho)) h₁)

omit [DecidableEq V] in
/-- The delivery ends in a state it reaches from the processed state. -/
theorem deliver_reach (nd : Node (protoOf F E)) (v : V) (o : (protoOf F E).Object) (t : Time) :
    TickReach (protoOf F E) ((protoOf F E).deliverDuties t)
      ((protoOf F E).process nd.st o (digests rho.hash o)) (rho.deliver nd v o t).1.st :=
  rho.deliver_invariant _ nd v o t (fun _ _ hd hs => .act hd hs)
    (fun _ o' hs _ h => .recordOwn o' hs h) .refl

/-- A signed duty candidate of a delivery to node `v` at `t` whose processed
state is `st₁`: the candidate of a delivery duty at a state the delivery
reaches. -/
def DeliverCandidate (st₁ : (protoOf F E).State) (v : V) (t : Time)
    (o : (protoOf F E).Object) : Prop :=
  ∃ d ∈ (protoOf F E).deliverDuties t, ∃ st,
    TickReach (protoOf F E) ((protoOf F E).deliverDuties t) st₁ st ∧
      o ∈ rho.signedCandidate v d ((protoOf F E).act st d).2

omit [DecidableEq V] in
theorem deliverCandidate_iff {st₁ : (protoOf F E).State} {v : V} {t : Time}
    {o : (protoOf F E).Object} : rho.DeliverCandidate st₁ v t o ↔
      ∃ d ∈ (protoOf F E).deliverDuties t, ∃ st,
        TickReach (protoOf F E) ((protoOf F E).deliverDuties t) st₁ st ∧
          o ∈ rho.signedCandidate v d ((protoOf F E).act st d).2 := Iff.rfl

omit [DecidableEq V] in
/-- The delivery releases what one `releaseAll` call from the processed node
(`nd.seen ++ [o]`) releases on the delivery's candidates, and leaves the same
`seen`: signed delivery-duty candidates at states the delivery reaches from
the processed state, and gossip at the state after the delivery duties. -/
theorem deliver_flat (nd : Node (protoOf F E)) (v : V) (o : (protoOf F E).Object) (t : Time) :
    ∃ cs : List (protoOf F E).Object,
      (∀ c ∈ cs,
        rho.DeliverCandidate ((protoOf F E).process nd.st o (digests rho.hash o)) v t c ∨
          c ∈ gossipCandidates (protoOf F E)
            (rho.runDuties v
              ⟨(protoOf F E).process nd.st o (digests rho.hash o), nd.seen ++ [o]⟩
              ((protoOf F E).deliverDuties t)).1.st t) ∧
      (rho.deliver nd v o t).2 = (releaseAll (protoOf F E) rho.hash (rho.ownKey v)
        ⟨(protoOf F E).process nd.st o (digests rho.hash o), nd.seen ++ [o]⟩ cs).2 ∧
      (rho.deliver nd v o t).1.seen = (releaseAll (protoOf F E) rho.hash (rho.ownKey v)
        ⟨(protoOf F E).process nd.st o (digests rho.hash o), nd.seen ++ [o]⟩ cs).1.seen := by
  obtain ⟨cs, hcs, h2, h1, -⟩ := foldl_duties_flat rho v ((protoOf F E).deliverDuties t)
    ((protoOf F E).deliverDuties t) (fun _ hd => hd)
    ((protoOf F E).process nd.st o (digests rho.hash o))
    ⟨(protoOf F E).process nd.st o (digests rho.hash o), nd.seen ++ [o]⟩ [] .refl
  generalize hR : rho.runDuties v
    ⟨(protoOf F E).process nd.st o (digests rho.hash o), nd.seen ++ [o]⟩
    ((protoOf F E).deliverDuties t) = R
  have hR' := hR
  unfold runDuties at hR'
  rw [hR'] at h1 h2
  have hdel : rho.deliver nd v o t =
      ((releaseAll (protoOf F E) rho.hash (rho.ownKey v) R.1
          (gossipCandidates (protoOf F E) R.1.st t)).1,
        R.2 ++ (releaseAll (protoOf F E) rho.hash (rho.ownKey v) R.1
          (gossipCandidates (protoOf F E) R.1.st t)).2) := by
    rw [← hR]; rfl
  have hgo := releaseAll_seen_only rho.hash (rho.ownKey v) h1
    (gossipCandidates (protoOf F E) R.1.st t)
  refine ⟨cs ++ gossipCandidates (protoOf F E) R.1.st t, ?_, ?_, ?_⟩
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact Or.inl (hcs c hc)
    · exact Or.inr hc
  · rw [hdel, releaseAll_append, h2, List.nil_append, hgo.1]
  · rw [hdel, releaseAll_append, hgo.2]

omit [DecidableEq V] in
/-- Delivery releases may additionally use the just-processed received object. -/
theorem deliver_ready (nd : Node (protoOf F E)) (v : V) (p : (protoOf F E).Object)
    (t : Time) (i : Nat) (o : (protoOf F E).Object)
    (ho : (rho.deliver nd v p t).2[i]? = some o) :
    (protoOf F E).dependencies.ready
      (closure ((nd.seen ++ [p]) ++ (rho.deliver nd v p t).2.take i)) o = true := by
  obtain ⟨cs, _, h2, _⟩ := rho.deliver_flat nd v p t
  rw [h2] at ho ⊢
  exact releaseAll_ready rho.hash (rho.ownKey v) _ cs i o ho

omit [DecidableEq V] in
/-- Every object a delivery to `v` releases is unsigned, or signed with `v`'s
own key in a role whose selection contains that key. -/
theorem deliver_auth (nd : Node (protoOf F E)) (v : V) (o : (protoOf F E).Object) (t : Time)
    {o' : (protoOf F E).Object} (ho : o' ∈ (rho.deliver nd v o t).2) :
    o'.auth = .none ∨ ∃ r, o'.auth = .signed (rho.ownKey v) r ∧ rho.ownKey v ∈ rho.sel r := by
  obtain ⟨cs, hcs, h2, -⟩ := rho.deliver_flat nd v o t
  rw [h2] at ho
  rcases hcs o' (releaseAll_subset _ _ _ _ o' ho) with ⟨d, -, st, -, hc⟩ | hc
  · obtain ⟨m, cs, -, hk, rfl⟩ := (rho.mem_signedCandidate).mp hc
    exact Or.inr ⟨_, rfl, hk⟩
  · obtain ⟨mc, -, rfl⟩ := mem_gossipCandidates.mp hc
    exact Or.inl rfl

omit [DecidableEq V] in
/-- Every object a delivery to `v` releases is unsigned or signed by `v`'s own
key. -/
theorem deliver_signer (nd : Node (protoOf F E)) (v : V) (o : (protoOf F E).Object) (t : Time)
    {o' : (protoOf F E).Object} (ho : o' ∈ (rho.deliver nd v o t).2) :
    o'.signer? = none ∨ o'.signer? = some (rho.ownKey v) := by
  rcases rho.deliver_auth nd v o t ho with h | ⟨r, h, _⟩
  · exact Or.inl (by simp [Obj.signer?, h])
  · exact Or.inr (by simp [Obj.signer?, h])

omit [DecidableEq V] in
/-- Every signed object a delivery releases is signed by a key selected for
its role. -/
theorem deliver_selected (nd : Node (protoOf F E)) (v : V) (o : (protoOf F E).Object)
    (t : Time) {o' : (protoOf F E).Object} (ho : o' ∈ (rho.deliver nd v o t).2) {k r}
    (ha : o'.auth = .signed k r) : k ∈ rho.sel r := by
  rcases rho.deliver_auth nd v o t ho with h | ⟨r', h, hk⟩
  · rw [h] at ha; cases ha
  · rw [h] at ha; cases ha; exact hk

omit [DecidableEq V] in
/-- Through the PKI, every signed object a delivery to `v` releases is signed
by `v`. -/
theorem deliver_signerOf (nd : Node (protoOf F E)) (v : V) (o : (protoOf F E).Object)
    (t : Time) {o' : (protoOf F E).Object} (ho : o' ∈ (rho.deliver nd v o t).2) :
    rho.signerOf o' = none ∨ rho.signerOf o' = some v := by
  rcases rho.deliver_auth nd v o t ho with h | ⟨r, h, _⟩
  · exact Or.inl (by simp [signerOf, Obj.signer?, h])
  · exact Or.inr (by simp [signerOf, Obj.signer?, ownKey, h])

omit [DecidableEq V] in
/-- A signed object a delivery releases is the candidate of a delivery duty of
its role at a state the delivery reaches from the processed state: `act`'s
message and carried objects there. -/
theorem deliver_duty (nd : Node (protoOf F E)) (v : V) (o : (protoOf F E).Object) (t : Time)
    {a : Model.Auth (Fintype.card V) (protoOf F E).Role} {m cs}
    (ho : Obj.mk a m cs ∈ (rho.deliver nd v o t).2) {k r} (ha : a = .signed k r) :
    ∃ d ∈ (protoOf F E).deliverDuties t, (protoOf F E).role d = r ∧ ∃ st,
      TickReach (protoOf F E) ((protoOf F E).deliverDuties t)
        ((protoOf F E).process nd.st o (digests rho.hash o)) st ∧
      (m, cs) ∈ ((protoOf F E).act st d).2 := by
  subst ha
  obtain ⟨cs', hcs, h2, -⟩ := rho.deliver_flat nd v o t
  rw [h2] at ho
  rcases hcs _ (releaseAll_subset _ _ _ _ _ ho) with ⟨d, hd, st, hst, hc⟩ | hc
  · obtain ⟨m', cs'', hact, -, he⟩ := (rho.mem_signedCandidate).mp hc
    injection he with h₁ h₂ h₃
    injection h₁ with _ hr
    subst h₂ h₃
    exact ⟨d, hd, hr.symm, st, hst, hact⟩
  · obtain ⟨mc, -, he⟩ := mem_gossipCandidates.mp hc
    injection he with h₁
    cases h₁

end Run
end Consensus.Model
end

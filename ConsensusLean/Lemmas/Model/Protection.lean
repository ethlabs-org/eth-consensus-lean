module
public import ConsensusLean.Lemmas.Model.Canonical.Unforgeable
public import ConsensusLean.Lemmas.Model.View
public import ConsensusLean.Lemmas.Model.Laws
public import ConsensusLean.Spec.Model.Guard

public section

/-! # Non-framing from an idle slashing guard (L1)

The engine has no slashing protection. On a run whose slashing protection never fires
(`Run.GuardIdle`), every own-signed candidate passes `protects` at its turn: it conflicts, under
the protocol's `conflicts`, neither with itself nor with an own-signed object in the closure of
`seen`. Because `seen` is append-only and survives restarts, and every object an honest node saw
that is signed by an honest validator was released by that validator
(`Run.signed_seen_released`, from `Unforgeable`), no honest validator is then slashable on what
the honest nodes saw (`Run.honestNeverSlashed`). Hence L0 non-framing holds for every model
system whose valid runs have an idle guard (`sysOf_nonFraming`). -/

namespace Consensus.Model

section Engine

variable {pub : Public} {Out : Type} {P : Protocol pub Out}

theorem closure_append (l l' : List P.Object) : closure (l ++ l') = closure l ++ closure l' := by
  simp [closure, List.flatMap_append]

theorem mem_closure_of_mem {l : List P.Object} {o : P.Object} (h : o ∈ l) : o ∈ closure l :=
  (mem_closure_iff l o).mpr ⟨o, h, .refl _⟩

theorem closure_mono {l l' : List P.Object} (h : ∀ o ∈ l, o ∈ l') {o : P.Object}
    (ho : o ∈ closure l) : o ∈ closure l' := by
  obtain ⟨r, hr, hc⟩ := (mem_closure_iff _ _).mp ho
  exact (mem_closure_iff _ _).mpr ⟨r, h r hr, hc⟩

/-- What `protects` means: a `k`-signed candidate does not conflict with
itself, nor, in either order, with a `k`-signed object in the closure of
`seen`. -/
theorem protects_iff {k : Key pub} {seen : List P.Object} {c : P.Object} :
    protects P k seen c = true ↔
      (c.signer? = some k → P.conflicts c c = false ∧
        ∀ o ∈ closure seen, o.signer? = some k →
          P.conflicts c o = false ∧ P.conflicts o c = false) := by
  unfold protects
  split
  next hs =>
    simp only [hs, forall_const, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true,
      Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_false_iff]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun o ho hos => ?_⟩
      rcases h2 o ho with h | h
      · exact absurd hos h
      · exact h
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun o ho => by
        by_cases hos : o.signer? = some k
        · exact Or.inr (h2 o ho hos)
        · exact Or.inl hos⟩
  next hs => simp [hs]

/-- The refusals of `c :: cs`: `c` if `protects` refuses it, then those of `cs` from the node
the release of `c` leaves. -/
theorem guardRefusals_cons (hash : P.Item → Nat) (k : Key pub) (nd : Node P) (c : P.Object)
    (cs : List P.Object) :
    guardRefusals P hash k nd (c :: cs) =
      (if protects P k nd.seen c then [] else [c]) ++
        guardRefusals P hash k (releaseAll P hash k nd [c]).1 cs := rfl

/-- The refusals depend only on `seen`, not on the state. -/
theorem guardRefusals_seen_only (hash : P.Item → Nat) (k : Key pub) {nd nd' : Node P}
    (h : nd.seen = nd'.seen) (cs : List P.Object) :
    guardRefusals P hash k nd cs = guardRefusals P hash k nd' cs := by
  induction cs generalizing nd nd' with
  | nil => rfl
  | cons c cs ih =>
    rw [guardRefusals_cons, guardRefusals_cons, h,
      ih (releaseAll_seen_only hash k h [c]).2]

/-- Checking `cs ++ cs'` checks `cs`, then `cs'` from the node the release of `cs` leaves. -/
theorem guardRefusals_append (hash : P.Item → Nat) (k : Key pub) (cs cs' : List P.Object) :
    ∀ nd, guardRefusals P hash k nd (cs ++ cs') =
      guardRefusals P hash k nd cs ++
        guardRefusals P hash k (releaseAll P hash k nd cs).1 cs' := by
  induction cs with
  | nil => intro _; rfl
  | cons c cs ih =>
    intro nd
    have hr : (releaseAll P hash k nd (c :: cs)).1 =
        (releaseAll P hash k (releaseAll P hash k nd [c]).1 cs).1 := by
      rw [show c :: cs = [c] ++ cs from rfl, releaseAll_append]
    simp only [List.cons_append, guardRefusals_cons, ih, hr, List.append_assoc]

/-- With no refusal, the head candidate passes `protects`, and the rest have no refusal from the
node its release leaves. -/
private theorem guardRefusals_cons_nil {hash : P.Item → Nat} {k : Key pub} {nd : Node P}
    {c : P.Object} {cs : List P.Object} (h : guardRefusals P hash k nd (c :: cs) = []) :
    protects P k nd.seen c = true ∧
      guardRefusals P hash k (releaseAll P hash k nd [c]).1 cs = [] := by
  rw [guardRefusals_cons, List.append_eq_nil_iff] at h
  refine ⟨?_, h.2⟩
  have h1 := h.1
  split at h1
  · assumption
  · exact absurd h1 (List.cons_ne_nil _ _)

/-- The node the release of one candidate leaves. -/
private theorem releaseAll_single (hash : P.Item → Nat) (k : Key pub) (nd : Node P)
    (c : P.Object) :
    (releaseAll P hash k nd [c]).1 =
      if releasable nd.seen c && P.dependencies.ready (closure nd.seen) c then
        ⟨P.recordOwn nd.st c (digests hash c), nd.seen ++ [c]⟩ else nd := by
  unfold releaseAll
  split <;> rfl

/-- With no refusal, a released `k`-signed object never conflicts, in either order, with a
`k`-signed object in the closure of `nd.seen`. -/
theorem releaseAll_noConflict_seen {hash : P.Item → Nat} {k : Key pub} {nd : Node P}
    {cs : List P.Object} {c o : P.Object} (hg : guardRefusals P hash k nd cs = [])
    (h : c ∈ (releaseAll P hash k nd cs).2)
    (ho : o ∈ closure nd.seen) (hs : c.signer? = some k) (hs' : o.signer? = some k) :
    P.conflicts c o = false ∧ P.conflicts o c = false := by
  induction cs generalizing nd with
  | nil => simp [releaseAll] at h
  | cons d cs ih =>
    obtain ⟨hp, hg⟩ := guardRefusals_cons_nil hg
    rw [releaseAll_single] at hg
    unfold releaseAll at h
    split at h
    next hf =>
      rw [ite_eq_left hf] at hg
      dsimp only at h
      rcases List.mem_cons.mp h with rfl | h
      · exact (protects_iff.mp hp hs).2 o ho hs'
      · exact ih hg h (closure_mono (fun x hx => List.mem_append_left _ hx) ho)
    next hf =>
      rw [ite_eq_right hf] at hg
      exact ih hg h ho

/-- With no refusal, two `k`-signed objects released by one `releaseAll` call never conflict (in
either order, or with themselves). -/
theorem releaseAll_noConflict {hash : P.Item → Nat} {k : Key pub} {nd : Node P}
    {cs : List P.Object} {c c' : P.Object} (hg : guardRefusals P hash k nd cs = [])
    (h : c ∈ (releaseAll P hash k nd cs).2)
    (h' : c' ∈ (releaseAll P hash k nd cs).2) (hs : c.signer? = some k)
    (hs' : c'.signer? = some k) : P.conflicts c c' = false := by
  induction cs generalizing nd with
  | nil => simp [releaseAll] at h
  | cons d cs ih =>
    obtain ⟨hp, hg⟩ := guardRefusals_cons_nil hg
    rw [releaseAll_single] at hg
    unfold releaseAll at h h'
    by_cases hf : (releasable nd.seen d && P.dependencies.ready (closure nd.seen) d) = true
    · rw [ite_eq_left hf] at hg
      simp only [hf, ↓reduceIte] at h h'
      have hd : d ∈ closure (nd.seen ++ [d]) :=
        mem_closure_of_mem (List.mem_append_right _ (List.mem_singleton_self d))
      rcases List.mem_cons.mp h with rfl | h <;> rcases List.mem_cons.mp h' with rfl | h'
      · exact (protects_iff.mp hp hs).1
      · exact (releaseAll_noConflict_seen hg h' hd hs' hs).2
      · exact (releaseAll_noConflict_seen hg h hd hs hs').1
      · exact ih hg h h'
    · rw [ite_eq_right hf] at hg
      simp only [hf, Bool.false_eq_true, ↓reduceIte] at h h'
      exact ih hg h h'

end Engine

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : ProtocolFamily O}
    {E : Env V}

namespace Run

variable (rho : Run F E)

omit [DecidableEq V] in
/-- Through the PKI, an object signed by validator `x` is signed by `x`'s own
key. -/
theorem signer_of_signerOf {o : (protoOf F E).Object} {x : V}
    (h : rho.signerOf o = some x) : o.signer? = some (rho.ownKey x) := by
  obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp h
  simp [ownKey, hk]

/-- What node `v` has seen before cut `i` is in the closure of its `seen`
log (the definition of `ViewIdx`). -/
theorem viewIdx_closure {v : V} {i : Nat} {o : (protoOf F E).Object}
    (ho : o ∈ rho.ViewIdx v i) : o ∈ closure (rho.stateBefore i v).seen := ho

/-- In a valid run, everything in any node's `seen` before cut `i` is safe
before `i`: every object it contains that is signed by an honest validator
was released by that validator at an earlier sending event (a tick or a
delivery). -/
theorem seen_safe (hv : rho.ExecutionValid) (H : V → Prop) (i : Nat)
    (hH : ∀ k < i, ∀ e, rho.events[k]? = some e →
      ∀ u, H u → u ∉ rho.faultyAt e.time) :
    ∀ v, ∀ o ∈ (rho.stateBefore i v).seen, rho.SafeBeforeOn H i o := by
  induction i with
  | zero => simp [stateBefore, initWorld]
  | succ k ih =>
    have ih := ih (fun j hj => hH j (by omega))
    cases he : rho.events[k]? with
    | none =>
      have hworld : rho.stateBefore (k + 1) = rho.stateBefore k := by
        simp [stateBefore, List.take_add_one, he]
      rw [hworld]
      exact fun v o ho => rho.safeBeforeOn_mono (Nat.le_succ k) (ih v o ho)
    | some e =>
      rw [rho.stateBefore_succ he]
      cases e with
      | tick v t =>
        have hsafe := rho.tick_safeOn he (ih v)
        intro w o ho
        by_cases hw : w = v
        · subst w; exact hsafe o (by simpa [step] using ho)
        · exact rho.safeBeforeOn_mono (Nat.le_succ k) (ih w o (by simpa [step, hw] using ho))
      | restart v t =>
        intro w o ho
        by_cases hw : w = v
        · subst w
          exact rho.safeBeforeOn_mono (Nat.le_succ k) (ih v o (by simpa [step] using ho))
        · exact rho.safeBeforeOn_mono (Nat.le_succ k) (ih w o (by simpa [step, hw] using ho))
      | deliver v p t =>
        have hp : rho.SafeBeforeOn H k p := (rho.safeBeforeOn_iff).mpr fun d hd u hs hu =>
          hv.unforgeable k v p t he d hd u hs (hH k (by omega) _ he u hu)
        have hsafe := rho.deliver_safeOn he (ih v) hp
        intro w o ho
        by_cases hw : w = v
        · subst w; exact hsafe o (by simpa [step] using ho)
        · exact rho.safeBeforeOn_mono (Nat.le_succ k) (ih w o (by simpa [step, hw] using ho))

/-- General invariant for every valid run: an object in the closure of a
node's `seen` before event `i`, signed by honest `u`, was released by `u` at a
sending event (tick or delivery) `j < i`. -/
theorem signed_seen_released (hv : rho.ExecutionValid) {i : Nat} {v : V}
    {o : (protoOf F E).Object} {u : V}
    (hi : i ≤ rho.events.length)
    (ho : o ∈ closure (rho.stateBefore i v).seen) (hu : u ∉ rho.faultyAt (rho.cutTime i))
    (hs : rho.signerOf o = some u) :
    ∃ j < i, ∃ t, rho.SendsAt u j t ∧ o ∈ rho.releasesAt j := by
  obtain ⟨r, hr, hc⟩ := (mem_closure_iff _ _).mp ho
  have hH : ∀ k < i, ∀ e, rho.events[k]? = some e →
      ∀ x, x ∉ rho.faultyAt (rho.cutTime i) → x ∉ rho.faultyAt e.time := by
    intro k hk e he x hx hmem
    have ht := ((sysOf_laws O F V).trace ⟨E, rho⟩ hv).cutTime_mono
      (k + 1) i (by omega) hi
    change rho.cutTime (k + 1) ≤ rho.cutTime i at ht
    simp only [cutTime, he] at ht
    exact hx (rho.faultyAt_mono ht hmem)
  obtain ⟨j, t, hj, he, hjo⟩ := (rho.safeBeforeOn_iff).mp (rho.seen_safe hv
    (fun x => x ∉ rho.faultyAt (rho.cutTime i)) i hH v r hr) o hc u hs hu
  exact ⟨j, hj, t, he, hjo⟩

/-- Every object signed by an honest validator that an honest node saw was
released by that validator at a sending event (a tick or a delivery). -/
theorem released_of_observed (hv : rho.ExecutionValid) {o : (protoOf F E).Object}
    {d : Time}
    (ho : ∃ v i, i ≤ rho.events.length ∧ rho.cutTime i ≤ d ∧ o ∈ rho.ViewIdx v i)
    {u : V} (hu : u ∉ rho.faultyAt d)
    (hs : rho.signerOf o = some u) :
    ∃ j t, rho.SendsAt u j t ∧ o ∈ rho.releasesAt j := by
  obtain ⟨v, i, hi, ht, hov⟩ := ho
  have hui : u ∉ rho.faultyAt (rho.cutTime i) := fun h => hu (rho.faultyAt_mono ht h)
  obtain ⟨j, -, t, he, hjo⟩ :=
    rho.signed_seen_released hv hi (rho.viewIdx_closure hov) hui hs
  exact ⟨j, t, he, hjo⟩

omit [DecidableEq V] in
/-- The duties `ds` release what one `releaseAll` call from `nd` releases on their candidates, leave
the same `seen`, and have the refusals of one `guardRefusals` call on the same candidates. -/
theorem runDuties_flat_guard (v : V) (ds : List (protoOf F E).Duty) :
    ∀ nd : Node (protoOf F E), ∃ cs : List (protoOf F E).Object,
      (rho.runDuties v nd ds).2 = (releaseAll (protoOf F E) rho.hash (rho.ownKey v) nd cs).2 ∧
      (rho.runDuties v nd ds).1.seen =
        (releaseAll (protoOf F E) rho.hash (rho.ownKey v) nd cs).1.seen ∧
      rho.runDutiesRefusals v nd ds =
        guardRefusals (protoOf F E) rho.hash (rho.ownKey v) nd cs := by
  induction ds with
  | nil => intro _; exact ⟨[], rfl, rfl, rfl⟩
  | cons d ds ih =>
    intro nd
    obtain ⟨cs, h2, h1, h3⟩ := ih (rho.dutyStep v nd d).1
    by_cases hk : rho.ownKey v ∈ rho.sel ((protoOf F E).role d)
    · have hstep : rho.dutyStep v nd d = releaseAll (protoOf F E) rho.hash (rho.ownKey v)
          ⟨((protoOf F E).act nd.st d).1, nd.seen⟩
          (rho.signedCandidate v d ((protoOf F E).act nd.st d).2) := by
        rw [rho.dutyStep_eq, ite_eq_left hk]
      have hrefs : rho.dutyRefusals v nd d = guardRefusals (protoOf F E) rho.hash (rho.ownKey v)
          ⟨((protoOf F E).act nd.st d).1, nd.seen⟩
          (rho.signedCandidate v d ((protoOf F E).act nd.st d).2) := by
        unfold dutyRefusals
        rw [ite_eq_left hk]
      rw [hstep] at h1 h2 h3
      have hso := releaseAll_seen_only rho.hash (rho.ownKey v)
        (nd := ⟨((protoOf F E).act nd.st d).1, nd.seen⟩) (nd' := nd) rfl
        (rho.signedCandidate v d ((protoOf F E).act nd.st d).2)
      have hso' := releaseAll_seen_only rho.hash (rho.ownKey v) hso.2 cs
      refine ⟨rho.signedCandidate v d ((protoOf F E).act nd.st d).2 ++ cs, ?_, ?_, ?_⟩
      · rw [rho.runDuties_cons, hstep, h2, releaseAll_append, hso.1, hso'.1]
      · rw [rho.runDuties_cons, hstep, h1, releaseAll_append, hso'.2]
      · rw [runDutiesRefusals, hrefs, hstep, h3, guardRefusals_append,
          guardRefusals_seen_only rho.hash (rho.ownKey v)
            (nd := ⟨((protoOf F E).act nd.st d).1, nd.seen⟩) (nd' := nd) rfl,
          guardRefusals_seen_only rho.hash (rho.ownKey v) hso.2]
    · have hstep : rho.dutyStep v nd d = (nd, []) := by rw [rho.dutyStep_eq, ite_eq_right hk]
      have hrefs : rho.dutyRefusals v nd d = [] := by
        unfold dutyRefusals
        rw [ite_eq_right hk]
      rw [hstep] at h1 h2 h3
      refine ⟨cs, ?_, ?_, ?_⟩
      · rw [rho.runDuties_cons, hstep, List.nil_append]
        exact h2
      · rw [rho.runDuties_cons, hstep]
        exact h1
      · rw [runDutiesRefusals, hrefs, hstep, List.nil_append]
        exact h3

omit [DecidableEq V] in
/-- A tick releases what one `releaseAll` call from its starting node releases on some candidates,
and its refusals are those of one `guardRefusals` call on the same candidates. -/
theorem tick_flat_guard (nd : Node (protoOf F E)) (v : V) (t : Time) :
    ∃ cs : List (protoOf F E).Object,
      (rho.tick nd v t).2 = (releaseAll (protoOf F E) rho.hash (rho.ownKey v) nd cs).2 ∧
      rho.tickRefusals nd v t = guardRefusals (protoOf F E) rho.hash (rho.ownKey v) nd cs := by
  by_cases hw : E.awake v t = true
  · obtain ⟨cs, h2, h1, h3⟩ := rho.runDuties_flat_guard v ((protoOf F E).duties t)
      ⟨(protoOf F E).clock nd.st t (mempool rho.inbox v t), nd.seen⟩
    have hso := releaseAll_seen_only rho.hash (rho.ownKey v)
      (nd := ⟨(protoOf F E).clock nd.st t (mempool rho.inbox v t), nd.seen⟩) (nd' := nd) rfl cs
    refine ⟨cs ++ gossipCandidates (protoOf F E) (rho.runDuties v
      ⟨(protoOf F E).clock nd.st t (mempool rho.inbox v t), nd.seen⟩
        ((protoOf F E).duties t)).1.st t, ?_, ?_⟩
    · rw [rho.tick_of_awake nd v t hw, releaseAll_append, h2, hso.1,
        (releaseAll_seen_only rho.hash (rho.ownKey v) (h1.trans hso.2) _).1]
    · unfold tickRefusals
      rw [ite_eq_left hw]
      dsimp only
      rw [h3, guardRefusals_append, guardRefusals_seen_only rho.hash (rho.ownKey v)
          (nd := ⟨(protoOf F E).clock nd.st t (mempool rho.inbox v t), nd.seen⟩) (nd' := nd) rfl,
        guardRefusals_seen_only rho.hash (rho.ownKey v) (h1.trans hso.2)]
  · refine ⟨[], ?_, ?_⟩
    · rw [rho.tick_of_asleep nd v t (by simpa using hw)]
      rfl
    · unfold tickRefusals
      rw [ite_eq_right hw]
      rfl

omit [DecidableEq V] in
/-- A delivery releases what one `releaseAll` call from the processed node releases on some
candidates, and its refusals are those of one `guardRefusals` call on the same candidates. -/
theorem deliver_flat_guard (nd : Node (protoOf F E)) (v : V) (o : (protoOf F E).Object)
    (t : Time) :
    ∃ cs : List (protoOf F E).Object,
      (rho.deliver nd v o t).2 = (releaseAll (protoOf F E) rho.hash (rho.ownKey v)
        ⟨(protoOf F E).process nd.st o (digests rho.hash o), nd.seen ++ [o]⟩ cs).2 ∧
      rho.deliverRefusals nd v o t = guardRefusals (protoOf F E) rho.hash (rho.ownKey v)
        ⟨(protoOf F E).process nd.st o (digests rho.hash o), nd.seen ++ [o]⟩ cs := by
  obtain ⟨cs, h2, h1, h3⟩ := rho.runDuties_flat_guard v ((protoOf F E).deliverDuties t)
    ⟨(protoOf F E).process nd.st o (digests rho.hash o), nd.seen ++ [o]⟩
  refine ⟨cs ++ gossipCandidates (protoOf F E) (rho.runDuties v
    ⟨(protoOf F E).process nd.st o (digests rho.hash o), nd.seen ++ [o]⟩
      ((protoOf F E).deliverDuties t)).1.st t, ?_, ?_⟩
  · change _ ++ _ = _
    rw [releaseAll_append, h2, (releaseAll_seen_only rho.hash (rho.ownKey v) h1 _).1]
  · unfold deliverRefusals
    dsimp only
    rw [h3, guardRefusals_append, guardRefusals_seen_only rho.hash (rho.ownKey v) h1]

/-- With no refusal at the tick, two own-signed objects released by it never conflict. -/
theorem tick_noConflict {i : Nat} {v : V} {t : Time} (he : rho.events[i]? = some (.tick v t))
    (hg : rho.guardRefusalsAt i = [])
    {c c' : (protoOf F E).Object} (hc : c ∈ rho.releasesAt i) (hc' : c' ∈ rho.releasesAt i)
    (hs : c.signer? = some (rho.ownKey v)) (hs' : c'.signer? = some (rho.ownKey v)) :
    (protoOf F E).conflicts c c' = false := by
  simp only [releasesAt, he] at hc hc'
  simp only [guardRefusalsAt, he] at hg
  obtain ⟨cs, h2, h3⟩ := rho.tick_flat_guard (rho.stateBefore i v) v t
  rw [h2] at hc hc'
  rw [h3] at hg
  exact releaseAll_noConflict hg hc hc' hs hs'

/-- With no refusal at the tick, an own-signed object it releases never conflicts, in either
order, with an own-signed object in the closure of the node's `seen` before it. -/
theorem tick_noConflict_seen {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) (hg : rho.guardRefusalsAt i = [])
    {c o : (protoOf F E).Object}
    (hc : c ∈ rho.releasesAt i) (ho : o ∈ closure (rho.stateBefore i v).seen)
    (hs : c.signer? = some (rho.ownKey v)) (hs' : o.signer? = some (rho.ownKey v)) :
    (protoOf F E).conflicts c o = false ∧ (protoOf F E).conflicts o c = false := by
  simp only [releasesAt, he] at hc
  simp only [guardRefusalsAt, he] at hg
  obtain ⟨cs, h2, h3⟩ := rho.tick_flat_guard (rho.stateBefore i v) v t
  rw [h2] at hc
  rw [h3] at hg
  exact releaseAll_noConflict_seen hg hc ho hs hs'

/-- With no refusal at the delivery, two own-signed objects released by it never conflict. -/
theorem deliver_noConflict {i : Nat} {v : V} {p : (protoOf F E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v p t)) (hg : rho.guardRefusalsAt i = [])
    {c c' : (protoOf F E).Object} (hc : c ∈ rho.releasesAt i) (hc' : c' ∈ rho.releasesAt i)
    (hs : c.signer? = some (rho.ownKey v)) (hs' : c'.signer? = some (rho.ownKey v)) :
    (protoOf F E).conflicts c c' = false := by
  simp only [releasesAt, he] at hc hc'
  simp only [guardRefusalsAt, he] at hg
  obtain ⟨cs, h2, h3⟩ := rho.deliver_flat_guard (rho.stateBefore i v) v p t
  rw [h2] at hc hc'
  rw [h3] at hg
  exact releaseAll_noConflict hg hc hc' hs hs'

/-- With no refusal at the delivery, an own-signed object it releases never conflicts, in either
order, with an own-signed object in the closure of the node's `seen` before it. -/
theorem deliver_noConflict_seen {i : Nat} {v : V} {p : (protoOf F E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v p t)) (hg : rho.guardRefusalsAt i = [])
    {c o : (protoOf F E).Object}
    (hc : c ∈ rho.releasesAt i) (ho : o ∈ closure (rho.stateBefore i v).seen)
    (hs : c.signer? = some (rho.ownKey v)) (hs' : o.signer? = some (rho.ownKey v)) :
    (protoOf F E).conflicts c o = false ∧ (protoOf F E).conflicts o c = false := by
  simp only [releasesAt, he] at hc
  simp only [guardRefusalsAt, he] at hg
  obtain ⟨cs, h2, h3⟩ := rho.deliver_flat_guard (rho.stateBefore i v) v p t
  rw [h2] at hc
  rw [h3] at hg
  exact releaseAll_noConflict_seen hg hc (closure_mono (fun x hx => List.mem_append_left _ hx) ho)
    hs hs'

/-- On a run with an idle slashing guard, a validator whose signed objects in `A` it released
itself is not slashable on `A`: the later of two conflicting objects (by event, or by position
within one tick or delivery) would have been refused against the earlier one. -/
theorem not_slashable_of_released {A : Set (protoOf F E).Object} {x : V}
    (hg : rho.GuardIdle) (hr : ∀ o ∈ A, rho.signerOf o = some x →
      ∃ j t, rho.SendsAt x j t ∧ o ∈ rho.releasesAt j) : ¬ rho.Slashable A x := by
  rintro ⟨o, ho, o', ho', hs, hs', hc⟩
  obtain ⟨j, t, hj, hjo⟩ := hr o ho hs
  obtain ⟨j', t', hj', hjo'⟩ := hr o' ho' hs'
  have hk := rho.signer_of_signerOf hs
  have hk' := rho.signer_of_signerOf hs'
  have nc {i t c c'} (hi : rho.SendsAt x i t) (hc : c ∈ rho.releasesAt i)
      (hc' : c' ∈ rho.releasesAt i) (hs : c.signer? = some (rho.ownKey x))
      (hs' : c'.signer? = some (rho.ownKey x)) : (protoOf F E).conflicts c c' = false := by
    rcases hi with he | ⟨p, he⟩
    · exact rho.tick_noConflict he (hg i) hc hc' hs hs'
    · exact rho.deliver_noConflict he (hg i) hc hc' hs hs'
  have ncs {i t c o} (hi : rho.SendsAt x i t) (hc : c ∈ rho.releasesAt i)
      (ho : o ∈ closure (rho.stateBefore i x).seen) (hs : c.signer? = some (rho.ownKey x))
      (hs' : o.signer? = some (rho.ownKey x)) :
      (protoOf F E).conflicts c o = false ∧ (protoOf F E).conflicts o c = false := by
    rcases hi with he | ⟨p, he⟩
    · exact rho.tick_noConflict_seen he (hg i) hc ho hs hs'
    · exact rho.deliver_noConflict_seen he (hg i) hc ho hs hs'
  rcases lt_trichotomy j j' with hlt | rfl | hgt
  · have hm : o ∈ closure (rho.stateBefore j' x).seen :=
      mem_closure_of_mem (rho.seen_mono hlt x (rho.releasesAt_seen hj hjo))
    have := (ncs hj' hjo' hm hk' hk).2
    rw [hc] at this
    cases this
  · have := nc hj hjo hjo' hk hk'
    rw [hc] at this
    cases this
  · have hm : o' ∈ closure (rho.stateBefore j x).seen :=
      mem_closure_of_mem (rho.seen_mono hgt x (rho.releasesAt_seen hj' hjo'))
    have := (ncs hj hjo hm hk hk').1
    rw [hc] at this
    cases this

/-- On a valid run with an idle slashing guard, no validator honest at `d` is slashable on what
the nodes saw by `d`. -/
theorem honestNeverSlashed (hv : rho.ExecutionValid) (hg : rho.GuardIdle) :
    ∀ v d, v ∉ rho.faultyAt d →
      ¬ rho.Slashable {o | ∃ w i, i ≤ rho.events.length ∧
        rho.cutTime i ≤ d ∧ o ∈ rho.ViewIdx w i} v := by
  intro v d hvh
  exact rho.not_slashable_of_released hg fun _ ho hs => rho.released_of_observed hv ho hvh hs

end Run

/-- The honest evidence of a system run is what the honest nodes of the run
saw. -/
theorem mem_honestEvidence_iff (rho : Run F E) (hv : rho.ExecutionValid)
    (p : (protoOf F E).Object) :
    (⟨E, p⟩ : (sysOf O F V).Obs) ∈
      (sysOf O F V).honestEvidenceBy ⟨E, rho⟩ rho.horizon ↔
      p ∈ rho.Observed := by
  constructor
  · rintro ⟨w, i, hi, _, hw, q, hq, heq⟩
    obtain rfl : p = q := eq_of_heq (Sigma.mk.inj heq).2
    exact ⟨w, i, hi, hw, hq⟩
  · rintro ⟨w, i, hi, hw, hp⟩
    exact ⟨w, i, hi, ((sysOf_laws O F V).trace ⟨E, rho⟩ hv).cutTime_le_horizon i hi,
      hw, p, hp, rfl⟩

/-- L0 non-framing holds for every model system whose valid runs have an idle slashing guard. -/
theorem sysOf_nonFraming (O : OutputSchema) (F : ProtocolFamily O) (V : Type) [Fintype V]
    [DecidableEq V] (hg : (sysOf O F V).HoldsAlways fun r => r.2.GuardIdle) :
    (sysOf O F V).HoldsAlways (sysOf O F V).NonFraming := by
  rintro ⟨E, rho⟩ hv v d hvh hconv
  apply rho.honestNeverSlashed hv (hg ⟨E, rho⟩ hv) v d hvh
  obtain ⟨o, ho, o', ho', h1, h2, h3⟩ := hconv
  have obs {p : (protoOf F E).Object}
      (hp : (⟨E, p⟩ : (sysOf O F V).Obs) ∈
        (sysOf O F V).honestEvidenceBy ⟨E, rho⟩ d) :
      ∃ w i, i ≤ rho.events.length ∧ rho.cutTime i ≤ d ∧ p ∈ rho.ViewIdx w i := by
    obtain ⟨w, i, hi, ht, _, q, hq, heq⟩ := hp
    obtain rfl : p = q := eq_of_heq (Sigma.mk.inj heq).2
    exact ⟨w, i, hi, ht, hq⟩
  exact ⟨o, obs ho, o', obs ho', h1, h2, h3⟩

end Consensus.Model

end

module
public import ConsensusLean.Lemmas.Model.Canonical.Unforgeable
public import ConsensusLean.Lemmas.Model.View
public import ConsensusLean.Lemmas.Model.Laws

public section

/-! # Slashing protection (L1)

The engine refuses an own-signed candidate that conflicts, under the
protocol's `conflicts`, with itself or with an own-signed object in the
closure of `seen` (`protects`). Because `seen` is append-only and survives
restarts, and every object an honest node saw that is signed by an honest
validator was released by that validator (`Run.signed_seen_released`, from
`Unforgeable`), no honest validator is ever slashable on what the honest
nodes saw (`Run.honestNeverSlashed`), for every protocol. Hence L0
non-framing holds for every model system (`sysOf_nonFraming`).

`releaseAll_eq_carried`: when own-signed objects never conflict, the guard is
a no-op, and `releaseAll` is the carried-only release `releaseAllCarried`
(for liveness proofs). -/

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

/-- A released `k`-signed object never conflicts, in either order, with a
`k`-signed object in the closure of `nd.seen`. -/
theorem releaseAll_noConflict_seen {hash : P.Item → Nat} {k : Key pub} {nd : Node P}
    {cs : List P.Object} {c o : P.Object} (h : c ∈ (releaseAll P hash k nd cs).2)
    (ho : o ∈ closure nd.seen) (hs : c.signer? = some k) (hs' : o.signer? = some k) :
    P.conflicts c o = false ∧ P.conflicts o c = false := by
  induction cs generalizing nd with
  | nil => simp [releaseAll] at h
  | cons d cs ih =>
    unfold releaseAll at h
    split at h
    next hf =>
      dsimp only at h
      rcases List.mem_cons.mp h with rfl | h
      · exact (protects_iff.mp (Bool.and_eq_true_iff.mp
          (Bool.and_eq_true_iff.mp hf).1).2 hs).2 o ho hs'
      · exact ih h (closure_mono (fun x hx => List.mem_append_left _ hx) ho)
    next => exact ih h ho

/-- Same-call protection: two `k`-signed objects released by one `releaseAll`
call never conflict (in either order, or with themselves). -/
theorem releaseAll_noConflict {hash : P.Item → Nat} {k : Key pub} {nd : Node P}
    {cs : List P.Object} {c c' : P.Object} (h : c ∈ (releaseAll P hash k nd cs).2)
    (h' : c' ∈ (releaseAll P hash k nd cs).2) (hs : c.signer? = some k)
    (hs' : c'.signer? = some k) : P.conflicts c c' = false := by
  induction cs generalizing nd with
  | nil => simp [releaseAll] at h
  | cons d cs ih =>
    unfold releaseAll at h h'
    by_cases hf : ((releasable nd.seen d && protects P k nd.seen d) &&
        P.dependencies.ready (closure nd.seen) d) = true
    · simp only [hf, ↓reduceIte] at h h'
      have hp := protects_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hf).1).2
      have hd : d ∈ closure (nd.seen ++ [d]) :=
        mem_closure_of_mem (List.mem_append_right _ (List.mem_singleton_self d))
      rcases List.mem_cons.mp h with rfl | h <;> rcases List.mem_cons.mp h' with rfl | h'
      · exact (hp hs).1
      · exact (releaseAll_noConflict_seen h' hd hs' hs).2
      · exact (releaseAll_noConflict_seen h hd hs hs').1
      · exact ih h h'
    · simp only [hf, Bool.false_eq_true, ↓reduceIte] at h h'
      exact ih h h'

/-- The carried/dependency release: the engine's release without slashing
protection, retaining the dependency guard. -/
def releaseAllCarried (P : Protocol pub Out) (hash : P.Item → Nat) :
    Node P → List P.Object → Node P × List P.Object
  | nd, [] => (nd, [])
  | nd, c :: cs =>
    if releasable nd.seen c && P.dependencies.ready (closure nd.seen) c then
      let nd' : Node P := ⟨P.recordOwn nd.st c (digests hash c), nd.seen ++ [c]⟩
      let r := releaseAllCarried P hash nd' cs
      (r.1, c :: r.2)
    else releaseAllCarried P hash nd cs

theorem releaseAllCarried_cons (hash : P.Item → Nat) (nd : Node P) (c : P.Object)
    (cs : List P.Object) :
    releaseAllCarried P hash nd (c :: cs) =
      if releasable nd.seen c && P.dependencies.ready (closure nd.seen) c then
        let nd' : Node P := ⟨P.recordOwn nd.st c (digests hash c), nd.seen ++ [c]⟩
        let r := releaseAllCarried P hash nd' cs
        (r.1, c :: r.2)
      else releaseAllCarried P hash nd cs := by rfl

/-- The guard is a no-op when own-signed objects never conflict (for liveness
proofs): with no conflicting pair among `k`-signed objects of
`closure nd.seen ++ closure cs`, `releaseAll` is the carried-only release. -/
theorem releaseAll_eq_carried (hash : P.Item → Nat) (k : Key pub) (nd : Node P)
    (cs : List P.Object)
    (h : ∀ o ∈ closure nd.seen ++ closure cs, ∀ o' ∈ closure nd.seen ++ closure cs,
      o.signer? = some k → o'.signer? = some k → P.conflicts o o' = false) :
    releaseAll P hash k nd cs = releaseAllCarried P hash nd cs := by
  induction cs generalizing nd with
  | nil => rfl
  | cons c cs ih =>
    have hc : c ∈ closure nd.seen ++ closure (c :: cs) :=
      List.mem_append_right _ (mem_closure_of_mem List.mem_cons_self)
    have hseen : ∀ o ∈ closure nd.seen, o ∈ closure nd.seen ++ closure (c :: cs) :=
      fun o ho => List.mem_append_left _ ho
    have hp : protects P k nd.seen c = true :=
      protects_iff.mpr fun hs =>
        ⟨h c hc c hc hs hs, fun o ho hos =>
          ⟨h c hc o (hseen o ho) hs hos, h o (hseen o ho) c hc hos hs⟩⟩
    have htail : ∀ o ∈ closure cs, o ∈ closure nd.seen ++ closure (c :: cs) := by
      intro o ho
      refine List.mem_append_right _ ?_
      simp only [closure, List.flatMap_cons, List.mem_append] at ho ⊢
      exact Or.inr ho
    unfold releaseAll
    rw [releaseAllCarried_cons]
    rw [hp, Bool.and_true]
    split
    · dsimp only
      rw [ih]
      intro o ho o' ho' hs hs'
      have hsub : ∀ x ∈ closure (nd.seen ++ [c]) ++ closure cs,
          x ∈ closure nd.seen ++ closure (c :: cs) := by
        intro x hx
        rw [closure_append, List.mem_append, List.mem_append] at hx
        rcases hx with (hx | hx) | hx
        · exact hseen x hx
        · refine List.mem_append_right _ ?_
          simp only [closure, List.flatMap_cons, List.flatMap_nil, List.append_nil,
            List.mem_append] at hx ⊢
          exact Or.inl hx
        · exact htail x hx
      exact h o (hsub o ho) o' (hsub o' ho') hs hs'
    · rw [ih]
      intro o ho o' ho' hs hs'
      have hsub : ∀ x ∈ closure nd.seen ++ closure cs,
          x ∈ closure nd.seen ++ closure (c :: cs) := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hseen x hx
        · exact htail x hx
      exact h o (hsub o ho) o' (hsub o' ho') hs hs'

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

/-- Two own-signed objects released by one tick never conflict. -/
theorem tick_noConflict {i : Nat} {v : V} {t : Time} (he : rho.events[i]? = some (.tick v t))
    {c c' : (protoOf F E).Object} (hc : c ∈ rho.releasesAt i) (hc' : c' ∈ rho.releasesAt i)
    (hs : c.signer? = some (rho.ownKey v)) (hs' : c'.signer? = some (rho.ownKey v)) :
    (protoOf F E).conflicts c c' = false := by
  simp only [releasesAt, he] at hc hc'
  obtain ⟨cs, -, h2, -⟩ := rho.tick_flat (rho.stateBefore i v) v t
  rw [h2] at hc hc'
  exact releaseAll_noConflict hc hc' hs hs'

/-- An own-signed object released by a tick never conflicts, in either order,
with an own-signed object in the closure of the node's `seen` before it. -/
theorem tick_noConflict_seen {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) {c o : (protoOf F E).Object}
    (hc : c ∈ rho.releasesAt i) (ho : o ∈ closure (rho.stateBefore i v).seen)
    (hs : c.signer? = some (rho.ownKey v)) (hs' : o.signer? = some (rho.ownKey v)) :
    (protoOf F E).conflicts c o = false ∧ (protoOf F E).conflicts o c = false := by
  simp only [releasesAt, he] at hc
  obtain ⟨cs, -, h2, -⟩ := rho.tick_flat (rho.stateBefore i v) v t
  rw [h2] at hc
  exact releaseAll_noConflict_seen hc ho hs hs'

/-- Two own-signed objects released by one delivery never conflict. -/
theorem deliver_noConflict {i : Nat} {v : V} {p : (protoOf F E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v p t))
    {c c' : (protoOf F E).Object} (hc : c ∈ rho.releasesAt i) (hc' : c' ∈ rho.releasesAt i)
    (hs : c.signer? = some (rho.ownKey v)) (hs' : c'.signer? = some (rho.ownKey v)) :
    (protoOf F E).conflicts c c' = false := by
  simp only [releasesAt, he] at hc hc'
  obtain ⟨cs, -, h2, -⟩ := rho.deliver_flat (rho.stateBefore i v) v p t
  rw [h2] at hc hc'
  exact releaseAll_noConflict hc hc' hs hs'

/-- An own-signed object released by a delivery never conflicts, in either
order, with an own-signed object in the closure of the node's `seen` before
it. -/
theorem deliver_noConflict_seen {i : Nat} {v : V} {p : (protoOf F E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v p t)) {c o : (protoOf F E).Object}
    (hc : c ∈ rho.releasesAt i) (ho : o ∈ closure (rho.stateBefore i v).seen)
    (hs : c.signer? = some (rho.ownKey v)) (hs' : o.signer? = some (rho.ownKey v)) :
    (protoOf F E).conflicts c o = false ∧ (protoOf F E).conflicts o c = false := by
  simp only [releasesAt, he] at hc
  obtain ⟨cs, -, h2, -⟩ := rho.deliver_flat (rho.stateBefore i v) v p t
  rw [h2] at hc
  exact releaseAll_noConflict_seen hc (closure_mono (fun x hx => List.mem_append_left _ hx) ho)
    hs hs'

/-- No honest validator is slashable on what the honest nodes saw, for every
protocol: both conflicting objects were released by the validator itself, and
the later one (by event, or by position within one tick or delivery) was
checked against the earlier one. -/
theorem not_slashable_of_released {A : Set (protoOf F E).Object} {x : V}
    (hr : ∀ o ∈ A, rho.signerOf o = some x →
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
    · exact rho.tick_noConflict he hc hc' hs hs'
    · exact rho.deliver_noConflict he hc hc' hs hs'
  have ncs {i t c o} (hi : rho.SendsAt x i t) (hc : c ∈ rho.releasesAt i)
      (ho : o ∈ closure (rho.stateBefore i x).seen) (hs : c.signer? = some (rho.ownKey x))
      (hs' : o.signer? = some (rho.ownKey x)) :
      (protoOf F E).conflicts c o = false ∧ (protoOf F E).conflicts o c = false := by
    rcases hi with he | ⟨p, he⟩
    · exact rho.tick_noConflict_seen he hc ho hs hs'
    · exact rho.deliver_noConflict_seen he hc ho hs hs'
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

theorem honestNeverSlashed (hv : rho.ExecutionValid) :
    ∀ v d, v ∉ rho.faultyAt d →
      ¬ rho.Slashable {o | ∃ w i, i ≤ rho.events.length ∧
        rho.cutTime i ≤ d ∧ o ∈ rho.ViewIdx w i} v := by
  intro v d hvh
  exact rho.not_slashable_of_released fun _ ho hs => rho.released_of_observed hv ho hvh hs

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

/-- L0 non-framing holds for every model system. -/
theorem sysOf_nonFraming (O : OutputSchema) (F : ProtocolFamily O) (V : Type) [Fintype V]
    [DecidableEq V] : (sysOf O F V).HoldsAlways (sysOf O F V).NonFraming := by
  rintro ⟨E, rho⟩ hv v d hvh hconv
  apply rho.honestNeverSlashed hv v d hvh
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

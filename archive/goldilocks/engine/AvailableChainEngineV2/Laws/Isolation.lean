module
public import AvailableChainEngineV2.Engine.Run
public import AvailableChainEngineV2.Conditions.Committees

@[expose] public section

/-! Isolation laws (design §2 E5; plan 2a, Task 3). The law shapes are those of
`Isolated` and `foldl_recordOwn_base` in the pre-2a prototype `Sketch.lean`
(deleted at the 2a gate; see git history), on the v2 spec. -/

namespace AvailableChain.V2

open AvailableChain

variable {In : Type} {P : ProtocolSpec In}

/-- An object of the AP projection: an object signed with a seat of an AP
label (`F.ap`), or an unsigned object. Unsigned objects belong to the
projection because it emits unsigned gossip (`Isolation.gossip_base`; for
example the SA-PC proposal certificates). -/
def LabelFamilies.APObject (F : LabelFamilies P) (o : P.Object) : Prop :=
  match o.auth with
  | .seat ℓ _ => F.ap ℓ
  | .none => True

@[simp] theorem LabelFamilies.apObject_seat (F : LabelFamilies P) (ℓ : P.Label)
    (i : Fin (P.seats ℓ)) (p : P.Payload) : F.APObject ⟨.seat ℓ i, p⟩ ↔ F.ap ℓ :=
  Iff.rfl

@[simp] theorem LabelFamilies.apObject_none (F : LabelFamilies P) (p : P.Payload) :
    F.APObject ⟨.none, p⟩ :=
  trivial

/-- The isolation laws of a protocol with the label families `F` (design §2
E5). `base` is the part of the state that the AP protocol reads.

* `clock` and `process` change `base` as a function of `base` and of the time
  or the object (`clockB`, `processB`); `recordOwn` does not change `base`.
* `act` on the AP labels (`actB`, with the input) and all `gossip`
  (`gossipB`) factor through `base`.
* The hooks restricted to objects of the AP projection (`F.APObject`: AP
  labels and unsigned objects) factor through `base` (`depsB`,
  `processedB`, `excludesB`, `handlesB`; law `hooks_base`).
* Separation: AP labels and the fresh labels are not self-visible.

The E6 restore law is not a field. Plan 2c adds it as a separate structure
`RestoreLaw` with both directions: `restore_base` (the base after a restore
depends only on the base-visible part of the durable data) and
`durable_base` (that part depends only on the base). -/
structure Isolation (P : ProtocolSpec In) (F : LabelFamilies P) where
  Base : Type
  base : P.State → Base
  clockB : Base → Time → Base
  clock_base : ∀ st t, base (P.clock st t) = clockB (base st) t
  processB : Base → P.Object → Base
  process_base : ∀ st o, base (P.process st o) = processB (base st) o
  recordOwn_base : ∀ st o, base (P.recordOwn st o) = base st
  actB : Base → P.Label → In → Option P.Payload
  act_base : ∀ st ℓ x, F.ap ℓ → P.act st ℓ x = actB (base st) ℓ x
  gossipB : Base → Time → List P.Payload
  gossip_base : ∀ st t, P.gossip st t = gossipB (base st) t
  /-- The factor of `depsPresent` on `Base`. -/
  depsB : Base → P.Object → Bool
  /-- The factor of `processed` on `Base`. -/
  processedB : Base → P.Object → Bool
  /-- The factor of `excludes` on `Base`. -/
  excludesB : Base → P.Object → Bool
  /-- The factor of `handles` on `Base`. `handles` is a proposition, so its
  factor is a relation. -/
  handlesB : Base → P.Object → P.Object → Prop
  /-- Hook projection (design §2 E5): on objects of the AP projection
  (`F.APObject`), `depsPresent`, `processed` and `excludes` equal their
  factors at `base st`; `handles` does when both objects are objects of the
  AP projection (the law is an `↔`). The factors are data, like `clockB`, so
  the AP projection can use them directly. `wellFormed` reads no state, so it
  has no factor. `Isolation.hooks_congr` gives the form for two states with
  equal bases. -/
  hooks_base : ∀ st o, F.APObject o →
    P.depsPresent st o = depsB (base st) o ∧ P.processed st o = processedB (base st) o ∧
      P.excludes st o = excludesB (base st) o ∧
      ∀ o', F.APObject o' → (P.handles st o o' ↔ handlesB (base st) o o')
  /-- Separation (design §2 E5): no AP label and no label of the designated
  fresh family is self-visible. `F.linked` labels may be self-visible.

  A one-seat label (a proposal) cannot be in `F.fresh` unless `|V| = 1`:
  regimes put `CStar` on `F.fresh`, and `CStar` needs `seats ℓ = |V|`
  (`CStar.seats_eq`). The FG-SA reference assignment (DC N9): HEAD labels in
  `ap` and `fresh`; FG labels in `linked`; proposal labels in `ap`, with
  `SingleSeat`. -/
  separation : ∀ ℓ, F.ap ℓ ∨ F.fresh ℓ → P.selfVisible ℓ = false

namespace Isolation

variable {F : LabelFamilies P}

/-- The own record does not move the base (the pre-2a prototype `Sketch.lean`
(deleted at the 2a gate; see git history), `foldl_recordOwn_base`). -/
theorem foldl_recordOwn_base (iso : Isolation P F) :
    ∀ (l : List P.Object) (s : P.State), iso.base (l.foldl P.recordOwn s) = iso.base s := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons o rest ih =>
      intro s
      simp only [List.foldl_cons]
      rw [ih]
      exact iso.recordOwn_base s o

/-- The base after a tick is the clock update of the base before it. The
released objects, AP payloads included, are not a further dependency. -/
theorem base_tick {V : Type} [DecidableEq V] (iso : Isolation P F) (E : Generic.Env V)
    (rho : Run V P) (st : P.State) (v : V) (t : Time) :
    iso.base (tick E rho st v t).1 = iso.clockB (iso.base st) t := by
  rw [tick_decomp, iso.foldl_recordOwn_base, iso.clock_base]

/-- The hook projection for two states with equal bases. -/
theorem hooks_congr (iso : Isolation P F) {st st' : P.State}
    (h : iso.base st = iso.base st') {o : P.Object} (ho : F.APObject o) :
    P.depsPresent st o = P.depsPresent st' o ∧ P.processed st o = P.processed st' o ∧
      P.excludes st o = P.excludes st' o ∧
      ∀ o', F.APObject o' → (P.handles st o o' ↔ P.handles st' o o') := by
  obtain ⟨hd, hp, hx, hh⟩ := iso.hooks_base st o ho
  obtain ⟨hd', hp', hx', hh'⟩ := iso.hooks_base st' o ho
  refine ⟨by rw [hd, hd', h], by rw [hp, hp', h], by rw [hx, hx', h], fun o' ho' => ?_⟩
  rw [hh o' ho', hh' o' ho', h]

/-- A self-visible label is not an AP label and not a fresh label. -/
theorem not_ap_of_selfVisible (iso : Isolation P F) {ℓ : P.Label}
    (h : P.selfVisible ℓ = true) : ¬ F.ap ℓ ∧ ¬ F.fresh ℓ := by
  refine ⟨fun ha => ?_, fun hf => ?_⟩
  · rw [iso.separation ℓ (Or.inl ha)] at h; exact Bool.false_ne_true h
  · rw [iso.separation ℓ (Or.inr hf)] at h; exact Bool.false_ne_true h

end Isolation

end AvailableChain.V2

end
